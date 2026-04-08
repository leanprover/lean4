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
extern lean_object* l_instMonadBaseIO;
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
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
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ":static"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_value;
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " (without exports)"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1_value;
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " (with exports)"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2_value;
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
lean_inc_ref_n(v_root_142_, 2);
v_modSet_164_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_modSet_144_, v_root_142_, v___x_163_);
v___x_165_ = l_Lake_Module_importsFacet;
lean_inc(v_name_161_);
lean_inc(v_keyName_162_);
v___x_166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_166_, 0, v_keyName_162_);
lean_ctor_set(v___x_166_, 1, v_name_161_);
v___x_167_ = l_Lake_Module_keyword;
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
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec(v___y_246_);
lean_dec(v___y_245_);
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
lean_dec_ref(v_a_262_);
lean_dec(v_a_261_);
lean_dec(v_a_260_);
lean_dec(v_a_259_);
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
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec(v___y_331_);
lean_dec(v___y_330_);
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
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec(v___y_410_);
lean_dec(v___y_409_);
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
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec(v_a_441_);
lean_dec(v_a_440_);
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
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec(v___y_579_);
lean_dec(v___y_578_);
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
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec(v_a_668_);
lean_dec(v_a_667_);
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
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec(v___y_719_);
lean_dec(v___y_718_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(uint8_t v_shouldExport_725_, lean_object* v___x_726_, lean_object* v_bs_727_, lean_object* v_a_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_lib_736_; lean_object* v_config_737_; lean_object* v_nativeFacets_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_741_; size_t v_sz_742_; size_t v___x_743_; lean_object* v___x_196942__overap_744_; lean_object* v___x_745_; 
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
v___x_196942__overap_744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_726_, v___f_739_, v_sz_742_, v___x_743_, v___x_741_);
lean_inc_ref(v___y_733_);
lean_inc(v___y_732_);
lean_inc(v___y_731_);
lean_inc(v___y_730_);
v___x_745_ = lean_apply_7(v___x_196942__overap_744_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, lean_box(0));
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
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec(v___y_762_);
lean_dec(v___y_761_);
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
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec(v___y_785_);
lean_dec(v___y_784_);
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
lean_dec_ref(v___y_862_);
lean_dec_ref(v___x_860_);
v_toContext_869_ = lean_ctor_get(v___y_866_, 1);
v_lakeEnv_870_ = lean_ctor_get(v_toContext_869_, 1);
v_lean_871_ = lean_ctor_get(v_lakeEnv_870_, 1);
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
v_ar_880_ = lean_ctor_get(v_lean_871_, 13);
lean_inc_ref(v_ar_880_);
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
lean_dec_ref(v___y_862_);
lean_dec_ref(v___x_860_);
v___x_908_ = l_System_Platform_isWindows;
if (v___x_908_ == 0)
{
lean_object* v_toContext_909_; lean_object* v_lakeEnv_910_; lean_object* v_lean_911_; lean_object* v_log_912_; uint8_t v_action_913_; uint8_t v_wantsRebuild_914_; lean_object* v_trace_915_; lean_object* v_buildTime_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_946_; 
v_toContext_909_ = lean_ctor_get(v___y_866_, 1);
v_lakeEnv_910_ = lean_ctor_get(v_toContext_909_, 1);
v_lean_911_ = lean_ctor_get(v_lakeEnv_910_, 1);
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
v_ar_920_ = lean_ctor_get(v_lean_911_, 13);
lean_inc_ref(v_ar_920_);
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
v_lakeEnv_948_ = lean_ctor_get(v_toContext_947_, 1);
v_lean_949_ = lean_ctor_get(v_lakeEnv_948_, 1);
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
v_ar_958_ = lean_ctor_get(v_lean_949_, 13);
lean_inc_ref(v_ar_958_);
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
lean_dec_ref(v___y_862_);
lean_dec_ref(v_oFiles_857_);
v_a_994_ = v___y_867_;
goto v___jp_993_;
}
else
{
size_t v___x_1053_; lean_object* v___x_197100__overap_1054_; lean_object* v___x_1055_; 
v___x_1053_ = lean_usize_of_nat(v___x_1048_);
v___x_197100__overap_1054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1046_, v___f_1050_, v_oFiles_857_, v___x_861_, v___x_1053_, v___x_1051_);
lean_inc_ref(v___y_866_);
lean_inc(v___y_865_);
lean_inc(v___y_864_);
lean_inc(v___y_863_);
v___x_1055_ = lean_apply_7(v___x_197100__overap_1054_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, lean_box(0));
v___y_1041_ = v___x_1055_;
goto v___jp_1040_;
}
}
else
{
size_t v___x_1056_; lean_object* v___x_197102__overap_1057_; lean_object* v___x_1058_; 
v___x_1056_ = lean_usize_of_nat(v___x_1048_);
v___x_197102__overap_1057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1046_, v___f_1050_, v_oFiles_857_, v___x_861_, v___x_1056_, v___x_1051_);
lean_inc_ref(v___y_866_);
lean_inc(v___y_865_);
lean_inc(v___y_864_);
lean_inc(v___y_863_);
v___x_1058_ = lean_apply_7(v___x_197102__overap_1057_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, lean_box(0));
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
uint8_t v_bootstrap_boxed_1107_; uint8_t v_shouldExport_boxed_1108_; uint8_t v___x_197474__boxed_1109_; size_t v___x_197476__boxed_1110_; lean_object* v_res_1111_; 
v_bootstrap_boxed_1107_ = lean_unbox(v_bootstrap_1093_);
v_shouldExport_boxed_1108_ = lean_unbox(v_shouldExport_1096_);
v___x_197474__boxed_1109_ = lean_unbox(v___x_1097_);
v___x_197476__boxed_1110_ = lean_unbox_usize(v___x_1099_);
lean_dec(v___x_1099_);
v_res_1111_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(v_bootstrap_boxed_1107_, v___y_1094_, v_oFiles_1095_, v_shouldExport_boxed_1108_, v___x_197474__boxed_1109_, v___x_1098_, v___x_197476__boxed_1110_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec(v___y_1101_);
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
uint8_t v_bootstrap_boxed_1168_; uint8_t v_shouldExport_boxed_1169_; uint8_t v___x_197899__boxed_1170_; size_t v___x_197901__boxed_1171_; lean_object* v_res_1172_; 
v_bootstrap_boxed_1168_ = lean_unbox(v_bootstrap_1154_);
v_shouldExport_boxed_1169_ = lean_unbox(v_shouldExport_1156_);
v___x_197899__boxed_1170_ = lean_unbox(v___x_1157_);
v___x_197901__boxed_1171_ = lean_unbox_usize(v___x_1159_);
lean_dec(v___x_1159_);
v_res_1172_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(v_bootstrap_boxed_1168_, v___y_1155_, v_shouldExport_boxed_1169_, v___x_197899__boxed_1170_, v___x_1158_, v___x_197901__boxed_1171_, v_oFiles_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec(v___y_1162_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object* v___x_1177_, lean_object* v___x_1178_, lean_object* v_config_1179_, lean_object* v_config_1180_, lean_object* v___x_1181_, lean_object* v___f_1182_, uint8_t v_shouldExport_1183_, uint8_t v___x_1184_, lean_object* v___x_1185_, lean_object* v___x_1186_, lean_object* v_dir_1187_, lean_object* v_self_1188_, lean_object* v___f_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___y_1198_; lean_object* v___y_1199_; size_t v___y_1200_; uint8_t v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v_a_1218_; lean_object* v_a_1219_; lean_object* v___y_1263_; lean_object* v___x_1275_; 
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
size_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_197239__overap_1288_; lean_object* v___x_1289_; 
v___x_1286_ = ((size_t)0ULL);
v___x_1287_ = lean_usize_of_nat(v___x_1283_);
lean_inc_ref(v___x_1181_);
v___x_197239__overap_1288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1181_, v___f_1189_, v_a_1279_, v___x_1286_, v___x_1287_, v___x_1282_);
lean_inc_ref(v___y_1194_);
lean_inc(v___y_1193_);
lean_inc(v___y_1192_);
lean_inc(v___x_1178_);
lean_inc_ref(v___y_1190_);
v___x_1289_ = lean_apply_7(v___x_197239__overap_1288_, v___y_1190_, v___x_1178_, v___y_1192_, v___y_1193_, v___y_1194_, v_a_1280_, lean_box(0));
v___y_1263_ = v___x_1289_;
goto v___jp_1262_;
}
}
else
{
size_t v___x_1290_; size_t v___x_1291_; lean_object* v___x_197242__overap_1292_; lean_object* v___x_1293_; 
v___x_1290_ = ((size_t)0ULL);
v___x_1291_ = lean_usize_of_nat(v___x_1283_);
lean_inc_ref(v___x_1181_);
v___x_197242__overap_1292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1181_, v___f_1189_, v_a_1279_, v___x_1290_, v___x_1291_, v___x_1282_);
lean_inc_ref(v___y_1194_);
lean_inc(v___y_1193_);
lean_inc(v___y_1192_);
lean_inc(v___x_1178_);
lean_inc_ref(v___y_1190_);
v___x_1293_ = lean_apply_7(v___x_197242__overap_1292_, v___y_1190_, v___x_1178_, v___y_1192_, v___y_1193_, v___y_1194_, v_a_1280_, lean_box(0));
v___y_1263_ = v___x_1293_;
goto v___jp_1262_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
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
v___x_1204_ = lean_box(v___y_1201_);
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
lean_dec(v___x_1178_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___y_1199_);
return v___x_1216_;
}
v___jp_1217_:
{
lean_object* v_toLeanConfig_1220_; lean_object* v_toLeanConfig_1221_; uint8_t v_bootstrap_1222_; lean_object* v_buildDir_1223_; lean_object* v_nativeLibDir_1224_; lean_object* v_moreLinkObjs_1225_; lean_object* v_moreLinkObjs_1226_; lean_object* v___x_1227_; size_t v_sz_1228_; size_t v___x_1229_; lean_object* v___x_197179__overap_1230_; lean_object* v___x_1231_; 
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
v___x_197179__overap_1230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1181_, v___f_1182_, v_sz_1228_, v___x_1229_, v___x_1227_);
lean_inc_ref(v___y_1194_);
lean_inc(v___y_1193_);
lean_inc(v___y_1192_);
lean_inc(v___x_1178_);
lean_inc_ref(v___y_1190_);
v___x_1231_ = lean_apply_7(v___x_197179__overap_1230_, v___y_1190_, v___x_1178_, v___y_1192_, v___y_1193_, v___y_1194_, v_a_1219_, lean_box(0));
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
v___y_1199_ = v_a_1233_;
v___y_1200_ = v___x_1229_;
v___y_1201_ = v_bootstrap_1222_;
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
v___y_1199_ = v_a_1242_;
v___y_1200_ = v___x_1229_;
v___y_1201_ = v_bootstrap_1222_;
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
uint8_t v_shouldExport_boxed_1332_; uint8_t v___x_198003__boxed_1333_; lean_object* v_res_1334_; 
v_shouldExport_boxed_1332_ = lean_unbox(v_shouldExport_1318_);
v___x_198003__boxed_1333_ = lean_unbox(v___x_1319_);
v_res_1334_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(v___x_1312_, v___x_1313_, v_config_1314_, v_config_1315_, v___x_1316_, v___f_1317_, v_shouldExport_boxed_1332_, v___x_198003__boxed_1333_, v___x_1320_, v___x_1321_, v_dir_1322_, v_self_1323_, v___f_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec(v_config_1315_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object* v_self_1338_, uint8_t v_shouldExport_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v_toApplicative_1348_; lean_object* v_toBind_1349_; lean_object* v_toFunctor_1350_; lean_object* v_toPure_1351_; lean_object* v___f_1352_; lean_object* v___f_1353_; lean_object* v___f_1354_; lean_object* v___f_1355_; lean_object* v___x_1356_; lean_object* v___f_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_toBuildConfig_1365_; lean_object* v_registeredJobs_1366_; uint8_t v_verbosity_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___f_1370_; uint8_t v___x_1371_; uint8_t v___x_1372_; uint8_t v___x_1373_; lean_object* v___y_1375_; 
v___x_1347_ = l_instMonadBaseIO;
v_toApplicative_1348_ = lean_ctor_get(v___x_1347_, 0);
v_toBind_1349_ = lean_ctor_get(v___x_1347_, 1);
v_toFunctor_1350_ = lean_ctor_get(v_toApplicative_1348_, 0);
v_toPure_1351_ = lean_ctor_get(v_toApplicative_1348_, 1);
lean_inc_n(v_toBind_1349_, 3);
lean_inc_n(v_toPure_1351_, 5);
v___f_1352_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1352_, 0, v_toPure_1351_);
lean_closure_set(v___f_1352_, 1, v_toBind_1349_);
v___f_1353_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1353_, 0, v_toPure_1351_);
lean_closure_set(v___f_1353_, 1, v_toBind_1349_);
lean_inc_ref(v___f_1352_);
v___f_1354_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1354_, 0, v_toPure_1351_);
lean_closure_set(v___f_1354_, 1, v___f_1352_);
lean_inc_ref_n(v_toFunctor_1350_, 2);
v___f_1355_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1355_, 0, v_toFunctor_1350_);
lean_closure_set(v___f_1355_, 1, v_toPure_1351_);
lean_closure_set(v___f_1355_, 2, v_toBind_1349_);
v___x_1356_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1350_);
v___f_1357_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1357_, 0, v_toPure_1351_);
v___x_1358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
lean_ctor_set(v___x_1358_, 1, v___f_1357_);
lean_ctor_set(v___x_1358_, 2, v___f_1355_);
lean_ctor_set(v___x_1358_, 3, v___f_1354_);
lean_ctor_set(v___x_1358_, 4, v___f_1353_);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v___f_1352_);
v___x_1360_ = l_ReaderT_instMonad___redArg(v___x_1359_);
v___x_1361_ = l_StateRefT_x27_instMonad___redArg(v___x_1360_);
v___x_1362_ = l_ReaderT_instMonad___redArg(v___x_1361_);
v___x_1363_ = l_ReaderT_instMonad___redArg(v___x_1362_);
lean_inc_ref(v___x_1363_);
v___x_1364_ = l_Lake_EquipT_instMonad___redArg(v___x_1363_);
v_toBuildConfig_1365_ = lean_ctor_get(v_a_1344_, 0);
v_registeredJobs_1366_ = lean_ctor_get(v_a_1344_, 3);
v_verbosity_1367_ = lean_ctor_get_uint8(v_toBuildConfig_1365_, sizeof(void*)*2 + 3);
v___x_1368_ = l_Lake_instDataKindFilePath;
v___x_1369_ = lean_box(v_shouldExport_1339_);
lean_inc_ref(v___x_1364_);
v___f_1370_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1370_, 0, v___x_1369_);
lean_closure_set(v___f_1370_, 1, v___x_1364_);
v___x_1371_ = 2;
v___x_1372_ = l_Lake_instDecidableEqVerbosity(v_verbosity_1367_, v___x_1371_);
v___x_1373_ = 1;
if (v___x_1372_ == 0)
{
lean_object* v___x_1421_; 
v___x_1421_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_1375_ = v___x_1421_;
goto v___jp_1374_;
}
else
{
if (v_shouldExport_1339_ == 0)
{
lean_object* v___x_1422_; 
v___x_1422_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___y_1375_ = v___x_1422_;
goto v___jp_1374_;
}
else
{
lean_object* v___x_1423_; 
v___x_1423_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_1375_ = v___x_1423_;
goto v___jp_1374_;
}
}
v___jp_1374_:
{
lean_object* v_pkg_1376_; lean_object* v_name_1377_; lean_object* v_config_1378_; lean_object* v_keyName_1379_; lean_object* v_dir_1380_; lean_object* v_config_1381_; lean_object* v___f_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___f_1390_; lean_object* v___x_1391_; 
v_pkg_1376_ = lean_ctor_get(v_self_1338_, 0);
v_name_1377_ = lean_ctor_get(v_self_1338_, 1);
lean_inc_n(v_name_1377_, 2);
v_config_1378_ = lean_ctor_get(v_self_1338_, 2);
lean_inc(v_config_1378_);
v_keyName_1379_ = lean_ctor_get(v_pkg_1376_, 2);
v_dir_1380_ = lean_ctor_get(v_pkg_1376_, 4);
lean_inc_ref(v_dir_1380_);
v_config_1381_ = lean_ctor_get(v_pkg_1376_, 6);
lean_inc_ref(v_config_1381_);
lean_inc_ref_n(v_pkg_1376_, 2);
v___f_1382_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(v___f_1382_, 0, v___x_1368_);
lean_closure_set(v___f_1382_, 1, v_pkg_1376_);
v___x_1383_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_1379_);
v___x_1384_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_keyName_1379_);
lean_ctor_set(v___x_1384_, 1, v_name_1377_);
v___x_1385_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_1338_);
v___x_1386_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1384_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
lean_ctor_set(v___x_1386_, 2, v_self_1338_);
lean_ctor_set(v___x_1386_, 3, v___x_1383_);
v___x_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1387_, 0, v_pkg_1376_);
v___x_1388_ = lean_box(v_shouldExport_1339_);
v___x_1389_ = lean_box(v___x_1373_);
v___f_1390_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed), 20, 13);
lean_closure_set(v___f_1390_, 0, v___x_1386_);
lean_closure_set(v___f_1390_, 1, v___x_1387_);
lean_closure_set(v___f_1390_, 2, v_config_1381_);
lean_closure_set(v___f_1390_, 3, v_config_1378_);
lean_closure_set(v___f_1390_, 4, v___x_1364_);
lean_closure_set(v___f_1390_, 5, v___f_1382_);
lean_closure_set(v___f_1390_, 6, v___x_1388_);
lean_closure_set(v___f_1390_, 7, v___x_1389_);
lean_closure_set(v___f_1390_, 8, v___x_1363_);
lean_closure_set(v___f_1390_, 9, v___x_1368_);
lean_closure_set(v___f_1390_, 10, v_dir_1380_);
lean_closure_set(v___f_1390_, 11, v_self_1338_);
lean_closure_set(v___f_1390_, 12, v___f_1370_);
v___x_1391_ = l_Lake_ensureJob___redArg(v___x_1368_, v___f_1390_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1420_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_a_1393_ = lean_ctor_get(v___x_1391_, 1);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1395_ = v___x_1391_;
v_isShared_1396_ = v_isSharedCheck_1420_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1420_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v_task_1397_; lean_object* v_kind_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1418_; 
v_task_1397_ = lean_ctor_get(v_a_1392_, 0);
v_kind_1398_ = lean_ctor_get(v_a_1392_, 1);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_a_1392_);
if (v_isSharedCheck_1418_ == 0)
{
lean_object* v_unused_1419_; 
v_unused_1419_ = lean_ctor_get(v_a_1392_, 2);
lean_dec(v_unused_1419_);
v___x_1400_ = v_a_1392_;
v_isShared_1401_ = v_isSharedCheck_1418_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_kind_1398_);
lean_inc(v_task_1397_);
lean_dec(v_a_1392_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1418_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; lean_object* v_job_1409_; 
v___x_1402_ = lean_st_ref_take(v_registeredJobs_1366_);
v___x_1403_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1377_, v___x_1373_);
v___x_1404_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0));
v___x_1405_ = lean_string_append(v___x_1403_, v___x_1404_);
v___x_1406_ = lean_string_append(v___x_1405_, v___y_1375_);
v___x_1407_ = 0;
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 2, v___x_1406_);
v_job_1409_ = v___x_1400_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_task_1397_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_kind_1398_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v___x_1406_);
v_job_1409_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1415_; 
lean_ctor_set_uint8(v_job_1409_, sizeof(void*)*3, v___x_1407_);
lean_inc_ref(v_job_1409_);
v___x_1410_ = l_Lake_Job_toOpaque___redArg(v_job_1409_);
v___x_1411_ = lean_array_push(v___x_1402_, v___x_1410_);
v___x_1412_ = lean_st_ref_set(v_registeredJobs_1366_, v___x_1411_);
v___x_1413_ = l_Lake_Job_renew___redArg(v_job_1409_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v___x_1413_);
v___x_1415_ = v___x_1395_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_a_1393_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
else
{
lean_dec(v_name_1377_);
return v___x_1391_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object* v_self_1424_, lean_object* v_shouldExport_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
uint8_t v_shouldExport_boxed_1433_; lean_object* v_res_1434_; 
v_shouldExport_boxed_1433_ = lean_unbox(v_shouldExport_1425_);
v_res_1434_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1424_, v_shouldExport_boxed_1433_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_);
lean_dec_ref(v_a_1430_);
lean_dec(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec(v_a_1427_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t v_fmt_1435_, lean_object* v_a_1436_){
_start:
{
if (v_fmt_1435_ == 0)
{
return v_a_1436_;
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = l_Lake_mkRelPathString(v_a_1436_);
v___x_1438_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
v___x_1439_ = l_Lean_Json_compress(v___x_1438_);
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object* v_fmt_1440_, lean_object* v_a_1441_){
_start:
{
uint8_t v_fmt_boxed_1442_; lean_object* v_res_1443_; 
v_fmt_boxed_1442_ = lean_unbox(v_fmt_1440_);
v_res_1443_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_boxed_1442_, v_a_1441_);
return v_res_1443_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2(void){
_start:
{
uint8_t v___x_1446_; lean_object* v_name_1447_; lean_object* v___x_1448_; 
v___x_1446_ = 1;
v_name_1447_ = l_Lake_instDataKindFilePath;
v___x_1448_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1447_, v___x_1446_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* v_defaultPkg_1452_, lean_object* v_self_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
uint8_t v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = 1;
lean_inc_ref_n(v_self_1453_, 2);
v___x_1462_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1452_, v_self_1453_, v_self_1453_, v___x_1461_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v_snd_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1505_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
v_snd_1464_ = lean_ctor_get(v_a_1463_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_a_1463_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v_a_1463_, 0);
lean_dec(v_unused_1506_);
v___x_1466_ = v_a_1463_;
v_isShared_1467_ = v_isSharedCheck_1505_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_snd_1464_);
lean_dec(v_a_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1505_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1503_; 
v_a_1468_ = lean_ctor_get(v___x_1462_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v___x_1462_, 0);
lean_dec(v_unused_1504_);
v___x_1470_ = v___x_1462_;
v_isShared_1471_ = v_isSharedCheck_1503_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1462_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1503_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v_kind_1472_; lean_object* v_name_1473_; lean_object* v___y_1475_; uint8_t v___x_1493_; 
v_kind_1472_ = lean_ctor_get(v_snd_1464_, 1);
v_name_1473_ = l_Lake_instDataKindFilePath;
v___x_1493_ = lean_name_eq(v_kind_1472_, v_name_1473_);
if (v___x_1493_ == 0)
{
uint8_t v___x_1494_; 
lean_inc(v_kind_1472_);
lean_del_object(v___x_1466_);
lean_dec(v_snd_1464_);
v___x_1494_ = l_Lean_Name_isAnonymous(v_kind_1472_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1495_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1496_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1472_, v___x_1461_);
v___x_1497_ = lean_string_append(v___x_1495_, v___x_1496_);
lean_dec_ref(v___x_1496_);
v___x_1498_ = lean_string_append(v___x_1497_, v___x_1495_);
v___y_1475_ = v___x_1498_;
goto v___jp_1474_;
}
else
{
lean_object* v___x_1499_; 
lean_dec(v_kind_1472_);
v___x_1499_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1475_ = v___x_1499_;
goto v___jp_1474_;
}
}
else
{
lean_object* v___x_1501_; 
lean_del_object(v___x_1470_);
lean_dec_ref(v_self_1453_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 1, v_a_1468_);
lean_ctor_set(v___x_1466_, 0, v_snd_1464_);
v___x_1501_ = v___x_1466_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_snd_1464_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_a_1468_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
v___jp_1474_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1476_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1477_ = l_Lake_PartialBuildKey_toString(v_self_1453_);
v___x_1478_ = lean_string_append(v___x_1476_, v___x_1477_);
lean_dec_ref(v___x_1477_);
v___x_1479_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1480_ = lean_string_append(v___x_1478_, v___x_1479_);
v___x_1481_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
v___x_1482_ = lean_string_append(v___x_1480_, v___x_1481_);
v___x_1483_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1484_ = lean_string_append(v___x_1482_, v___x_1483_);
v___x_1485_ = lean_string_append(v___x_1484_, v___y_1475_);
lean_dec_ref(v___y_1475_);
v___x_1486_ = 3;
v___x_1487_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set_uint8(v___x_1487_, sizeof(void*)*1, v___x_1486_);
v___x_1488_ = lean_array_get_size(v_a_1468_);
v___x_1489_ = lean_array_push(v_a_1468_, v___x_1487_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set_tag(v___x_1470_, 1);
lean_ctor_set(v___x_1470_, 1, v___x_1489_);
lean_ctor_set(v___x_1470_, 0, v___x_1488_);
v___x_1491_ = v___x_1470_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec_ref(v_self_1453_);
v_a_1507_ = lean_ctor_get(v___x_1462_, 0);
v_a_1508_ = lean_ctor_get(v___x_1462_, 1);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1462_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_inc(v_a_1507_);
lean_dec(v___x_1462_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1507_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* v_defaultPkg_1516_, lean_object* v_self_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1516_, v_self_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
lean_dec_ref(v_a_1522_);
lean_dec(v_a_1521_);
lean_dec(v_a_1520_);
lean_dec(v_a_1519_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* v___x_1526_, size_t v_sz_1527_, size_t v_i_1528_, lean_object* v_bs_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
uint8_t v___x_1537_; 
v___x_1537_ = lean_usize_dec_lt(v_i_1528_, v_sz_1527_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; 
lean_dec_ref(v___y_1530_);
lean_dec_ref(v___x_1526_);
v___x_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1538_, 0, v_bs_1529_);
lean_ctor_set(v___x_1538_, 1, v___y_1535_);
return v___x_1538_;
}
else
{
lean_object* v_v_1539_; lean_object* v___x_1540_; 
v_v_1539_ = lean_array_uget_borrowed(v_bs_1529_, v_i_1528_);
lean_inc_ref(v___y_1530_);
lean_inc(v_v_1539_);
lean_inc_ref(v___x_1526_);
v___x_1540_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1526_, v_v_1539_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v_a_1542_; lean_object* v___x_1543_; lean_object* v_bs_x27_1544_; size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
v_a_1542_ = lean_ctor_get(v___x_1540_, 1);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1540_);
v___x_1543_ = lean_unsigned_to_nat(0u);
v_bs_x27_1544_ = lean_array_uset(v_bs_1529_, v_i_1528_, v___x_1543_);
v___x_1545_ = ((size_t)1ULL);
v___x_1546_ = lean_usize_add(v_i_1528_, v___x_1545_);
v___x_1547_ = lean_array_uset(v_bs_x27_1544_, v_i_1528_, v_a_1541_);
v_i_1528_ = v___x_1546_;
v_bs_1529_ = v___x_1547_;
v___y_1535_ = v_a_1542_;
goto _start;
}
else
{
lean_object* v_a_1549_; lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_dec_ref(v___y_1530_);
lean_dec_ref(v_bs_1529_);
lean_dec_ref(v___x_1526_);
v_a_1549_ = lean_ctor_get(v___x_1540_, 0);
v_a_1550_ = lean_ctor_get(v___x_1540_, 1);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1540_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_inc(v_a_1549_);
lean_dec(v___x_1540_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1549_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* v___x_1558_, lean_object* v_sz_1559_, lean_object* v_i_1560_, lean_object* v_bs_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
size_t v_sz_boxed_1569_; size_t v_i_boxed_1570_; lean_object* v_res_1571_; 
v_sz_boxed_1569_ = lean_unbox_usize(v_sz_1559_);
lean_dec(v_sz_1559_);
v_i_boxed_1570_ = lean_unbox_usize(v_i_1560_);
lean_dec(v_i_1560_);
v_res_1571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1558_, v_sz_boxed_1569_, v_i_boxed_1570_, v_bs_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec(v___y_1563_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(lean_object* v_a_1572_, lean_object* v_as_1573_, size_t v_i_1574_, size_t v_stop_1575_, lean_object* v_b_1576_, lean_object* v___y_1577_){
_start:
{
uint8_t v___x_1579_; 
v___x_1579_ = lean_usize_dec_eq(v_i_1574_, v_stop_1575_);
if (v___x_1579_ == 0)
{
lean_object* v_log_1580_; uint8_t v_action_1581_; uint8_t v_wantsRebuild_1582_; lean_object* v_trace_1583_; lean_object* v_buildTime_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_log_1580_ = lean_ctor_get(v___y_1577_, 0);
v_action_1581_ = lean_ctor_get_uint8(v___y_1577_, sizeof(void*)*3);
v_wantsRebuild_1582_ = lean_ctor_get_uint8(v___y_1577_, sizeof(void*)*3 + 1);
v_trace_1583_ = lean_ctor_get(v___y_1577_, 1);
v_buildTime_1584_ = lean_ctor_get(v___y_1577_, 2);
v___x_1585_ = lean_array_uget_borrowed(v_as_1573_, v_i_1574_);
v___x_1586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
lean_inc(v___x_1585_);
v___x_1587_ = lean_string_append(v___x_1585_, v___x_1586_);
v___x_1588_ = lean_io_prim_handle_put_str(v_a_1572_, v___x_1587_);
lean_dec_ref(v___x_1587_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; size_t v___x_1590_; size_t v___x_1591_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref(v___x_1588_);
v___x_1590_ = ((size_t)1ULL);
v___x_1591_ = lean_usize_add(v_i_1574_, v___x_1590_);
v_i_1574_ = v___x_1591_;
v_b_1576_ = v_a_1589_;
goto _start;
}
else
{
lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1606_; 
lean_inc(v_buildTime_1584_);
lean_inc_ref(v_trace_1583_);
lean_inc_ref(v_log_1580_);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___y_1577_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; 
v_unused_1607_ = lean_ctor_get(v___y_1577_, 2);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v___y_1577_, 1);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v___y_1577_, 0);
lean_dec(v_unused_1609_);
v___x_1594_ = v___y_1577_;
v_isShared_1595_ = v_isSharedCheck_1606_;
goto v_resetjp_1593_;
}
else
{
lean_dec(v___y_1577_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1606_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_a_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; 
v_a_1596_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1596_);
lean_dec_ref(v___x_1588_);
v___x_1597_ = lean_io_error_to_string(v_a_1596_);
v___x_1598_ = 3;
v___x_1599_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set_uint8(v___x_1599_, sizeof(void*)*1, v___x_1598_);
v___x_1600_ = lean_array_get_size(v_log_1580_);
v___x_1601_ = lean_array_push(v_log_1580_, v___x_1599_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1601_);
v___x_1603_ = v___x_1594_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1601_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_trace_1583_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_buildTime_1584_);
lean_ctor_set_uint8(v_reuseFailAlloc_1605_, sizeof(void*)*3, v_action_1581_);
lean_ctor_set_uint8(v_reuseFailAlloc_1605_, sizeof(void*)*3 + 1, v_wantsRebuild_1582_);
v___x_1603_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1600_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
return v___x_1604_;
}
}
}
}
else
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v_b_1576_);
lean_ctor_set(v___x_1610_, 1, v___y_1577_);
return v___x_1610_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(lean_object* v_a_1611_, lean_object* v_as_1612_, lean_object* v_i_1613_, lean_object* v_stop_1614_, lean_object* v_b_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
size_t v_i_boxed_1618_; size_t v_stop_boxed_1619_; lean_object* v_res_1620_; 
v_i_boxed_1618_ = lean_unbox_usize(v_i_1613_);
lean_dec(v_i_1613_);
v_stop_boxed_1619_ = lean_unbox_usize(v_stop_1614_);
lean_dec(v_stop_1614_);
v_res_1620_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1611_, v_as_1612_, v_i_boxed_1618_, v_stop_boxed_1619_, v_b_1615_, v___y_1616_);
lean_dec_ref(v_as_1612_);
lean_dec(v_a_1611_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(uint8_t v_bootstrap_1621_, lean_object* v___y_1622_, lean_object* v_oFiles_1623_, uint8_t v_shouldExport_1624_, uint8_t v___x_1625_, size_t v___x_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
if (v_bootstrap_1621_ == 0)
{
lean_object* v_toContext_1634_; lean_object* v_lakeEnv_1635_; lean_object* v_lean_1636_; lean_object* v_log_1637_; uint8_t v_action_1638_; uint8_t v_wantsRebuild_1639_; lean_object* v_trace_1640_; lean_object* v_buildTime_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1671_; 
v_toContext_1634_ = lean_ctor_get(v___y_1631_, 1);
v_lakeEnv_1635_ = lean_ctor_get(v_toContext_1634_, 1);
v_lean_1636_ = lean_ctor_get(v_lakeEnv_1635_, 1);
v_log_1637_ = lean_ctor_get(v___y_1632_, 0);
v_action_1638_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*3);
v_wantsRebuild_1639_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*3 + 1);
v_trace_1640_ = lean_ctor_get(v___y_1632_, 1);
v_buildTime_1641_ = lean_ctor_get(v___y_1632_, 2);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___y_1632_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1643_ = v___y_1632_;
v_isShared_1644_ = v_isSharedCheck_1671_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_buildTime_1641_);
lean_inc(v_trace_1640_);
lean_inc(v_log_1637_);
lean_dec(v___y_1632_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1671_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v_ar_1645_; lean_object* v___x_1646_; 
v_ar_1645_ = lean_ctor_get(v_lean_1636_, 13);
lean_inc_ref(v_ar_1645_);
v___x_1646_ = l_Lake_compileStaticLib(v___y_1622_, v_oFiles_1623_, v_ar_1645_, v_bootstrap_1621_, v_log_1637_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1658_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_a_1648_ = lean_ctor_get(v___x_1646_, 1);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1650_ = v___x_1646_;
v_isShared_1651_ = v_isSharedCheck_1658_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1658_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v_a_1648_);
v___x_1653_ = v___x_1643_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1648_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_trace_1640_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_buildTime_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*3, v_action_1638_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*3 + 1, v_wantsRebuild_1639_);
v___x_1653_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 1, v___x_1653_);
v___x_1655_ = v___x_1650_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1647_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1670_; 
v_a_1659_ = lean_ctor_get(v___x_1646_, 0);
v_a_1660_ = lean_ctor_get(v___x_1646_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1662_ = v___x_1646_;
v_isShared_1663_ = v_isSharedCheck_1670_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_inc(v_a_1659_);
lean_dec(v___x_1646_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1670_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v_a_1660_);
v___x_1665_ = v___x_1643_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1660_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_trace_1640_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_buildTime_1641_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*3, v_action_1638_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*3 + 1, v_wantsRebuild_1639_);
v___x_1665_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1667_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v___x_1665_);
v___x_1667_ = v___x_1662_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1659_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
}
}
else
{
uint8_t v___x_1672_; 
v___x_1672_ = l_System_Platform_isOSX;
if (v___x_1672_ == 0)
{
uint8_t v___x_1673_; 
v___x_1673_ = l_System_Platform_isWindows;
if (v___x_1673_ == 0)
{
lean_object* v_toContext_1674_; lean_object* v_lakeEnv_1675_; lean_object* v_lean_1676_; lean_object* v_log_1677_; uint8_t v_action_1678_; uint8_t v_wantsRebuild_1679_; lean_object* v_trace_1680_; lean_object* v_buildTime_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1711_; 
v_toContext_1674_ = lean_ctor_get(v___y_1631_, 1);
v_lakeEnv_1675_ = lean_ctor_get(v_toContext_1674_, 1);
v_lean_1676_ = lean_ctor_get(v_lakeEnv_1675_, 1);
v_log_1677_ = lean_ctor_get(v___y_1632_, 0);
v_action_1678_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*3);
v_wantsRebuild_1679_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*3 + 1);
v_trace_1680_ = lean_ctor_get(v___y_1632_, 1);
v_buildTime_1681_ = lean_ctor_get(v___y_1632_, 2);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___y_1632_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1683_ = v___y_1632_;
v_isShared_1684_ = v_isSharedCheck_1711_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_buildTime_1681_);
lean_inc(v_trace_1680_);
lean_inc(v_log_1677_);
lean_dec(v___y_1632_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1711_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v_ar_1685_; lean_object* v___x_1686_; 
v_ar_1685_ = lean_ctor_get(v_lean_1676_, 13);
lean_inc_ref(v_ar_1685_);
v___x_1686_ = l_Lake_compileStaticLib(v___y_1622_, v_oFiles_1623_, v_ar_1685_, v___x_1673_, v_log_1677_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1698_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
v_a_1688_ = lean_ctor_get(v___x_1686_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1690_ = v___x_1686_;
v_isShared_1691_ = v_isSharedCheck_1698_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_inc(v_a_1687_);
lean_dec(v___x_1686_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1698_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v_a_1688_);
v___x_1693_ = v___x_1683_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1688_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_trace_1680_);
lean_ctor_set(v_reuseFailAlloc_1697_, 2, v_buildTime_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1697_, sizeof(void*)*3, v_action_1678_);
lean_ctor_set_uint8(v_reuseFailAlloc_1697_, sizeof(void*)*3 + 1, v_wantsRebuild_1679_);
v___x_1693_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1695_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 1, v___x_1693_);
v___x_1695_ = v___x_1690_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1687_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1710_; 
v_a_1699_ = lean_ctor_get(v___x_1686_, 0);
v_a_1700_ = lean_ctor_get(v___x_1686_, 1);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1702_ = v___x_1686_;
v_isShared_1703_ = v_isSharedCheck_1710_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_inc(v_a_1699_);
lean_dec(v___x_1686_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1710_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v_a_1700_);
v___x_1705_ = v___x_1683_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1700_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_trace_1680_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v_buildTime_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1709_, sizeof(void*)*3, v_action_1678_);
lean_ctor_set_uint8(v_reuseFailAlloc_1709_, sizeof(void*)*3 + 1, v_wantsRebuild_1679_);
v___x_1705_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1707_; 
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v___x_1705_);
v___x_1707_ = v___x_1702_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1699_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1712_; lean_object* v_lakeEnv_1713_; lean_object* v_lean_1714_; lean_object* v_log_1715_; uint8_t v_action_1716_; uint8_t v_wantsRebuild_1717_; lean_object* v_trace_1718_; lean_object* v_buildTime_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1749_; 
v_toContext_1712_ = lean_ctor_get(v___y_1631_, 1);
v_lakeEnv_1713_ = lean_ctor_get(v_toContext_1712_, 1);
v_lean_1714_ = lean_ctor_get(v_lakeEnv_1713_, 1);
v_log_1715_ = lean_ctor_get(v___y_1632_, 0);
v_action_1716_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*3);
v_wantsRebuild_1717_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*3 + 1);
v_trace_1718_ = lean_ctor_get(v___y_1632_, 1);
v_buildTime_1719_ = lean_ctor_get(v___y_1632_, 2);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___y_1632_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1721_ = v___y_1632_;
v_isShared_1722_ = v_isSharedCheck_1749_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_buildTime_1719_);
lean_inc(v_trace_1718_);
lean_inc(v_log_1715_);
lean_dec(v___y_1632_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1749_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_ar_1723_; lean_object* v___x_1724_; 
v_ar_1723_ = lean_ctor_get(v_lean_1714_, 13);
lean_inc_ref(v_ar_1723_);
v___x_1724_ = l_Lake_compileStaticLib(v___y_1622_, v_oFiles_1623_, v_ar_1723_, v_shouldExport_1624_, v_log_1715_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1736_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_a_1726_ = lean_ctor_get(v___x_1724_, 1);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1728_ = v___x_1724_;
v_isShared_1729_ = v_isSharedCheck_1736_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1736_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v_a_1726_);
v___x_1731_ = v___x_1721_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1726_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_trace_1718_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_buildTime_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, sizeof(void*)*3, v_action_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1735_, sizeof(void*)*3 + 1, v_wantsRebuild_1717_);
v___x_1731_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1733_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 1, v___x_1731_);
v___x_1733_ = v___x_1728_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1725_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1748_; 
v_a_1737_ = lean_ctor_get(v___x_1724_, 0);
v_a_1738_ = lean_ctor_get(v___x_1724_, 1);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1740_ = v___x_1724_;
v_isShared_1741_ = v_isSharedCheck_1748_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_inc(v_a_1737_);
lean_dec(v___x_1724_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1748_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v_a_1738_);
v___x_1743_ = v___x_1721_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1738_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_trace_1718_);
lean_ctor_set(v_reuseFailAlloc_1747_, 2, v_buildTime_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1747_, sizeof(void*)*3, v_action_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1747_, sizeof(void*)*3 + 1, v_wantsRebuild_1717_);
v___x_1743_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1745_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 1, v___x_1743_);
v___x_1745_ = v___x_1740_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1737_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1750_; uint8_t v_action_1751_; uint8_t v_wantsRebuild_1752_; lean_object* v_trace_1753_; lean_object* v_buildTime_1754_; lean_object* v___x_1755_; 
v_log_1750_ = lean_ctor_get(v___y_1632_, 0);
v_action_1751_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*3);
v_wantsRebuild_1752_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*3 + 1);
v_trace_1753_ = lean_ctor_get(v___y_1632_, 1);
v_buildTime_1754_ = lean_ctor_get(v___y_1632_, 2);
lean_inc_ref(v___y_1622_);
v___x_1755_ = l_Lake_createParentDirs(v___y_1622_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v_a_1759_; lean_object* v___y_1808_; uint8_t v___x_1810_; lean_object* v___x_1811_; 
lean_dec_ref(v___x_1755_);
v___x_1756_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1622_);
v___x_1757_ = l_System_FilePath_addExtension(v___y_1622_, v___x_1756_);
v___x_1810_ = 1;
v___x_1811_ = lean_io_prim_handle_mk(v___x_1757_, v___x_1810_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref(v___x_1811_);
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_array_get_size(v_oFiles_1623_);
v___x_1815_ = lean_nat_dec_lt(v___x_1813_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_dec(v_a_1812_);
lean_dec_ref(v_oFiles_1623_);
v_a_1759_ = v___y_1632_;
goto v___jp_1758_;
}
else
{
lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1816_ = lean_box(0);
v___x_1817_ = lean_nat_dec_le(v___x_1814_, v___x_1814_);
if (v___x_1817_ == 0)
{
if (v___x_1815_ == 0)
{
lean_dec(v_a_1812_);
lean_dec_ref(v_oFiles_1623_);
v_a_1759_ = v___y_1632_;
goto v___jp_1758_;
}
else
{
size_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = lean_usize_of_nat(v___x_1814_);
v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1812_, v_oFiles_1623_, v___x_1626_, v___x_1818_, v___x_1816_, v___y_1632_);
lean_dec_ref(v_oFiles_1623_);
lean_dec(v_a_1812_);
v___y_1808_ = v___x_1819_;
goto v___jp_1807_;
}
}
else
{
size_t v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_usize_of_nat(v___x_1814_);
v___x_1821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1812_, v_oFiles_1623_, v___x_1626_, v___x_1820_, v___x_1816_, v___y_1632_);
lean_dec_ref(v_oFiles_1623_);
lean_dec(v_a_1812_);
v___y_1808_ = v___x_1821_;
goto v___jp_1807_;
}
}
}
else
{
lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1835_; 
lean_inc(v_buildTime_1754_);
lean_inc_ref(v_trace_1753_);
lean_inc_ref(v_log_1750_);
lean_dec_ref(v___x_1757_);
lean_dec_ref(v_oFiles_1623_);
lean_dec_ref(v___y_1622_);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___y_1632_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; lean_object* v_unused_1837_; lean_object* v_unused_1838_; 
v_unused_1836_ = lean_ctor_get(v___y_1632_, 2);
lean_dec(v_unused_1836_);
v_unused_1837_ = lean_ctor_get(v___y_1632_, 1);
lean_dec(v_unused_1837_);
v_unused_1838_ = lean_ctor_get(v___y_1632_, 0);
lean_dec(v_unused_1838_);
v___x_1823_ = v___y_1632_;
v_isShared_1824_ = v_isSharedCheck_1835_;
goto v_resetjp_1822_;
}
else
{
lean_dec(v___y_1632_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1835_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v_a_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1832_; 
v_a_1825_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1825_);
lean_dec_ref(v___x_1811_);
v___x_1826_ = lean_io_error_to_string(v_a_1825_);
v___x_1827_ = 3;
v___x_1828_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1828_, 0, v___x_1826_);
lean_ctor_set_uint8(v___x_1828_, sizeof(void*)*1, v___x_1827_);
v___x_1829_ = lean_array_get_size(v_log_1750_);
v___x_1830_ = lean_array_push(v_log_1750_, v___x_1828_);
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 0, v___x_1830_);
v___x_1832_ = v___x_1823_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_trace_1753_);
lean_ctor_set(v_reuseFailAlloc_1834_, 2, v_buildTime_1754_);
lean_ctor_set_uint8(v_reuseFailAlloc_1834_, sizeof(void*)*3, v_action_1751_);
lean_ctor_set_uint8(v_reuseFailAlloc_1834_, sizeof(void*)*3 + 1, v_wantsRebuild_1752_);
v___x_1832_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1829_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
return v___x_1833_;
}
}
}
v___jp_1758_:
{
lean_object* v___x_1760_; lean_object* v_log_1761_; uint8_t v_action_1762_; uint8_t v_wantsRebuild_1763_; lean_object* v_trace_1764_; lean_object* v_buildTime_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1806_; 
v___x_1760_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1761_ = lean_ctor_get(v_a_1759_, 0);
v_action_1762_ = lean_ctor_get_uint8(v_a_1759_, sizeof(void*)*3);
v_wantsRebuild_1763_ = lean_ctor_get_uint8(v_a_1759_, sizeof(void*)*3 + 1);
v_trace_1764_ = lean_ctor_get(v_a_1759_, 1);
v_buildTime_1765_ = lean_ctor_get(v_a_1759_, 2);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_a_1759_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1767_ = v_a_1759_;
v_isShared_1768_ = v_isSharedCheck_1806_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_buildTime_1765_);
lean_inc(v_trace_1764_);
lean_inc(v_log_1761_);
lean_dec(v_a_1759_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1806_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1769_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1770_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1771_ = lean_unsigned_to_nat(5u);
v___x_1772_ = lean_mk_empty_array_with_capacity(v___x_1771_);
lean_dec_ref(v___x_1772_);
v___x_1773_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1774_ = lean_array_push(v___x_1773_, v___y_1622_);
v___x_1775_ = lean_array_push(v___x_1774_, v___x_1770_);
v___x_1776_ = lean_array_push(v___x_1775_, v___x_1757_);
v___x_1777_ = lean_box(0);
v___x_1778_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1779_ = 0;
v___x_1780_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1780_, 0, v___x_1760_);
lean_ctor_set(v___x_1780_, 1, v___x_1769_);
lean_ctor_set(v___x_1780_, 2, v___x_1776_);
lean_ctor_set(v___x_1780_, 3, v___x_1777_);
lean_ctor_set(v___x_1780_, 4, v___x_1778_);
lean_ctor_set_uint8(v___x_1780_, sizeof(void*)*5, v___x_1625_);
lean_ctor_set_uint8(v___x_1780_, sizeof(void*)*5 + 1, v___x_1779_);
v___x_1781_ = l_Lake_proc(v___x_1780_, v___x_1779_, v_log_1761_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1793_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_a_1783_ = lean_ctor_get(v___x_1781_, 1);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1785_ = v___x_1781_;
v_isShared_1786_ = v_isSharedCheck_1793_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1793_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v_a_1783_);
v___x_1788_ = v___x_1767_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1783_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_trace_1764_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_buildTime_1765_);
lean_ctor_set_uint8(v_reuseFailAlloc_1792_, sizeof(void*)*3, v_action_1762_);
lean_ctor_set_uint8(v_reuseFailAlloc_1792_, sizeof(void*)*3 + 1, v_wantsRebuild_1763_);
v___x_1788_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1790_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 1, v___x_1788_);
v___x_1790_ = v___x_1785_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1782_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v___x_1788_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1805_; 
v_a_1794_ = lean_ctor_get(v___x_1781_, 0);
v_a_1795_ = lean_ctor_get(v___x_1781_, 1);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1797_ = v___x_1781_;
v_isShared_1798_ = v_isSharedCheck_1805_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_inc(v_a_1794_);
lean_dec(v___x_1781_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1805_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v_a_1795_);
v___x_1800_ = v___x_1767_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1795_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_trace_1764_);
lean_ctor_set(v_reuseFailAlloc_1804_, 2, v_buildTime_1765_);
lean_ctor_set_uint8(v_reuseFailAlloc_1804_, sizeof(void*)*3, v_action_1762_);
lean_ctor_set_uint8(v_reuseFailAlloc_1804_, sizeof(void*)*3 + 1, v_wantsRebuild_1763_);
v___x_1800_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1802_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 1, v___x_1800_);
v___x_1802_ = v___x_1797_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1794_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
}
}
v___jp_1807_:
{
if (lean_obj_tag(v___y_1808_) == 0)
{
lean_object* v_a_1809_; 
v_a_1809_ = lean_ctor_get(v___y_1808_, 1);
lean_inc(v_a_1809_);
lean_dec_ref(v___y_1808_);
v_a_1759_ = v_a_1809_;
goto v___jp_1758_;
}
else
{
lean_dec_ref(v___x_1757_);
lean_dec_ref(v___y_1622_);
return v___y_1808_;
}
}
}
else
{
lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1852_; 
lean_inc(v_buildTime_1754_);
lean_inc_ref(v_trace_1753_);
lean_inc_ref(v_log_1750_);
lean_dec_ref(v_oFiles_1623_);
lean_dec_ref(v___y_1622_);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___y_1632_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; lean_object* v_unused_1854_; lean_object* v_unused_1855_; 
v_unused_1853_ = lean_ctor_get(v___y_1632_, 2);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v___y_1632_, 1);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v___y_1632_, 0);
lean_dec(v_unused_1855_);
v___x_1840_ = v___y_1632_;
v_isShared_1841_ = v_isSharedCheck_1852_;
goto v_resetjp_1839_;
}
else
{
lean_dec(v___y_1632_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1852_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v_a_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1849_; 
v_a_1842_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1755_);
v___x_1843_ = lean_io_error_to_string(v_a_1842_);
v___x_1844_ = 3;
v___x_1845_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1845_, 0, v___x_1843_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*1, v___x_1844_);
v___x_1846_ = lean_array_get_size(v_log_1750_);
v___x_1847_ = lean_array_push(v_log_1750_, v___x_1845_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1847_);
v___x_1849_ = v___x_1840_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_trace_1753_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v_buildTime_1754_);
lean_ctor_set_uint8(v_reuseFailAlloc_1851_, sizeof(void*)*3, v_action_1751_);
lean_ctor_set_uint8(v_reuseFailAlloc_1851_, sizeof(void*)*3 + 1, v_wantsRebuild_1752_);
v___x_1849_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1850_; 
v___x_1850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1846_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
return v___x_1850_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object* v_bootstrap_1856_, lean_object* v___y_1857_, lean_object* v_oFiles_1858_, lean_object* v_shouldExport_1859_, lean_object* v___x_1860_, lean_object* v___x_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
uint8_t v_bootstrap_boxed_1869_; uint8_t v_shouldExport_boxed_1870_; uint8_t v___x_6740__boxed_1871_; size_t v___x_6741__boxed_1872_; lean_object* v_res_1873_; 
v_bootstrap_boxed_1869_ = lean_unbox(v_bootstrap_1856_);
v_shouldExport_boxed_1870_ = lean_unbox(v_shouldExport_1859_);
v___x_6740__boxed_1871_ = lean_unbox(v___x_1860_);
v___x_6741__boxed_1872_ = lean_unbox_usize(v___x_1861_);
lean_dec(v___x_1861_);
v_res_1873_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_boxed_1869_, v___y_1857_, v_oFiles_1858_, v_shouldExport_boxed_1870_, v___x_6740__boxed_1871_, v___x_6741__boxed_1872_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t v_bootstrap_1874_, lean_object* v___y_1875_, uint8_t v_shouldExport_1876_, uint8_t v___x_1877_, size_t v___x_1878_, lean_object* v_oFiles_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___y_1891_; uint8_t v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1887_ = lean_box(v_bootstrap_1874_);
v___x_1888_ = lean_box(v_shouldExport_1876_);
v___x_1889_ = lean_box(v___x_1877_);
v___x_1890_ = lean_box_usize(v___x_1878_);
lean_inc_ref(v___y_1875_);
v___y_1891_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed), 13, 6);
lean_closure_set(v___y_1891_, 0, v___x_1887_);
lean_closure_set(v___y_1891_, 1, v___y_1875_);
lean_closure_set(v___y_1891_, 2, v_oFiles_1879_);
lean_closure_set(v___y_1891_, 3, v___x_1888_);
lean_closure_set(v___y_1891_, 4, v___x_1889_);
lean_closure_set(v___y_1891_, 5, v___x_1890_);
v___x_1892_ = 0;
v___x_1893_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1894_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1875_, v___y_1891_, v___x_1892_, v___x_1893_, v___x_1877_, v___x_1892_, v___x_1892_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1904_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_a_1896_ = lean_ctor_get(v___x_1894_, 1);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1898_ = v___x_1894_;
v_isShared_1899_ = v_isSharedCheck_1904_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1904_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v_path_1900_; lean_object* v___x_1902_; 
v_path_1900_ = lean_ctor_get(v_a_1895_, 1);
lean_inc_ref(v_path_1900_);
lean_dec(v_a_1895_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v_path_1900_);
v___x_1902_ = v___x_1898_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_path_1900_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v_a_1896_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
v_a_1905_ = lean_ctor_get(v___x_1894_, 0);
v_a_1906_ = lean_ctor_get(v___x_1894_, 1);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1894_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_inc(v_a_1905_);
lean_dec(v___x_1894_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1905_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* v_bootstrap_1914_, lean_object* v___y_1915_, lean_object* v_shouldExport_1916_, lean_object* v___x_1917_, lean_object* v___x_1918_, lean_object* v_oFiles_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
uint8_t v_bootstrap_boxed_1927_; uint8_t v_shouldExport_boxed_1928_; uint8_t v___x_7150__boxed_1929_; size_t v___x_7151__boxed_1930_; lean_object* v_res_1931_; 
v_bootstrap_boxed_1927_ = lean_unbox(v_bootstrap_1914_);
v_shouldExport_boxed_1928_ = lean_unbox(v_shouldExport_1916_);
v___x_7150__boxed_1929_ = lean_unbox(v___x_1917_);
v___x_7151__boxed_1930_ = lean_unbox_usize(v___x_1918_);
lean_dec(v___x_1918_);
v_res_1931_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_boxed_1927_, v___y_1915_, v_shouldExport_boxed_1928_, v___x_7150__boxed_1929_, v___x_7151__boxed_1930_, v_oFiles_1919_, v___y_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec(v___y_1921_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* v_a_1932_, size_t v_sz_1933_, size_t v_i_1934_, lean_object* v_bs_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
uint8_t v___x_1943_; 
v___x_1943_ = lean_usize_dec_lt(v_i_1934_, v_sz_1933_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
lean_dec_ref(v___y_1936_);
lean_dec_ref(v_a_1932_);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v_bs_1935_);
lean_ctor_set(v___x_1944_, 1, v___y_1941_);
return v___x_1944_;
}
else
{
lean_object* v_v_1945_; lean_object* v___x_1946_; 
v_v_1945_ = lean_array_uget_borrowed(v_bs_1935_, v_i_1934_);
lean_inc_ref(v___y_1936_);
lean_inc_ref(v_a_1932_);
lean_inc(v_v_1945_);
v___x_1946_ = l_Lake_ModuleFacet_fetch___redArg(v_v_1945_, v_a_1932_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v_a_1948_; lean_object* v___x_1949_; lean_object* v_bs_x27_1950_; size_t v___x_1951_; size_t v___x_1952_; lean_object* v___x_1953_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
v_a_1948_ = lean_ctor_get(v___x_1946_, 1);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1946_);
v___x_1949_ = lean_unsigned_to_nat(0u);
v_bs_x27_1950_ = lean_array_uset(v_bs_1935_, v_i_1934_, v___x_1949_);
v___x_1951_ = ((size_t)1ULL);
v___x_1952_ = lean_usize_add(v_i_1934_, v___x_1951_);
v___x_1953_ = lean_array_uset(v_bs_x27_1950_, v_i_1934_, v_a_1947_);
v_i_1934_ = v___x_1952_;
v_bs_1935_ = v___x_1953_;
v___y_1941_ = v_a_1948_;
goto _start;
}
else
{
lean_object* v_a_1955_; lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec_ref(v___y_1936_);
lean_dec_ref(v_bs_1935_);
lean_dec_ref(v_a_1932_);
v_a_1955_ = lean_ctor_get(v___x_1946_, 0);
v_a_1956_ = lean_ctor_get(v___x_1946_, 1);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1946_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_inc(v_a_1955_);
lean_dec(v___x_1946_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1955_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object* v_a_1964_, lean_object* v_sz_1965_, lean_object* v_i_1966_, lean_object* v_bs_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
size_t v_sz_boxed_1975_; size_t v_i_boxed_1976_; lean_object* v_res_1977_; 
v_sz_boxed_1975_ = lean_unbox_usize(v_sz_1965_);
lean_dec(v_sz_1965_);
v_i_boxed_1976_ = lean_unbox_usize(v_i_1966_);
lean_dec(v_i_1966_);
v_res_1977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_1964_, v_sz_boxed_1975_, v_i_boxed_1976_, v_bs_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec(v___y_1969_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(uint8_t v_shouldExport_1978_, lean_object* v_as_1979_, size_t v_i_1980_, size_t v_stop_1981_, lean_object* v_b_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
uint8_t v___x_1990_; 
v___x_1990_ = lean_usize_dec_eq(v_i_1980_, v_stop_1981_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; lean_object* v_lib_1992_; lean_object* v_config_1993_; lean_object* v_nativeFacets_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; size_t v_sz_1997_; size_t v___x_1998_; lean_object* v___x_1999_; 
v___x_1991_ = lean_array_uget_borrowed(v_as_1979_, v_i_1980_);
v_lib_1992_ = lean_ctor_get(v___x_1991_, 0);
v_config_1993_ = lean_ctor_get(v_lib_1992_, 2);
v_nativeFacets_1994_ = lean_ctor_get(v_config_1993_, 8);
v___x_1995_ = lean_box(v_shouldExport_1978_);
lean_inc_ref(v_nativeFacets_1994_);
v___x_1996_ = lean_apply_1(v_nativeFacets_1994_, v___x_1995_);
v_sz_1997_ = lean_array_size(v___x_1996_);
v___x_1998_ = ((size_t)0ULL);
lean_inc_ref(v___y_1983_);
lean_inc(v___x_1991_);
v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_1991_, v_sz_1997_, v___x_1998_, v___x_1996_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v_a_2001_; lean_object* v___x_2002_; size_t v___x_2003_; size_t v___x_2004_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
v_a_2001_ = lean_ctor_get(v___x_1999_, 1);
lean_inc(v_a_2001_);
lean_dec_ref(v___x_1999_);
v___x_2002_ = l_Array_append___redArg(v_b_1982_, v_a_2000_);
lean_dec(v_a_2000_);
v___x_2003_ = ((size_t)1ULL);
v___x_2004_ = lean_usize_add(v_i_1980_, v___x_2003_);
v_i_1980_ = v___x_2004_;
v_b_1982_ = v___x_2002_;
v___y_1988_ = v_a_2001_;
goto _start;
}
else
{
lean_dec_ref(v___y_1983_);
lean_dec_ref(v_b_1982_);
return v___x_1999_;
}
}
else
{
lean_object* v___x_2006_; 
lean_dec_ref(v___y_1983_);
v___x_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2006_, 0, v_b_1982_);
lean_ctor_set(v___x_2006_, 1, v___y_1988_);
return v___x_2006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(lean_object* v_shouldExport_2007_, lean_object* v_as_2008_, lean_object* v_i_2009_, lean_object* v_stop_2010_, lean_object* v_b_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
uint8_t v_shouldExport_boxed_2019_; size_t v_i_boxed_2020_; size_t v_stop_boxed_2021_; lean_object* v_res_2022_; 
v_shouldExport_boxed_2019_ = lean_unbox(v_shouldExport_2007_);
v_i_boxed_2020_ = lean_unbox_usize(v_i_2009_);
lean_dec(v_i_2009_);
v_stop_boxed_2021_ = lean_unbox_usize(v_stop_2010_);
lean_dec(v_stop_2010_);
v_res_2022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_boxed_2019_, v_as_2008_, v_i_boxed_2020_, v_stop_boxed_2021_, v_b_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v_as_2008_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object* v___x_2023_, lean_object* v___x_2024_, lean_object* v_config_2025_, lean_object* v_config_2026_, lean_object* v_pkg_2027_, uint8_t v_shouldExport_2028_, uint8_t v___x_2029_, lean_object* v___x_2030_, lean_object* v_dir_2031_, lean_object* v_self_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
uint8_t v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; size_t v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v_a_2061_; lean_object* v_a_2062_; lean_object* v___y_2105_; lean_object* v___x_2117_; 
lean_inc_ref(v___y_2033_);
lean_inc_ref(v___y_2037_);
lean_inc(v___y_2036_);
lean_inc(v___y_2035_);
lean_inc(v___x_2024_);
v___x_2117_ = lean_apply_7(v___y_2033_, v___x_2023_, v___x_2024_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, lean_box(0));
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v_a_2119_; lean_object* v___x_2120_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
v_a_2119_ = lean_ctor_get(v___x_2117_, 1);
lean_inc(v_a_2119_);
lean_dec_ref(v___x_2117_);
v___x_2120_ = l_Lake_Job_await___redArg(v_a_2118_, v_a_2119_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v_a_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; uint8_t v___x_2126_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
v_a_2122_ = lean_ctor_get(v___x_2120_, 1);
lean_inc(v_a_2122_);
lean_dec_ref(v___x_2120_);
v___x_2123_ = lean_unsigned_to_nat(0u);
v___x_2124_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_2125_ = lean_array_get_size(v_a_2121_);
v___x_2126_ = lean_nat_dec_lt(v___x_2123_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_dec(v_a_2121_);
v_a_2061_ = v___x_2124_;
v_a_2062_ = v_a_2122_;
goto v___jp_2060_;
}
else
{
uint8_t v___x_2127_; 
v___x_2127_ = lean_nat_dec_le(v___x_2125_, v___x_2125_);
if (v___x_2127_ == 0)
{
if (v___x_2126_ == 0)
{
lean_dec(v_a_2121_);
v_a_2061_ = v___x_2124_;
v_a_2062_ = v_a_2122_;
goto v___jp_2060_;
}
else
{
size_t v___x_2128_; size_t v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = ((size_t)0ULL);
v___x_2129_ = lean_usize_of_nat(v___x_2125_);
lean_inc_ref(v___y_2033_);
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2028_, v_a_2121_, v___x_2128_, v___x_2129_, v___x_2124_, v___y_2033_, v___x_2024_, v___y_2035_, v___y_2036_, v___y_2037_, v_a_2122_);
lean_dec(v_a_2121_);
v___y_2105_ = v___x_2130_;
goto v___jp_2104_;
}
}
else
{
size_t v___x_2131_; size_t v___x_2132_; lean_object* v___x_2133_; 
v___x_2131_ = ((size_t)0ULL);
v___x_2132_ = lean_usize_of_nat(v___x_2125_);
lean_inc_ref(v___y_2033_);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2028_, v_a_2121_, v___x_2131_, v___x_2132_, v___x_2124_, v___y_2033_, v___x_2024_, v___y_2035_, v___y_2036_, v___y_2037_, v_a_2122_);
lean_dec(v_a_2121_);
v___y_2105_ = v___x_2133_;
goto v___jp_2104_;
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref(v___y_2033_);
lean_dec_ref(v_self_2032_);
lean_dec_ref(v_dir_2031_);
lean_dec(v___x_2030_);
lean_dec_ref(v_pkg_2027_);
lean_dec_ref(v_config_2025_);
lean_dec(v___x_2024_);
v_a_2134_ = lean_ctor_get(v___x_2120_, 0);
v_a_2135_ = lean_ctor_get(v___x_2120_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2120_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_inc(v_a_2134_);
lean_dec(v___x_2120_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2134_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v___y_2033_);
lean_dec_ref(v_self_2032_);
lean_dec_ref(v_dir_2031_);
lean_dec(v___x_2030_);
lean_dec_ref(v_pkg_2027_);
lean_dec_ref(v_config_2025_);
lean_dec(v___x_2024_);
v_a_2143_ = lean_ctor_get(v___x_2117_, 0);
v_a_2144_ = lean_ctor_get(v___x_2117_, 1);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2117_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_inc(v_a_2143_);
lean_dec(v___x_2117_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2143_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
v___jp_2040_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___f_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2047_ = lean_box(v___y_2041_);
v___x_2048_ = lean_box(v_shouldExport_2028_);
v___x_2049_ = lean_box(v___x_2029_);
v___x_2050_ = lean_box_usize(v___y_2044_);
v___f_2051_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2051_, 0, v___x_2047_);
lean_closure_set(v___f_2051_, 1, v___y_2046_);
lean_closure_set(v___f_2051_, 2, v___x_2048_);
lean_closure_set(v___f_2051_, 3, v___x_2049_);
lean_closure_set(v___f_2051_, 4, v___x_2050_);
v___x_2052_ = l_Array_append___redArg(v___y_2045_, v___y_2042_);
lean_dec_ref(v___y_2042_);
v___x_2053_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_2054_ = l_Lake_Job_collectArray___redArg(v___x_2052_, v___x_2053_);
lean_dec_ref(v___x_2052_);
v___x_2055_ = lean_unsigned_to_nat(0u);
v___x_2056_ = 0;
v___x_2057_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2058_ = l_Lake_Job_mapM___redArg(v___x_2030_, v___x_2054_, v___f_2051_, v___x_2055_, v___x_2056_, v___y_2033_, v___x_2024_, v___y_2035_, v___y_2036_, v___y_2037_, v___x_2057_);
lean_dec(v___x_2024_);
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v___y_2043_);
return v___x_2059_;
}
v___jp_2060_:
{
lean_object* v_toLeanConfig_2063_; lean_object* v_toLeanConfig_2064_; uint8_t v_bootstrap_2065_; lean_object* v_buildDir_2066_; lean_object* v_nativeLibDir_2067_; lean_object* v_moreLinkObjs_2068_; lean_object* v_moreLinkObjs_2069_; lean_object* v___x_2070_; size_t v_sz_2071_; size_t v___x_2072_; lean_object* v___x_2073_; 
v_toLeanConfig_2063_ = lean_ctor_get(v_config_2025_, 1);
lean_inc_ref(v_toLeanConfig_2063_);
v_toLeanConfig_2064_ = lean_ctor_get(v_config_2026_, 0);
v_bootstrap_2065_ = lean_ctor_get_uint8(v_config_2025_, sizeof(void*)*26);
v_buildDir_2066_ = lean_ctor_get(v_config_2025_, 5);
lean_inc_ref(v_buildDir_2066_);
v_nativeLibDir_2067_ = lean_ctor_get(v_config_2025_, 7);
lean_inc_ref(v_nativeLibDir_2067_);
lean_dec_ref(v_config_2025_);
v_moreLinkObjs_2068_ = lean_ctor_get(v_toLeanConfig_2063_, 6);
lean_inc_ref(v_moreLinkObjs_2068_);
lean_dec_ref(v_toLeanConfig_2063_);
v_moreLinkObjs_2069_ = lean_ctor_get(v_toLeanConfig_2064_, 6);
v___x_2070_ = l_Array_append___redArg(v_moreLinkObjs_2068_, v_moreLinkObjs_2069_);
v_sz_2071_ = lean_array_size(v___x_2070_);
v___x_2072_ = ((size_t)0ULL);
lean_inc_ref(v___y_2033_);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_2027_, v_sz_2071_, v___x_2072_, v___x_2070_, v___y_2033_, v___x_2024_, v___y_2035_, v___y_2036_, v___y_2037_, v_a_2062_);
if (lean_obj_tag(v___x_2073_) == 0)
{
if (v_shouldExport_2028_ == 0)
{
lean_object* v_a_2074_; lean_object* v_a_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
v_a_2075_ = lean_ctor_get(v___x_2073_, 1);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2073_);
v___x_2076_ = l_System_FilePath_normalize(v_buildDir_2066_);
v___x_2077_ = l_Lake_joinRelative(v_dir_2031_, v___x_2076_);
v___x_2078_ = l_System_FilePath_normalize(v_nativeLibDir_2067_);
v___x_2079_ = l_Lake_joinRelative(v___x_2077_, v___x_2078_);
v___x_2080_ = l_Lake_LeanLib_libName(v_self_2032_);
v___x_2081_ = l_Lake_nameToStaticLib(v___x_2080_, v_shouldExport_2028_);
v___x_2082_ = l_Lake_joinRelative(v___x_2079_, v___x_2081_);
v___y_2041_ = v_bootstrap_2065_;
v___y_2042_ = v_a_2074_;
v___y_2043_ = v_a_2075_;
v___y_2044_ = v___x_2072_;
v___y_2045_ = v_a_2061_;
v___y_2046_ = v___x_2082_;
goto v___jp_2040_;
}
else
{
lean_object* v_a_2083_; lean_object* v_a_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_a_2083_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2083_);
v_a_2084_ = lean_ctor_get(v___x_2073_, 1);
lean_inc(v_a_2084_);
lean_dec_ref(v___x_2073_);
v___x_2085_ = l_System_FilePath_normalize(v_buildDir_2066_);
v___x_2086_ = l_Lake_joinRelative(v_dir_2031_, v___x_2085_);
v___x_2087_ = l_System_FilePath_normalize(v_nativeLibDir_2067_);
v___x_2088_ = l_Lake_joinRelative(v___x_2086_, v___x_2087_);
v___x_2089_ = l_Lake_LeanLib_libName(v_self_2032_);
v___x_2090_ = 0;
v___x_2091_ = l_Lake_nameToStaticLib(v___x_2089_, v___x_2090_);
v___x_2092_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_2093_ = l_System_FilePath_addExtension(v___x_2091_, v___x_2092_);
v___x_2094_ = l_Lake_joinRelative(v___x_2088_, v___x_2093_);
v___y_2041_ = v_bootstrap_2065_;
v___y_2042_ = v_a_2083_;
v___y_2043_ = v_a_2084_;
v___y_2044_ = v___x_2072_;
v___y_2045_ = v_a_2061_;
v___y_2046_ = v___x_2094_;
goto v___jp_2040_;
}
}
else
{
lean_object* v_a_2095_; lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_nativeLibDir_2067_);
lean_dec_ref(v_buildDir_2066_);
lean_dec_ref(v_a_2061_);
lean_dec_ref(v___y_2033_);
lean_dec_ref(v_self_2032_);
lean_dec_ref(v_dir_2031_);
lean_dec(v___x_2030_);
lean_dec(v___x_2024_);
v_a_2095_ = lean_ctor_get(v___x_2073_, 0);
v_a_2096_ = lean_ctor_get(v___x_2073_, 1);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2073_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_inc(v_a_2095_);
lean_dec(v___x_2073_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2095_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
v___jp_2104_:
{
if (lean_obj_tag(v___y_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v_a_2107_; 
v_a_2106_ = lean_ctor_get(v___y_2105_, 0);
lean_inc(v_a_2106_);
v_a_2107_ = lean_ctor_get(v___y_2105_, 1);
lean_inc(v_a_2107_);
lean_dec_ref(v___y_2105_);
v_a_2061_ = v_a_2106_;
v_a_2062_ = v_a_2107_;
goto v___jp_2060_;
}
else
{
lean_object* v_a_2108_; lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec_ref(v___y_2033_);
lean_dec_ref(v_self_2032_);
lean_dec_ref(v_dir_2031_);
lean_dec(v___x_2030_);
lean_dec_ref(v_pkg_2027_);
lean_dec_ref(v_config_2025_);
lean_dec(v___x_2024_);
v_a_2108_ = lean_ctor_get(v___y_2105_, 0);
v_a_2109_ = lean_ctor_get(v___y_2105_, 1);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___y_2105_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___y_2105_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_inc(v_a_2108_);
lean_dec(v___y_2105_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2108_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(lean_object** _args){
lean_object* v___x_2152_ = _args[0];
lean_object* v___x_2153_ = _args[1];
lean_object* v_config_2154_ = _args[2];
lean_object* v_config_2155_ = _args[3];
lean_object* v_pkg_2156_ = _args[4];
lean_object* v_shouldExport_2157_ = _args[5];
lean_object* v___x_2158_ = _args[6];
lean_object* v___x_2159_ = _args[7];
lean_object* v_dir_2160_ = _args[8];
lean_object* v_self_2161_ = _args[9];
lean_object* v___y_2162_ = _args[10];
lean_object* v___y_2163_ = _args[11];
lean_object* v___y_2164_ = _args[12];
lean_object* v___y_2165_ = _args[13];
lean_object* v___y_2166_ = _args[14];
lean_object* v___y_2167_ = _args[15];
lean_object* v___y_2168_ = _args[16];
_start:
{
uint8_t v_shouldExport_boxed_2169_; uint8_t v___x_7352__boxed_2170_; lean_object* v_res_2171_; 
v_shouldExport_boxed_2169_ = lean_unbox(v_shouldExport_2157_);
v___x_7352__boxed_2170_ = lean_unbox(v___x_2158_);
v_res_2171_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v___x_2152_, v___x_2153_, v_config_2154_, v_config_2155_, v_pkg_2156_, v_shouldExport_boxed_2169_, v___x_7352__boxed_2170_, v___x_2159_, v_dir_2160_, v_self_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec(v_config_2155_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object* v___y_2172_, lean_object* v_self_2173_, uint8_t v_shouldExport_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v_toBuildConfig_2181_; lean_object* v_registeredJobs_2182_; uint8_t v_verbosity_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; uint8_t v___x_2186_; uint8_t v___x_2187_; lean_object* v___y_2189_; 
v_toBuildConfig_2181_ = lean_ctor_get(v_a_2178_, 0);
v_registeredJobs_2182_ = lean_ctor_get(v_a_2178_, 3);
v_verbosity_2183_ = lean_ctor_get_uint8(v_toBuildConfig_2181_, sizeof(void*)*2 + 3);
v___x_2184_ = l_Lake_instDataKindFilePath;
v___x_2185_ = 2;
v___x_2186_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2183_, v___x_2185_);
v___x_2187_ = 1;
if (v___x_2186_ == 0)
{
lean_object* v___x_2234_; 
v___x_2234_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_2189_ = v___x_2234_;
goto v___jp_2188_;
}
else
{
if (v_shouldExport_2174_ == 0)
{
lean_object* v___x_2235_; 
v___x_2235_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___y_2189_ = v___x_2235_;
goto v___jp_2188_;
}
else
{
lean_object* v___x_2236_; 
v___x_2236_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_2189_ = v___x_2236_;
goto v___jp_2188_;
}
}
v___jp_2188_:
{
lean_object* v_pkg_2190_; lean_object* v_name_2191_; lean_object* v_config_2192_; lean_object* v_keyName_2193_; lean_object* v_dir_2194_; lean_object* v_config_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___f_2203_; lean_object* v___x_2204_; 
v_pkg_2190_ = lean_ctor_get(v_self_2173_, 0);
lean_inc_ref_n(v_pkg_2190_, 2);
v_name_2191_ = lean_ctor_get(v_self_2173_, 1);
lean_inc_n(v_name_2191_, 2);
v_config_2192_ = lean_ctor_get(v_self_2173_, 2);
lean_inc(v_config_2192_);
v_keyName_2193_ = lean_ctor_get(v_pkg_2190_, 2);
v_dir_2194_ = lean_ctor_get(v_pkg_2190_, 4);
lean_inc_ref(v_dir_2194_);
v_config_2195_ = lean_ctor_get(v_pkg_2190_, 6);
lean_inc_ref(v_config_2195_);
v___x_2196_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_2193_);
v___x_2197_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_keyName_2193_);
lean_ctor_set(v___x_2197_, 1, v_name_2191_);
v___x_2198_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_2173_);
v___x_2199_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
lean_ctor_set(v___x_2199_, 2, v_self_2173_);
lean_ctor_set(v___x_2199_, 3, v___x_2196_);
v___x_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2200_, 0, v_pkg_2190_);
v___x_2201_ = lean_box(v_shouldExport_2174_);
v___x_2202_ = lean_box(v___x_2187_);
v___f_2203_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed), 17, 10);
lean_closure_set(v___f_2203_, 0, v___x_2199_);
lean_closure_set(v___f_2203_, 1, v___x_2200_);
lean_closure_set(v___f_2203_, 2, v_config_2195_);
lean_closure_set(v___f_2203_, 3, v_config_2192_);
lean_closure_set(v___f_2203_, 4, v_pkg_2190_);
lean_closure_set(v___f_2203_, 5, v___x_2201_);
lean_closure_set(v___f_2203_, 6, v___x_2202_);
lean_closure_set(v___f_2203_, 7, v___x_2184_);
lean_closure_set(v___f_2203_, 8, v_dir_2194_);
lean_closure_set(v___f_2203_, 9, v_self_2173_);
v___x_2204_ = l_Lake_ensureJob___redArg(v___x_2184_, v___f_2203_, v___y_2172_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2233_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_a_2206_ = lean_ctor_get(v___x_2204_, 1);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2208_ = v___x_2204_;
v_isShared_2209_ = v_isSharedCheck_2233_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2233_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v_task_2210_; lean_object* v_kind_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2231_; 
v_task_2210_ = lean_ctor_get(v_a_2205_, 0);
v_kind_2211_ = lean_ctor_get(v_a_2205_, 1);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_a_2205_);
if (v_isSharedCheck_2231_ == 0)
{
lean_object* v_unused_2232_; 
v_unused_2232_ = lean_ctor_get(v_a_2205_, 2);
lean_dec(v_unused_2232_);
v___x_2213_ = v_a_2205_;
v_isShared_2214_ = v_isSharedCheck_2231_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_kind_2211_);
lean_inc(v_task_2210_);
lean_dec(v_a_2205_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2231_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; lean_object* v_job_2222_; 
v___x_2215_ = lean_st_ref_take(v_registeredJobs_2182_);
v___x_2216_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2191_, v___x_2187_);
v___x_2217_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0));
v___x_2218_ = lean_string_append(v___x_2216_, v___x_2217_);
v___x_2219_ = lean_string_append(v___x_2218_, v___y_2189_);
v___x_2220_ = 0;
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 2, v___x_2219_);
v_job_2222_ = v___x_2213_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_task_2210_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_kind_2211_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v___x_2219_);
v_job_2222_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
lean_ctor_set_uint8(v_job_2222_, sizeof(void*)*3, v___x_2220_);
lean_inc_ref(v_job_2222_);
v___x_2223_ = l_Lake_Job_toOpaque___redArg(v_job_2222_);
v___x_2224_ = lean_array_push(v___x_2215_, v___x_2223_);
v___x_2225_ = lean_st_ref_set(v_registeredJobs_2182_, v___x_2224_);
v___x_2226_ = l_Lake_Job_renew___redArg(v_job_2222_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2226_);
v___x_2228_ = v___x_2208_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_a_2206_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
else
{
lean_dec(v_name_2191_);
return v___x_2204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* v___y_2237_, lean_object* v_self_2238_, lean_object* v_shouldExport_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
uint8_t v_shouldExport_boxed_2246_; lean_object* v_res_2247_; 
v_shouldExport_boxed_2246_ = lean_unbox(v_shouldExport_2239_);
v_res_2247_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2237_, v_self_2238_, v_shouldExport_boxed_2246_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
lean_dec_ref(v_a_2243_);
lean_dec(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec(v_a_2240_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* v_x_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
uint8_t v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = 0;
v___x_2257_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2249_, v_x_2248_, v___x_2256_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object* v_x_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec(v___y_2260_);
return v_res_2266_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2269_; uint8_t v___x_2270_; lean_object* v___x_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___f_2269_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2270_ = 1;
v___x_2271_ = l_Lake_instDataKindFilePath;
v___f_2272_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__0));
v___x_2273_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2274_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v___f_2272_);
lean_ctor_set(v___x_2274_, 2, v___x_2271_);
lean_ctor_set(v___x_2274_, 3, v___f_2269_);
lean_ctor_set_uint8(v___x_2274_, sizeof(void*)*4, v___x_2270_);
lean_ctor_set_uint8(v___x_2274_, sizeof(void*)*4 + 1, v___x_2270_);
return v___x_2274_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = lean_obj_once(&l_Lake_LeanLib_staticFacetConfig___closed__2, &l_Lake_LeanLib_staticFacetConfig___closed__2_once, _init_l_Lake_LeanLib_staticFacetConfig___closed__2);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(lean_object* v_a_2276_, lean_object* v_as_2277_, size_t v_i_2278_, size_t v_stop_2279_, lean_object* v_b_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2276_, v_as_2277_, v_i_2278_, v_stop_2279_, v_b_2280_, v___y_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* v_a_2289_, lean_object* v_as_2290_, lean_object* v_i_2291_, lean_object* v_stop_2292_, lean_object* v_b_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
size_t v_i_boxed_2301_; size_t v_stop_boxed_2302_; lean_object* v_res_2303_; 
v_i_boxed_2301_ = lean_unbox_usize(v_i_2291_);
lean_dec(v_i_2291_);
v_stop_boxed_2302_ = lean_unbox_usize(v_stop_2292_);
lean_dec(v_stop_2292_);
v_res_2303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_2289_, v_as_2290_, v_i_boxed_2301_, v_stop_boxed_2302_, v_b_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec_ref(v_as_2290_);
lean_dec(v_a_2289_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* v_x_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
uint8_t v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = 1;
v___x_2313_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2305_, v_x_2304_, v___x_2312_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object* v_x_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec(v___y_2316_);
return v_res_2322_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___f_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___f_2324_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2325_ = 1;
v___x_2326_ = l_Lake_instDataKindFilePath;
v___f_2327_ = ((lean_object*)(l_Lake_LeanLib_staticExportFacetConfig___closed__0));
v___x_2328_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2329_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v___f_2327_);
lean_ctor_set(v___x_2329_, 2, v___x_2326_);
lean_ctor_set(v___x_2329_, 3, v___f_2324_);
lean_ctor_set_uint8(v___x_2329_, sizeof(void*)*4, v___x_2325_);
lean_ctor_set_uint8(v___x_2329_, sizeof(void*)*4 + 1, v___x_2325_);
return v___x_2329_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig(void){
_start:
{
lean_object* v___x_2330_; 
v___x_2330_ = lean_obj_once(&l_Lake_LeanLib_staticExportFacetConfig___closed__1, &l_Lake_LeanLib_staticExportFacetConfig___closed__1_once, _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1);
return v___x_2330_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0(void){
_start:
{
uint8_t v___x_2331_; lean_object* v_name_2332_; lean_object* v___x_2333_; 
v___x_2331_ = 1;
v_name_2332_ = l_Lake_instDataKindDynlib;
v___x_2333_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2332_, v___x_2331_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object* v_defaultPkg_2334_, lean_object* v_self_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
uint8_t v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = 1;
lean_inc_ref_n(v_self_2335_, 2);
v___x_2344_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_2334_, v_self_2335_, v_self_2335_, v___x_2343_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v_snd_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2387_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
v_snd_2346_ = lean_ctor_get(v_a_2345_, 1);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_a_2345_);
if (v_isSharedCheck_2387_ == 0)
{
lean_object* v_unused_2388_; 
v_unused_2388_ = lean_ctor_get(v_a_2345_, 0);
lean_dec(v_unused_2388_);
v___x_2348_ = v_a_2345_;
v_isShared_2349_ = v_isSharedCheck_2387_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_snd_2346_);
lean_dec(v_a_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2387_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2385_; 
v_a_2350_ = lean_ctor_get(v___x_2344_, 1);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; 
v_unused_2386_ = lean_ctor_get(v___x_2344_, 0);
lean_dec(v_unused_2386_);
v___x_2352_ = v___x_2344_;
v_isShared_2353_ = v_isSharedCheck_2385_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2344_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2385_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v_kind_2354_; lean_object* v_name_2355_; lean_object* v___y_2357_; uint8_t v___x_2375_; 
v_kind_2354_ = lean_ctor_get(v_snd_2346_, 1);
v_name_2355_ = l_Lake_instDataKindDynlib;
v___x_2375_ = lean_name_eq(v_kind_2354_, v_name_2355_);
if (v___x_2375_ == 0)
{
uint8_t v___x_2376_; 
lean_inc(v_kind_2354_);
lean_del_object(v___x_2348_);
lean_dec(v_snd_2346_);
v___x_2376_ = l_Lean_Name_isAnonymous(v_kind_2354_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2377_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_2378_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2354_, v___x_2343_);
v___x_2379_ = lean_string_append(v___x_2377_, v___x_2378_);
lean_dec_ref(v___x_2378_);
v___x_2380_ = lean_string_append(v___x_2379_, v___x_2377_);
v___y_2357_ = v___x_2380_;
goto v___jp_2356_;
}
else
{
lean_object* v___x_2381_; 
lean_dec(v_kind_2354_);
v___x_2381_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_2357_ = v___x_2381_;
goto v___jp_2356_;
}
}
else
{
lean_object* v___x_2383_; 
lean_del_object(v___x_2352_);
lean_dec_ref(v_self_2335_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 1, v_a_2350_);
lean_ctor_set(v___x_2348_, 0, v_snd_2346_);
v___x_2383_ = v___x_2348_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_snd_2346_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_a_2350_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
v___jp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2358_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_2359_ = l_Lake_PartialBuildKey_toString(v_self_2335_);
v___x_2360_ = lean_string_append(v___x_2358_, v___x_2359_);
lean_dec_ref(v___x_2359_);
v___x_2361_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_2362_ = lean_string_append(v___x_2360_, v___x_2361_);
v___x_2363_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0);
v___x_2364_ = lean_string_append(v___x_2362_, v___x_2363_);
v___x_2365_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_2366_ = lean_string_append(v___x_2364_, v___x_2365_);
v___x_2367_ = lean_string_append(v___x_2366_, v___y_2357_);
lean_dec_ref(v___y_2357_);
v___x_2368_ = 3;
v___x_2369_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set_uint8(v___x_2369_, sizeof(void*)*1, v___x_2368_);
v___x_2370_ = lean_array_get_size(v_a_2350_);
v___x_2371_ = lean_array_push(v_a_2350_, v___x_2369_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set_tag(v___x_2352_, 1);
lean_ctor_set(v___x_2352_, 1, v___x_2371_);
lean_ctor_set(v___x_2352_, 0, v___x_2370_);
v___x_2373_ = v___x_2352_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v_self_2335_);
v_a_2389_ = lean_ctor_get(v___x_2344_, 0);
v_a_2390_ = lean_ctor_get(v___x_2344_, 1);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2344_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_inc(v_a_2389_);
lean_dec(v___x_2344_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2389_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* v_defaultPkg_2398_, lean_object* v_self_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_2398_, v_self_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec(v_a_2401_);
return v_res_2407_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0));
v___x_2411_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
lean_ctor_set(v___x_2412_, 1, v___x_2410_);
return v___x_2412_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5(void){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object* v___x_2414_, lean_object* v_as_2415_, size_t v_i_2416_, size_t v_stop_2417_, lean_object* v_b_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
uint8_t v___x_2426_; 
v___x_2426_ = lean_usize_dec_eq(v_i_2416_, v_stop_2417_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = lean_array_uget_borrowed(v_as_2415_, v_i_2416_);
lean_inc_ref(v___y_2419_);
lean_inc(v___x_2427_);
lean_inc_ref(v___x_2414_);
v___x_2428_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_2414_, v___x_2427_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v_a_2430_; lean_object* v___x_2431_; size_t v___x_2432_; size_t v___x_2433_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
v_a_2430_ = lean_ctor_get(v___x_2428_, 1);
lean_inc(v_a_2430_);
lean_dec_ref(v___x_2428_);
v___x_2431_ = lean_array_push(v_b_2418_, v_a_2429_);
v___x_2432_ = ((size_t)1ULL);
v___x_2433_ = lean_usize_add(v_i_2416_, v___x_2432_);
v_i_2416_ = v___x_2433_;
v_b_2418_ = v___x_2431_;
v___y_2424_ = v_a_2430_;
goto _start;
}
else
{
lean_object* v_a_2435_; lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec_ref(v___y_2419_);
lean_dec_ref(v_b_2418_);
lean_dec_ref(v___x_2414_);
v_a_2435_ = lean_ctor_get(v___x_2428_, 0);
v_a_2436_ = lean_ctor_get(v___x_2428_, 1);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2428_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_inc(v_a_2435_);
lean_dec(v___x_2428_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2435_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
lean_object* v___x_2444_; 
lean_dec_ref(v___y_2419_);
lean_dec_ref(v___x_2414_);
v___x_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2444_, 0, v_b_2418_);
lean_ctor_set(v___x_2444_, 1, v___y_2424_);
return v___x_2444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* v___x_2445_, lean_object* v_as_2446_, lean_object* v_i_2447_, lean_object* v_stop_2448_, lean_object* v_b_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
size_t v_i_boxed_2457_; size_t v_stop_boxed_2458_; lean_object* v_res_2459_; 
v_i_boxed_2457_ = lean_unbox_usize(v_i_2447_);
lean_dec(v_i_2447_);
v_stop_boxed_2458_ = lean_unbox_usize(v_stop_2448_);
lean_dec(v_stop_2448_);
v_res_2459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_2445_, v_as_2446_, v_i_boxed_2457_, v_stop_boxed_2458_, v_b_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v_as_2446_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object* v_self_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v_toHashSet_2462_; lean_object* v_toArray_2463_; uint8_t v___x_2464_; 
v_toHashSet_2462_ = lean_ctor_get(v_self_2460_, 0);
v_toArray_2463_ = lean_ctor_get(v_self_2460_, 1);
v___x_2464_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_2462_, v_a_2461_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2474_; 
lean_inc_ref(v_toArray_2463_);
lean_inc_ref(v_toHashSet_2462_);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_self_2460_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; lean_object* v_unused_2476_; 
v_unused_2475_ = lean_ctor_get(v_self_2460_, 1);
lean_dec(v_unused_2475_);
v_unused_2476_ = lean_ctor_get(v_self_2460_, 0);
lean_dec(v_unused_2476_);
v___x_2466_ = v_self_2460_;
v_isShared_2467_ = v_isSharedCheck_2474_;
goto v_resetjp_2465_;
}
else
{
lean_dec(v_self_2460_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2474_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2468_ = lean_box(0);
lean_inc_ref(v_a_2461_);
v___x_2469_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_toHashSet_2462_, v_a_2461_, v___x_2468_);
v___x_2470_ = lean_array_push(v_toArray_2463_, v_a_2461_);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 1, v___x_2470_);
lean_ctor_set(v___x_2466_, 0, v___x_2469_);
v___x_2472_ = v___x_2466_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
else
{
lean_dec_ref(v_a_2461_);
return v_self_2460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object* v_as_2477_, size_t v_i_2478_, size_t v_stop_2479_, lean_object* v_b_2480_){
_start:
{
uint8_t v___x_2481_; 
v___x_2481_ = lean_usize_dec_eq(v_i_2478_, v_stop_2479_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; size_t v___x_2484_; size_t v___x_2485_; 
v___x_2482_ = lean_array_uget_borrowed(v_as_2477_, v_i_2478_);
lean_inc(v___x_2482_);
v___x_2483_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_2480_, v___x_2482_);
v___x_2484_ = ((size_t)1ULL);
v___x_2485_ = lean_usize_add(v_i_2478_, v___x_2484_);
v_i_2478_ = v___x_2485_;
v_b_2480_ = v___x_2483_;
goto _start;
}
else
{
return v_b_2480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object* v_as_2487_, lean_object* v_i_2488_, lean_object* v_stop_2489_, lean_object* v_b_2490_){
_start:
{
size_t v_i_boxed_2491_; size_t v_stop_boxed_2492_; lean_object* v_res_2493_; 
v_i_boxed_2491_ = lean_unbox_usize(v_i_2488_);
lean_dec(v_i_2488_);
v_stop_boxed_2492_ = lean_unbox_usize(v_stop_2489_);
lean_dec(v_stop_2489_);
v_res_2493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_2487_, v_i_boxed_2491_, v_stop_boxed_2492_, v_b_2490_);
lean_dec_ref(v_as_2487_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object* v_self_2494_, lean_object* v_arr_2495_){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v___x_2496_ = lean_unsigned_to_nat(0u);
v___x_2497_ = lean_array_get_size(v_arr_2495_);
v___x_2498_ = lean_nat_dec_lt(v___x_2496_, v___x_2497_);
if (v___x_2498_ == 0)
{
return v_self_2494_;
}
else
{
uint8_t v___x_2499_; 
v___x_2499_ = lean_nat_dec_le(v___x_2497_, v___x_2497_);
if (v___x_2499_ == 0)
{
if (v___x_2498_ == 0)
{
return v_self_2494_;
}
else
{
size_t v___x_2500_; size_t v___x_2501_; lean_object* v___x_2502_; 
v___x_2500_ = ((size_t)0ULL);
v___x_2501_ = lean_usize_of_nat(v___x_2497_);
v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2495_, v___x_2500_, v___x_2501_, v_self_2494_);
return v___x_2502_;
}
}
else
{
size_t v___x_2503_; size_t v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = ((size_t)0ULL);
v___x_2504_ = lean_usize_of_nat(v___x_2497_);
v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2495_, v___x_2503_, v___x_2504_, v_self_2494_);
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(lean_object* v_self_2506_, lean_object* v_arr_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_self_2506_, v_arr_2507_);
lean_dec_ref(v_arr_2507_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(lean_object* v_as_2509_, size_t v_i_2510_, size_t v_stop_2511_, lean_object* v_b_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_usize_dec_eq(v_i_2510_, v_stop_2511_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; lean_object* v_lib_2522_; lean_object* v_pkg_2523_; lean_object* v_name_2524_; lean_object* v_keyName_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2521_ = lean_array_uget_borrowed(v_as_2509_, v_i_2510_);
v_lib_2522_ = lean_ctor_get(v___x_2521_, 0);
v_pkg_2523_ = lean_ctor_get(v_lib_2522_, 0);
v_name_2524_ = lean_ctor_get(v___x_2521_, 1);
v_keyName_2525_ = lean_ctor_get(v_pkg_2523_, 2);
v___x_2526_ = l_Lake_Module_transImportsFacet;
lean_inc(v_name_2524_);
lean_inc(v_keyName_2525_);
v___x_2527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2527_, 0, v_keyName_2525_);
lean_ctor_set(v___x_2527_, 1, v_name_2524_);
v___x_2528_ = l_Lake_Module_keyword;
lean_inc(v___x_2521_);
v___x_2529_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2527_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
lean_ctor_set(v___x_2529_, 2, v___x_2521_);
lean_ctor_set(v___x_2529_, 3, v___x_2526_);
lean_inc_ref(v___y_2513_);
lean_inc_ref(v___y_2517_);
lean_inc(v___y_2516_);
lean_inc(v___y_2515_);
lean_inc(v___y_2514_);
v___x_2530_ = lean_apply_7(v___y_2513_, v___x_2529_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, lean_box(0));
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v_a_2532_; lean_object* v___x_2533_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
v_a_2532_ = lean_ctor_get(v___x_2530_, 1);
lean_inc(v_a_2532_);
lean_dec_ref(v___x_2530_);
v___x_2533_ = l_Lake_Job_await___redArg(v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v_a_2535_; lean_object* v___x_2536_; size_t v___x_2537_; size_t v___x_2538_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
v_a_2535_ = lean_ctor_get(v___x_2533_, 1);
lean_inc(v_a_2535_);
lean_dec_ref(v___x_2533_);
v___x_2536_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_b_2512_, v_a_2534_);
lean_dec(v_a_2534_);
v___x_2537_ = ((size_t)1ULL);
v___x_2538_ = lean_usize_add(v_i_2510_, v___x_2537_);
v_i_2510_ = v___x_2538_;
v_b_2512_ = v___x_2536_;
v___y_2518_ = v_a_2535_;
goto _start;
}
else
{
lean_object* v_a_2540_; lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec_ref(v___y_2513_);
lean_dec_ref(v_b_2512_);
v_a_2540_ = lean_ctor_get(v___x_2533_, 0);
v_a_2541_ = lean_ctor_get(v___x_2533_, 1);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2533_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_inc(v_a_2540_);
lean_dec(v___x_2533_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2540_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
lean_dec_ref(v___y_2513_);
lean_dec_ref(v_b_2512_);
v_a_2549_ = lean_ctor_get(v___x_2530_, 0);
v_a_2550_ = lean_ctor_get(v___x_2530_, 1);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2530_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_inc(v_a_2549_);
lean_dec(v___x_2530_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2549_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v_a_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
else
{
lean_object* v___x_2558_; 
lean_dec_ref(v___y_2513_);
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v_b_2512_);
lean_ctor_set(v___x_2558_, 1, v___y_2518_);
return v___x_2558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object* v_as_2559_, lean_object* v_i_2560_, lean_object* v_stop_2561_, lean_object* v_b_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
size_t v_i_boxed_2570_; size_t v_stop_boxed_2571_; lean_object* v_res_2572_; 
v_i_boxed_2570_ = lean_unbox_usize(v_i_2560_);
lean_dec(v_i_2560_);
v_stop_boxed_2571_ = lean_unbox_usize(v_stop_2561_);
lean_dec(v_stop_2561_);
v_res_2572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_as_2559_, v_i_boxed_2570_, v_stop_boxed_2571_, v_b_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v_as_2559_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(lean_object* v_as_2573_, size_t v_i_2574_, size_t v_stop_2575_, lean_object* v_b_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_){
_start:
{
uint8_t v___x_2584_; 
v___x_2584_ = lean_usize_dec_eq(v_i_2574_, v_stop_2575_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; lean_object* v_pkg_2586_; lean_object* v_name_2587_; lean_object* v_keyName_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2585_ = lean_array_uget_borrowed(v_as_2573_, v_i_2574_);
v_pkg_2586_ = lean_ctor_get(v___x_2585_, 0);
v_name_2587_ = lean_ctor_get(v___x_2585_, 1);
v_keyName_2588_ = lean_ctor_get(v_pkg_2586_, 2);
v___x_2589_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_2587_);
lean_inc(v_keyName_2588_);
v___x_2590_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2590_, 0, v_keyName_2588_);
lean_ctor_set(v___x_2590_, 1, v_name_2587_);
v___x_2591_ = l_Lake_ExternLib_keyword;
lean_inc(v___x_2585_);
v___x_2592_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2590_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
lean_ctor_set(v___x_2592_, 2, v___x_2585_);
lean_ctor_set(v___x_2592_, 3, v___x_2589_);
lean_inc_ref(v___y_2577_);
lean_inc_ref(v___y_2581_);
lean_inc(v___y_2580_);
lean_inc(v___y_2579_);
lean_inc(v___y_2578_);
v___x_2593_ = lean_apply_7(v___y_2577_, v___x_2592_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, lean_box(0));
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v_a_2595_; lean_object* v___x_2596_; size_t v___x_2597_; size_t v___x_2598_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
v_a_2595_ = lean_ctor_get(v___x_2593_, 1);
lean_inc(v_a_2595_);
lean_dec_ref(v___x_2593_);
v___x_2596_ = lean_array_push(v_b_2576_, v_a_2594_);
v___x_2597_ = ((size_t)1ULL);
v___x_2598_ = lean_usize_add(v_i_2574_, v___x_2597_);
v_i_2574_ = v___x_2598_;
v_b_2576_ = v___x_2596_;
v___y_2582_ = v_a_2595_;
goto _start;
}
else
{
lean_object* v_a_2600_; lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec_ref(v___y_2577_);
lean_dec_ref(v_b_2576_);
v_a_2600_ = lean_ctor_get(v___x_2593_, 0);
v_a_2601_ = lean_ctor_get(v___x_2593_, 1);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2593_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_inc(v_a_2600_);
lean_dec(v___x_2593_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2600_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
else
{
lean_object* v___x_2609_; 
lean_dec_ref(v___y_2577_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v_b_2576_);
lean_ctor_set(v___x_2609_, 1, v___y_2582_);
return v___x_2609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(lean_object* v_as_2610_, lean_object* v_i_2611_, lean_object* v_stop_2612_, lean_object* v_b_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
size_t v_i_boxed_2621_; size_t v_stop_boxed_2622_; lean_object* v_res_2623_; 
v_i_boxed_2621_ = lean_unbox_usize(v_i_2611_);
lean_dec(v_i_2611_);
v_stop_boxed_2622_ = lean_unbox_usize(v_stop_2612_);
lean_dec(v_stop_2612_);
v_res_2623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v_as_2610_, v_i_boxed_2621_, v_stop_boxed_2622_, v_b_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v_as_2610_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(lean_object* v_as_2624_, size_t v_i_2625_, size_t v_stop_2626_, lean_object* v_b_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v_a_2636_; lean_object* v_a_2637_; uint8_t v___x_2641_; 
v___x_2641_ = lean_usize_dec_eq(v_i_2625_, v_stop_2626_);
if (v___x_2641_ == 0)
{
lean_object* v_fst_2642_; lean_object* v_snd_2643_; lean_object* v___x_2644_; lean_object* v_lib_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2682_; 
v_fst_2642_ = lean_ctor_get(v_b_2627_, 0);
v_snd_2643_ = lean_ctor_get(v_b_2627_, 1);
v___x_2644_ = lean_array_uget(v_as_2624_, v_i_2625_);
v_lib_2645_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2682_ == 0)
{
lean_object* v_unused_2683_; 
v_unused_2683_ = lean_ctor_get(v___x_2644_, 1);
lean_dec(v_unused_2683_);
v___x_2647_ = v___x_2644_;
v_isShared_2648_ = v_isSharedCheck_2682_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_lib_2645_);
lean_dec(v___x_2644_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2682_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v_pkg_2649_; lean_object* v_name_2650_; uint8_t v___x_2651_; 
v_pkg_2649_ = lean_ctor_get(v_lib_2645_, 0);
v_name_2650_ = lean_ctor_get(v_lib_2645_, 1);
lean_inc(v_name_2650_);
v___x_2651_ = l_Lean_NameSet_contains(v_fst_2642_, v_name_2650_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2679_; 
lean_inc(v_snd_2643_);
lean_inc(v_fst_2642_);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_b_2627_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; lean_object* v_unused_2681_; 
v_unused_2680_ = lean_ctor_get(v_b_2627_, 1);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_b_2627_, 0);
lean_dec(v_unused_2681_);
v___x_2653_ = v_b_2627_;
v_isShared_2654_ = v_isSharedCheck_2679_;
goto v_resetjp_2652_;
}
else
{
lean_dec(v_b_2627_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2679_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v_keyName_2655_; lean_object* v___x_2656_; lean_object* v___x_2658_; 
v_keyName_2655_ = lean_ctor_get(v_pkg_2649_, 2);
v___x_2656_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_2650_);
lean_inc(v_keyName_2655_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set_tag(v___x_2647_, 3);
lean_ctor_set(v___x_2647_, 1, v_name_2650_);
lean_ctor_set(v___x_2647_, 0, v_keyName_2655_);
v___x_2658_ = v___x_2647_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_keyName_2655_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_name_2650_);
v___x_2658_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2659_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2660_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2658_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
lean_ctor_set(v___x_2660_, 2, v_lib_2645_);
lean_ctor_set(v___x_2660_, 3, v___x_2656_);
lean_inc_ref(v___y_2628_);
lean_inc_ref(v___y_2632_);
lean_inc(v___y_2631_);
lean_inc(v___y_2630_);
lean_inc(v___y_2629_);
v___x_2661_ = lean_apply_7(v___y_2628_, v___x_2660_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, lean_box(0));
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v_a_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
v_a_2663_ = lean_ctor_get(v___x_2661_, 1);
lean_inc(v_a_2663_);
lean_dec_ref(v___x_2661_);
v___x_2664_ = lean_array_push(v_snd_2643_, v_a_2662_);
v___x_2665_ = l_Lean_NameSet_insert(v_fst_2642_, v_name_2650_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 1, v___x_2664_);
lean_ctor_set(v___x_2653_, 0, v___x_2665_);
v___x_2667_ = v___x_2653_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v___x_2664_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
v_a_2636_ = v___x_2667_;
v_a_2637_ = v_a_2663_;
goto v___jp_2635_;
}
}
else
{
lean_object* v_a_2669_; lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_del_object(v___x_2653_);
lean_dec(v_name_2650_);
lean_dec(v_snd_2643_);
lean_dec(v_fst_2642_);
lean_dec_ref(v___y_2628_);
v_a_2669_ = lean_ctor_get(v___x_2661_, 0);
v_a_2670_ = lean_ctor_get(v___x_2661_, 1);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2661_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_inc(v_a_2669_);
lean_dec(v___x_2661_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2669_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
}
else
{
lean_dec(v_name_2650_);
lean_del_object(v___x_2647_);
lean_dec_ref(v_lib_2645_);
v_a_2636_ = v_b_2627_;
v_a_2637_ = v___y_2633_;
goto v___jp_2635_;
}
}
}
else
{
lean_object* v___x_2684_; 
lean_dec_ref(v___y_2628_);
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v_b_2627_);
lean_ctor_set(v___x_2684_, 1, v___y_2633_);
return v___x_2684_;
}
v___jp_2635_:
{
size_t v___x_2638_; size_t v___x_2639_; 
v___x_2638_ = ((size_t)1ULL);
v___x_2639_ = lean_usize_add(v_i_2625_, v___x_2638_);
v_i_2625_ = v___x_2639_;
v_b_2627_ = v_a_2636_;
v___y_2633_ = v_a_2637_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object* v_as_2685_, lean_object* v_i_2686_, lean_object* v_stop_2687_, lean_object* v_b_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
size_t v_i_boxed_2696_; size_t v_stop_boxed_2697_; lean_object* v_res_2698_; 
v_i_boxed_2696_ = lean_unbox_usize(v_i_2686_);
lean_dec(v_i_2686_);
v_stop_boxed_2697_ = lean_unbox_usize(v_stop_2687_);
lean_dec(v_stop_2687_);
v_res_2698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_as_2685_, v_i_boxed_2696_, v_stop_boxed_2697_, v_b_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v_as_2685_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(lean_object* v___x_2699_, lean_object* v_as_2700_, size_t v_i_2701_, size_t v_stop_2702_, lean_object* v_b_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
uint8_t v___x_2711_; 
v___x_2711_ = lean_usize_dec_eq(v_i_2701_, v_stop_2702_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = lean_array_uget_borrowed(v_as_2700_, v_i_2701_);
lean_inc_ref(v___y_2704_);
lean_inc(v___x_2712_);
lean_inc_ref(v___x_2699_);
v___x_2713_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v___x_2699_, v___x_2712_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v_a_2715_; lean_object* v___x_2716_; size_t v___x_2717_; size_t v___x_2718_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
v_a_2715_ = lean_ctor_get(v___x_2713_, 1);
lean_inc(v_a_2715_);
lean_dec_ref(v___x_2713_);
v___x_2716_ = lean_array_push(v_b_2703_, v_a_2714_);
v___x_2717_ = ((size_t)1ULL);
v___x_2718_ = lean_usize_add(v_i_2701_, v___x_2717_);
v_i_2701_ = v___x_2718_;
v_b_2703_ = v___x_2716_;
v___y_2709_ = v_a_2715_;
goto _start;
}
else
{
lean_object* v_a_2720_; lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
lean_dec_ref(v___y_2704_);
lean_dec_ref(v_b_2703_);
lean_dec_ref(v___x_2699_);
v_a_2720_ = lean_ctor_get(v___x_2713_, 0);
v_a_2721_ = lean_ctor_get(v___x_2713_, 1);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2713_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_inc(v_a_2720_);
lean_dec(v___x_2713_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2720_);
lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
else
{
lean_object* v___x_2729_; 
lean_dec_ref(v___y_2704_);
lean_dec_ref(v___x_2699_);
v___x_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2729_, 0, v_b_2703_);
lean_ctor_set(v___x_2729_, 1, v___y_2709_);
return v___x_2729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object* v___x_2730_, lean_object* v_as_2731_, lean_object* v_i_2732_, lean_object* v_stop_2733_, lean_object* v_b_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
size_t v_i_boxed_2742_; size_t v_stop_boxed_2743_; lean_object* v_res_2744_; 
v_i_boxed_2742_ = lean_unbox_usize(v_i_2732_);
lean_dec(v_i_2732_);
v_stop_boxed_2743_ = lean_unbox_usize(v_stop_2733_);
lean_dec(v_stop_2733_);
v_res_2744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v___x_2730_, v_as_2731_, v_i_boxed_2742_, v_stop_boxed_2743_, v_b_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v_as_2731_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(lean_object* v___x_2745_, lean_object* v_as_2746_, size_t v_i_2747_, size_t v_stop_2748_, lean_object* v_b_2749_){
_start:
{
lean_object* v___y_2751_; uint8_t v___x_2755_; 
v___x_2755_ = lean_usize_dec_eq(v_i_2747_, v_stop_2748_);
if (v___x_2755_ == 0)
{
lean_object* v_toConfigDecl_2756_; lean_object* v_name_2757_; lean_object* v_kind_2758_; lean_object* v_config_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; 
v_toConfigDecl_2756_ = lean_array_uget_borrowed(v_as_2746_, v_i_2747_);
v_name_2757_ = lean_ctor_get(v_toConfigDecl_2756_, 1);
v_kind_2758_ = lean_ctor_get(v_toConfigDecl_2756_, 2);
v_config_2759_ = lean_ctor_get(v_toConfigDecl_2756_, 3);
v___x_2760_ = l_Lake_ExternLib_keyword;
v___x_2761_ = lean_name_eq(v_kind_2758_, v___x_2760_);
if (v___x_2761_ == 0)
{
v___y_2751_ = v_b_2749_;
goto v___jp_2750_;
}
else
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_inc(v_config_2759_);
lean_inc(v_name_2757_);
lean_inc_ref(v___x_2745_);
v___x_2762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2745_);
lean_ctor_set(v___x_2762_, 1, v_name_2757_);
lean_ctor_set(v___x_2762_, 2, v_config_2759_);
v___x_2763_ = lean_array_push(v_b_2749_, v___x_2762_);
v___y_2751_ = v___x_2763_;
goto v___jp_2750_;
}
}
else
{
lean_dec_ref(v___x_2745_);
return v_b_2749_;
}
v___jp_2750_:
{
size_t v___x_2752_; size_t v___x_2753_; 
v___x_2752_ = ((size_t)1ULL);
v___x_2753_ = lean_usize_add(v_i_2747_, v___x_2752_);
v_i_2747_ = v___x_2753_;
v_b_2749_ = v___y_2751_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(lean_object* v___x_2764_, lean_object* v_as_2765_, lean_object* v_i_2766_, lean_object* v_stop_2767_, lean_object* v_b_2768_){
_start:
{
size_t v_i_boxed_2769_; size_t v_stop_boxed_2770_; lean_object* v_res_2771_; 
v_i_boxed_2769_ = lean_unbox_usize(v_i_2766_);
lean_dec(v_i_2766_);
v_stop_boxed_2770_ = lean_unbox_usize(v_stop_2767_);
lean_dec(v_stop_2767_);
v_res_2771_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v___x_2764_, v_as_2765_, v_i_boxed_2769_, v_stop_boxed_2770_, v_b_2768_);
lean_dec_ref(v_as_2765_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(lean_object* v_as_2772_, size_t v_i_2773_, size_t v_stop_2774_, lean_object* v_b_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
uint8_t v___x_2783_; 
v___x_2783_ = lean_usize_dec_eq(v_i_2773_, v_stop_2774_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; lean_object* v_lib_2785_; lean_object* v_config_2786_; lean_object* v_nativeFacets_2787_; uint8_t v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; size_t v_sz_2791_; size_t v___x_2792_; lean_object* v___x_2793_; 
v___x_2784_ = lean_array_uget_borrowed(v_as_2772_, v_i_2773_);
v_lib_2785_ = lean_ctor_get(v___x_2784_, 0);
v_config_2786_ = lean_ctor_get(v_lib_2785_, 2);
v_nativeFacets_2787_ = lean_ctor_get(v_config_2786_, 8);
v___x_2788_ = 1;
v___x_2789_ = lean_box(v___x_2788_);
lean_inc_ref(v_nativeFacets_2787_);
v___x_2790_ = lean_apply_1(v_nativeFacets_2787_, v___x_2789_);
v_sz_2791_ = lean_array_size(v___x_2790_);
v___x_2792_ = ((size_t)0ULL);
lean_inc_ref(v___y_2776_);
lean_inc(v___x_2784_);
v___x_2793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2784_, v_sz_2791_, v___x_2792_, v___x_2790_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v_a_2795_; lean_object* v___x_2796_; size_t v___x_2797_; size_t v___x_2798_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
v_a_2795_ = lean_ctor_get(v___x_2793_, 1);
lean_inc(v_a_2795_);
lean_dec_ref(v___x_2793_);
v___x_2796_ = l_Array_append___redArg(v_b_2775_, v_a_2794_);
lean_dec(v_a_2794_);
v___x_2797_ = ((size_t)1ULL);
v___x_2798_ = lean_usize_add(v_i_2773_, v___x_2797_);
v_i_2773_ = v___x_2798_;
v_b_2775_ = v___x_2796_;
v___y_2781_ = v_a_2795_;
goto _start;
}
else
{
lean_dec_ref(v___y_2776_);
lean_dec_ref(v_b_2775_);
return v___x_2793_;
}
}
else
{
lean_object* v___x_2800_; 
lean_dec_ref(v___y_2776_);
v___x_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2800_, 0, v_b_2775_);
lean_ctor_set(v___x_2800_, 1, v___y_2781_);
return v___x_2800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object* v_as_2801_, lean_object* v_i_2802_, lean_object* v_stop_2803_, lean_object* v_b_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
size_t v_i_boxed_2812_; size_t v_stop_boxed_2813_; lean_object* v_res_2814_; 
v_i_boxed_2812_ = lean_unbox_usize(v_i_2802_);
lean_dec(v_i_2802_);
v_stop_boxed_2813_ = lean_unbox_usize(v_stop_2803_);
lean_dec(v_stop_2803_);
v_res_2814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_as_2801_, v_i_boxed_2812_, v_stop_boxed_2813_, v_b_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v_as_2801_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(lean_object* v___x_2815_, lean_object* v___x_2816_, lean_object* v_self_2817_, lean_object* v_dir_2818_, lean_object* v_targetDecls_2819_, lean_object* v_pkg_2820_, lean_object* v_name_2821_, lean_object* v_config_2822_, lean_object* v_config_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v_a_2839_; lean_object* v_a_2840_; lean_object* v_a_2857_; lean_object* v_a_2858_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v_a_2903_; lean_object* v_a_2904_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v_snd_2940_; lean_object* v_a_2941_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v_a_2980_; lean_object* v_a_2981_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___x_3019_; 
lean_inc_ref(v___y_2824_);
lean_inc_ref(v___y_2828_);
lean_inc(v___y_2827_);
lean_inc(v___y_2826_);
lean_inc(v___x_2816_);
v___x_3019_ = lean_apply_7(v___y_2824_, v___x_2815_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, lean_box(0));
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v_a_3021_; lean_object* v___x_3022_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
v_a_3021_ = lean_ctor_get(v___x_3019_, 1);
lean_inc(v_a_3021_);
lean_dec_ref(v___x_3019_);
v___x_3022_ = l_Lake_Job_await___redArg(v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v_a_3024_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v_a_3035_; lean_object* v_a_3036_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v_a_3070_; lean_object* v_a_3071_; lean_object* v___y_3096_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
v_a_3024_ = lean_ctor_get(v___x_3022_, 1);
lean_inc(v_a_3024_);
lean_dec_ref(v___x_3022_);
v___x_3108_ = lean_unsigned_to_nat(0u);
v___x_3109_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_3110_ = lean_array_get_size(v_a_3023_);
v___x_3111_ = lean_nat_dec_lt(v___x_3108_, v___x_3110_);
if (v___x_3111_ == 0)
{
v_a_3070_ = v___x_3109_;
v_a_3071_ = v_a_3024_;
goto v___jp_3069_;
}
else
{
uint8_t v___x_3112_; 
v___x_3112_ = lean_nat_dec_le(v___x_3110_, v___x_3110_);
if (v___x_3112_ == 0)
{
if (v___x_3111_ == 0)
{
v_a_3070_ = v___x_3109_;
v_a_3071_ = v_a_3024_;
goto v___jp_3069_;
}
else
{
size_t v___x_3113_; size_t v___x_3114_; lean_object* v___x_3115_; 
v___x_3113_ = ((size_t)0ULL);
v___x_3114_ = lean_usize_of_nat(v___x_3110_);
lean_inc_ref(v___y_2824_);
v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3023_, v___x_3113_, v___x_3114_, v___x_3109_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_3024_);
v___y_3096_ = v___x_3115_;
goto v___jp_3095_;
}
}
else
{
size_t v___x_3116_; size_t v___x_3117_; lean_object* v___x_3118_; 
v___x_3116_ = ((size_t)0ULL);
v___x_3117_ = lean_usize_of_nat(v___x_3110_);
lean_inc_ref(v___y_2824_);
v___x_3118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3023_, v___x_3116_, v___x_3117_, v___x_3109_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_3024_);
v___y_3096_ = v___x_3118_;
goto v___jp_3095_;
}
}
v___jp_3025_:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; uint8_t v___x_3039_; 
v___x_3037_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
v___x_3038_ = lean_array_get_size(v_a_3023_);
v___x_3039_ = lean_nat_dec_lt(v___y_3032_, v___x_3038_);
if (v___x_3039_ == 0)
{
lean_dec(v_a_3023_);
v___y_2970_ = v___y_3026_;
v___y_2971_ = v___y_3027_;
v___y_2972_ = v___y_3028_;
v___y_2973_ = v___y_3029_;
v___y_2974_ = v___y_3030_;
v___y_2975_ = v_a_3035_;
v___y_2976_ = v___y_3031_;
v___y_2977_ = v___y_3032_;
v___y_2978_ = v___y_3033_;
v___y_2979_ = v___y_3034_;
v_a_2980_ = v___x_3037_;
v_a_2981_ = v_a_3036_;
goto v___jp_2969_;
}
else
{
uint8_t v___x_3040_; 
v___x_3040_ = lean_nat_dec_le(v___x_3038_, v___x_3038_);
if (v___x_3040_ == 0)
{
if (v___x_3039_ == 0)
{
lean_dec(v_a_3023_);
v___y_2970_ = v___y_3026_;
v___y_2971_ = v___y_3027_;
v___y_2972_ = v___y_3028_;
v___y_2973_ = v___y_3029_;
v___y_2974_ = v___y_3030_;
v___y_2975_ = v_a_3035_;
v___y_2976_ = v___y_3031_;
v___y_2977_ = v___y_3032_;
v___y_2978_ = v___y_3033_;
v___y_2979_ = v___y_3034_;
v_a_2980_ = v___x_3037_;
v_a_2981_ = v_a_3036_;
goto v___jp_2969_;
}
else
{
size_t v___x_3041_; size_t v___x_3042_; lean_object* v___x_3043_; 
v___x_3041_ = ((size_t)0ULL);
v___x_3042_ = lean_usize_of_nat(v___x_3038_);
lean_inc_ref(v___y_2824_);
v___x_3043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3023_, v___x_3041_, v___x_3042_, v___x_3037_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_3036_);
lean_dec(v_a_3023_);
v___y_3004_ = v___y_3027_;
v___y_3005_ = v___y_3026_;
v___y_3006_ = v___y_3028_;
v___y_3007_ = v___y_3029_;
v___y_3008_ = v___y_3030_;
v___y_3009_ = v_a_3035_;
v___y_3010_ = v___y_3032_;
v___y_3011_ = v___y_3031_;
v___y_3012_ = v___y_3034_;
v___y_3013_ = v___y_3033_;
v___y_3014_ = v___x_3043_;
goto v___jp_3003_;
}
}
else
{
size_t v___x_3044_; size_t v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = ((size_t)0ULL);
v___x_3045_ = lean_usize_of_nat(v___x_3038_);
lean_inc_ref(v___y_2824_);
v___x_3046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3023_, v___x_3044_, v___x_3045_, v___x_3037_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_3036_);
lean_dec(v_a_3023_);
v___y_3004_ = v___y_3027_;
v___y_3005_ = v___y_3026_;
v___y_3006_ = v___y_3028_;
v___y_3007_ = v___y_3029_;
v___y_3008_ = v___y_3030_;
v___y_3009_ = v_a_3035_;
v___y_3010_ = v___y_3032_;
v___y_3011_ = v___y_3031_;
v___y_3012_ = v___y_3034_;
v___y_3013_ = v___y_3033_;
v___y_3014_ = v___x_3046_;
goto v___jp_3003_;
}
}
}
v___jp_3047_:
{
if (lean_obj_tag(v___y_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v_a_3059_; 
v_a_3058_ = lean_ctor_get(v___y_3057_, 0);
lean_inc(v_a_3058_);
v_a_3059_ = lean_ctor_get(v___y_3057_, 1);
lean_inc(v_a_3059_);
lean_dec_ref(v___y_3057_);
v___y_3026_ = v___y_3049_;
v___y_3027_ = v___y_3048_;
v___y_3028_ = v___y_3050_;
v___y_3029_ = v___y_3051_;
v___y_3030_ = v___y_3052_;
v___y_3031_ = v___y_3054_;
v___y_3032_ = v___y_3053_;
v___y_3033_ = v___y_3056_;
v___y_3034_ = v___y_3055_;
v_a_3035_ = v_a_3058_;
v_a_3036_ = v_a_3059_;
goto v___jp_3025_;
}
else
{
lean_object* v_a_3060_; lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec_ref(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec_ref(v___y_3051_);
lean_dec_ref(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v_a_3023_);
lean_dec_ref(v___y_2824_);
lean_dec(v_name_2821_);
lean_dec_ref(v_pkg_2820_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_3060_ = lean_ctor_get(v___y_3057_, 0);
v_a_3061_ = lean_ctor_get(v___y_3057_, 1);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___y_3057_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___y_3057_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_inc(v_a_3060_);
lean_dec(v___y_3057_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3060_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
v___jp_3069_:
{
lean_object* v_toLeanConfig_3072_; lean_object* v_toLeanConfig_3073_; lean_object* v_buildDir_3074_; lean_object* v_nativeLibDir_3075_; lean_object* v_moreLinkObjs_3076_; lean_object* v_moreLinkLibs_3077_; lean_object* v_moreLinkArgs_3078_; lean_object* v_weakLinkArgs_3079_; lean_object* v_moreLinkObjs_3080_; lean_object* v_moreLinkLibs_3081_; lean_object* v_moreLinkArgs_3082_; lean_object* v_weakLinkArgs_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; 
v_toLeanConfig_3072_ = lean_ctor_get(v_config_2822_, 1);
lean_inc_ref(v_toLeanConfig_3072_);
v_toLeanConfig_3073_ = lean_ctor_get(v_config_2823_, 0);
v_buildDir_3074_ = lean_ctor_get(v_config_2822_, 5);
lean_inc_ref(v_buildDir_3074_);
v_nativeLibDir_3075_ = lean_ctor_get(v_config_2822_, 7);
lean_inc_ref(v_nativeLibDir_3075_);
lean_dec_ref(v_config_2822_);
v_moreLinkObjs_3076_ = lean_ctor_get(v_toLeanConfig_3072_, 6);
lean_inc_ref(v_moreLinkObjs_3076_);
v_moreLinkLibs_3077_ = lean_ctor_get(v_toLeanConfig_3072_, 7);
lean_inc_ref(v_moreLinkLibs_3077_);
v_moreLinkArgs_3078_ = lean_ctor_get(v_toLeanConfig_3072_, 8);
lean_inc_ref(v_moreLinkArgs_3078_);
v_weakLinkArgs_3079_ = lean_ctor_get(v_toLeanConfig_3072_, 9);
lean_inc_ref(v_weakLinkArgs_3079_);
lean_dec_ref(v_toLeanConfig_3072_);
v_moreLinkObjs_3080_ = lean_ctor_get(v_toLeanConfig_3073_, 6);
v_moreLinkLibs_3081_ = lean_ctor_get(v_toLeanConfig_3073_, 7);
v_moreLinkArgs_3082_ = lean_ctor_get(v_toLeanConfig_3073_, 8);
v_weakLinkArgs_3083_ = lean_ctor_get(v_toLeanConfig_3073_, 9);
v___x_3084_ = l_Array_append___redArg(v_moreLinkObjs_3076_, v_moreLinkObjs_3080_);
v___x_3085_ = lean_unsigned_to_nat(0u);
v___x_3086_ = lean_array_get_size(v___x_3084_);
v___x_3087_ = lean_nat_dec_lt(v___x_3085_, v___x_3086_);
if (v___x_3087_ == 0)
{
lean_dec_ref(v___x_3084_);
v___y_3026_ = v_moreLinkLibs_3077_;
v___y_3027_ = v_moreLinkArgs_3078_;
v___y_3028_ = v_moreLinkLibs_3081_;
v___y_3029_ = v_buildDir_3074_;
v___y_3030_ = v_moreLinkArgs_3082_;
v___y_3031_ = v_nativeLibDir_3075_;
v___y_3032_ = v___x_3085_;
v___y_3033_ = v_weakLinkArgs_3083_;
v___y_3034_ = v_weakLinkArgs_3079_;
v_a_3035_ = v_a_3070_;
v_a_3036_ = v_a_3071_;
goto v___jp_3025_;
}
else
{
uint8_t v___x_3088_; 
v___x_3088_ = lean_nat_dec_le(v___x_3086_, v___x_3086_);
if (v___x_3088_ == 0)
{
if (v___x_3087_ == 0)
{
lean_dec_ref(v___x_3084_);
v___y_3026_ = v_moreLinkLibs_3077_;
v___y_3027_ = v_moreLinkArgs_3078_;
v___y_3028_ = v_moreLinkLibs_3081_;
v___y_3029_ = v_buildDir_3074_;
v___y_3030_ = v_moreLinkArgs_3082_;
v___y_3031_ = v_nativeLibDir_3075_;
v___y_3032_ = v___x_3085_;
v___y_3033_ = v_weakLinkArgs_3083_;
v___y_3034_ = v_weakLinkArgs_3079_;
v_a_3035_ = v_a_3070_;
v_a_3036_ = v_a_3071_;
goto v___jp_3025_;
}
else
{
size_t v___x_3089_; size_t v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = ((size_t)0ULL);
v___x_3090_ = lean_usize_of_nat(v___x_3086_);
lean_inc_ref(v___y_2824_);
lean_inc_ref(v_pkg_2820_);
v___x_3091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2820_, v___x_3084_, v___x_3089_, v___x_3090_, v_a_3070_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_3071_);
lean_dec_ref(v___x_3084_);
v___y_3048_ = v_moreLinkArgs_3078_;
v___y_3049_ = v_moreLinkLibs_3077_;
v___y_3050_ = v_moreLinkLibs_3081_;
v___y_3051_ = v_buildDir_3074_;
v___y_3052_ = v_moreLinkArgs_3082_;
v___y_3053_ = v___x_3085_;
v___y_3054_ = v_nativeLibDir_3075_;
v___y_3055_ = v_weakLinkArgs_3079_;
v___y_3056_ = v_weakLinkArgs_3083_;
v___y_3057_ = v___x_3091_;
goto v___jp_3047_;
}
}
else
{
size_t v___x_3092_; size_t v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = ((size_t)0ULL);
v___x_3093_ = lean_usize_of_nat(v___x_3086_);
lean_inc_ref(v___y_2824_);
lean_inc_ref(v_pkg_2820_);
v___x_3094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2820_, v___x_3084_, v___x_3092_, v___x_3093_, v_a_3070_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_3071_);
lean_dec_ref(v___x_3084_);
v___y_3048_ = v_moreLinkArgs_3078_;
v___y_3049_ = v_moreLinkLibs_3077_;
v___y_3050_ = v_moreLinkLibs_3081_;
v___y_3051_ = v_buildDir_3074_;
v___y_3052_ = v_moreLinkArgs_3082_;
v___y_3053_ = v___x_3085_;
v___y_3054_ = v_nativeLibDir_3075_;
v___y_3055_ = v_weakLinkArgs_3079_;
v___y_3056_ = v_weakLinkArgs_3083_;
v___y_3057_ = v___x_3094_;
goto v___jp_3047_;
}
}
}
v___jp_3095_:
{
if (lean_obj_tag(v___y_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v_a_3098_; 
v_a_3097_ = lean_ctor_get(v___y_3096_, 0);
lean_inc(v_a_3097_);
v_a_3098_ = lean_ctor_get(v___y_3096_, 1);
lean_inc(v_a_3098_);
lean_dec_ref(v___y_3096_);
v_a_3070_ = v_a_3097_;
v_a_3071_ = v_a_3098_;
goto v___jp_3069_;
}
else
{
lean_object* v_a_3099_; lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec(v_a_3023_);
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_config_2822_);
lean_dec(v_name_2821_);
lean_dec_ref(v_pkg_2820_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_3099_ = lean_ctor_get(v___y_3096_, 0);
v_a_3100_ = lean_ctor_get(v___y_3096_, 1);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___y_3096_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___y_3096_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_inc(v_a_3099_);
lean_dec(v___y_3096_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3099_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_config_2822_);
lean_dec(v_name_2821_);
lean_dec_ref(v_pkg_2820_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_3119_ = lean_ctor_get(v___x_3022_, 0);
v_a_3120_ = lean_ctor_get(v___x_3022_, 1);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3022_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_inc(v_a_3119_);
lean_dec(v___x_3022_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3119_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
else
{
lean_object* v_a_3128_; lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_config_2822_);
lean_dec(v_name_2821_);
lean_dec_ref(v_pkg_2820_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_3128_ = lean_ctor_get(v___x_3019_, 0);
v_a_3129_ = lean_ctor_get(v___x_3019_, 1);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3019_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_inc(v_a_3128_);
lean_dec(v___x_3019_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3128_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
v___jp_2831_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_inc_ref(v_self_2817_);
v___x_2841_ = l_Lake_LeanLib_libName(v_self_2817_);
v___x_2842_ = l_System_FilePath_normalize(v___y_2833_);
v___x_2843_ = l_Lake_joinRelative(v_dir_2818_, v___x_2842_);
v___x_2844_ = l_System_FilePath_normalize(v___y_2836_);
v___x_2845_ = l_Lake_joinRelative(v___x_2843_, v___x_2844_);
v___x_2846_ = 0;
v___x_2847_ = l_Lake_nameToSharedLib(v___x_2841_, v___x_2846_);
v___x_2848_ = l_Lake_joinRelative(v___x_2845_, v___x_2847_);
v___x_2849_ = l_Array_append___redArg(v___y_2838_, v___y_2837_);
v___x_2850_ = l_Array_append___redArg(v___y_2832_, v___y_2834_);
v___x_2851_ = l_Lake_LeanLib_isPlugin(v_self_2817_);
v___x_2852_ = l_System_Platform_isWindows;
v___x_2853_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2854_ = l_Lake_buildLeanSharedLib(v___x_2841_, v___x_2848_, v___y_2835_, v_a_2839_, v___x_2849_, v___x_2850_, v___x_2851_, v___x_2852_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v___x_2853_);
lean_dec(v___x_2816_);
lean_dec_ref(v___y_2835_);
v___x_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v_a_2840_);
return v___x_2855_;
}
v___jp_2856_:
{
lean_object* v___x_2859_; 
v___x_2859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2859_, 0, v_a_2857_);
lean_ctor_set(v___x_2859_, 1, v_a_2858_);
return v___x_2859_;
}
v___jp_2860_:
{
if (lean_obj_tag(v___y_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v_a_2870_; 
v_a_2869_ = lean_ctor_get(v___y_2868_, 0);
lean_inc(v_a_2869_);
v_a_2870_ = lean_ctor_get(v___y_2868_, 1);
lean_inc(v_a_2870_);
lean_dec_ref(v___y_2868_);
v___y_2832_ = v___y_2861_;
v___y_2833_ = v___y_2862_;
v___y_2834_ = v___y_2863_;
v___y_2835_ = v___y_2864_;
v___y_2836_ = v___y_2865_;
v___y_2837_ = v___y_2867_;
v___y_2838_ = v___y_2866_;
v_a_2839_ = v_a_2869_;
v_a_2840_ = v_a_2870_;
goto v___jp_2831_;
}
else
{
lean_object* v_a_2871_; lean_object* v_a_2872_; 
lean_dec_ref(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_2871_ = lean_ctor_get(v___y_2868_, 0);
lean_inc(v_a_2871_);
v_a_2872_ = lean_ctor_get(v___y_2868_, 1);
lean_inc(v_a_2872_);
lean_dec_ref(v___y_2868_);
v_a_2857_ = v_a_2871_;
v_a_2858_ = v_a_2872_;
goto v___jp_2856_;
}
}
v___jp_2873_:
{
lean_object* v___x_2885_; uint8_t v___x_2886_; 
v___x_2885_ = lean_array_get_size(v___y_2884_);
v___x_2886_ = lean_nat_dec_lt(v___y_2879_, v___x_2885_);
if (v___x_2886_ == 0)
{
lean_dec_ref(v___y_2884_);
v___y_2832_ = v___y_2875_;
v___y_2833_ = v___y_2876_;
v___y_2834_ = v___y_2877_;
v___y_2835_ = v___y_2878_;
v___y_2836_ = v___y_2880_;
v___y_2837_ = v___y_2883_;
v___y_2838_ = v___y_2882_;
v_a_2839_ = v___y_2881_;
v_a_2840_ = v___y_2874_;
goto v___jp_2831_;
}
else
{
uint8_t v___x_2887_; 
v___x_2887_ = lean_nat_dec_le(v___x_2885_, v___x_2885_);
if (v___x_2887_ == 0)
{
if (v___x_2886_ == 0)
{
lean_dec_ref(v___y_2884_);
v___y_2832_ = v___y_2875_;
v___y_2833_ = v___y_2876_;
v___y_2834_ = v___y_2877_;
v___y_2835_ = v___y_2878_;
v___y_2836_ = v___y_2880_;
v___y_2837_ = v___y_2883_;
v___y_2838_ = v___y_2882_;
v_a_2839_ = v___y_2881_;
v_a_2840_ = v___y_2874_;
goto v___jp_2831_;
}
else
{
size_t v___x_2888_; size_t v___x_2889_; lean_object* v___x_2890_; 
v___x_2888_ = ((size_t)0ULL);
v___x_2889_ = lean_usize_of_nat(v___x_2885_);
lean_inc_ref(v___y_2824_);
v___x_2890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2884_, v___x_2888_, v___x_2889_, v___y_2881_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2874_);
lean_dec_ref(v___y_2884_);
v___y_2861_ = v___y_2875_;
v___y_2862_ = v___y_2876_;
v___y_2863_ = v___y_2877_;
v___y_2864_ = v___y_2878_;
v___y_2865_ = v___y_2880_;
v___y_2866_ = v___y_2882_;
v___y_2867_ = v___y_2883_;
v___y_2868_ = v___x_2890_;
goto v___jp_2860_;
}
}
else
{
size_t v___x_2891_; size_t v___x_2892_; lean_object* v___x_2893_; 
v___x_2891_ = ((size_t)0ULL);
v___x_2892_ = lean_usize_of_nat(v___x_2885_);
lean_inc_ref(v___y_2824_);
v___x_2893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2884_, v___x_2891_, v___x_2892_, v___y_2881_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2874_);
lean_dec_ref(v___y_2884_);
v___y_2861_ = v___y_2875_;
v___y_2862_ = v___y_2876_;
v___y_2863_ = v___y_2877_;
v___y_2864_ = v___y_2878_;
v___y_2865_ = v___y_2880_;
v___y_2866_ = v___y_2882_;
v___y_2867_ = v___y_2883_;
v___y_2868_ = v___x_2893_;
goto v___jp_2860_;
}
}
}
v___jp_2894_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v___x_2905_ = lean_mk_empty_array_with_capacity(v___y_2900_);
v___x_2906_ = lean_array_get_size(v_targetDecls_2819_);
v___x_2907_ = lean_nat_dec_lt(v___y_2900_, v___x_2906_);
if (v___x_2907_ == 0)
{
lean_dec_ref(v_pkg_2820_);
v___y_2874_ = v_a_2904_;
v___y_2875_ = v___y_2895_;
v___y_2876_ = v___y_2896_;
v___y_2877_ = v___y_2897_;
v___y_2878_ = v___y_2898_;
v___y_2879_ = v___y_2900_;
v___y_2880_ = v___y_2899_;
v___y_2881_ = v_a_2903_;
v___y_2882_ = v___y_2902_;
v___y_2883_ = v___y_2901_;
v___y_2884_ = v___x_2905_;
goto v___jp_2873_;
}
else
{
uint8_t v___x_2908_; 
v___x_2908_ = lean_nat_dec_le(v___x_2906_, v___x_2906_);
if (v___x_2908_ == 0)
{
if (v___x_2907_ == 0)
{
lean_dec_ref(v_pkg_2820_);
v___y_2874_ = v_a_2904_;
v___y_2875_ = v___y_2895_;
v___y_2876_ = v___y_2896_;
v___y_2877_ = v___y_2897_;
v___y_2878_ = v___y_2898_;
v___y_2879_ = v___y_2900_;
v___y_2880_ = v___y_2899_;
v___y_2881_ = v_a_2903_;
v___y_2882_ = v___y_2902_;
v___y_2883_ = v___y_2901_;
v___y_2884_ = v___x_2905_;
goto v___jp_2873_;
}
else
{
size_t v___x_2909_; size_t v___x_2910_; lean_object* v___x_2911_; 
v___x_2909_ = ((size_t)0ULL);
v___x_2910_ = lean_usize_of_nat(v___x_2906_);
v___x_2911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2820_, v_targetDecls_2819_, v___x_2909_, v___x_2910_, v___x_2905_);
v___y_2874_ = v_a_2904_;
v___y_2875_ = v___y_2895_;
v___y_2876_ = v___y_2896_;
v___y_2877_ = v___y_2897_;
v___y_2878_ = v___y_2898_;
v___y_2879_ = v___y_2900_;
v___y_2880_ = v___y_2899_;
v___y_2881_ = v_a_2903_;
v___y_2882_ = v___y_2902_;
v___y_2883_ = v___y_2901_;
v___y_2884_ = v___x_2911_;
goto v___jp_2873_;
}
}
else
{
size_t v___x_2912_; size_t v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = ((size_t)0ULL);
v___x_2913_ = lean_usize_of_nat(v___x_2906_);
v___x_2914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2820_, v_targetDecls_2819_, v___x_2912_, v___x_2913_, v___x_2905_);
v___y_2874_ = v_a_2904_;
v___y_2875_ = v___y_2895_;
v___y_2876_ = v___y_2896_;
v___y_2877_ = v___y_2897_;
v___y_2878_ = v___y_2898_;
v___y_2879_ = v___y_2900_;
v___y_2880_ = v___y_2899_;
v___y_2881_ = v_a_2903_;
v___y_2882_ = v___y_2902_;
v___y_2883_ = v___y_2901_;
v___y_2884_ = v___x_2914_;
goto v___jp_2873_;
}
}
}
v___jp_2915_:
{
if (lean_obj_tag(v___y_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v_a_2926_; 
v_a_2925_ = lean_ctor_get(v___y_2924_, 0);
lean_inc(v_a_2925_);
v_a_2926_ = lean_ctor_get(v___y_2924_, 1);
lean_inc(v_a_2926_);
lean_dec_ref(v___y_2924_);
v___y_2895_ = v___y_2916_;
v___y_2896_ = v___y_2917_;
v___y_2897_ = v___y_2918_;
v___y_2898_ = v___y_2919_;
v___y_2899_ = v___y_2921_;
v___y_2900_ = v___y_2920_;
v___y_2901_ = v___y_2923_;
v___y_2902_ = v___y_2922_;
v_a_2903_ = v_a_2925_;
v_a_2904_ = v_a_2926_;
goto v___jp_2894_;
}
else
{
lean_object* v_a_2927_; lean_object* v_a_2928_; 
lean_dec_ref(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec_ref(v___y_2919_);
lean_dec_ref(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_pkg_2820_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_2927_ = lean_ctor_get(v___y_2924_, 0);
lean_inc(v_a_2927_);
v_a_2928_ = lean_ctor_get(v___y_2924_, 1);
lean_inc(v_a_2928_);
lean_dec_ref(v___y_2924_);
v_a_2857_ = v_a_2927_;
v_a_2858_ = v_a_2928_;
goto v___jp_2856_;
}
}
v___jp_2929_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2942_ = l_Array_append___redArg(v___y_2931_, v___y_2932_);
v___x_2943_ = lean_array_get_size(v___x_2942_);
v___x_2944_ = lean_nat_dec_lt(v___y_2936_, v___x_2943_);
if (v___x_2944_ == 0)
{
lean_dec_ref(v___x_2942_);
v___y_2895_ = v___y_2930_;
v___y_2896_ = v___y_2933_;
v___y_2897_ = v___y_2934_;
v___y_2898_ = v___y_2935_;
v___y_2899_ = v___y_2937_;
v___y_2900_ = v___y_2936_;
v___y_2901_ = v___y_2939_;
v___y_2902_ = v___y_2938_;
v_a_2903_ = v_snd_2940_;
v_a_2904_ = v_a_2941_;
goto v___jp_2894_;
}
else
{
uint8_t v___x_2945_; 
v___x_2945_ = lean_nat_dec_le(v___x_2943_, v___x_2943_);
if (v___x_2945_ == 0)
{
if (v___x_2944_ == 0)
{
lean_dec_ref(v___x_2942_);
v___y_2895_ = v___y_2930_;
v___y_2896_ = v___y_2933_;
v___y_2897_ = v___y_2934_;
v___y_2898_ = v___y_2935_;
v___y_2899_ = v___y_2937_;
v___y_2900_ = v___y_2936_;
v___y_2901_ = v___y_2939_;
v___y_2902_ = v___y_2938_;
v_a_2903_ = v_snd_2940_;
v_a_2904_ = v_a_2941_;
goto v___jp_2894_;
}
else
{
size_t v___x_2946_; size_t v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = ((size_t)0ULL);
v___x_2947_ = lean_usize_of_nat(v___x_2943_);
lean_inc_ref(v___y_2824_);
lean_inc_ref(v_pkg_2820_);
v___x_2948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2820_, v___x_2942_, v___x_2946_, v___x_2947_, v_snd_2940_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_2941_);
lean_dec_ref(v___x_2942_);
v___y_2916_ = v___y_2930_;
v___y_2917_ = v___y_2933_;
v___y_2918_ = v___y_2934_;
v___y_2919_ = v___y_2935_;
v___y_2920_ = v___y_2936_;
v___y_2921_ = v___y_2937_;
v___y_2922_ = v___y_2938_;
v___y_2923_ = v___y_2939_;
v___y_2924_ = v___x_2948_;
goto v___jp_2915_;
}
}
else
{
size_t v___x_2949_; size_t v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = ((size_t)0ULL);
v___x_2950_ = lean_usize_of_nat(v___x_2943_);
lean_inc_ref(v___y_2824_);
lean_inc_ref(v_pkg_2820_);
v___x_2951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2820_, v___x_2942_, v___x_2949_, v___x_2950_, v_snd_2940_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_2941_);
lean_dec_ref(v___x_2942_);
v___y_2916_ = v___y_2930_;
v___y_2917_ = v___y_2933_;
v___y_2918_ = v___y_2934_;
v___y_2919_ = v___y_2935_;
v___y_2920_ = v___y_2936_;
v___y_2921_ = v___y_2937_;
v___y_2922_ = v___y_2938_;
v___y_2923_ = v___y_2939_;
v___y_2924_ = v___x_2951_;
goto v___jp_2915_;
}
}
}
v___jp_2952_:
{
if (lean_obj_tag(v___y_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v_a_2965_; lean_object* v_snd_2966_; 
v_a_2964_ = lean_ctor_get(v___y_2963_, 0);
lean_inc(v_a_2964_);
v_a_2965_ = lean_ctor_get(v___y_2963_, 1);
lean_inc(v_a_2965_);
lean_dec_ref(v___y_2963_);
v_snd_2966_ = lean_ctor_get(v_a_2964_, 1);
lean_inc(v_snd_2966_);
lean_dec(v_a_2964_);
v___y_2930_ = v___y_2954_;
v___y_2931_ = v___y_2953_;
v___y_2932_ = v___y_2955_;
v___y_2933_ = v___y_2956_;
v___y_2934_ = v___y_2957_;
v___y_2935_ = v___y_2958_;
v___y_2936_ = v___y_2960_;
v___y_2937_ = v___y_2959_;
v___y_2938_ = v___y_2962_;
v___y_2939_ = v___y_2961_;
v_snd_2940_ = v_snd_2966_;
v_a_2941_ = v_a_2965_;
goto v___jp_2929_;
}
else
{
lean_object* v_a_2967_; lean_object* v_a_2968_; 
lean_dec_ref(v___y_2962_);
lean_dec_ref(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec_ref(v___y_2956_);
lean_dec_ref(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_pkg_2820_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_2967_ = lean_ctor_get(v___y_2963_, 0);
lean_inc(v_a_2967_);
v_a_2968_ = lean_ctor_get(v___y_2963_, 1);
lean_inc(v_a_2968_);
lean_dec_ref(v___y_2963_);
v_a_2857_ = v_a_2967_;
v_a_2858_ = v_a_2968_;
goto v___jp_2856_;
}
}
v___jp_2969_:
{
lean_object* v_toArray_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3001_; 
v_toArray_2982_ = lean_ctor_get(v_a_2980_, 1);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_a_2980_);
if (v_isSharedCheck_3001_ == 0)
{
lean_object* v_unused_3002_; 
v_unused_3002_ = lean_ctor_get(v_a_2980_, 0);
lean_dec(v_unused_3002_);
v___x_2984_ = v_a_2980_;
v_isShared_2985_ = v_isSharedCheck_3001_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_toArray_2982_);
lean_dec(v_a_2980_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3001_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; 
v___x_2986_ = lean_mk_empty_array_with_capacity(v___y_2977_);
v___x_2987_ = lean_array_get_size(v_toArray_2982_);
v___x_2988_ = lean_nat_dec_lt(v___y_2977_, v___x_2987_);
if (v___x_2988_ == 0)
{
lean_del_object(v___x_2984_);
lean_dec_ref(v_toArray_2982_);
lean_dec(v_name_2821_);
v___y_2930_ = v___y_2971_;
v___y_2931_ = v___y_2970_;
v___y_2932_ = v___y_2972_;
v___y_2933_ = v___y_2973_;
v___y_2934_ = v___y_2974_;
v___y_2935_ = v___y_2975_;
v___y_2936_ = v___y_2977_;
v___y_2937_ = v___y_2976_;
v___y_2938_ = v___y_2979_;
v___y_2939_ = v___y_2978_;
v_snd_2940_ = v___x_2986_;
v_a_2941_ = v_a_2981_;
goto v___jp_2929_;
}
else
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2992_; 
v___x_2989_ = l_Lean_NameSet_empty;
v___x_2990_ = l_Lean_NameSet_insert(v___x_2989_, v_name_2821_);
lean_inc_ref(v___x_2986_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 1, v___x_2986_);
lean_ctor_set(v___x_2984_, 0, v___x_2990_);
v___x_2992_ = v___x_2984_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2990_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v___x_2986_);
v___x_2992_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
uint8_t v___x_2993_; 
v___x_2993_ = lean_nat_dec_le(v___x_2987_, v___x_2987_);
if (v___x_2993_ == 0)
{
if (v___x_2988_ == 0)
{
lean_dec_ref(v___x_2992_);
lean_dec_ref(v_toArray_2982_);
v___y_2930_ = v___y_2971_;
v___y_2931_ = v___y_2970_;
v___y_2932_ = v___y_2972_;
v___y_2933_ = v___y_2973_;
v___y_2934_ = v___y_2974_;
v___y_2935_ = v___y_2975_;
v___y_2936_ = v___y_2977_;
v___y_2937_ = v___y_2976_;
v___y_2938_ = v___y_2979_;
v___y_2939_ = v___y_2978_;
v_snd_2940_ = v___x_2986_;
v_a_2941_ = v_a_2981_;
goto v___jp_2929_;
}
else
{
size_t v___x_2994_; size_t v___x_2995_; lean_object* v___x_2996_; 
lean_dec_ref(v___x_2986_);
v___x_2994_ = ((size_t)0ULL);
v___x_2995_ = lean_usize_of_nat(v___x_2987_);
lean_inc_ref(v___y_2824_);
v___x_2996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_2982_, v___x_2994_, v___x_2995_, v___x_2992_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_2981_);
lean_dec_ref(v_toArray_2982_);
v___y_2953_ = v___y_2970_;
v___y_2954_ = v___y_2971_;
v___y_2955_ = v___y_2972_;
v___y_2956_ = v___y_2973_;
v___y_2957_ = v___y_2974_;
v___y_2958_ = v___y_2975_;
v___y_2959_ = v___y_2976_;
v___y_2960_ = v___y_2977_;
v___y_2961_ = v___y_2978_;
v___y_2962_ = v___y_2979_;
v___y_2963_ = v___x_2996_;
goto v___jp_2952_;
}
}
else
{
size_t v___x_2997_; size_t v___x_2998_; lean_object* v___x_2999_; 
lean_dec_ref(v___x_2986_);
v___x_2997_ = ((size_t)0ULL);
v___x_2998_ = lean_usize_of_nat(v___x_2987_);
lean_inc_ref(v___y_2824_);
v___x_2999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_2982_, v___x_2997_, v___x_2998_, v___x_2992_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_2981_);
lean_dec_ref(v_toArray_2982_);
v___y_2953_ = v___y_2970_;
v___y_2954_ = v___y_2971_;
v___y_2955_ = v___y_2972_;
v___y_2956_ = v___y_2973_;
v___y_2957_ = v___y_2974_;
v___y_2958_ = v___y_2975_;
v___y_2959_ = v___y_2976_;
v___y_2960_ = v___y_2977_;
v___y_2961_ = v___y_2978_;
v___y_2962_ = v___y_2979_;
v___y_2963_ = v___x_2999_;
goto v___jp_2952_;
}
}
}
}
}
v___jp_3003_:
{
if (lean_obj_tag(v___y_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v_a_3016_; 
v_a_3015_ = lean_ctor_get(v___y_3014_, 0);
lean_inc(v_a_3015_);
v_a_3016_ = lean_ctor_get(v___y_3014_, 1);
lean_inc(v_a_3016_);
lean_dec_ref(v___y_3014_);
v___y_2970_ = v___y_3005_;
v___y_2971_ = v___y_3004_;
v___y_2972_ = v___y_3006_;
v___y_2973_ = v___y_3007_;
v___y_2974_ = v___y_3008_;
v___y_2975_ = v___y_3009_;
v___y_2976_ = v___y_3011_;
v___y_2977_ = v___y_3010_;
v___y_2978_ = v___y_3013_;
v___y_2979_ = v___y_3012_;
v_a_2980_ = v_a_3015_;
v_a_2981_ = v_a_3016_;
goto v___jp_2969_;
}
else
{
lean_object* v_a_3017_; lean_object* v_a_3018_; 
lean_dec_ref(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec_ref(v___y_3009_);
lean_dec_ref(v___y_3007_);
lean_dec_ref(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec_ref(v___y_2824_);
lean_dec(v_name_2821_);
lean_dec_ref(v_pkg_2820_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_3017_ = lean_ctor_get(v___y_3014_, 0);
lean_inc(v_a_3017_);
v_a_3018_ = lean_ctor_get(v___y_3014_, 1);
lean_inc(v_a_3018_);
lean_dec_ref(v___y_3014_);
v_a_2857_ = v_a_3017_;
v_a_2858_ = v_a_3018_;
goto v___jp_2856_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* v___x_3137_, lean_object* v___x_3138_, lean_object* v_self_3139_, lean_object* v_dir_3140_, lean_object* v_targetDecls_3141_, lean_object* v_pkg_3142_, lean_object* v_name_3143_, lean_object* v_config_3144_, lean_object* v_config_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v___x_3137_, v___x_3138_, v_self_3139_, v_dir_3140_, v_targetDecls_3141_, v_pkg_3142_, v_name_3143_, v_config_3144_, v_config_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec(v_config_3145_);
lean_dec_ref(v_targetDecls_3141_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object* v_self_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v_pkg_3163_; lean_object* v_name_3164_; lean_object* v_config_3165_; lean_object* v_keyName_3166_; lean_object* v_dir_3167_; lean_object* v_config_3168_; lean_object* v_targetDecls_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___f_3176_; lean_object* v___x_3177_; 
v_pkg_3163_ = lean_ctor_get(v_self_3155_, 0);
lean_inc_ref_n(v_pkg_3163_, 2);
v_name_3164_ = lean_ctor_get(v_self_3155_, 1);
lean_inc_n(v_name_3164_, 3);
v_config_3165_ = lean_ctor_get(v_self_3155_, 2);
lean_inc(v_config_3165_);
v_keyName_3166_ = lean_ctor_get(v_pkg_3163_, 2);
v_dir_3167_ = lean_ctor_get(v_pkg_3163_, 4);
lean_inc_ref(v_dir_3167_);
v_config_3168_ = lean_ctor_get(v_pkg_3163_, 6);
lean_inc_ref(v_config_3168_);
v_targetDecls_3169_ = lean_ctor_get(v_pkg_3163_, 13);
lean_inc_ref(v_targetDecls_3169_);
v___x_3170_ = l_Lake_instDataKindDynlib;
v___x_3171_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_3166_);
v___x_3172_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3172_, 0, v_keyName_3166_);
lean_ctor_set(v___x_3172_, 1, v_name_3164_);
v___x_3173_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3155_);
v___x_3174_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3172_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
lean_ctor_set(v___x_3174_, 2, v_self_3155_);
lean_ctor_set(v___x_3174_, 3, v___x_3171_);
v___x_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3175_, 0, v_pkg_3163_);
v___f_3176_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3176_, 0, v___x_3174_);
lean_closure_set(v___f_3176_, 1, v___x_3175_);
lean_closure_set(v___f_3176_, 2, v_self_3155_);
lean_closure_set(v___f_3176_, 3, v_dir_3167_);
lean_closure_set(v___f_3176_, 4, v_targetDecls_3169_);
lean_closure_set(v___f_3176_, 5, v_pkg_3163_);
lean_closure_set(v___f_3176_, 6, v_name_3164_);
lean_closure_set(v___f_3176_, 7, v_config_3168_);
lean_closure_set(v___f_3176_, 8, v_config_3165_);
v___x_3177_ = l_Lake_ensureJob___redArg(v___x_3170_, v___f_3176_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3207_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_a_3179_ = lean_ctor_get(v___x_3177_, 1);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3181_ = v___x_3177_;
v_isShared_3182_ = v_isSharedCheck_3207_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3207_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v_task_3183_; lean_object* v_kind_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3205_; 
v_task_3183_ = lean_ctor_get(v_a_3178_, 0);
v_kind_3184_ = lean_ctor_get(v_a_3178_, 1);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_a_3178_);
if (v_isSharedCheck_3205_ == 0)
{
lean_object* v_unused_3206_; 
v_unused_3206_ = lean_ctor_get(v_a_3178_, 2);
lean_dec(v_unused_3206_);
v___x_3186_ = v_a_3178_;
v_isShared_3187_ = v_isSharedCheck_3205_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_kind_3184_);
lean_inc(v_task_3183_);
lean_dec(v_a_3178_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3205_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v_registeredJobs_3188_; lean_object* v___x_3189_; uint8_t v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; uint8_t v___x_3194_; lean_object* v_job_3196_; 
v_registeredJobs_3188_ = lean_ctor_get(v_a_3160_, 3);
v___x_3189_ = lean_st_ref_take(v_registeredJobs_3188_);
v___x_3190_ = 1;
v___x_3191_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3164_, v___x_3190_);
v___x_3192_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0));
v___x_3193_ = lean_string_append(v___x_3191_, v___x_3192_);
v___x_3194_ = 0;
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 2, v___x_3193_);
v_job_3196_ = v___x_3186_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_task_3183_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_kind_3184_);
lean_ctor_set(v_reuseFailAlloc_3204_, 2, v___x_3193_);
v_job_3196_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3202_; 
lean_ctor_set_uint8(v_job_3196_, sizeof(void*)*3, v___x_3194_);
lean_inc_ref(v_job_3196_);
v___x_3197_ = l_Lake_Job_toOpaque___redArg(v_job_3196_);
v___x_3198_ = lean_array_push(v___x_3189_, v___x_3197_);
v___x_3199_ = lean_st_ref_set(v_registeredJobs_3188_, v___x_3198_);
v___x_3200_ = l_Lake_Job_renew___redArg(v_job_3196_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v___x_3200_);
v___x_3202_ = v___x_3181_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_a_3179_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
}
else
{
lean_dec(v_name_3164_);
return v___x_3177_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object* v_self_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_a_3212_);
lean_dec(v_a_3211_);
lean_dec(v_a_3210_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t v_fmt_3217_, lean_object* v_a_3218_){
_start:
{
if (v_fmt_3217_ == 0)
{
lean_object* v_path_3219_; 
v_path_3219_ = lean_ctor_get(v_a_3218_, 0);
lean_inc_ref(v_path_3219_);
return v_path_3219_;
}
else
{
lean_object* v_path_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v_path_3220_ = lean_ctor_get(v_a_3218_, 0);
lean_inc_ref(v_path_3220_);
v___x_3221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3221_, 0, v_path_3220_);
v___x_3222_ = l_Lean_Json_compress(v___x_3221_);
return v___x_3222_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* v_fmt_3223_, lean_object* v_a_3224_){
_start:
{
uint8_t v_fmt_boxed_3225_; lean_object* v_res_3226_; 
v_fmt_boxed_3225_ = lean_unbox(v_fmt_3223_);
v_res_3226_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_boxed_3225_, v_a_3224_);
lean_dec_ref(v_a_3224_);
return v_res_3226_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3229_; uint8_t v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___f_3229_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__0));
v___x_3230_ = 1;
v___x_3231_ = l_Lake_instDataKindDynlib;
v___x_3232_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__1));
v___x_3233_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3234_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
lean_ctor_set(v___x_3234_, 1, v___x_3232_);
lean_ctor_set(v___x_3234_, 2, v___x_3231_);
lean_ctor_set(v___x_3234_, 3, v___f_3229_);
lean_ctor_set_uint8(v___x_3234_, sizeof(void*)*4, v___x_3230_);
lean_ctor_set_uint8(v___x_3234_, sizeof(void*)*4 + 1, v___x_3230_);
return v___x_3234_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_obj_once(&l_Lake_LeanLib_sharedFacetConfig___closed__2, &l_Lake_LeanLib_sharedFacetConfig___closed__2_once, _init_l_Lake_LeanLib_sharedFacetConfig___closed__2);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* v___x_3236_, lean_object* v_as_3237_, size_t v_sz_3238_, size_t v_i_3239_, lean_object* v_b_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
uint8_t v___x_3248_; 
v___x_3248_ = lean_usize_dec_lt(v_i_3239_, v_sz_3238_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; 
lean_dec_ref(v___y_3241_);
lean_dec_ref(v___x_3236_);
v___x_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3249_, 0, v_b_3240_);
lean_ctor_set(v___x_3249_, 1, v___y_3246_);
return v___x_3249_;
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3251_; 
v_a_3250_ = lean_array_uget_borrowed(v_as_3237_, v_i_3239_);
lean_inc_ref(v___y_3241_);
lean_inc_n(v_a_3250_, 2);
lean_inc_ref(v___x_3236_);
v___x_3251_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v___x_3236_, v_a_3250_, v_a_3250_, v___x_3248_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v_a_3253_; lean_object* v_snd_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; size_t v___x_3257_; size_t v___x_3258_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
v_a_3253_ = lean_ctor_get(v___x_3251_, 1);
lean_inc(v_a_3253_);
lean_dec_ref(v___x_3251_);
v_snd_3254_ = lean_ctor_get(v_a_3252_, 1);
lean_inc(v_snd_3254_);
lean_dec(v_a_3252_);
v___x_3255_ = l_Lake_Job_toOpaque___redArg(v_snd_3254_);
v___x_3256_ = l_Lake_Job_mix___redArg(v_b_3240_, v___x_3255_);
v___x_3257_ = ((size_t)1ULL);
v___x_3258_ = lean_usize_add(v_i_3239_, v___x_3257_);
v_i_3239_ = v___x_3258_;
v_b_3240_ = v___x_3256_;
v___y_3246_ = v_a_3253_;
goto _start;
}
else
{
lean_object* v_a_3260_; lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_dec_ref(v___y_3241_);
lean_dec_ref(v_b_3240_);
lean_dec_ref(v___x_3236_);
v_a_3260_ = lean_ctor_get(v___x_3251_, 0);
v_a_3261_ = lean_ctor_get(v___x_3251_, 1);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3251_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_inc(v_a_3260_);
lean_dec(v___x_3251_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3260_);
lean_ctor_set(v_reuseFailAlloc_3267_, 1, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* v___x_3269_, lean_object* v_as_3270_, lean_object* v_sz_3271_, lean_object* v_i_3272_, lean_object* v_b_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
size_t v_sz_boxed_3281_; size_t v_i_boxed_3282_; lean_object* v_res_3283_; 
v_sz_boxed_3281_ = lean_unbox_usize(v_sz_3271_);
lean_dec(v_sz_3271_);
v_i_boxed_3282_ = lean_unbox_usize(v_i_3272_);
lean_dec(v_i_3272_);
v_res_3283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_3269_, v_as_3270_, v_sz_boxed_3281_, v_i_boxed_3282_, v_b_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec(v___y_3275_);
lean_dec_ref(v_as_3270_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* v___x_3284_, lean_object* v_as_3285_, size_t v_sz_3286_, size_t v_i_3287_, lean_object* v_b_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
uint8_t v___x_3296_; 
v___x_3296_ = lean_usize_dec_lt(v_i_3287_, v_sz_3286_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; 
lean_dec_ref(v___y_3289_);
lean_dec_ref(v___x_3284_);
v___x_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3297_, 0, v_b_3288_);
lean_ctor_set(v___x_3297_, 1, v___y_3294_);
return v___x_3297_;
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3299_; 
v_a_3298_ = lean_array_uget_borrowed(v_as_3285_, v_i_3287_);
lean_inc_ref(v___y_3289_);
lean_inc(v_a_3298_);
lean_inc_ref(v___x_3284_);
v___x_3299_ = l_Lake_Package_fetchTargetJob(v___x_3284_, v_a_3298_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v_a_3301_; lean_object* v___x_3302_; size_t v___x_3303_; size_t v___x_3304_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
v_a_3301_ = lean_ctor_get(v___x_3299_, 1);
lean_inc(v_a_3301_);
lean_dec_ref(v___x_3299_);
v___x_3302_ = l_Lake_Job_mix___redArg(v_b_3288_, v_a_3300_);
v___x_3303_ = ((size_t)1ULL);
v___x_3304_ = lean_usize_add(v_i_3287_, v___x_3303_);
v_i_3287_ = v___x_3304_;
v_b_3288_ = v___x_3302_;
v___y_3294_ = v_a_3301_;
goto _start;
}
else
{
lean_object* v_a_3306_; lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_dec_ref(v___y_3289_);
lean_dec_ref(v_b_3288_);
lean_dec_ref(v___x_3284_);
v_a_3306_ = lean_ctor_get(v___x_3299_, 0);
v_a_3307_ = lean_ctor_get(v___x_3299_, 1);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3299_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_inc(v_a_3306_);
lean_dec(v___x_3299_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3306_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* v___x_3315_, lean_object* v_as_3316_, lean_object* v_sz_3317_, lean_object* v_i_3318_, lean_object* v_b_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
size_t v_sz_boxed_3327_; size_t v_i_boxed_3328_; lean_object* v_res_3329_; 
v_sz_boxed_3327_ = lean_unbox_usize(v_sz_3317_);
lean_dec(v_sz_3317_);
v_i_boxed_3328_ = lean_unbox_usize(v_i_3318_);
lean_dec(v_i_3318_);
v_res_3329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_3315_, v_as_3316_, v_sz_boxed_3327_, v_i_boxed_3328_, v_b_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v_as_3316_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object* v_self_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_){
_start:
{
lean_object* v_pkg_3340_; lean_object* v_name_3341_; lean_object* v_config_3342_; lean_object* v_baseName_3343_; lean_object* v_keyName_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v_pkg_3340_ = lean_ctor_get(v_self_3332_, 0);
lean_inc_ref_n(v_pkg_3340_, 2);
v_name_3341_ = lean_ctor_get(v_self_3332_, 1);
lean_inc(v_name_3341_);
v_config_3342_ = lean_ctor_get(v_self_3332_, 2);
lean_inc(v_config_3342_);
lean_dec_ref(v_self_3332_);
v_baseName_3343_ = lean_ctor_get(v_pkg_3340_, 1);
v_keyName_3344_ = lean_ctor_get(v_pkg_3340_, 2);
v___x_3345_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_3344_);
v___x_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3346_, 0, v_keyName_3344_);
v___x_3347_ = l_Lake_Package_keyword;
v___x_3348_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3346_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
lean_ctor_set(v___x_3348_, 2, v_pkg_3340_);
lean_ctor_set(v___x_3348_, 3, v___x_3345_);
lean_inc_ref(v_a_3333_);
lean_inc_ref(v_a_3337_);
lean_inc(v_a_3336_);
lean_inc(v_a_3335_);
lean_inc(v_a_3334_);
v___x_3349_ = lean_apply_7(v_a_3333_, v___x_3348_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, lean_box(0));
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3387_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
v_a_3351_ = lean_ctor_get(v___x_3349_, 1);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3353_ = v___x_3349_;
v_isShared_3354_ = v_isSharedCheck_3387_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_inc(v_a_3350_);
lean_dec(v___x_3349_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3387_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
uint8_t v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v_needs_3359_; lean_object* v_extraDepTargets_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; uint8_t v___x_3367_; uint8_t v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3355_ = 1;
lean_inc(v_baseName_3343_);
v___x_3356_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3343_, v___x_3355_);
v___x_3357_ = lean_unsigned_to_nat(0u);
v___x_3358_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v_needs_3359_ = lean_ctor_get(v_config_3342_, 5);
lean_inc_ref(v_needs_3359_);
v_extraDepTargets_3360_ = lean_ctor_get(v_config_3342_, 6);
lean_inc_ref(v_extraDepTargets_3360_);
lean_dec(v_config_3342_);
v___x_3361_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0));
v___x_3362_ = lean_string_append(v___x_3356_, v___x_3361_);
v___x_3363_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3341_, v___x_3355_);
v___x_3364_ = lean_string_append(v___x_3362_, v___x_3363_);
lean_dec_ref(v___x_3363_);
v___x_3365_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1));
v___x_3366_ = lean_string_append(v___x_3364_, v___x_3365_);
v___x_3367_ = 0;
v___x_3368_ = 0;
v___x_3369_ = l_Lake_BuildTrace_nil(v___x_3366_);
v___x_3370_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3370_, 0, v___x_3358_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
lean_ctor_set(v___x_3370_, 2, v___x_3357_);
lean_ctor_set_uint8(v___x_3370_, sizeof(void*)*3, v___x_3367_);
lean_ctor_set_uint8(v___x_3370_, sizeof(void*)*3 + 1, v___x_3368_);
v___x_3371_ = lean_box(0);
v___x_3372_ = lean_box(0);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 1, v___x_3370_);
lean_ctor_set(v___x_3353_, 0, v___x_3372_);
v___x_3374_ = v___x_3353_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3372_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v___x_3370_);
v___x_3374_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v_job_3377_; lean_object* v___x_3378_; size_t v_sz_3379_; size_t v___x_3380_; lean_object* v___x_3381_; 
v___x_3375_ = lean_task_pure(v___x_3374_);
v___x_3376_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v_job_3377_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_3377_, 0, v___x_3375_);
lean_ctor_set(v_job_3377_, 1, v___x_3371_);
lean_ctor_set(v_job_3377_, 2, v___x_3376_);
lean_ctor_set_uint8(v_job_3377_, sizeof(void*)*3, v___x_3368_);
v___x_3378_ = l_Lake_Job_mix___redArg(v_job_3377_, v_a_3350_);
v_sz_3379_ = lean_array_size(v_extraDepTargets_3360_);
v___x_3380_ = ((size_t)0ULL);
lean_inc_ref(v_a_3333_);
lean_inc_ref(v_pkg_3340_);
v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_3340_, v_extraDepTargets_3360_, v_sz_3379_, v___x_3380_, v___x_3378_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3351_);
lean_dec_ref(v_extraDepTargets_3360_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v_a_3383_; size_t v_sz_3384_; lean_object* v___x_3385_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
v_a_3383_ = lean_ctor_get(v___x_3381_, 1);
lean_inc(v_a_3383_);
lean_dec_ref(v___x_3381_);
v_sz_3384_ = lean_array_size(v_needs_3359_);
v___x_3385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_3340_, v_needs_3359_, v_sz_3384_, v___x_3380_, v_a_3382_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3383_);
lean_dec_ref(v_needs_3359_);
return v___x_3385_;
}
else
{
lean_dec_ref(v_needs_3359_);
lean_dec_ref(v_pkg_3340_);
lean_dec_ref(v_a_3333_);
return v___x_3381_;
}
}
}
}
else
{
lean_dec(v_config_3342_);
lean_dec(v_name_3341_);
lean_dec_ref(v_pkg_3340_);
lean_dec_ref(v_a_3333_);
return v___x_3349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object* v_self_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_);
lean_dec_ref(v_a_3393_);
lean_dec(v_a_3392_);
lean_dec(v_a_3391_);
lean_dec(v_a_3390_);
return v_res_3396_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3398_; uint8_t v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___f_3398_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3399_ = 1;
v___x_3400_ = l_Lake_instDataKindUnit;
v___x_3401_ = ((lean_object*)(l_Lake_LeanLib_extraDepFacetConfig___closed__0));
v___x_3402_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3403_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
lean_ctor_set(v___x_3403_, 1, v___x_3401_);
lean_ctor_set(v___x_3403_, 2, v___x_3400_);
lean_ctor_set(v___x_3403_, 3, v___f_3398_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*4, v___x_3399_);
lean_ctor_set_uint8(v___x_3403_, sizeof(void*)*4 + 1, v___x_3399_);
return v___x_3403_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = lean_obj_once(&l_Lake_LeanLib_extraDepFacetConfig___closed__1, &l_Lake_LeanLib_extraDepFacetConfig___closed__1_once, _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* v_self_3405_, size_t v_sz_3406_, size_t v_i_3407_, lean_object* v_bs_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
uint8_t v___x_3416_; 
v___x_3416_ = lean_usize_dec_lt(v_i_3407_, v_sz_3406_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3417_; 
lean_dec_ref(v___y_3409_);
lean_dec_ref(v_self_3405_);
v___x_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3417_, 0, v_bs_3408_);
lean_ctor_set(v___x_3417_, 1, v___y_3414_);
return v___x_3417_;
}
else
{
lean_object* v_pkg_3418_; lean_object* v_name_3419_; lean_object* v_keyName_3420_; lean_object* v_v_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v_pkg_3418_ = lean_ctor_get(v_self_3405_, 0);
v_name_3419_ = lean_ctor_get(v_self_3405_, 1);
v_keyName_3420_ = lean_ctor_get(v_pkg_3418_, 2);
v_v_3421_ = lean_array_uget_borrowed(v_bs_3408_, v_i_3407_);
lean_inc(v_name_3419_);
lean_inc(v_keyName_3420_);
v___x_3422_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3422_, 0, v_keyName_3420_);
lean_ctor_set(v___x_3422_, 1, v_name_3419_);
v___x_3423_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc(v_v_3421_);
lean_inc_ref(v_self_3405_);
v___x_3424_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
lean_ctor_set(v___x_3424_, 2, v_self_3405_);
lean_ctor_set(v___x_3424_, 3, v_v_3421_);
lean_inc_ref(v___y_3409_);
lean_inc_ref(v___y_3413_);
lean_inc(v___y_3412_);
lean_inc(v___y_3411_);
lean_inc(v___y_3410_);
v___x_3425_ = lean_apply_7(v___y_3409_, v___x_3424_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, lean_box(0));
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v_a_3427_; lean_object* v___x_3428_; lean_object* v_bs_x27_3429_; lean_object* v___x_3430_; size_t v___x_3431_; size_t v___x_3432_; lean_object* v___x_3433_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
v_a_3427_ = lean_ctor_get(v___x_3425_, 1);
lean_inc(v_a_3427_);
lean_dec_ref(v___x_3425_);
v___x_3428_ = lean_unsigned_to_nat(0u);
v_bs_x27_3429_ = lean_array_uset(v_bs_3408_, v_i_3407_, v___x_3428_);
v___x_3430_ = l_Lake_Job_toOpaque___redArg(v_a_3426_);
v___x_3431_ = ((size_t)1ULL);
v___x_3432_ = lean_usize_add(v_i_3407_, v___x_3431_);
v___x_3433_ = lean_array_uset(v_bs_x27_3429_, v_i_3407_, v___x_3430_);
v_i_3407_ = v___x_3432_;
v_bs_3408_ = v___x_3433_;
v___y_3414_ = v_a_3427_;
goto _start;
}
else
{
lean_object* v_a_3435_; lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_dec_ref(v___y_3409_);
lean_dec_ref(v_bs_3408_);
lean_dec_ref(v_self_3405_);
v_a_3435_ = lean_ctor_get(v___x_3425_, 0);
v_a_3436_ = lean_ctor_get(v___x_3425_, 1);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3425_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_inc(v_a_3435_);
lean_dec(v___x_3425_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3435_);
lean_ctor_set(v_reuseFailAlloc_3442_, 1, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* v_self_3444_, lean_object* v_sz_3445_, lean_object* v_i_3446_, lean_object* v_bs_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
size_t v_sz_boxed_3455_; size_t v_i_boxed_3456_; lean_object* v_res_3457_; 
v_sz_boxed_3455_ = lean_unbox_usize(v_sz_3445_);
lean_dec(v_sz_3445_);
v_i_boxed_3456_ = lean_unbox_usize(v_i_3446_);
lean_dec(v_i_3446_);
v_res_3457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3444_, v_sz_boxed_3455_, v_i_boxed_3456_, v_bs_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec(v___y_3449_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object* v_self_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v_config_3467_; lean_object* v_defaultFacets_3468_; size_t v_sz_3469_; size_t v___x_3470_; lean_object* v___x_3471_; 
v_config_3467_ = lean_ctor_get(v_self_3459_, 2);
v_defaultFacets_3468_ = lean_ctor_get(v_config_3467_, 7);
lean_inc_ref(v_defaultFacets_3468_);
v_sz_3469_ = lean_array_size(v_defaultFacets_3468_);
v___x_3470_ = ((size_t)0ULL);
v___x_3471_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3459_, v_sz_3469_, v___x_3470_, v_defaultFacets_3468_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3482_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
v_a_3473_ = lean_ctor_get(v___x_3471_, 1);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3475_ = v___x_3471_;
v_isShared_3476_ = v_isSharedCheck_3482_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_inc(v_a_3472_);
lean_dec(v___x_3471_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3482_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3480_; 
v___x_3477_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0));
v___x_3478_ = l_Lake_Job_mixArray___redArg(v_a_3472_, v___x_3477_);
lean_dec(v_a_3472_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v___x_3478_);
v___x_3480_ = v___x_3475_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3478_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_a_3473_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
v_a_3483_ = lean_ctor_get(v___x_3471_, 0);
v_a_3484_ = lean_ctor_get(v___x_3471_, 1);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3471_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_inc(v_a_3483_);
lean_dec(v___x_3471_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3483_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object* v_self_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_);
lean_dec_ref(v_a_3497_);
lean_dec(v_a_3496_);
lean_dec(v_a_3495_);
lean_dec(v_a_3494_);
return v_res_3500_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3502_; uint8_t v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___f_3502_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3503_ = 1;
v___x_3504_ = l_Lake_instDataKindUnit;
v___x_3505_ = ((lean_object*)(l_Lake_LeanLib_defaultFacetConfig___closed__0));
v___x_3506_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3507_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3507_, 0, v___x_3506_);
lean_ctor_set(v___x_3507_, 1, v___x_3505_);
lean_ctor_set(v___x_3507_, 2, v___x_3504_);
lean_ctor_set(v___x_3507_, 3, v___f_3502_);
lean_ctor_set_uint8(v___x_3507_, sizeof(void*)*4, v___x_3503_);
lean_ctor_set_uint8(v___x_3507_, sizeof(void*)*4 + 1, v___x_3503_);
return v___x_3507_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = lean_obj_once(&l_Lake_LeanLib_defaultFacetConfig___closed__1, &l_Lake_LeanLib_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanLib_defaultFacetConfig___closed__1);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_3509_, lean_object* v_v_3510_, lean_object* v_t_3511_){
_start:
{
if (lean_obj_tag(v_t_3511_) == 0)
{
lean_object* v_size_3512_; lean_object* v_k_3513_; lean_object* v_v_3514_; lean_object* v_l_3515_; lean_object* v_r_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3796_; 
v_size_3512_ = lean_ctor_get(v_t_3511_, 0);
v_k_3513_ = lean_ctor_get(v_t_3511_, 1);
v_v_3514_ = lean_ctor_get(v_t_3511_, 2);
v_l_3515_ = lean_ctor_get(v_t_3511_, 3);
v_r_3516_ = lean_ctor_get(v_t_3511_, 4);
v_isSharedCheck_3796_ = !lean_is_exclusive(v_t_3511_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3518_ = v_t_3511_;
v_isShared_3519_ = v_isSharedCheck_3796_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_r_3516_);
lean_inc(v_l_3515_);
lean_inc(v_v_3514_);
lean_inc(v_k_3513_);
lean_inc(v_size_3512_);
lean_dec(v_t_3511_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3796_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
uint8_t v___x_3520_; 
v___x_3520_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3509_, v_k_3513_);
switch(v___x_3520_)
{
case 0:
{
lean_object* v_impl_3521_; lean_object* v___x_3522_; 
lean_dec(v_size_3512_);
v_impl_3521_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3509_, v_v_3510_, v_l_3515_);
v___x_3522_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3516_) == 0)
{
lean_object* v_size_3523_; lean_object* v_size_3524_; lean_object* v_k_3525_; lean_object* v_v_3526_; lean_object* v_l_3527_; lean_object* v_r_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; uint8_t v___x_3531_; 
v_size_3523_ = lean_ctor_get(v_r_3516_, 0);
v_size_3524_ = lean_ctor_get(v_impl_3521_, 0);
lean_inc(v_size_3524_);
v_k_3525_ = lean_ctor_get(v_impl_3521_, 1);
lean_inc(v_k_3525_);
v_v_3526_ = lean_ctor_get(v_impl_3521_, 2);
lean_inc(v_v_3526_);
v_l_3527_ = lean_ctor_get(v_impl_3521_, 3);
lean_inc(v_l_3527_);
v_r_3528_ = lean_ctor_get(v_impl_3521_, 4);
lean_inc(v_r_3528_);
v___x_3529_ = lean_unsigned_to_nat(3u);
v___x_3530_ = lean_nat_mul(v___x_3529_, v_size_3523_);
v___x_3531_ = lean_nat_dec_lt(v___x_3530_, v_size_3524_);
lean_dec(v___x_3530_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3535_; 
lean_dec(v_r_3528_);
lean_dec(v_l_3527_);
lean_dec(v_v_3526_);
lean_dec(v_k_3525_);
v___x_3532_ = lean_nat_add(v___x_3522_, v_size_3524_);
lean_dec(v_size_3524_);
v___x_3533_ = lean_nat_add(v___x_3532_, v_size_3523_);
lean_dec(v___x_3532_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 3, v_impl_3521_);
lean_ctor_set(v___x_3518_, 0, v___x_3533_);
v___x_3535_ = v___x_3518_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v_k_3513_);
lean_ctor_set(v_reuseFailAlloc_3536_, 2, v_v_3514_);
lean_ctor_set(v_reuseFailAlloc_3536_, 3, v_impl_3521_);
lean_ctor_set(v_reuseFailAlloc_3536_, 4, v_r_3516_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
else
{
lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3602_; 
v_isSharedCheck_3602_ = !lean_is_exclusive(v_impl_3521_);
if (v_isSharedCheck_3602_ == 0)
{
lean_object* v_unused_3603_; lean_object* v_unused_3604_; lean_object* v_unused_3605_; lean_object* v_unused_3606_; lean_object* v_unused_3607_; 
v_unused_3603_ = lean_ctor_get(v_impl_3521_, 4);
lean_dec(v_unused_3603_);
v_unused_3604_ = lean_ctor_get(v_impl_3521_, 3);
lean_dec(v_unused_3604_);
v_unused_3605_ = lean_ctor_get(v_impl_3521_, 2);
lean_dec(v_unused_3605_);
v_unused_3606_ = lean_ctor_get(v_impl_3521_, 1);
lean_dec(v_unused_3606_);
v_unused_3607_ = lean_ctor_get(v_impl_3521_, 0);
lean_dec(v_unused_3607_);
v___x_3538_ = v_impl_3521_;
v_isShared_3539_ = v_isSharedCheck_3602_;
goto v_resetjp_3537_;
}
else
{
lean_dec(v_impl_3521_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3602_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v_size_3540_; lean_object* v_size_3541_; lean_object* v_k_3542_; lean_object* v_v_3543_; lean_object* v_l_3544_; lean_object* v_r_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; uint8_t v___x_3548_; 
v_size_3540_ = lean_ctor_get(v_l_3527_, 0);
v_size_3541_ = lean_ctor_get(v_r_3528_, 0);
v_k_3542_ = lean_ctor_get(v_r_3528_, 1);
v_v_3543_ = lean_ctor_get(v_r_3528_, 2);
v_l_3544_ = lean_ctor_get(v_r_3528_, 3);
v_r_3545_ = lean_ctor_get(v_r_3528_, 4);
v___x_3546_ = lean_unsigned_to_nat(2u);
v___x_3547_ = lean_nat_mul(v___x_3546_, v_size_3540_);
v___x_3548_ = lean_nat_dec_lt(v_size_3541_, v___x_3547_);
lean_dec(v___x_3547_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3577_; 
lean_inc(v_r_3545_);
lean_inc(v_l_3544_);
lean_inc(v_v_3543_);
lean_inc(v_k_3542_);
v_isSharedCheck_3577_ = !lean_is_exclusive(v_r_3528_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; lean_object* v_unused_3579_; lean_object* v_unused_3580_; lean_object* v_unused_3581_; lean_object* v_unused_3582_; 
v_unused_3578_ = lean_ctor_get(v_r_3528_, 4);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_r_3528_, 3);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_r_3528_, 2);
lean_dec(v_unused_3580_);
v_unused_3581_ = lean_ctor_get(v_r_3528_, 1);
lean_dec(v_unused_3581_);
v_unused_3582_ = lean_ctor_get(v_r_3528_, 0);
lean_dec(v_unused_3582_);
v___x_3550_ = v_r_3528_;
v_isShared_3551_ = v_isSharedCheck_3577_;
goto v_resetjp_3549_;
}
else
{
lean_dec(v_r_3528_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3577_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___x_3565_; lean_object* v___y_3567_; 
v___x_3552_ = lean_nat_add(v___x_3522_, v_size_3524_);
lean_dec(v_size_3524_);
v___x_3553_ = lean_nat_add(v___x_3552_, v_size_3523_);
lean_dec(v___x_3552_);
v___x_3565_ = lean_nat_add(v___x_3522_, v_size_3540_);
if (lean_obj_tag(v_l_3544_) == 0)
{
lean_object* v_size_3575_; 
v_size_3575_ = lean_ctor_get(v_l_3544_, 0);
lean_inc(v_size_3575_);
v___y_3567_ = v_size_3575_;
goto v___jp_3566_;
}
else
{
lean_object* v___x_3576_; 
v___x_3576_ = lean_unsigned_to_nat(0u);
v___y_3567_ = v___x_3576_;
goto v___jp_3566_;
}
v___jp_3554_:
{
lean_object* v___x_3558_; lean_object* v___x_3560_; 
v___x_3558_ = lean_nat_add(v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec(v___y_3556_);
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 4, v_r_3516_);
lean_ctor_set(v___x_3550_, 3, v_r_3545_);
lean_ctor_set(v___x_3550_, 2, v_v_3514_);
lean_ctor_set(v___x_3550_, 1, v_k_3513_);
lean_ctor_set(v___x_3550_, 0, v___x_3558_);
v___x_3560_ = v___x_3550_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3558_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_k_3513_);
lean_ctor_set(v_reuseFailAlloc_3564_, 2, v_v_3514_);
lean_ctor_set(v_reuseFailAlloc_3564_, 3, v_r_3545_);
lean_ctor_set(v_reuseFailAlloc_3564_, 4, v_r_3516_);
v___x_3560_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
lean_object* v___x_3562_; 
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 4, v___x_3560_);
lean_ctor_set(v___x_3538_, 3, v___y_3555_);
lean_ctor_set(v___x_3538_, 2, v_v_3543_);
lean_ctor_set(v___x_3538_, 1, v_k_3542_);
lean_ctor_set(v___x_3538_, 0, v___x_3553_);
v___x_3562_ = v___x_3538_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3563_, 1, v_k_3542_);
lean_ctor_set(v_reuseFailAlloc_3563_, 2, v_v_3543_);
lean_ctor_set(v_reuseFailAlloc_3563_, 3, v___y_3555_);
lean_ctor_set(v_reuseFailAlloc_3563_, 4, v___x_3560_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
v___jp_3566_:
{
lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3568_ = lean_nat_add(v___x_3565_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec(v___x_3565_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 4, v_l_3544_);
lean_ctor_set(v___x_3518_, 3, v_l_3527_);
lean_ctor_set(v___x_3518_, 2, v_v_3526_);
lean_ctor_set(v___x_3518_, 1, v_k_3525_);
lean_ctor_set(v___x_3518_, 0, v___x_3568_);
v___x_3570_ = v___x_3518_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3568_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v_k_3525_);
lean_ctor_set(v_reuseFailAlloc_3574_, 2, v_v_3526_);
lean_ctor_set(v_reuseFailAlloc_3574_, 3, v_l_3527_);
lean_ctor_set(v_reuseFailAlloc_3574_, 4, v_l_3544_);
v___x_3570_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_nat_add(v___x_3522_, v_size_3523_);
if (lean_obj_tag(v_r_3545_) == 0)
{
lean_object* v_size_3572_; 
v_size_3572_ = lean_ctor_get(v_r_3545_, 0);
lean_inc(v_size_3572_);
v___y_3555_ = v___x_3570_;
v___y_3556_ = v___x_3571_;
v___y_3557_ = v_size_3572_;
goto v___jp_3554_;
}
else
{
lean_object* v___x_3573_; 
v___x_3573_ = lean_unsigned_to_nat(0u);
v___y_3555_ = v___x_3570_;
v___y_3556_ = v___x_3571_;
v___y_3557_ = v___x_3573_;
goto v___jp_3554_;
}
}
}
}
}
else
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3588_; 
lean_del_object(v___x_3518_);
v___x_3583_ = lean_nat_add(v___x_3522_, v_size_3524_);
lean_dec(v_size_3524_);
v___x_3584_ = lean_nat_add(v___x_3583_, v_size_3523_);
lean_dec(v___x_3583_);
v___x_3585_ = lean_nat_add(v___x_3522_, v_size_3523_);
v___x_3586_ = lean_nat_add(v___x_3585_, v_size_3541_);
lean_dec(v___x_3585_);
lean_inc_ref(v_r_3516_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 4, v_r_3516_);
lean_ctor_set(v___x_3538_, 3, v_r_3528_);
lean_ctor_set(v___x_3538_, 2, v_v_3514_);
lean_ctor_set(v___x_3538_, 1, v_k_3513_);
lean_ctor_set(v___x_3538_, 0, v___x_3586_);
v___x_3588_ = v___x_3538_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3586_);
lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_k_3513_);
lean_ctor_set(v_reuseFailAlloc_3601_, 2, v_v_3514_);
lean_ctor_set(v_reuseFailAlloc_3601_, 3, v_r_3528_);
lean_ctor_set(v_reuseFailAlloc_3601_, 4, v_r_3516_);
v___x_3588_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
v_isSharedCheck_3595_ = !lean_is_exclusive(v_r_3516_);
if (v_isSharedCheck_3595_ == 0)
{
lean_object* v_unused_3596_; lean_object* v_unused_3597_; lean_object* v_unused_3598_; lean_object* v_unused_3599_; lean_object* v_unused_3600_; 
v_unused_3596_ = lean_ctor_get(v_r_3516_, 4);
lean_dec(v_unused_3596_);
v_unused_3597_ = lean_ctor_get(v_r_3516_, 3);
lean_dec(v_unused_3597_);
v_unused_3598_ = lean_ctor_get(v_r_3516_, 2);
lean_dec(v_unused_3598_);
v_unused_3599_ = lean_ctor_get(v_r_3516_, 1);
lean_dec(v_unused_3599_);
v_unused_3600_ = lean_ctor_get(v_r_3516_, 0);
lean_dec(v_unused_3600_);
v___x_3590_ = v_r_3516_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_dec(v_r_3516_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 4, v___x_3588_);
lean_ctor_set(v___x_3590_, 3, v_l_3527_);
lean_ctor_set(v___x_3590_, 2, v_v_3526_);
lean_ctor_set(v___x_3590_, 1, v_k_3525_);
lean_ctor_set(v___x_3590_, 0, v___x_3584_);
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3584_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v_k_3525_);
lean_ctor_set(v_reuseFailAlloc_3594_, 2, v_v_3526_);
lean_ctor_set(v_reuseFailAlloc_3594_, 3, v_l_3527_);
lean_ctor_set(v_reuseFailAlloc_3594_, 4, v___x_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3608_; 
v_l_3608_ = lean_ctor_get(v_impl_3521_, 3);
lean_inc(v_l_3608_);
if (lean_obj_tag(v_l_3608_) == 0)
{
lean_object* v_r_3609_; lean_object* v_k_3610_; lean_object* v_v_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3622_; 
v_r_3609_ = lean_ctor_get(v_impl_3521_, 4);
v_k_3610_ = lean_ctor_get(v_impl_3521_, 1);
v_v_3611_ = lean_ctor_get(v_impl_3521_, 2);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_impl_3521_);
if (v_isSharedCheck_3622_ == 0)
{
lean_object* v_unused_3623_; lean_object* v_unused_3624_; 
v_unused_3623_ = lean_ctor_get(v_impl_3521_, 3);
lean_dec(v_unused_3623_);
v_unused_3624_ = lean_ctor_get(v_impl_3521_, 0);
lean_dec(v_unused_3624_);
v___x_3613_ = v_impl_3521_;
v_isShared_3614_ = v_isSharedCheck_3622_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_r_3609_);
lean_inc(v_v_3611_);
lean_inc(v_k_3610_);
lean_dec(v_impl_3521_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3622_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; lean_object* v___x_3617_; 
v___x_3615_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3609_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 3, v_r_3609_);
lean_ctor_set(v___x_3613_, 2, v_v_3514_);
lean_ctor_set(v___x_3613_, 1, v_k_3513_);
lean_ctor_set(v___x_3613_, 0, v___x_3522_);
v___x_3617_ = v___x_3613_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3522_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v_k_3513_);
lean_ctor_set(v_reuseFailAlloc_3621_, 2, v_v_3514_);
lean_ctor_set(v_reuseFailAlloc_3621_, 3, v_r_3609_);
lean_ctor_set(v_reuseFailAlloc_3621_, 4, v_r_3609_);
v___x_3617_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3619_; 
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 4, v___x_3617_);
lean_ctor_set(v___x_3518_, 3, v_l_3608_);
lean_ctor_set(v___x_3518_, 2, v_v_3611_);
lean_ctor_set(v___x_3518_, 1, v_k_3610_);
lean_ctor_set(v___x_3518_, 0, v___x_3615_);
v___x_3619_ = v___x_3518_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3615_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_k_3610_);
lean_ctor_set(v_reuseFailAlloc_3620_, 2, v_v_3611_);
lean_ctor_set(v_reuseFailAlloc_3620_, 3, v_l_3608_);
lean_ctor_set(v_reuseFailAlloc_3620_, 4, v___x_3617_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
else
{
lean_object* v_r_3625_; 
v_r_3625_ = lean_ctor_get(v_impl_3521_, 4);
lean_inc(v_r_3625_);
if (lean_obj_tag(v_r_3625_) == 0)
{
lean_object* v_k_3626_; lean_object* v_v_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3650_; 
v_k_3626_ = lean_ctor_get(v_impl_3521_, 1);
v_v_3627_ = lean_ctor_get(v_impl_3521_, 2);
v_isSharedCheck_3650_ = !lean_is_exclusive(v_impl_3521_);
if (v_isSharedCheck_3650_ == 0)
{
lean_object* v_unused_3651_; lean_object* v_unused_3652_; lean_object* v_unused_3653_; 
v_unused_3651_ = lean_ctor_get(v_impl_3521_, 4);
lean_dec(v_unused_3651_);
v_unused_3652_ = lean_ctor_get(v_impl_3521_, 3);
lean_dec(v_unused_3652_);
v_unused_3653_ = lean_ctor_get(v_impl_3521_, 0);
lean_dec(v_unused_3653_);
v___x_3629_ = v_impl_3521_;
v_isShared_3630_ = v_isSharedCheck_3650_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_v_3627_);
lean_inc(v_k_3626_);
lean_dec(v_impl_3521_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3650_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v_k_3631_; lean_object* v_v_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3646_; 
v_k_3631_ = lean_ctor_get(v_r_3625_, 1);
v_v_3632_ = lean_ctor_get(v_r_3625_, 2);
v_isSharedCheck_3646_ = !lean_is_exclusive(v_r_3625_);
if (v_isSharedCheck_3646_ == 0)
{
lean_object* v_unused_3647_; lean_object* v_unused_3648_; lean_object* v_unused_3649_; 
v_unused_3647_ = lean_ctor_get(v_r_3625_, 4);
lean_dec(v_unused_3647_);
v_unused_3648_ = lean_ctor_get(v_r_3625_, 3);
lean_dec(v_unused_3648_);
v_unused_3649_ = lean_ctor_get(v_r_3625_, 0);
lean_dec(v_unused_3649_);
v___x_3634_ = v_r_3625_;
v_isShared_3635_ = v_isSharedCheck_3646_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_v_3632_);
lean_inc(v_k_3631_);
lean_dec(v_r_3625_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3646_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3636_ = lean_unsigned_to_nat(3u);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 4, v_l_3608_);
lean_ctor_set(v___x_3634_, 3, v_l_3608_);
lean_ctor_set(v___x_3634_, 2, v_v_3627_);
lean_ctor_set(v___x_3634_, 1, v_k_3626_);
lean_ctor_set(v___x_3634_, 0, v___x_3522_);
v___x_3638_ = v___x_3634_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3522_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_k_3626_);
lean_ctor_set(v_reuseFailAlloc_3645_, 2, v_v_3627_);
lean_ctor_set(v_reuseFailAlloc_3645_, 3, v_l_3608_);
lean_ctor_set(v_reuseFailAlloc_3645_, 4, v_l_3608_);
v___x_3638_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3640_; 
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 4, v_l_3608_);
lean_ctor_set(v___x_3629_, 2, v_v_3514_);
lean_ctor_set(v___x_3629_, 1, v_k_3513_);
lean_ctor_set(v___x_3629_, 0, v___x_3522_);
v___x_3640_ = v___x_3629_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3522_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_k_3513_);
lean_ctor_set(v_reuseFailAlloc_3644_, 2, v_v_3514_);
lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_l_3608_);
lean_ctor_set(v_reuseFailAlloc_3644_, 4, v_l_3608_);
v___x_3640_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3642_; 
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 4, v___x_3640_);
lean_ctor_set(v___x_3518_, 3, v___x_3638_);
lean_ctor_set(v___x_3518_, 2, v_v_3632_);
lean_ctor_set(v___x_3518_, 1, v_k_3631_);
lean_ctor_set(v___x_3518_, 0, v___x_3636_);
v___x_3642_ = v___x_3518_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3636_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_k_3631_);
lean_ctor_set(v_reuseFailAlloc_3643_, 2, v_v_3632_);
lean_ctor_set(v_reuseFailAlloc_3643_, 3, v___x_3638_);
lean_ctor_set(v_reuseFailAlloc_3643_, 4, v___x_3640_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
}
}
else
{
lean_object* v___x_3654_; lean_object* v___x_3656_; 
v___x_3654_ = lean_unsigned_to_nat(2u);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 4, v_r_3625_);
lean_ctor_set(v___x_3518_, 3, v_impl_3521_);
lean_ctor_set(v___x_3518_, 0, v___x_3654_);
v___x_3656_ = v___x_3518_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_k_3513_);
lean_ctor_set(v_reuseFailAlloc_3657_, 2, v_v_3514_);
lean_ctor_set(v_reuseFailAlloc_3657_, 3, v_impl_3521_);
lean_ctor_set(v_reuseFailAlloc_3657_, 4, v_r_3625_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3659_; 
lean_dec(v_v_3514_);
lean_dec(v_k_3513_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 2, v_v_3510_);
lean_ctor_set(v___x_3518_, 1, v_k_3509_);
v___x_3659_ = v___x_3518_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_size_3512_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_k_3509_);
lean_ctor_set(v_reuseFailAlloc_3660_, 2, v_v_3510_);
lean_ctor_set(v_reuseFailAlloc_3660_, 3, v_l_3515_);
lean_ctor_set(v_reuseFailAlloc_3660_, 4, v_r_3516_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
default: 
{
lean_object* v_impl_3661_; lean_object* v___x_3662_; 
lean_dec(v_size_3512_);
v_impl_3661_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3509_, v_v_3510_, v_r_3516_);
v___x_3662_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3515_) == 0)
{
lean_object* v_size_3663_; lean_object* v_size_3664_; lean_object* v_k_3665_; lean_object* v_v_3666_; lean_object* v_l_3667_; lean_object* v_r_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v_size_3663_ = lean_ctor_get(v_l_3515_, 0);
v_size_3664_ = lean_ctor_get(v_impl_3661_, 0);
lean_inc(v_size_3664_);
v_k_3665_ = lean_ctor_get(v_impl_3661_, 1);
lean_inc(v_k_3665_);
v_v_3666_ = lean_ctor_get(v_impl_3661_, 2);
lean_inc(v_v_3666_);
v_l_3667_ = lean_ctor_get(v_impl_3661_, 3);
lean_inc(v_l_3667_);
v_r_3668_ = lean_ctor_get(v_impl_3661_, 4);
lean_inc(v_r_3668_);
v___x_3669_ = lean_unsigned_to_nat(3u);
v___x_3670_ = lean_nat_mul(v___x_3669_, v_size_3663_);
v___x_3671_ = lean_nat_dec_lt(v___x_3670_, v_size_3664_);
lean_dec(v___x_3670_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3675_; 
lean_dec(v_r_3668_);
lean_dec(v_l_3667_);
lean_dec(v_v_3666_);
lean_dec(v_k_3665_);
v___x_3672_ = lean_nat_add(v___x_3662_, v_size_3663_);
v___x_3673_ = lean_nat_add(v___x_3672_, v_size_3664_);
lean_dec(v_size_3664_);
lean_dec(v___x_3672_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 4, v_impl_3661_);
lean_ctor_set(v___x_3518_, 0, v___x_3673_);
v___x_3675_ = v___x_3518_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_k_3513_);
lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_v_3514_);
lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_l_3515_);
lean_ctor_set(v_reuseFailAlloc_3676_, 4, v_impl_3661_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
else
{
lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3740_; 
v_isSharedCheck_3740_ = !lean_is_exclusive(v_impl_3661_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; lean_object* v_unused_3742_; lean_object* v_unused_3743_; lean_object* v_unused_3744_; lean_object* v_unused_3745_; 
v_unused_3741_ = lean_ctor_get(v_impl_3661_, 4);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_impl_3661_, 3);
lean_dec(v_unused_3742_);
v_unused_3743_ = lean_ctor_get(v_impl_3661_, 2);
lean_dec(v_unused_3743_);
v_unused_3744_ = lean_ctor_get(v_impl_3661_, 1);
lean_dec(v_unused_3744_);
v_unused_3745_ = lean_ctor_get(v_impl_3661_, 0);
lean_dec(v_unused_3745_);
v___x_3678_ = v_impl_3661_;
v_isShared_3679_ = v_isSharedCheck_3740_;
goto v_resetjp_3677_;
}
else
{
lean_dec(v_impl_3661_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3740_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v_size_3680_; lean_object* v_k_3681_; lean_object* v_v_3682_; lean_object* v_l_3683_; lean_object* v_r_3684_; lean_object* v_size_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; uint8_t v___x_3688_; 
v_size_3680_ = lean_ctor_get(v_l_3667_, 0);
v_k_3681_ = lean_ctor_get(v_l_3667_, 1);
v_v_3682_ = lean_ctor_get(v_l_3667_, 2);
v_l_3683_ = lean_ctor_get(v_l_3667_, 3);
v_r_3684_ = lean_ctor_get(v_l_3667_, 4);
v_size_3685_ = lean_ctor_get(v_r_3668_, 0);
v___x_3686_ = lean_unsigned_to_nat(2u);
v___x_3687_ = lean_nat_mul(v___x_3686_, v_size_3685_);
v___x_3688_ = lean_nat_dec_lt(v_size_3680_, v___x_3687_);
lean_dec(v___x_3687_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3716_; 
lean_inc(v_r_3684_);
lean_inc(v_l_3683_);
lean_inc(v_v_3682_);
lean_inc(v_k_3681_);
v_isSharedCheck_3716_ = !lean_is_exclusive(v_l_3667_);
if (v_isSharedCheck_3716_ == 0)
{
lean_object* v_unused_3717_; lean_object* v_unused_3718_; lean_object* v_unused_3719_; lean_object* v_unused_3720_; lean_object* v_unused_3721_; 
v_unused_3717_ = lean_ctor_get(v_l_3667_, 4);
lean_dec(v_unused_3717_);
v_unused_3718_ = lean_ctor_get(v_l_3667_, 3);
lean_dec(v_unused_3718_);
v_unused_3719_ = lean_ctor_get(v_l_3667_, 2);
lean_dec(v_unused_3719_);
v_unused_3720_ = lean_ctor_get(v_l_3667_, 1);
lean_dec(v_unused_3720_);
v_unused_3721_ = lean_ctor_get(v_l_3667_, 0);
lean_dec(v_unused_3721_);
v___x_3690_ = v_l_3667_;
v_isShared_3691_ = v_isSharedCheck_3716_;
goto v_resetjp_3689_;
}
else
{
lean_dec(v_l_3667_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3716_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3706_; 
v___x_3692_ = lean_nat_add(v___x_3662_, v_size_3663_);
v___x_3693_ = lean_nat_add(v___x_3692_, v_size_3664_);
lean_dec(v_size_3664_);
if (lean_obj_tag(v_l_3683_) == 0)
{
lean_object* v_size_3714_; 
v_size_3714_ = lean_ctor_get(v_l_3683_, 0);
lean_inc(v_size_3714_);
v___y_3706_ = v_size_3714_;
goto v___jp_3705_;
}
else
{
lean_object* v___x_3715_; 
v___x_3715_ = lean_unsigned_to_nat(0u);
v___y_3706_ = v___x_3715_;
goto v___jp_3705_;
}
v___jp_3694_:
{
lean_object* v___x_3698_; lean_object* v___x_3700_; 
v___x_3698_ = lean_nat_add(v___y_3695_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec(v___y_3695_);
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 4, v_r_3668_);
lean_ctor_set(v___x_3690_, 3, v_r_3684_);
lean_ctor_set(v___x_3690_, 2, v_v_3666_);
lean_ctor_set(v___x_3690_, 1, v_k_3665_);
lean_ctor_set(v___x_3690_, 0, v___x_3698_);
v___x_3700_ = v___x_3690_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v_k_3665_);
lean_ctor_set(v_reuseFailAlloc_3704_, 2, v_v_3666_);
lean_ctor_set(v_reuseFailAlloc_3704_, 3, v_r_3684_);
lean_ctor_set(v_reuseFailAlloc_3704_, 4, v_r_3668_);
v___x_3700_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
lean_object* v___x_3702_; 
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 4, v___x_3700_);
lean_ctor_set(v___x_3678_, 3, v___y_3696_);
lean_ctor_set(v___x_3678_, 2, v_v_3682_);
lean_ctor_set(v___x_3678_, 1, v_k_3681_);
lean_ctor_set(v___x_3678_, 0, v___x_3693_);
v___x_3702_ = v___x_3678_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3693_);
lean_ctor_set(v_reuseFailAlloc_3703_, 1, v_k_3681_);
lean_ctor_set(v_reuseFailAlloc_3703_, 2, v_v_3682_);
lean_ctor_set(v_reuseFailAlloc_3703_, 3, v___y_3696_);
lean_ctor_set(v_reuseFailAlloc_3703_, 4, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
v___jp_3705_:
{
lean_object* v___x_3707_; lean_object* v___x_3709_; 
v___x_3707_ = lean_nat_add(v___x_3692_, v___y_3706_);
lean_dec(v___y_3706_);
lean_dec(v___x_3692_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 4, v_l_3683_);
lean_ctor_set(v___x_3518_, 0, v___x_3707_);
v___x_3709_ = v___x_3518_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3707_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_k_3513_);
lean_ctor_set(v_reuseFailAlloc_3713_, 2, v_v_3514_);
lean_ctor_set(v_reuseFailAlloc_3713_, 3, v_l_3515_);
lean_ctor_set(v_reuseFailAlloc_3713_, 4, v_l_3683_);
v___x_3709_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
lean_object* v___x_3710_; 
v___x_3710_ = lean_nat_add(v___x_3662_, v_size_3685_);
if (lean_obj_tag(v_r_3684_) == 0)
{
lean_object* v_size_3711_; 
v_size_3711_ = lean_ctor_get(v_r_3684_, 0);
lean_inc(v_size_3711_);
v___y_3695_ = v___x_3710_;
v___y_3696_ = v___x_3709_;
v___y_3697_ = v_size_3711_;
goto v___jp_3694_;
}
else
{
lean_object* v___x_3712_; 
v___x_3712_ = lean_unsigned_to_nat(0u);
v___y_3695_ = v___x_3710_;
v___y_3696_ = v___x_3709_;
v___y_3697_ = v___x_3712_;
goto v___jp_3694_;
}
}
}
}
}
else
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3726_; 
lean_del_object(v___x_3518_);
v___x_3722_ = lean_nat_add(v___x_3662_, v_size_3663_);
v___x_3723_ = lean_nat_add(v___x_3722_, v_size_3664_);
lean_dec(v_size_3664_);
v___x_3724_ = lean_nat_add(v___x_3722_, v_size_3680_);
lean_dec(v___x_3722_);
lean_inc_ref(v_l_3515_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 4, v_l_3667_);
lean_ctor_set(v___x_3678_, 3, v_l_3515_);
lean_ctor_set(v___x_3678_, 2, v_v_3514_);
lean_ctor_set(v___x_3678_, 1, v_k_3513_);
lean_ctor_set(v___x_3678_, 0, v___x_3724_);
v___x_3726_ = v___x_3678_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3724_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v_k_3513_);
lean_ctor_set(v_reuseFailAlloc_3739_, 2, v_v_3514_);
lean_ctor_set(v_reuseFailAlloc_3739_, 3, v_l_3515_);
lean_ctor_set(v_reuseFailAlloc_3739_, 4, v_l_3667_);
v___x_3726_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
v_isSharedCheck_3733_ = !lean_is_exclusive(v_l_3515_);
if (v_isSharedCheck_3733_ == 0)
{
lean_object* v_unused_3734_; lean_object* v_unused_3735_; lean_object* v_unused_3736_; lean_object* v_unused_3737_; lean_object* v_unused_3738_; 
v_unused_3734_ = lean_ctor_get(v_l_3515_, 4);
lean_dec(v_unused_3734_);
v_unused_3735_ = lean_ctor_get(v_l_3515_, 3);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_l_3515_, 2);
lean_dec(v_unused_3736_);
v_unused_3737_ = lean_ctor_get(v_l_3515_, 1);
lean_dec(v_unused_3737_);
v_unused_3738_ = lean_ctor_get(v_l_3515_, 0);
lean_dec(v_unused_3738_);
v___x_3728_ = v_l_3515_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_dec(v_l_3515_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 4, v_r_3668_);
lean_ctor_set(v___x_3728_, 3, v___x_3726_);
lean_ctor_set(v___x_3728_, 2, v_v_3666_);
lean_ctor_set(v___x_3728_, 1, v_k_3665_);
lean_ctor_set(v___x_3728_, 0, v___x_3723_);
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3723_);
lean_ctor_set(v_reuseFailAlloc_3732_, 1, v_k_3665_);
lean_ctor_set(v_reuseFailAlloc_3732_, 2, v_v_3666_);
lean_ctor_set(v_reuseFailAlloc_3732_, 3, v___x_3726_);
lean_ctor_set(v_reuseFailAlloc_3732_, 4, v_r_3668_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3746_; 
v_l_3746_ = lean_ctor_get(v_impl_3661_, 3);
lean_inc(v_l_3746_);
if (lean_obj_tag(v_l_3746_) == 0)
{
lean_object* v_r_3747_; lean_object* v_k_3748_; lean_object* v_v_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3772_; 
v_r_3747_ = lean_ctor_get(v_impl_3661_, 4);
v_k_3748_ = lean_ctor_get(v_impl_3661_, 1);
v_v_3749_ = lean_ctor_get(v_impl_3661_, 2);
v_isSharedCheck_3772_ = !lean_is_exclusive(v_impl_3661_);
if (v_isSharedCheck_3772_ == 0)
{
lean_object* v_unused_3773_; lean_object* v_unused_3774_; 
v_unused_3773_ = lean_ctor_get(v_impl_3661_, 3);
lean_dec(v_unused_3773_);
v_unused_3774_ = lean_ctor_get(v_impl_3661_, 0);
lean_dec(v_unused_3774_);
v___x_3751_ = v_impl_3661_;
v_isShared_3752_ = v_isSharedCheck_3772_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_r_3747_);
lean_inc(v_v_3749_);
lean_inc(v_k_3748_);
lean_dec(v_impl_3661_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3772_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v_k_3753_; lean_object* v_v_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3768_; 
v_k_3753_ = lean_ctor_get(v_l_3746_, 1);
v_v_3754_ = lean_ctor_get(v_l_3746_, 2);
v_isSharedCheck_3768_ = !lean_is_exclusive(v_l_3746_);
if (v_isSharedCheck_3768_ == 0)
{
lean_object* v_unused_3769_; lean_object* v_unused_3770_; lean_object* v_unused_3771_; 
v_unused_3769_ = lean_ctor_get(v_l_3746_, 4);
lean_dec(v_unused_3769_);
v_unused_3770_ = lean_ctor_get(v_l_3746_, 3);
lean_dec(v_unused_3770_);
v_unused_3771_ = lean_ctor_get(v_l_3746_, 0);
lean_dec(v_unused_3771_);
v___x_3756_ = v_l_3746_;
v_isShared_3757_ = v_isSharedCheck_3768_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_v_3754_);
lean_inc(v_k_3753_);
lean_dec(v_l_3746_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3768_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3758_; lean_object* v___x_3760_; 
v___x_3758_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3747_, 2);
if (v_isShared_3757_ == 0)
{
lean_ctor_set(v___x_3756_, 4, v_r_3747_);
lean_ctor_set(v___x_3756_, 3, v_r_3747_);
lean_ctor_set(v___x_3756_, 2, v_v_3514_);
lean_ctor_set(v___x_3756_, 1, v_k_3513_);
lean_ctor_set(v___x_3756_, 0, v___x_3662_);
v___x_3760_ = v___x_3756_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3767_, 1, v_k_3513_);
lean_ctor_set(v_reuseFailAlloc_3767_, 2, v_v_3514_);
lean_ctor_set(v_reuseFailAlloc_3767_, 3, v_r_3747_);
lean_ctor_set(v_reuseFailAlloc_3767_, 4, v_r_3747_);
v___x_3760_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3762_; 
lean_inc(v_r_3747_);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 3, v_r_3747_);
lean_ctor_set(v___x_3751_, 0, v___x_3662_);
v___x_3762_ = v___x_3751_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3766_, 1, v_k_3748_);
lean_ctor_set(v_reuseFailAlloc_3766_, 2, v_v_3749_);
lean_ctor_set(v_reuseFailAlloc_3766_, 3, v_r_3747_);
lean_ctor_set(v_reuseFailAlloc_3766_, 4, v_r_3747_);
v___x_3762_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3764_; 
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 4, v___x_3762_);
lean_ctor_set(v___x_3518_, 3, v___x_3760_);
lean_ctor_set(v___x_3518_, 2, v_v_3754_);
lean_ctor_set(v___x_3518_, 1, v_k_3753_);
lean_ctor_set(v___x_3518_, 0, v___x_3758_);
v___x_3764_ = v___x_3518_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3758_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v_k_3753_);
lean_ctor_set(v_reuseFailAlloc_3765_, 2, v_v_3754_);
lean_ctor_set(v_reuseFailAlloc_3765_, 3, v___x_3760_);
lean_ctor_set(v_reuseFailAlloc_3765_, 4, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
}
}
else
{
lean_object* v_r_3775_; 
v_r_3775_ = lean_ctor_get(v_impl_3661_, 4);
lean_inc(v_r_3775_);
if (lean_obj_tag(v_r_3775_) == 0)
{
lean_object* v_k_3776_; lean_object* v_v_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3788_; 
v_k_3776_ = lean_ctor_get(v_impl_3661_, 1);
v_v_3777_ = lean_ctor_get(v_impl_3661_, 2);
v_isSharedCheck_3788_ = !lean_is_exclusive(v_impl_3661_);
if (v_isSharedCheck_3788_ == 0)
{
lean_object* v_unused_3789_; lean_object* v_unused_3790_; lean_object* v_unused_3791_; 
v_unused_3789_ = lean_ctor_get(v_impl_3661_, 4);
lean_dec(v_unused_3789_);
v_unused_3790_ = lean_ctor_get(v_impl_3661_, 3);
lean_dec(v_unused_3790_);
v_unused_3791_ = lean_ctor_get(v_impl_3661_, 0);
lean_dec(v_unused_3791_);
v___x_3779_ = v_impl_3661_;
v_isShared_3780_ = v_isSharedCheck_3788_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_v_3777_);
lean_inc(v_k_3776_);
lean_dec(v_impl_3661_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3788_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3781_; lean_object* v___x_3783_; 
v___x_3781_ = lean_unsigned_to_nat(3u);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 4, v_l_3746_);
lean_ctor_set(v___x_3779_, 2, v_v_3514_);
lean_ctor_set(v___x_3779_, 1, v_k_3513_);
lean_ctor_set(v___x_3779_, 0, v___x_3662_);
v___x_3783_ = v___x_3779_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v_k_3513_);
lean_ctor_set(v_reuseFailAlloc_3787_, 2, v_v_3514_);
lean_ctor_set(v_reuseFailAlloc_3787_, 3, v_l_3746_);
lean_ctor_set(v_reuseFailAlloc_3787_, 4, v_l_3746_);
v___x_3783_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
lean_object* v___x_3785_; 
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 4, v_r_3775_);
lean_ctor_set(v___x_3518_, 3, v___x_3783_);
lean_ctor_set(v___x_3518_, 2, v_v_3777_);
lean_ctor_set(v___x_3518_, 1, v_k_3776_);
lean_ctor_set(v___x_3518_, 0, v___x_3781_);
v___x_3785_ = v___x_3518_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3781_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_k_3776_);
lean_ctor_set(v_reuseFailAlloc_3786_, 2, v_v_3777_);
lean_ctor_set(v_reuseFailAlloc_3786_, 3, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3786_, 4, v_r_3775_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
else
{
lean_object* v___x_3792_; lean_object* v___x_3794_; 
v___x_3792_ = lean_unsigned_to_nat(2u);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 4, v_impl_3661_);
lean_ctor_set(v___x_3518_, 3, v_r_3775_);
lean_ctor_set(v___x_3518_, 0, v___x_3792_);
v___x_3794_ = v___x_3518_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3792_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v_k_3513_);
lean_ctor_set(v_reuseFailAlloc_3795_, 2, v_v_3514_);
lean_ctor_set(v_reuseFailAlloc_3795_, 3, v_r_3775_);
lean_ctor_set(v_reuseFailAlloc_3795_, 4, v_impl_3661_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
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
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = lean_unsigned_to_nat(1u);
v___x_3798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3797_);
lean_ctor_set(v___x_3798_, 1, v_k_3509_);
lean_ctor_set(v___x_3798_, 2, v_v_3510_);
lean_ctor_set(v___x_3798_, 3, v_t_3511_);
lean_ctor_set(v___x_3798_, 4, v_t_3511_);
return v___x_3798_;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3799_ = lean_box(1);
v___x_3800_ = l_Lake_LeanLib_defaultFacetConfig;
v___x_3801_ = l_Lake_LeanLib_defaultFacet;
v___x_3802_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3801_, v___x_3800_, v___x_3799_);
return v___x_3802_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3803_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__0, &l_Lake_LeanLib_initFacetConfigs___closed__0_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__0);
v___x_3804_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig));
v___x_3805_ = l_Lake_LeanLib_modulesFacet;
v___x_3806_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3805_, v___x_3804_, v___x_3803_);
return v___x_3806_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3807_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__1, &l_Lake_LeanLib_initFacetConfigs___closed__1_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__1);
v___x_3808_ = l_Lake_LeanLib_leanArtsFacetConfig;
v___x_3809_ = l_Lake_LeanLib_leanArtsFacet;
v___x_3810_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3809_, v___x_3808_, v___x_3807_);
return v___x_3810_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3811_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__2, &l_Lake_LeanLib_initFacetConfigs___closed__2_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__2);
v___x_3812_ = l_Lake_LeanLib_staticFacetConfig;
v___x_3813_ = l_Lake_LeanLib_staticFacet;
v___x_3814_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3813_, v___x_3812_, v___x_3811_);
return v___x_3814_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3815_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__3, &l_Lake_LeanLib_initFacetConfigs___closed__3_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__3);
v___x_3816_ = l_Lake_LeanLib_staticExportFacetConfig;
v___x_3817_ = l_Lake_LeanLib_staticExportFacet;
v___x_3818_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3817_, v___x_3816_, v___x_3815_);
return v___x_3818_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3819_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__4, &l_Lake_LeanLib_initFacetConfigs___closed__4_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__4);
v___x_3820_ = l_Lake_LeanLib_sharedFacetConfig;
v___x_3821_ = l_Lake_LeanLib_sharedFacet;
v___x_3822_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3821_, v___x_3820_, v___x_3819_);
return v___x_3822_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3823_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__5, &l_Lake_LeanLib_initFacetConfigs___closed__5_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__5);
v___x_3824_ = l_Lake_LeanLib_extraDepFacetConfig;
v___x_3825_ = l_Lake_LeanLib_extraDepFacet;
v___x_3826_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3825_, v___x_3824_, v___x_3823_);
return v___x_3826_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_3827_; 
v___x_3827_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__6, &l_Lake_LeanLib_initFacetConfigs___closed__6_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__6);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3828_, lean_object* v_k_3829_, lean_object* v_v_3830_, lean_object* v_t_3831_, lean_object* v_hl_3832_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3829_, v_v_3830_, v_t_3831_);
return v___x_3833_;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs(void){
_start:
{
lean_object* v___x_3834_; 
v___x_3834_ = l_Lake_LeanLib_initFacetConfigs;
return v___x_3834_;
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
