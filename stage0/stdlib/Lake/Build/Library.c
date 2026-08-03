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
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* lean_io_wait(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = ": some modules have bad imports or could not be read"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__3 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0_value;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(lean_object* v_self_141_, lean_object* v_root_142_, lean_object* v_col_143_, uint8_t v_viaImport_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_col_153_; lean_object* v___y_154_; lean_object* v_mods_156_; lean_object* v_modSet_157_; uint8_t v_hasErrors_158_; uint8_t v___x_159_; 
v_mods_156_ = lean_ctor_get(v_col_143_, 0);
v_modSet_157_ = lean_ctor_get(v_col_143_, 1);
v_hasErrors_158_ = lean_ctor_get_uint8(v_col_143_, sizeof(void*)*2);
v___x_159_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_modSet_157_, v_root_142_);
if (v___x_159_ == 0)
{
lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_224_; 
lean_inc_ref(v_modSet_157_);
lean_inc_ref(v_mods_156_);
v_isSharedCheck_224_ = !lean_is_exclusive(v_col_143_);
if (v_isSharedCheck_224_ == 0)
{
lean_object* v_unused_225_; lean_object* v_unused_226_; 
v_unused_225_ = lean_ctor_get(v_col_143_, 1);
lean_dec(v_unused_225_);
v_unused_226_ = lean_ctor_get(v_col_143_, 0);
lean_dec(v_unused_226_);
v___x_161_ = v_col_143_;
v_isShared_162_ = v_isSharedCheck_224_;
goto v_resetjp_160_;
}
else
{
lean_dec(v_col_143_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_224_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v_lib_163_; lean_object* v_pkg_164_; lean_object* v_name_165_; lean_object* v_keyName_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v_lib_163_ = lean_ctor_get(v_root_142_, 0);
v_pkg_164_ = lean_ctor_get(v_lib_163_, 0);
v_name_165_ = lean_ctor_get(v_root_142_, 1);
v_keyName_166_ = lean_ctor_get(v_pkg_164_, 2);
v___x_167_ = lean_box(0);
lean_inc_ref_n(v_root_142_, 2);
v___x_168_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_modSet_157_, v_root_142_, v___x_167_);
v___x_169_ = l_Lake_Module_importsFacet;
lean_inc(v_name_165_);
lean_inc(v_keyName_166_);
v___x_170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_170_, 0, v_keyName_166_);
lean_ctor_set(v___x_170_, 1, v_name_165_);
v___x_171_ = l_Lake_Module_keyword;
v___x_172_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
lean_ctor_set(v___x_172_, 2, v_root_142_);
lean_ctor_set(v___x_172_, 3, v___x_169_);
lean_inc_ref(v_a_145_);
lean_inc_ref(v_a_149_);
lean_inc(v_a_148_);
lean_inc(v_a_147_);
lean_inc(v_a_146_);
v___x_173_ = lean_apply_7(v_a_145_, v___x_172_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, lean_box(0));
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_214_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_a_175_ = lean_ctor_get(v___x_173_, 1);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_214_ == 0)
{
v___x_177_ = v___x_173_;
v_isShared_178_ = v_isSharedCheck_214_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_214_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v_task_179_; lean_object* v___x_180_; lean_object* v___y_182_; 
v_task_179_ = lean_ctor_get(v_a_174_, 0);
lean_inc_ref(v_task_179_);
lean_dec(v_a_174_);
v___x_180_ = lean_io_wait(v_task_179_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_186_; lean_object* v_col_188_; 
lean_del_object(v___x_177_);
v_a_186_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_180_, 2);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v___x_168_);
v_col_188_ = v___x_161_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_mods_156_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_168_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, sizeof(void*)*2, v_hasErrors_158_);
v_col_188_ = v_reuseFailAlloc_205_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
size_t v_sz_189_; size_t v___x_190_; lean_object* v___x_191_; 
v_sz_189_ = lean_array_size(v_a_186_);
v___x_190_ = ((size_t)0ULL);
v___x_191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_141_, v_a_186_, v_sz_189_, v___x_190_, v_col_188_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_175_);
lean_dec(v_a_186_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v_a_193_; lean_object* v_mods_194_; lean_object* v_modSet_195_; uint8_t v_hasErrors_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_204_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_192_);
v_a_193_ = lean_ctor_get(v___x_191_, 1);
lean_inc(v_a_193_);
lean_dec_ref_known(v___x_191_, 2);
v_mods_194_ = lean_ctor_get(v_a_192_, 0);
v_modSet_195_ = lean_ctor_get(v_a_192_, 1);
v_hasErrors_196_ = lean_ctor_get_uint8(v_a_192_, sizeof(void*)*2);
v_isSharedCheck_204_ = !lean_is_exclusive(v_a_192_);
if (v_isSharedCheck_204_ == 0)
{
v___x_198_ = v_a_192_;
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_modSet_195_);
lean_inc(v_mods_194_);
lean_dec(v_a_192_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = lean_array_push(v_mods_194_, v_root_142_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_200_);
v___x_202_ = v___x_198_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_modSet_195_);
lean_ctor_set_uint8(v_reuseFailAlloc_203_, sizeof(void*)*2, v_hasErrors_196_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
v_col_153_ = v___x_202_;
v___y_154_ = v_a_193_;
goto v___jp_152_;
}
}
}
else
{
lean_dec_ref(v_root_142_);
return v___x_191_;
}
}
}
else
{
uint8_t v___x_206_; 
lean_dec_ref_known(v___x_180_, 2);
lean_dec_ref(v_a_145_);
v___x_206_ = 1;
if (v_viaImport_144_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = lean_array_push(v_mods_156_, v_root_142_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v___x_168_);
lean_ctor_set(v___x_161_, 0, v___x_207_);
v___x_209_ = v___x_161_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v___x_168_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*2, v___x_206_);
v___y_182_ = v___x_209_;
goto v___jp_181_;
}
}
else
{
lean_object* v___x_212_; 
lean_dec_ref(v_root_142_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v___x_168_);
v___x_212_ = v___x_161_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_mods_156_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___x_168_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*2, v___x_206_);
v___y_182_ = v___x_212_;
goto v___jp_181_;
}
}
}
v___jp_181_:
{
lean_object* v___x_184_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___y_182_);
v___x_184_ = v___x_177_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___y_182_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_a_175_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
lean_object* v_a_215_; lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec_ref(v___x_168_);
lean_del_object(v___x_161_);
lean_dec_ref(v_mods_156_);
lean_dec_ref(v_a_145_);
lean_dec_ref(v_root_142_);
v_a_215_ = lean_ctor_get(v___x_173_, 0);
v_a_216_ = lean_ctor_get(v___x_173_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_173_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_inc(v_a_215_);
lean_dec(v___x_173_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_215_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_145_);
lean_dec_ref(v_root_142_);
v_col_153_ = v_col_143_;
v___y_154_ = v_a_150_;
goto v___jp_152_;
}
v___jp_152_:
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v_col_153_);
lean_ctor_set(v___x_155_, 1, v___y_154_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(lean_object* v_self_227_, lean_object* v_as_228_, size_t v_sz_229_, size_t v_i_230_, lean_object* v_b_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_a_240_; lean_object* v_a_241_; uint8_t v___x_245_; 
v___x_245_ = lean_usize_dec_lt(v_i_230_, v_sz_229_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
lean_dec_ref(v___y_232_);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v_b_231_);
lean_ctor_set(v___x_246_, 1, v___y_237_);
return v___x_246_;
}
else
{
lean_object* v_a_247_; lean_object* v_lib_248_; lean_object* v_name_249_; lean_object* v_name_250_; uint8_t v___x_251_; 
v_a_247_ = lean_array_uget_borrowed(v_as_228_, v_i_230_);
v_lib_248_ = lean_ctor_get(v_a_247_, 0);
v_name_249_ = lean_ctor_get(v_lib_248_, 1);
v_name_250_ = lean_ctor_get(v_self_227_, 1);
v___x_251_ = lean_name_eq(v_name_249_, v_name_250_);
if (v___x_251_ == 0)
{
v_a_240_ = v_b_231_;
v_a_241_ = v___y_237_;
goto v___jp_239_;
}
else
{
lean_object* v___x_252_; 
lean_inc_ref(v___y_232_);
lean_inc(v_a_247_);
v___x_252_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_227_, v_a_247_, v_b_231_, v___x_251_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v_a_254_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
v_a_254_ = lean_ctor_get(v___x_252_, 1);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_252_, 2);
v_a_240_ = v_a_253_;
v_a_241_ = v_a_254_;
goto v___jp_239_;
}
else
{
lean_dec_ref(v___y_232_);
return v___x_252_;
}
}
}
v___jp_239_:
{
size_t v___x_242_; size_t v___x_243_; 
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_add(v_i_230_, v___x_242_);
v_i_230_ = v___x_243_;
v_b_231_ = v_a_240_;
v___y_237_ = v_a_241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(lean_object* v_self_255_, lean_object* v_as_256_, lean_object* v_sz_257_, lean_object* v_i_258_, lean_object* v_b_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
size_t v_sz_boxed_267_; size_t v_i_boxed_268_; lean_object* v_res_269_; 
v_sz_boxed_267_ = lean_unbox_usize(v_sz_257_);
lean_dec(v_sz_257_);
v_i_boxed_268_ = lean_unbox_usize(v_i_258_);
lean_dec(v_i_258_);
v_res_269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_255_, v_as_256_, v_sz_boxed_267_, v_i_boxed_268_, v_b_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v_as_256_);
lean_dec_ref(v_self_255_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object* v_self_270_, lean_object* v_root_271_, lean_object* v_col_272_, lean_object* v_viaImport_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
uint8_t v_viaImport_boxed_281_; lean_object* v_res_282_; 
v_viaImport_boxed_281_ = lean_unbox(v_viaImport_273_);
v_res_282_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_270_, v_root_271_, v_col_272_, v_viaImport_boxed_281_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_self_270_);
return v_res_282_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_object* v_00_u03b2_283_, lean_object* v_m_284_, lean_object* v_a_285_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_284_, v_a_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(lean_object* v_00_u03b2_287_, lean_object* v_m_288_, lean_object* v_a_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(v_00_u03b2_287_, v_m_288_, v_a_289_);
lean_dec_ref(v_a_289_);
lean_dec_ref(v_m_288_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1(lean_object* v_00_u03b2_292_, lean_object* v_m_293_, lean_object* v_a_294_, lean_object* v_b_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_m_293_, v_a_294_, v_b_295_);
return v___x_296_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(lean_object* v_00_u03b2_297_, lean_object* v_a_298_, lean_object* v_x_299_){
_start:
{
uint8_t v___x_300_; 
v___x_300_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_298_, v_x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_301_, lean_object* v_a_302_, lean_object* v_x_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(v_00_u03b2_301_, v_a_302_, v_x_303_);
lean_dec(v_x_303_);
lean_dec_ref(v_a_302_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2(lean_object* v_00_u03b2_306_, lean_object* v_data_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(v_data_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_309_, lean_object* v_i_310_, lean_object* v_source_311_, lean_object* v_target_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(v_i_310_, v_source_311_, v_target_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_314_, lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(v_x_315_, v_x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(lean_object* v_self_318_, lean_object* v_as_319_, size_t v_sz_320_, size_t v_i_321_, lean_object* v_b_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = lean_usize_dec_lt(v_i_321_, v_sz_320_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec_ref(v___y_323_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v_b_322_);
lean_ctor_set(v___x_331_, 1, v___y_328_);
return v___x_331_;
}
else
{
uint8_t v___x_332_; lean_object* v_a_333_; lean_object* v___x_334_; 
v___x_332_ = 0;
v_a_333_ = lean_array_uget_borrowed(v_as_319_, v_i_321_);
lean_inc_ref(v___y_323_);
lean_inc(v_a_333_);
v___x_334_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_318_, v_a_333_, v_b_322_, v___x_332_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v_a_336_; size_t v___x_337_; size_t v___x_338_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
v_a_336_ = lean_ctor_get(v___x_334_, 1);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_334_, 2);
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_add(v_i_321_, v___x_337_);
v_i_321_ = v___x_338_;
v_b_322_ = v_a_335_;
v___y_328_ = v_a_336_;
goto _start;
}
else
{
lean_dec_ref(v___y_323_);
return v___x_334_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0___boxed(lean_object* v_self_340_, lean_object* v_as_341_, lean_object* v_sz_342_, lean_object* v_i_343_, lean_object* v_b_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
size_t v_sz_boxed_352_; size_t v_i_boxed_353_; lean_object* v_res_354_; 
v_sz_boxed_352_ = lean_unbox_usize(v_sz_342_);
lean_dec(v_sz_342_);
v_i_boxed_353_ = lean_unbox_usize(v_i_343_);
lean_dec(v_i_343_);
v_res_354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_340_, v_as_341_, v_sz_boxed_352_, v_i_boxed_353_, v_b_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec(v___y_347_);
lean_dec(v___y_346_);
lean_dec_ref(v_as_341_);
lean_dec_ref(v_self_340_);
return v_res_354_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2(void){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1));
v___x_358_ = l_Lake_BuildTrace_nil(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(lean_object* v_self_360_, lean_object* v_col_361_, lean_object* v___x_362_, uint8_t v___x_363_, lean_object* v___x_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; 
lean_inc_ref(v_self_360_);
v___x_372_ = l_Lake_LeanLib_getModuleArray(v_self_360_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; size_t v_sz_374_; size_t v___x_375_; lean_object* v___x_376_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_372_, 1);
v_sz_374_ = lean_array_size(v_a_373_);
v___x_375_ = ((size_t)0ULL);
v___x_376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_360_, v_a_373_, v_sz_374_, v___x_375_, v_col_361_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec(v_a_373_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_404_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_a_378_ = lean_ctor_get(v___x_376_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_404_ == 0)
{
v___x_380_ = v___x_376_;
v_isShared_381_ = v_isSharedCheck_404_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_404_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v_mods_382_; uint8_t v_hasErrors_383_; lean_object* v___y_385_; 
v_mods_382_ = lean_ctor_get(v_a_377_, 0);
lean_inc_ref(v_mods_382_);
v_hasErrors_383_ = lean_ctor_get_uint8(v_a_377_, sizeof(void*)*2);
lean_dec(v_a_377_);
if (v_hasErrors_383_ == 0)
{
lean_dec_ref(v_self_360_);
v___y_385_ = v_a_378_;
goto v___jp_384_;
}
else
{
lean_object* v_name_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_name_397_ = lean_ctor_get(v_self_360_, 1);
lean_inc(v_name_397_);
lean_dec_ref(v_self_360_);
v___x_398_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_397_, v_hasErrors_383_);
v___x_399_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__3));
v___x_400_ = lean_string_append(v___x_398_, v___x_399_);
v___x_401_ = 3;
v___x_402_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*1, v___x_401_);
v___x_403_ = lean_array_push(v_a_378_, v___x_402_);
v___y_385_ = v___x_403_;
goto v___jp_384_;
}
v___jp_384_:
{
lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_386_ = lean_mk_empty_array_with_capacity(v___x_362_);
v___x_387_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_388_ = 0;
v___x_389_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_390_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_390_, 0, v___x_386_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
lean_ctor_set(v___x_390_, 2, v___x_362_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*3, v___x_388_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*3 + 1, v___x_363_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 1, v___x_390_);
lean_ctor_set(v___x_380_, 0, v_mods_382_);
v___x_392_ = v___x_380_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_mods_382_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_390_);
v___x_392_ = v_reuseFailAlloc_396_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = lean_task_pure(v___x_392_);
v___x_394_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_364_);
lean_ctor_set(v___x_394_, 2, v___x_387_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*3, v___x_363_);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v___y_385_);
return v___x_395_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec(v___x_364_);
lean_dec(v___x_362_);
lean_dec_ref(v_self_360_);
v_a_405_ = lean_ctor_get(v___x_376_, 0);
v_a_406_ = lean_ctor_get(v___x_376_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_376_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_inc(v_a_405_);
lean_dec(v___x_376_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_405_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_415_; uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec_ref(v___y_365_);
lean_dec(v___x_364_);
lean_dec(v___x_362_);
lean_dec_ref(v_col_361_);
lean_dec_ref(v_self_360_);
v_a_414_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_372_, 1);
v___x_415_ = lean_io_error_to_string(v_a_414_);
v___x_416_ = 3;
v___x_417_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*1, v___x_416_);
v___x_418_ = lean_array_get_size(v___y_370_);
v___x_419_ = lean_array_push(v___y_370_, v___x_417_);
v___x_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed(lean_object* v_self_421_, lean_object* v_col_422_, lean_object* v___x_423_, lean_object* v___x_424_, lean_object* v___x_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
uint8_t v___x_7764__boxed_433_; lean_object* v_res_434_; 
v___x_7764__boxed_433_ = lean_unbox(v___x_424_);
v_res_434_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(v_self_421_, v_col_422_, v___x_423_, v___x_7764__boxed_433_, v___x_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec(v___y_428_);
lean_dec(v___y_427_);
return v_res_434_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = lean_box(0);
v___x_438_ = lean_unsigned_to_nat(16u);
v___x_439_ = lean_mk_array(v___x_438_, v___x_437_);
return v___x_439_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_440_);
return v___x_442_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3(void){
_start:
{
uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_col_446_; 
v___x_443_ = 0;
v___x_444_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_445_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0));
v_col_446_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_col_446_, 0, v___x_445_);
lean_ctor_set(v_col_446_, 1, v___x_444_);
lean_ctor_set_uint8(v_col_446_, sizeof(void*)*2, v___x_443_);
return v_col_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(lean_object* v_self_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v_col_458_; lean_object* v___x_459_; lean_object* v___f_460_; lean_object* v___x_461_; 
v___x_455_ = lean_box(0);
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = 0;
v_col_458_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3);
v___x_459_ = lean_box(v___x_457_);
v___f_460_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed), 12, 5);
lean_closure_set(v___f_460_, 0, v_self_447_);
lean_closure_set(v___f_460_, 1, v_col_458_);
lean_closure_set(v___f_460_, 2, v___x_456_);
lean_closure_set(v___f_460_, 3, v___x_459_);
lean_closure_set(v___f_460_, 4, v___x_455_);
v___x_461_ = l_Lake_ensureJob___redArg(v___x_455_, v___f_460_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___boxed(lean_object* v_self_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(v_self_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec(v_a_465_);
lean_dec(v_a_464_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(lean_object* v_as_472_, size_t v_i_473_, size_t v_stop_474_, lean_object* v_b_475_){
_start:
{
uint8_t v___x_476_; 
v___x_476_ = lean_usize_dec_eq(v_i_473_, v_stop_474_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v_name_478_; uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; size_t v___x_484_; size_t v___x_485_; 
v___x_477_ = lean_array_uget_borrowed(v_as_472_, v_i_473_);
v_name_478_ = lean_ctor_get(v___x_477_, 1);
v___x_479_ = 1;
lean_inc(v_name_478_);
v___x_480_ = l_Lean_Name_toString(v_name_478_, v___x_479_);
v___x_481_ = lean_string_append(v_b_475_, v___x_480_);
lean_dec_ref(v___x_480_);
v___x_482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_483_ = lean_string_append(v___x_481_, v___x_482_);
v___x_484_ = ((size_t)1ULL);
v___x_485_ = lean_usize_add(v_i_473_, v___x_484_);
v_i_473_ = v___x_485_;
v_b_475_ = v___x_483_;
goto _start;
}
else
{
return v_b_475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_487_, lean_object* v_i_488_, lean_object* v_stop_489_, lean_object* v_b_490_){
_start:
{
size_t v_i_boxed_491_; size_t v_stop_boxed_492_; lean_object* v_res_493_; 
v_i_boxed_491_ = lean_unbox_usize(v_i_488_);
lean_dec(v_i_488_);
v_stop_boxed_492_ = lean_unbox_usize(v_stop_489_);
lean_dec(v_stop_489_);
v_res_493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_as_487_, v_i_boxed_491_, v_stop_boxed_492_, v_b_490_);
lean_dec_ref(v_as_487_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(size_t v_sz_494_, size_t v_i_495_, lean_object* v_bs_496_){
_start:
{
uint8_t v___x_497_; 
v___x_497_ = lean_usize_dec_lt(v_i_495_, v_sz_494_);
if (v___x_497_ == 0)
{
return v_bs_496_;
}
else
{
lean_object* v_v_498_; lean_object* v_name_499_; lean_object* v___x_500_; lean_object* v_bs_x27_501_; lean_object* v___x_502_; lean_object* v___x_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v_v_498_ = lean_array_uget_borrowed(v_bs_496_, v_i_495_);
v_name_499_ = lean_ctor_get(v_v_498_, 1);
lean_inc(v_name_499_);
v___x_500_ = lean_unsigned_to_nat(0u);
v_bs_x27_501_ = lean_array_uset(v_bs_496_, v_i_495_, v___x_500_);
v___x_502_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_499_, v___x_497_);
v___x_503_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_add(v_i_495_, v___x_504_);
v___x_506_ = lean_array_uset(v_bs_x27_501_, v_i_495_, v___x_503_);
v_i_495_ = v___x_505_;
v_bs_496_ = v___x_506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_508_, lean_object* v_i_509_, lean_object* v_bs_510_){
_start:
{
size_t v_sz_boxed_511_; size_t v_i_boxed_512_; lean_object* v_res_513_; 
v_sz_boxed_511_ = lean_unbox_usize(v_sz_508_);
lean_dec(v_sz_508_);
v_i_boxed_512_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_511_, v_i_boxed_512_, v_bs_510_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(lean_object* v_a_514_){
_start:
{
size_t v_sz_515_; size_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_sz_515_ = lean_array_size(v_a_514_);
v___x_516_ = ((size_t)0ULL);
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_515_, v___x_516_, v_a_514_);
v___x_518_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(uint8_t v_fmt_519_, lean_object* v_a_520_){
_start:
{
lean_object* v___y_522_; 
if (v_fmt_519_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_529_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_array_get_size(v_a_520_);
v___x_532_ = lean_nat_dec_lt(v___x_530_, v___x_531_);
if (v___x_532_ == 0)
{
lean_dec_ref(v_a_520_);
v___y_522_ = v___x_529_;
goto v___jp_521_;
}
else
{
uint8_t v___x_533_; 
v___x_533_ = lean_nat_dec_le(v___x_531_, v___x_531_);
if (v___x_533_ == 0)
{
if (v___x_532_ == 0)
{
lean_dec_ref(v_a_520_);
v___y_522_ = v___x_529_;
goto v___jp_521_;
}
else
{
size_t v___x_534_; size_t v___x_535_; lean_object* v___x_536_; 
v___x_534_ = ((size_t)0ULL);
v___x_535_ = lean_usize_of_nat(v___x_531_);
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_520_, v___x_534_, v___x_535_, v___x_529_);
lean_dec_ref(v_a_520_);
v___y_522_ = v___x_536_;
goto v___jp_521_;
}
}
else
{
size_t v___x_537_; size_t v___x_538_; lean_object* v___x_539_; 
v___x_537_ = ((size_t)0ULL);
v___x_538_ = lean_usize_of_nat(v___x_531_);
v___x_539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_520_, v___x_537_, v___x_538_, v___x_529_);
lean_dec_ref(v_a_520_);
v___y_522_ = v___x_539_;
goto v___jp_521_;
}
}
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(v_a_520_);
v___x_541_ = l_Lean_Json_compress(v___x_540_);
return v___x_541_;
}
v___jp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = lean_string_utf8_byte_size(v___y_522_);
lean_inc_ref(v___y_522_);
v___x_526_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_526_, 0, v___y_522_);
lean_ctor_set(v___x_526_, 1, v___x_524_);
lean_ctor_set(v___x_526_, 2, v___x_525_);
v___x_527_ = l_String_Slice_Pos_prevn(v___x_526_, v___x_525_, v___x_523_);
lean_dec_ref_known(v___x_526_, 3);
v___x_528_ = lean_string_utf8_extract(v___y_522_, v___x_524_, v___x_527_);
lean_dec(v___x_527_);
lean_dec_ref(v___y_522_);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0___boxed(lean_object* v_fmt_542_, lean_object* v_a_543_){
_start:
{
uint8_t v_fmt_boxed_544_; lean_object* v_res_545_; 
v_fmt_boxed_544_ = lean_unbox(v_fmt_542_);
v_res_545_ = l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(v_fmt_boxed_544_, v_a_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(lean_object* v_as_559_, size_t v_i_560_, size_t v_stop_561_, lean_object* v_b_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
uint8_t v___x_570_; 
v___x_570_ = lean_usize_dec_eq(v_i_560_, v_stop_561_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v_lib_572_; lean_object* v_pkg_573_; lean_object* v_name_574_; lean_object* v_keyName_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_571_ = lean_array_uget_borrowed(v_as_559_, v_i_560_);
v_lib_572_ = lean_ctor_get(v___x_571_, 0);
v_pkg_573_ = lean_ctor_get(v_lib_572_, 0);
v_name_574_ = lean_ctor_get(v___x_571_, 1);
v_keyName_575_ = lean_ctor_get(v_pkg_573_, 2);
v___x_576_ = l_Lake_Module_leanArtsFacet;
lean_inc(v_name_574_);
lean_inc(v_keyName_575_);
v___x_577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_577_, 0, v_keyName_575_);
lean_ctor_set(v___x_577_, 1, v_name_574_);
v___x_578_ = l_Lake_Module_keyword;
lean_inc(v___x_571_);
v___x_579_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
lean_ctor_set(v___x_579_, 2, v___x_571_);
lean_ctor_set(v___x_579_, 3, v___x_576_);
lean_inc_ref(v___y_563_);
lean_inc_ref(v___y_567_);
lean_inc(v___y_566_);
lean_inc(v___y_565_);
lean_inc(v___y_564_);
v___x_580_ = lean_apply_7(v___y_563_, v___x_579_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, lean_box(0));
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v_a_582_; lean_object* v___x_583_; size_t v___x_584_; size_t v___x_585_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
v_a_582_ = lean_ctor_get(v___x_580_, 1);
lean_inc(v_a_582_);
lean_dec_ref_known(v___x_580_, 2);
v___x_583_ = l_Lake_Job_mix___redArg(v_b_562_, v_a_581_);
v___x_584_ = ((size_t)1ULL);
v___x_585_ = lean_usize_add(v_i_560_, v___x_584_);
v_i_560_ = v___x_585_;
v_b_562_ = v___x_583_;
v___y_568_ = v_a_582_;
goto _start;
}
else
{
lean_object* v_a_587_; lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v___y_563_);
lean_dec_ref(v_b_562_);
v_a_587_ = lean_ctor_get(v___x_580_, 0);
v_a_588_ = lean_ctor_get(v___x_580_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_580_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_inc(v_a_587_);
lean_dec(v___x_580_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_587_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
else
{
lean_object* v___x_596_; 
lean_dec_ref(v___y_563_);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v_b_562_);
lean_ctor_set(v___x_596_, 1, v___y_568_);
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0___boxed(lean_object* v_as_597_, lean_object* v_i_598_, lean_object* v_stop_599_, lean_object* v_b_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
size_t v_i_boxed_608_; size_t v_stop_boxed_609_; lean_object* v_res_610_; 
v_i_boxed_608_ = lean_unbox_usize(v_i_598_);
lean_dec(v_i_598_);
v_stop_boxed_609_ = lean_unbox_usize(v_stop_599_);
lean_dec(v_stop_599_);
v_res_610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_as_597_, v_i_boxed_608_, v_stop_boxed_609_, v_b_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v_as_597_);
return v_res_610_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; uint8_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_615_ = 0;
v___x_616_ = 0;
v___x_617_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v___x_618_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set(v___x_618_, 1, v___x_614_);
lean_ctor_set(v___x_618_, 2, v___x_613_);
lean_ctor_set_uint8(v___x_618_, sizeof(void*)*3, v___x_616_);
lean_ctor_set_uint8(v___x_618_, sizeof(void*)*3 + 1, v___x_615_);
return v___x_618_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1);
v___x_620_ = lean_box(0);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2);
v___x_623_ = lean_task_pure(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4(void){
_start:
{
uint8_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_624_ = 0;
v___x_625_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_626_ = lean_box(0);
v___x_627_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3);
v___x_628_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_626_);
lean_ctor_set(v___x_628_, 2, v___x_625_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*3, v___x_624_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(lean_object* v_self_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_pkg_637_; lean_object* v_name_638_; lean_object* v_keyName_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v_pkg_637_ = lean_ctor_get(v_self_629_, 0);
v_name_638_ = lean_ctor_get(v_self_629_, 1);
v_keyName_639_ = lean_ctor_get(v_pkg_637_, 2);
v___x_640_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_638_);
lean_inc(v_keyName_639_);
v___x_641_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_641_, 0, v_keyName_639_);
lean_ctor_set(v___x_641_, 1, v_name_638_);
v___x_642_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_643_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
lean_ctor_set(v___x_643_, 2, v_self_629_);
lean_ctor_set(v___x_643_, 3, v___x_640_);
lean_inc_ref(v_a_630_);
lean_inc_ref(v_a_634_);
lean_inc(v_a_633_);
lean_inc(v_a_632_);
lean_inc(v_a_631_);
v___x_644_ = lean_apply_7(v_a_630_, v___x_643_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, lean_box(0));
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v_a_646_; lean_object* v___x_647_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
v_a_646_ = lean_ctor_get(v___x_644_, 1);
lean_inc(v_a_646_);
lean_dec_ref_known(v___x_644_, 2);
v___x_647_ = l_Lake_Job_await___redArg(v_a_645_, v_a_646_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_670_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_a_649_ = lean_ctor_get(v___x_647_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_670_ == 0)
{
v___x_651_ = v___x_647_;
v_isShared_652_ = v_isSharedCheck_670_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_670_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4);
v___x_655_ = lean_array_get_size(v_a_648_);
v___x_656_ = lean_nat_dec_lt(v___x_653_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_658_; 
lean_dec(v_a_648_);
lean_dec_ref(v_a_630_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_654_);
v___x_658_ = v___x_651_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_a_649_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
else
{
uint8_t v___x_660_; 
v___x_660_ = lean_nat_dec_le(v___x_655_, v___x_655_);
if (v___x_660_ == 0)
{
if (v___x_656_ == 0)
{
lean_object* v___x_662_; 
lean_dec(v_a_648_);
lean_dec_ref(v_a_630_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_654_);
v___x_662_ = v___x_651_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_a_649_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
else
{
size_t v___x_664_; size_t v___x_665_; lean_object* v___x_666_; 
lean_del_object(v___x_651_);
v___x_664_ = ((size_t)0ULL);
v___x_665_ = lean_usize_of_nat(v___x_655_);
v___x_666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_648_, v___x_664_, v___x_665_, v___x_654_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_649_);
lean_dec(v_a_648_);
return v___x_666_;
}
}
else
{
size_t v___x_667_; size_t v___x_668_; lean_object* v___x_669_; 
lean_del_object(v___x_651_);
v___x_667_ = ((size_t)0ULL);
v___x_668_ = lean_usize_of_nat(v___x_655_);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_648_, v___x_667_, v___x_668_, v___x_654_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_649_);
lean_dec(v_a_648_);
return v___x_669_;
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec_ref(v_a_630_);
v_a_671_ = lean_ctor_get(v___x_647_, 0);
v_a_672_ = lean_ctor_get(v___x_647_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_647_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_inc(v_a_671_);
lean_dec(v___x_647_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_671_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
else
{
lean_object* v_a_680_; lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v_a_630_);
v_a_680_ = lean_ctor_get(v___x_644_, 0);
v_a_681_ = lean_ctor_get(v___x_644_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_644_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_inc(v_a_680_);
lean_dec(v___x_644_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_680_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_a_681_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___boxed(lean_object* v_self_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(v_self_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec(v_a_692_);
lean_dec(v_a_691_);
return v_res_697_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_box(0);
v___x_699_ = l_Lean_Json_compress(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(uint8_t v_fmt_700_){
_start:
{
if (v_fmt_700_ == 0)
{
lean_object* v___x_701_; 
v___x_701_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
return v___x_701_;
}
else
{
lean_object* v___x_702_; 
v___x_702_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_703_){
_start:
{
uint8_t v_fmt_boxed_704_; lean_object* v_res_705_; 
v_fmt_boxed_704_ = lean_unbox(v_fmt_703_);
v_res_705_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_boxed_704_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(uint8_t v_fmt_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___boxed(lean_object* v_fmt_709_, lean_object* v_a_710_){
_start:
{
uint8_t v_fmt_boxed_711_; lean_object* v_res_712_; 
v_fmt_boxed_711_ = lean_unbox(v_fmt_709_);
v_res_712_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(v_fmt_boxed_711_, v_a_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0(uint8_t v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v___y_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
uint8_t v___y_68__boxed_718_; lean_object* v_res_719_; 
v___y_68__boxed_718_ = lean_unbox(v___y_716_);
v_res_719_ = l_Lake_LeanLib_leanArtsFacetConfig___lam__0(v___y_68__boxed_718_, v___y_717_);
return v_res_719_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_722_; uint8_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___f_722_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_723_ = 1;
v___x_724_ = l_Lake_instDataKindUnit;
v___x_725_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__1));
v___x_726_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_727_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_725_);
lean_ctor_set(v___x_727_, 2, v___x_724_);
lean_ctor_set(v___x_727_, 3, v___f_722_);
lean_ctor_set_uint8(v___x_727_, sizeof(void*)*4, v___x_723_);
lean_ctor_set_uint8(v___x_727_, sizeof(void*)*4 + 1, v___x_723_);
return v___x_727_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig(void){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = lean_obj_once(&l_Lake_LeanLib_leanArtsFacetConfig___closed__2, &l_Lake_LeanLib_leanArtsFacetConfig___closed__2_once, _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(lean_object* v_a_729_, lean_object* v_x_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lake_ModuleFacet_fetch___redArg(v_x_730_, v_a_729_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object* v_a_739_, lean_object* v_x_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(v_a_739_, v_x_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec(v___y_743_);
lean_dec(v___y_742_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(uint8_t v_shouldExport_749_, lean_object* v___x_750_, lean_object* v_bs_751_, lean_object* v_a_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_lib_760_; lean_object* v_config_761_; lean_object* v_nativeFacets_762_; lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; size_t v_sz_766_; size_t v___x_767_; lean_object* v___x_197263__overap_768_; lean_object* v___x_769_; 
v_lib_760_ = lean_ctor_get(v_a_752_, 0);
v_config_761_ = lean_ctor_get(v_lib_760_, 2);
v_nativeFacets_762_ = lean_ctor_get(v_config_761_, 8);
lean_inc_ref(v_nativeFacets_762_);
v___f_763_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed), 9, 1);
lean_closure_set(v___f_763_, 0, v_a_752_);
v___x_764_ = lean_box(v_shouldExport_749_);
v___x_765_ = lean_apply_1(v_nativeFacets_762_, v___x_764_);
v_sz_766_ = lean_array_size(v___x_765_);
v___x_767_ = ((size_t)0ULL);
v___x_197263__overap_768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_750_, v___f_763_, v_sz_766_, v___x_767_, v___x_765_);
lean_inc_ref(v___y_757_);
lean_inc(v___y_756_);
lean_inc(v___y_755_);
lean_inc(v___y_754_);
v___x_769_ = lean_apply_7(v___x_197263__overap_768_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, lean_box(0));
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_779_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_a_771_ = lean_ctor_get(v___x_769_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_779_ == 0)
{
v___x_773_ = v___x_769_;
v_isShared_774_ = v_isSharedCheck_779_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_779_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_775_ = l_Array_append___redArg(v_bs_751_, v_a_770_);
lean_dec(v_a_770_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_775_);
v___x_777_ = v___x_773_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_a_771_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
else
{
lean_dec_ref(v_bs_751_);
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed(lean_object* v_shouldExport_780_, lean_object* v___x_781_, lean_object* v_bs_782_, lean_object* v_a_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
uint8_t v_shouldExport_boxed_791_; lean_object* v_res_792_; 
v_shouldExport_boxed_791_ = lean_unbox(v_shouldExport_780_);
v_res_792_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(v_shouldExport_boxed_791_, v___x_781_, v_bs_782_, v_a_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec(v___y_786_);
lean_dec(v___y_785_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(lean_object* v___x_793_, lean_object* v_pkg_794_, lean_object* v_x_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lake_Target_fetchIn___redArg(v___x_793_, v_pkg_794_, v_x_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object* v___x_804_, lean_object* v_pkg_805_, lean_object* v_x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(v___x_804_, v_pkg_805_, v_x_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec(v___y_809_);
lean_dec(v___y_808_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object* v_a_815_, lean_object* v_x_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_log_825_; uint8_t v_action_826_; uint8_t v_wantsRebuild_827_; lean_object* v_trace_828_; lean_object* v_buildTime_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_log_825_ = lean_ctor_get(v___y_823_, 0);
v_action_826_ = lean_ctor_get_uint8(v___y_823_, sizeof(void*)*3);
v_wantsRebuild_827_ = lean_ctor_get_uint8(v___y_823_, sizeof(void*)*3 + 1);
v_trace_828_ = lean_ctor_get(v___y_823_, 1);
v_buildTime_829_ = lean_ctor_get(v___y_823_, 2);
v___x_830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_831_ = lean_string_append(v___y_817_, v___x_830_);
v___x_832_ = lean_io_prim_handle_put_str(v_a_815_, v___x_831_);
lean_dec_ref(v___x_831_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_834_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v_a_833_);
lean_ctor_set(v___x_834_, 1, v___y_823_);
return v___x_834_;
}
else
{
lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_848_; 
lean_inc(v_buildTime_829_);
lean_inc_ref(v_trace_828_);
lean_inc_ref(v_log_825_);
v_isSharedCheck_848_ = !lean_is_exclusive(v___y_823_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; lean_object* v_unused_850_; lean_object* v_unused_851_; 
v_unused_849_ = lean_ctor_get(v___y_823_, 2);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v___y_823_, 1);
lean_dec(v_unused_850_);
v_unused_851_ = lean_ctor_get(v___y_823_, 0);
lean_dec(v_unused_851_);
v___x_836_ = v___y_823_;
v_isShared_837_ = v_isSharedCheck_848_;
goto v_resetjp_835_;
}
else
{
lean_dec(v___y_823_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_848_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_a_838_; lean_object* v___x_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v_a_838_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_832_, 1);
v___x_839_ = lean_io_error_to_string(v_a_838_);
v___x_840_ = 3;
v___x_841_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set_uint8(v___x_841_, sizeof(void*)*1, v___x_840_);
v___x_842_ = lean_array_get_size(v_log_825_);
v___x_843_ = lean_array_push(v_log_825_, v___x_841_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_843_);
v___x_845_ = v___x_836_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_trace_828_);
lean_ctor_set(v_reuseFailAlloc_847_, 2, v_buildTime_829_);
lean_ctor_set_uint8(v_reuseFailAlloc_847_, sizeof(void*)*3, v_action_826_);
lean_ctor_set_uint8(v_reuseFailAlloc_847_, sizeof(void*)*3 + 1, v_wantsRebuild_827_);
v___x_845_ = v_reuseFailAlloc_847_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; 
v___x_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_842_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
return v___x_846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object* v_a_852_, lean_object* v_x_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(v_a_852_, v_x_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v_a_852_);
return v_res_862_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_870_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3));
v___x_871_ = lean_unsigned_to_nat(5u);
v___x_872_ = lean_mk_empty_array_with_capacity(v___x_871_);
v___x_873_ = lean_array_push(v___x_872_, v___x_870_);
return v___x_873_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_874_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4));
v___x_875_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6);
v___x_876_ = lean_array_push(v___x_875_, v___x_874_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(uint8_t v_bootstrap_879_, lean_object* v___y_880_, lean_object* v_oFiles_881_, uint8_t v_shouldExport_882_, uint8_t v___x_883_, lean_object* v___x_884_, size_t v___x_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
if (v_bootstrap_879_ == 0)
{
lean_object* v_toContext_893_; lean_object* v_lakeEnv_894_; lean_object* v_lean_895_; lean_object* v_log_896_; uint8_t v_action_897_; uint8_t v_wantsRebuild_898_; lean_object* v_trace_899_; lean_object* v_buildTime_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_930_; 
lean_dec_ref(v___y_886_);
lean_dec_ref(v___x_884_);
v_toContext_893_ = lean_ctor_get(v___y_890_, 1);
v_lakeEnv_894_ = lean_ctor_get(v_toContext_893_, 0);
v_lean_895_ = lean_ctor_get(v_lakeEnv_894_, 1);
v_log_896_ = lean_ctor_get(v___y_891_, 0);
v_action_897_ = lean_ctor_get_uint8(v___y_891_, sizeof(void*)*3);
v_wantsRebuild_898_ = lean_ctor_get_uint8(v___y_891_, sizeof(void*)*3 + 1);
v_trace_899_ = lean_ctor_get(v___y_891_, 1);
v_buildTime_900_ = lean_ctor_get(v___y_891_, 2);
v_isSharedCheck_930_ = !lean_is_exclusive(v___y_891_);
if (v_isSharedCheck_930_ == 0)
{
v___x_902_ = v___y_891_;
v_isShared_903_ = v_isSharedCheck_930_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_buildTime_900_);
lean_inc(v_trace_899_);
lean_inc(v_log_896_);
lean_dec(v___y_891_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_930_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v_ar_904_; lean_object* v___x_905_; 
v_ar_904_ = lean_ctor_get(v_lean_895_, 13);
lean_inc_ref(v_ar_904_);
v___x_905_ = l_Lake_compileStaticLib(v___y_880_, v_oFiles_881_, v_ar_904_, v_bootstrap_879_, v_log_896_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_917_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v_a_907_ = lean_ctor_get(v___x_905_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_917_ == 0)
{
v___x_909_ = v___x_905_;
v_isShared_910_ = v_isSharedCheck_917_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_inc(v_a_906_);
lean_dec(v___x_905_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_917_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v_a_907_);
v___x_912_ = v___x_902_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_907_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_trace_899_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_buildTime_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_916_, sizeof(void*)*3, v_action_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_916_, sizeof(void*)*3 + 1, v_wantsRebuild_898_);
v___x_912_ = v_reuseFailAlloc_916_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
lean_object* v___x_914_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 1, v___x_912_);
v___x_914_ = v___x_909_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_906_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v_a_918_; lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_929_; 
v_a_918_ = lean_ctor_get(v___x_905_, 0);
v_a_919_ = lean_ctor_get(v___x_905_, 1);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_929_ == 0)
{
v___x_921_ = v___x_905_;
v_isShared_922_ = v_isSharedCheck_929_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_inc(v_a_918_);
lean_dec(v___x_905_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_929_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v_a_919_);
v___x_924_ = v___x_902_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_919_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_trace_899_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v_buildTime_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, sizeof(void*)*3, v_action_897_);
lean_ctor_set_uint8(v_reuseFailAlloc_928_, sizeof(void*)*3 + 1, v_wantsRebuild_898_);
v___x_924_ = v_reuseFailAlloc_928_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_926_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v___x_924_);
v___x_926_ = v___x_921_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_918_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v___x_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
}
else
{
uint8_t v___x_931_; 
v___x_931_ = l_System_Platform_isOSX;
if (v___x_931_ == 0)
{
uint8_t v___x_932_; 
lean_dec_ref(v___y_886_);
lean_dec_ref(v___x_884_);
v___x_932_ = l_System_Platform_isWindows;
if (v___x_932_ == 0)
{
lean_object* v_toContext_933_; lean_object* v_lakeEnv_934_; lean_object* v_lean_935_; lean_object* v_log_936_; uint8_t v_action_937_; uint8_t v_wantsRebuild_938_; lean_object* v_trace_939_; lean_object* v_buildTime_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_970_; 
v_toContext_933_ = lean_ctor_get(v___y_890_, 1);
v_lakeEnv_934_ = lean_ctor_get(v_toContext_933_, 0);
v_lean_935_ = lean_ctor_get(v_lakeEnv_934_, 1);
v_log_936_ = lean_ctor_get(v___y_891_, 0);
v_action_937_ = lean_ctor_get_uint8(v___y_891_, sizeof(void*)*3);
v_wantsRebuild_938_ = lean_ctor_get_uint8(v___y_891_, sizeof(void*)*3 + 1);
v_trace_939_ = lean_ctor_get(v___y_891_, 1);
v_buildTime_940_ = lean_ctor_get(v___y_891_, 2);
v_isSharedCheck_970_ = !lean_is_exclusive(v___y_891_);
if (v_isSharedCheck_970_ == 0)
{
v___x_942_ = v___y_891_;
v_isShared_943_ = v_isSharedCheck_970_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_buildTime_940_);
lean_inc(v_trace_939_);
lean_inc(v_log_936_);
lean_dec(v___y_891_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_970_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_ar_944_; lean_object* v___x_945_; 
v_ar_944_ = lean_ctor_get(v_lean_935_, 13);
lean_inc_ref(v_ar_944_);
v___x_945_ = l_Lake_compileStaticLib(v___y_880_, v_oFiles_881_, v_ar_944_, v___x_932_, v_log_936_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_957_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_a_947_ = lean_ctor_get(v___x_945_, 1);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_957_ == 0)
{
v___x_949_ = v___x_945_;
v_isShared_950_ = v_isSharedCheck_957_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_957_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_a_947_);
v___x_952_ = v___x_942_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_947_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_trace_939_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_buildTime_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, sizeof(void*)*3, v_action_937_);
lean_ctor_set_uint8(v_reuseFailAlloc_956_, sizeof(void*)*3 + 1, v_wantsRebuild_938_);
v___x_952_ = v_reuseFailAlloc_956_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_954_; 
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 1, v___x_952_);
v___x_954_ = v___x_949_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_946_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
else
{
lean_object* v_a_958_; lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_969_; 
v_a_958_ = lean_ctor_get(v___x_945_, 0);
v_a_959_ = lean_ctor_get(v___x_945_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_969_ == 0)
{
v___x_961_ = v___x_945_;
v_isShared_962_ = v_isSharedCheck_969_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_inc(v_a_958_);
lean_dec(v___x_945_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_969_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_a_959_);
v___x_964_ = v___x_942_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_959_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v_trace_939_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_buildTime_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, sizeof(void*)*3, v_action_937_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, sizeof(void*)*3 + 1, v_wantsRebuild_938_);
v___x_964_ = v_reuseFailAlloc_968_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_966_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___x_964_);
v___x_966_ = v___x_961_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_958_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_971_; lean_object* v_lakeEnv_972_; lean_object* v_lean_973_; lean_object* v_log_974_; uint8_t v_action_975_; uint8_t v_wantsRebuild_976_; lean_object* v_trace_977_; lean_object* v_buildTime_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1008_; 
v_toContext_971_ = lean_ctor_get(v___y_890_, 1);
v_lakeEnv_972_ = lean_ctor_get(v_toContext_971_, 0);
v_lean_973_ = lean_ctor_get(v_lakeEnv_972_, 1);
v_log_974_ = lean_ctor_get(v___y_891_, 0);
v_action_975_ = lean_ctor_get_uint8(v___y_891_, sizeof(void*)*3);
v_wantsRebuild_976_ = lean_ctor_get_uint8(v___y_891_, sizeof(void*)*3 + 1);
v_trace_977_ = lean_ctor_get(v___y_891_, 1);
v_buildTime_978_ = lean_ctor_get(v___y_891_, 2);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___y_891_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_980_ = v___y_891_;
v_isShared_981_ = v_isSharedCheck_1008_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_buildTime_978_);
lean_inc(v_trace_977_);
lean_inc(v_log_974_);
lean_dec(v___y_891_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1008_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_ar_982_; lean_object* v___x_983_; 
v_ar_982_ = lean_ctor_get(v_lean_973_, 13);
lean_inc_ref(v_ar_982_);
v___x_983_ = l_Lake_compileStaticLib(v___y_880_, v_oFiles_881_, v_ar_982_, v_shouldExport_882_, v_log_974_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_995_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
v_a_985_ = lean_ctor_get(v___x_983_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_995_ == 0)
{
v___x_987_ = v___x_983_;
v_isShared_988_ = v_isSharedCheck_995_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_995_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v_a_985_);
v___x_990_ = v___x_980_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_985_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_trace_977_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_buildTime_978_);
lean_ctor_set_uint8(v_reuseFailAlloc_994_, sizeof(void*)*3, v_action_975_);
lean_ctor_set_uint8(v_reuseFailAlloc_994_, sizeof(void*)*3 + 1, v_wantsRebuild_976_);
v___x_990_ = v_reuseFailAlloc_994_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_992_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v___x_990_);
v___x_992_ = v___x_987_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_984_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1007_; 
v_a_996_ = lean_ctor_get(v___x_983_, 0);
v_a_997_ = lean_ctor_get(v___x_983_, 1);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_999_ = v___x_983_;
v_isShared_1000_ = v_isSharedCheck_1007_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_inc(v_a_996_);
lean_dec(v___x_983_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1007_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v_a_997_);
v___x_1002_ = v___x_980_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_997_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_trace_977_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_buildTime_978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1006_, sizeof(void*)*3, v_action_975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1006_, sizeof(void*)*3 + 1, v_wantsRebuild_976_);
v___x_1002_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 1, v___x_1002_);
v___x_1004_ = v___x_999_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_996_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1009_; uint8_t v_action_1010_; uint8_t v_wantsRebuild_1011_; lean_object* v_trace_1012_; lean_object* v_buildTime_1013_; lean_object* v___x_1014_; 
v_log_1009_ = lean_ctor_get(v___y_891_, 0);
v_action_1010_ = lean_ctor_get_uint8(v___y_891_, sizeof(void*)*3);
v_wantsRebuild_1011_ = lean_ctor_get_uint8(v___y_891_, sizeof(void*)*3 + 1);
v_trace_1012_ = lean_ctor_get(v___y_891_, 1);
v_buildTime_1013_ = lean_ctor_get(v___y_891_, 2);
lean_inc_ref(v___y_880_);
v___x_1014_ = l_Lake_createParentDirs(v___y_880_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v_a_1018_; lean_object* v___y_1065_; uint8_t v___x_1067_; lean_object* v___x_1068_; 
lean_dec_ref_known(v___x_1014_, 1);
v___x_1015_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_880_);
v___x_1016_ = l_System_FilePath_addExtension(v___y_880_, v___x_1015_);
v___x_1067_ = 1;
v___x_1068_ = lean_io_prim_handle_mk(v___x_1016_, v___x_1067_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = l_Lake_EquipT_instMonad___redArg(v___x_884_);
v___x_1071_ = lean_unsigned_to_nat(0u);
v___x_1072_ = lean_array_get_size(v_oFiles_881_);
v___x_1073_ = lean_nat_dec_lt(v___x_1071_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_dec_ref(v___x_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v___y_886_);
lean_dec_ref(v_oFiles_881_);
v_a_1018_ = v___y_891_;
goto v___jp_1017_;
}
else
{
lean_object* v___f_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___f_1074_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1074_, 0, v_a_1069_);
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_nat_dec_le(v___x_1072_, v___x_1072_);
if (v___x_1076_ == 0)
{
if (v___x_1073_ == 0)
{
lean_dec_ref(v___f_1074_);
lean_dec_ref(v___x_1070_);
lean_dec_ref(v___y_886_);
lean_dec_ref(v_oFiles_881_);
v_a_1018_ = v___y_891_;
goto v___jp_1017_;
}
else
{
size_t v___x_1077_; lean_object* v___x_197422__overap_1078_; lean_object* v___x_1079_; 
v___x_1077_ = lean_usize_of_nat(v___x_1072_);
v___x_197422__overap_1078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1070_, v___f_1074_, v_oFiles_881_, v___x_885_, v___x_1077_, v___x_1075_);
lean_inc_ref(v___y_890_);
lean_inc(v___y_889_);
lean_inc(v___y_888_);
lean_inc(v___y_887_);
v___x_1079_ = lean_apply_7(v___x_197422__overap_1078_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, lean_box(0));
v___y_1065_ = v___x_1079_;
goto v___jp_1064_;
}
}
else
{
size_t v___x_1080_; lean_object* v___x_197424__overap_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_usize_of_nat(v___x_1072_);
v___x_197424__overap_1081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1070_, v___f_1074_, v_oFiles_881_, v___x_885_, v___x_1080_, v___x_1075_);
lean_inc_ref(v___y_890_);
lean_inc(v___y_889_);
lean_inc(v___y_888_);
lean_inc(v___y_887_);
v___x_1082_ = lean_apply_7(v___x_197424__overap_1081_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, lean_box(0));
v___y_1065_ = v___x_1082_;
goto v___jp_1064_;
}
}
}
else
{
lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1096_; 
lean_inc(v_buildTime_1013_);
lean_inc_ref(v_trace_1012_);
lean_inc_ref(v_log_1009_);
lean_dec_ref(v___x_1016_);
lean_dec_ref(v___y_886_);
lean_dec_ref(v___x_884_);
lean_dec_ref(v_oFiles_881_);
lean_dec_ref(v___y_880_);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___y_891_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; lean_object* v_unused_1098_; lean_object* v_unused_1099_; 
v_unused_1097_ = lean_ctor_get(v___y_891_, 2);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v___y_891_, 1);
lean_dec(v_unused_1098_);
v_unused_1099_ = lean_ctor_get(v___y_891_, 0);
lean_dec(v_unused_1099_);
v___x_1084_ = v___y_891_;
v_isShared_1085_ = v_isSharedCheck_1096_;
goto v_resetjp_1083_;
}
else
{
lean_dec(v___y_891_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1096_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_a_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v_a_1086_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1087_ = lean_io_error_to_string(v_a_1086_);
v___x_1088_ = 3;
v___x_1089_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*1, v___x_1088_);
v___x_1090_ = lean_array_get_size(v_log_1009_);
v___x_1091_ = lean_array_push(v_log_1009_, v___x_1089_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1091_);
v___x_1093_ = v___x_1084_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_trace_1012_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_buildTime_1013_);
lean_ctor_set_uint8(v_reuseFailAlloc_1095_, sizeof(void*)*3, v_action_1010_);
lean_ctor_set_uint8(v_reuseFailAlloc_1095_, sizeof(void*)*3 + 1, v_wantsRebuild_1011_);
v___x_1093_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1090_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
return v___x_1094_;
}
}
}
v___jp_1017_:
{
lean_object* v___x_1019_; lean_object* v_log_1020_; uint8_t v_action_1021_; uint8_t v_wantsRebuild_1022_; lean_object* v_trace_1023_; lean_object* v_buildTime_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1063_; 
v___x_1019_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1020_ = lean_ctor_get(v_a_1018_, 0);
v_action_1021_ = lean_ctor_get_uint8(v_a_1018_, sizeof(void*)*3);
v_wantsRebuild_1022_ = lean_ctor_get_uint8(v_a_1018_, sizeof(void*)*3 + 1);
v_trace_1023_ = lean_ctor_get(v_a_1018_, 1);
v_buildTime_1024_ = lean_ctor_get(v_a_1018_, 2);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_a_1018_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1026_ = v_a_1018_;
v_isShared_1027_ = v_isSharedCheck_1063_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_buildTime_1024_);
lean_inc(v_trace_1023_);
lean_inc(v_log_1020_);
lean_dec(v_a_1018_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1063_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1028_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1029_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1030_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1031_ = lean_array_push(v___x_1030_, v___y_880_);
v___x_1032_ = lean_array_push(v___x_1031_, v___x_1029_);
v___x_1033_ = lean_array_push(v___x_1032_, v___x_1016_);
v___x_1034_ = lean_box(0);
v___x_1035_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1036_ = 0;
v___x_1037_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1037_, 0, v___x_1019_);
lean_ctor_set(v___x_1037_, 1, v___x_1028_);
lean_ctor_set(v___x_1037_, 2, v___x_1033_);
lean_ctor_set(v___x_1037_, 3, v___x_1034_);
lean_ctor_set(v___x_1037_, 4, v___x_1035_);
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*5, v___x_883_);
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*5 + 1, v___x_1036_);
v___x_1038_ = l_Lake_proc(v___x_1037_, v___x_1036_, v___x_1034_, v_log_1020_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1050_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v_a_1040_ = lean_ctor_get(v___x_1038_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1042_ = v___x_1038_;
v_isShared_1043_ = v_isSharedCheck_1050_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_inc(v_a_1039_);
lean_dec(v___x_1038_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1050_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v_a_1040_);
v___x_1045_ = v___x_1026_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1040_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_trace_1023_);
lean_ctor_set(v_reuseFailAlloc_1049_, 2, v_buildTime_1024_);
lean_ctor_set_uint8(v_reuseFailAlloc_1049_, sizeof(void*)*3, v_action_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1049_, sizeof(void*)*3 + 1, v_wantsRebuild_1022_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 1, v___x_1045_);
v___x_1047_ = v___x_1042_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1039_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1062_; 
v_a_1051_ = lean_ctor_get(v___x_1038_, 0);
v_a_1052_ = lean_ctor_get(v___x_1038_, 1);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1054_ = v___x_1038_;
v_isShared_1055_ = v_isSharedCheck_1062_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_inc(v_a_1051_);
lean_dec(v___x_1038_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1062_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v_a_1052_);
v___x_1057_ = v___x_1026_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1052_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_trace_1023_);
lean_ctor_set(v_reuseFailAlloc_1061_, 2, v_buildTime_1024_);
lean_ctor_set_uint8(v_reuseFailAlloc_1061_, sizeof(void*)*3, v_action_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1061_, sizeof(void*)*3 + 1, v_wantsRebuild_1022_);
v___x_1057_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1059_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v___x_1057_);
v___x_1059_ = v___x_1054_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1051_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
}
v___jp_1064_:
{
if (lean_obj_tag(v___y_1065_) == 0)
{
lean_object* v_a_1066_; 
v_a_1066_ = lean_ctor_get(v___y_1065_, 1);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___y_1065_, 2);
v_a_1018_ = v_a_1066_;
goto v___jp_1017_;
}
else
{
lean_dec_ref(v___x_1016_);
lean_dec_ref(v___y_880_);
return v___y_1065_;
}
}
}
else
{
lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1113_; 
lean_inc(v_buildTime_1013_);
lean_inc_ref(v_trace_1012_);
lean_inc_ref(v_log_1009_);
lean_dec_ref(v___y_886_);
lean_dec_ref(v___x_884_);
lean_dec_ref(v_oFiles_881_);
lean_dec_ref(v___y_880_);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___y_891_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; lean_object* v_unused_1115_; lean_object* v_unused_1116_; 
v_unused_1114_ = lean_ctor_get(v___y_891_, 2);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v___y_891_, 1);
lean_dec(v_unused_1115_);
v_unused_1116_ = lean_ctor_get(v___y_891_, 0);
lean_dec(v_unused_1116_);
v___x_1101_ = v___y_891_;
v_isShared_1102_ = v_isSharedCheck_1113_;
goto v_resetjp_1100_;
}
else
{
lean_dec(v___y_891_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1113_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_a_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v_a_1103_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1104_ = lean_io_error_to_string(v_a_1103_);
v___x_1105_ = 3;
v___x_1106_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1106_, 0, v___x_1104_);
lean_ctor_set_uint8(v___x_1106_, sizeof(void*)*1, v___x_1105_);
v___x_1107_ = lean_array_get_size(v_log_1009_);
v___x_1108_ = lean_array_push(v_log_1009_, v___x_1106_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1108_);
v___x_1110_ = v___x_1101_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_trace_1012_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_buildTime_1013_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*3, v_action_1010_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*3 + 1, v_wantsRebuild_1011_);
v___x_1110_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1107_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
return v___x_1111_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object* v_bootstrap_1117_, lean_object* v___y_1118_, lean_object* v_oFiles_1119_, lean_object* v_shouldExport_1120_, lean_object* v___x_1121_, lean_object* v___x_1122_, lean_object* v___x_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v_bootstrap_boxed_1131_; uint8_t v_shouldExport_boxed_1132_; uint8_t v___x_197796__boxed_1133_; size_t v___x_197798__boxed_1134_; lean_object* v_res_1135_; 
v_bootstrap_boxed_1131_ = lean_unbox(v_bootstrap_1117_);
v_shouldExport_boxed_1132_ = lean_unbox(v_shouldExport_1120_);
v___x_197796__boxed_1133_ = lean_unbox(v___x_1121_);
v___x_197798__boxed_1134_ = lean_unbox_usize(v___x_1123_);
lean_dec(v___x_1123_);
v_res_1135_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(v_bootstrap_boxed_1131_, v___y_1118_, v_oFiles_1119_, v_shouldExport_boxed_1132_, v___x_197796__boxed_1133_, v___x_1122_, v___x_197798__boxed_1134_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec(v___y_1125_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(uint8_t v_bootstrap_1137_, lean_object* v___y_1138_, uint8_t v_shouldExport_1139_, uint8_t v___x_1140_, lean_object* v___x_1141_, size_t v___x_1142_, lean_object* v_oFiles_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___y_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1151_ = lean_box(v_bootstrap_1137_);
v___x_1152_ = lean_box(v_shouldExport_1139_);
v___x_1153_ = lean_box(v___x_1140_);
v___x_1154_ = lean_box_usize(v___x_1142_);
lean_inc_ref(v___y_1138_);
v___y_1155_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed), 14, 7);
lean_closure_set(v___y_1155_, 0, v___x_1151_);
lean_closure_set(v___y_1155_, 1, v___y_1138_);
lean_closure_set(v___y_1155_, 2, v_oFiles_1143_);
lean_closure_set(v___y_1155_, 3, v___x_1152_);
lean_closure_set(v___y_1155_, 4, v___x_1153_);
lean_closure_set(v___y_1155_, 5, v___x_1141_);
lean_closure_set(v___y_1155_, 6, v___x_1154_);
v___x_1156_ = 0;
v___x_1157_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1158_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1138_, v___y_1155_, v___x_1156_, v___x_1157_, v___x_1140_, v___x_1156_, v___x_1156_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1168_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_a_1160_ = lean_ctor_get(v___x_1158_, 1);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1162_ = v___x_1158_;
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v_path_1164_; lean_object* v___x_1166_; 
v_path_1164_ = lean_ctor_get(v_a_1159_, 1);
lean_inc_ref(v_path_1164_);
lean_dec(v_a_1159_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v_path_1164_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_path_1164_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_a_1160_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
v_a_1169_ = lean_ctor_get(v___x_1158_, 0);
v_a_1170_ = lean_ctor_get(v___x_1158_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1158_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_inc(v_a_1169_);
lean_dec(v___x_1158_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1169_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object* v_bootstrap_1178_, lean_object* v___y_1179_, lean_object* v_shouldExport_1180_, lean_object* v___x_1181_, lean_object* v___x_1182_, lean_object* v___x_1183_, lean_object* v_oFiles_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v_bootstrap_boxed_1192_; uint8_t v_shouldExport_boxed_1193_; uint8_t v___x_198221__boxed_1194_; size_t v___x_198223__boxed_1195_; lean_object* v_res_1196_; 
v_bootstrap_boxed_1192_ = lean_unbox(v_bootstrap_1178_);
v_shouldExport_boxed_1193_ = lean_unbox(v_shouldExport_1180_);
v___x_198221__boxed_1194_ = lean_unbox(v___x_1181_);
v___x_198223__boxed_1195_ = lean_unbox_usize(v___x_1183_);
lean_dec(v___x_1183_);
v_res_1196_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(v_bootstrap_boxed_1192_, v___y_1179_, v_shouldExport_boxed_1193_, v___x_198221__boxed_1194_, v___x_1182_, v___x_198223__boxed_1195_, v_oFiles_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec(v___y_1186_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object* v___x_1201_, lean_object* v___x_1202_, lean_object* v_config_1203_, lean_object* v_config_1204_, lean_object* v___x_1205_, lean_object* v___f_1206_, uint8_t v_shouldExport_1207_, uint8_t v___x_1208_, lean_object* v___x_1209_, lean_object* v___x_1210_, lean_object* v_dir_1211_, lean_object* v_self_1212_, lean_object* v___f_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
size_t v___y_1222_; lean_object* v___y_1223_; uint8_t v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v_a_1242_; lean_object* v_a_1243_; lean_object* v___y_1287_; lean_object* v___x_1299_; 
lean_inc_ref(v___y_1214_);
lean_inc_ref(v___y_1218_);
lean_inc(v___y_1217_);
lean_inc(v___y_1216_);
lean_inc(v___x_1202_);
v___x_1299_ = lean_apply_7(v___y_1214_, v___x_1201_, v___x_1202_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, lean_box(0));
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v_a_1301_; lean_object* v___x_1302_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
v_a_1301_ = lean_ctor_get(v___x_1299_, 1);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1299_, 2);
v___x_1302_ = l_Lake_Job_await___redArg(v_a_1300_, v_a_1301_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v_a_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
v_a_1304_ = lean_ctor_get(v___x_1302_, 1);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1302_, 2);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_1307_ = lean_array_get_size(v_a_1303_);
v___x_1308_ = lean_nat_dec_lt(v___x_1305_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_dec(v_a_1303_);
lean_dec_ref(v___f_1213_);
v_a_1242_ = v___x_1306_;
v_a_1243_ = v_a_1304_;
goto v___jp_1241_;
}
else
{
uint8_t v___x_1309_; 
v___x_1309_ = lean_nat_dec_le(v___x_1307_, v___x_1307_);
if (v___x_1309_ == 0)
{
if (v___x_1308_ == 0)
{
lean_dec(v_a_1303_);
lean_dec_ref(v___f_1213_);
v_a_1242_ = v___x_1306_;
v_a_1243_ = v_a_1304_;
goto v___jp_1241_;
}
else
{
size_t v___x_1310_; size_t v___x_1311_; lean_object* v___x_197561__overap_1312_; lean_object* v___x_1313_; 
v___x_1310_ = ((size_t)0ULL);
v___x_1311_ = lean_usize_of_nat(v___x_1307_);
lean_inc_ref(v___x_1205_);
v___x_197561__overap_1312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1205_, v___f_1213_, v_a_1303_, v___x_1310_, v___x_1311_, v___x_1306_);
lean_inc_ref(v___y_1218_);
lean_inc(v___y_1217_);
lean_inc(v___y_1216_);
lean_inc(v___x_1202_);
lean_inc_ref(v___y_1214_);
v___x_1313_ = lean_apply_7(v___x_197561__overap_1312_, v___y_1214_, v___x_1202_, v___y_1216_, v___y_1217_, v___y_1218_, v_a_1304_, lean_box(0));
v___y_1287_ = v___x_1313_;
goto v___jp_1286_;
}
}
else
{
size_t v___x_1314_; size_t v___x_1315_; lean_object* v___x_197564__overap_1316_; lean_object* v___x_1317_; 
v___x_1314_ = ((size_t)0ULL);
v___x_1315_ = lean_usize_of_nat(v___x_1307_);
lean_inc_ref(v___x_1205_);
v___x_197564__overap_1316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1205_, v___f_1213_, v_a_1303_, v___x_1314_, v___x_1315_, v___x_1306_);
lean_inc_ref(v___y_1218_);
lean_inc(v___y_1217_);
lean_inc(v___y_1216_);
lean_inc(v___x_1202_);
lean_inc_ref(v___y_1214_);
v___x_1317_ = lean_apply_7(v___x_197564__overap_1316_, v___y_1214_, v___x_1202_, v___y_1216_, v___y_1217_, v___y_1218_, v_a_1304_, lean_box(0));
v___y_1287_ = v___x_1317_;
goto v___jp_1286_;
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v___y_1214_);
lean_dec_ref(v___f_1213_);
lean_dec_ref(v_self_1212_);
lean_dec_ref(v_dir_1211_);
lean_dec(v___x_1210_);
lean_dec_ref(v___x_1209_);
lean_dec_ref(v___f_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v_config_1203_);
lean_dec(v___x_1202_);
v_a_1318_ = lean_ctor_get(v___x_1302_, 0);
v_a_1319_ = lean_ctor_get(v___x_1302_, 1);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1302_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_inc(v_a_1318_);
lean_dec(v___x_1302_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1318_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v___y_1214_);
lean_dec_ref(v___f_1213_);
lean_dec_ref(v_self_1212_);
lean_dec_ref(v_dir_1211_);
lean_dec(v___x_1210_);
lean_dec_ref(v___x_1209_);
lean_dec_ref(v___f_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v_config_1203_);
lean_dec(v___x_1202_);
v_a_1327_ = lean_ctor_get(v___x_1299_, 0);
v_a_1328_ = lean_ctor_get(v___x_1299_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1299_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_inc(v_a_1327_);
lean_dec(v___x_1299_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1327_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
v___jp_1221_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___f_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1228_ = lean_box(v___y_1224_);
v___x_1229_ = lean_box(v_shouldExport_1207_);
v___x_1230_ = lean_box(v___x_1208_);
v___x_1231_ = lean_box_usize(v___y_1222_);
v___f_1232_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed), 14, 6);
lean_closure_set(v___f_1232_, 0, v___x_1228_);
lean_closure_set(v___f_1232_, 1, v___y_1227_);
lean_closure_set(v___f_1232_, 2, v___x_1229_);
lean_closure_set(v___f_1232_, 3, v___x_1230_);
lean_closure_set(v___f_1232_, 4, v___x_1209_);
lean_closure_set(v___f_1232_, 5, v___x_1231_);
v___x_1233_ = l_Array_append___redArg(v___y_1226_, v___y_1223_);
lean_dec_ref(v___y_1223_);
v___x_1234_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_1235_ = l_Lake_Job_collectArray___redArg(v___x_1233_, v___x_1234_);
lean_dec_ref(v___x_1233_);
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1237_ = 0;
v___x_1238_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_1239_ = l_Lake_Job_mapM___redArg(v___x_1210_, v___x_1235_, v___f_1232_, v___x_1236_, v___x_1237_, v___y_1214_, v___x_1202_, v___y_1216_, v___y_1217_, v___y_1218_, v___x_1238_);
lean_dec(v___x_1202_);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v___y_1225_);
return v___x_1240_;
}
v___jp_1241_:
{
lean_object* v_toLeanConfig_1244_; lean_object* v_toLeanConfig_1245_; uint8_t v_bootstrap_1246_; lean_object* v_buildDir_1247_; lean_object* v_nativeLibDir_1248_; lean_object* v_moreLinkObjs_1249_; lean_object* v_moreLinkObjs_1250_; lean_object* v___x_1251_; size_t v_sz_1252_; size_t v___x_1253_; lean_object* v___x_197501__overap_1254_; lean_object* v___x_1255_; 
v_toLeanConfig_1244_ = lean_ctor_get(v_config_1203_, 1);
lean_inc_ref(v_toLeanConfig_1244_);
v_toLeanConfig_1245_ = lean_ctor_get(v_config_1204_, 0);
v_bootstrap_1246_ = lean_ctor_get_uint8(v_config_1203_, sizeof(void*)*27);
v_buildDir_1247_ = lean_ctor_get(v_config_1203_, 5);
lean_inc_ref(v_buildDir_1247_);
v_nativeLibDir_1248_ = lean_ctor_get(v_config_1203_, 7);
lean_inc_ref(v_nativeLibDir_1248_);
lean_dec_ref(v_config_1203_);
v_moreLinkObjs_1249_ = lean_ctor_get(v_toLeanConfig_1244_, 6);
lean_inc_ref(v_moreLinkObjs_1249_);
lean_dec_ref(v_toLeanConfig_1244_);
v_moreLinkObjs_1250_ = lean_ctor_get(v_toLeanConfig_1245_, 6);
v___x_1251_ = l_Array_append___redArg(v_moreLinkObjs_1249_, v_moreLinkObjs_1250_);
v_sz_1252_ = lean_array_size(v___x_1251_);
v___x_1253_ = ((size_t)0ULL);
v___x_197501__overap_1254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1205_, v___f_1206_, v_sz_1252_, v___x_1253_, v___x_1251_);
lean_inc_ref(v___y_1218_);
lean_inc(v___y_1217_);
lean_inc(v___y_1216_);
lean_inc(v___x_1202_);
lean_inc_ref(v___y_1214_);
v___x_1255_ = lean_apply_7(v___x_197501__overap_1254_, v___y_1214_, v___x_1202_, v___y_1216_, v___y_1217_, v___y_1218_, v_a_1243_, lean_box(0));
if (lean_obj_tag(v___x_1255_) == 0)
{
if (v_shouldExport_1207_ == 0)
{
lean_object* v_a_1256_; lean_object* v_a_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1256_);
v_a_1257_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_a_1257_);
lean_dec_ref_known(v___x_1255_, 2);
v___x_1258_ = l_System_FilePath_normalize(v_buildDir_1247_);
v___x_1259_ = l_Lake_joinRelative(v_dir_1211_, v___x_1258_);
v___x_1260_ = l_System_FilePath_normalize(v_nativeLibDir_1248_);
v___x_1261_ = l_Lake_joinRelative(v___x_1259_, v___x_1260_);
v___x_1262_ = l_Lake_LeanLib_libName(v_self_1212_);
v___x_1263_ = l_Lake_nameToStaticLib(v___x_1262_, v_shouldExport_1207_);
v___x_1264_ = l_Lake_joinRelative(v___x_1261_, v___x_1263_);
v___y_1222_ = v___x_1253_;
v___y_1223_ = v_a_1256_;
v___y_1224_ = v_bootstrap_1246_;
v___y_1225_ = v_a_1257_;
v___y_1226_ = v_a_1242_;
v___y_1227_ = v___x_1264_;
goto v___jp_1221_;
}
else
{
lean_object* v_a_1265_; lean_object* v_a_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_a_1265_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_a_1265_);
v_a_1266_ = lean_ctor_get(v___x_1255_, 1);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1255_, 2);
v___x_1267_ = l_System_FilePath_normalize(v_buildDir_1247_);
v___x_1268_ = l_Lake_joinRelative(v_dir_1211_, v___x_1267_);
v___x_1269_ = l_System_FilePath_normalize(v_nativeLibDir_1248_);
v___x_1270_ = l_Lake_joinRelative(v___x_1268_, v___x_1269_);
v___x_1271_ = l_Lake_LeanLib_libName(v_self_1212_);
v___x_1272_ = 0;
v___x_1273_ = l_Lake_nameToStaticLib(v___x_1271_, v___x_1272_);
v___x_1274_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_1275_ = l_System_FilePath_addExtension(v___x_1273_, v___x_1274_);
v___x_1276_ = l_Lake_joinRelative(v___x_1270_, v___x_1275_);
v___y_1222_ = v___x_1253_;
v___y_1223_ = v_a_1265_;
v___y_1224_ = v_bootstrap_1246_;
v___y_1225_ = v_a_1266_;
v___y_1226_ = v_a_1242_;
v___y_1227_ = v___x_1276_;
goto v___jp_1221_;
}
}
else
{
lean_object* v_a_1277_; lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref(v_nativeLibDir_1248_);
lean_dec_ref(v_buildDir_1247_);
lean_dec_ref(v_a_1242_);
lean_dec_ref(v___y_1214_);
lean_dec_ref(v_self_1212_);
lean_dec_ref(v_dir_1211_);
lean_dec(v___x_1210_);
lean_dec_ref(v___x_1209_);
lean_dec(v___x_1202_);
v_a_1277_ = lean_ctor_get(v___x_1255_, 0);
v_a_1278_ = lean_ctor_get(v___x_1255_, 1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1255_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_inc(v_a_1277_);
lean_dec(v___x_1255_);
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
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1277_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
v___jp_1286_:
{
if (lean_obj_tag(v___y_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v_a_1289_; 
v_a_1288_ = lean_ctor_get(v___y_1287_, 0);
lean_inc(v_a_1288_);
v_a_1289_ = lean_ctor_get(v___y_1287_, 1);
lean_inc(v_a_1289_);
lean_dec_ref_known(v___y_1287_, 2);
v_a_1242_ = v_a_1288_;
v_a_1243_ = v_a_1289_;
goto v___jp_1241_;
}
else
{
lean_object* v_a_1290_; lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v___y_1214_);
lean_dec_ref(v_self_1212_);
lean_dec_ref(v_dir_1211_);
lean_dec(v___x_1210_);
lean_dec_ref(v___x_1209_);
lean_dec_ref(v___f_1206_);
lean_dec_ref(v___x_1205_);
lean_dec_ref(v_config_1203_);
lean_dec(v___x_1202_);
v_a_1290_ = lean_ctor_get(v___y_1287_, 0);
v_a_1291_ = lean_ctor_get(v___y_1287_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___y_1287_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___y_1287_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_inc(v_a_1290_);
lean_dec(v___y_1287_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1290_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed(lean_object** _args){
lean_object* v___x_1336_ = _args[0];
lean_object* v___x_1337_ = _args[1];
lean_object* v_config_1338_ = _args[2];
lean_object* v_config_1339_ = _args[3];
lean_object* v___x_1340_ = _args[4];
lean_object* v___f_1341_ = _args[5];
lean_object* v_shouldExport_1342_ = _args[6];
lean_object* v___x_1343_ = _args[7];
lean_object* v___x_1344_ = _args[8];
lean_object* v___x_1345_ = _args[9];
lean_object* v_dir_1346_ = _args[10];
lean_object* v_self_1347_ = _args[11];
lean_object* v___f_1348_ = _args[12];
lean_object* v___y_1349_ = _args[13];
lean_object* v___y_1350_ = _args[14];
lean_object* v___y_1351_ = _args[15];
lean_object* v___y_1352_ = _args[16];
lean_object* v___y_1353_ = _args[17];
lean_object* v___y_1354_ = _args[18];
lean_object* v___y_1355_ = _args[19];
_start:
{
uint8_t v_shouldExport_boxed_1356_; uint8_t v___x_198325__boxed_1357_; lean_object* v_res_1358_; 
v_shouldExport_boxed_1356_ = lean_unbox(v_shouldExport_1342_);
v___x_198325__boxed_1357_ = lean_unbox(v___x_1343_);
v_res_1358_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(v___x_1336_, v___x_1337_, v_config_1338_, v_config_1339_, v___x_1340_, v___f_1341_, v_shouldExport_boxed_1356_, v___x_198325__boxed_1357_, v___x_1344_, v___x_1345_, v_dir_1346_, v_self_1347_, v___f_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec(v_config_1339_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object* v_self_1362_, uint8_t v_shouldExport_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v___x_1371_; lean_object* v_toApplicative_1372_; lean_object* v_toBind_1373_; lean_object* v_toFunctor_1374_; lean_object* v_toPure_1375_; lean_object* v___f_1376_; lean_object* v___f_1377_; lean_object* v___f_1378_; lean_object* v___f_1379_; lean_object* v___x_1380_; lean_object* v___f_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v_toBuildConfig_1389_; lean_object* v_registeredJobs_1390_; uint8_t v_verbosity_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___f_1394_; uint8_t v___x_1395_; uint8_t v___x_1396_; uint8_t v___x_1397_; lean_object* v___y_1399_; 
v___x_1371_ = l_instMonadBaseIO;
v_toApplicative_1372_ = lean_ctor_get(v___x_1371_, 0);
v_toBind_1373_ = lean_ctor_get(v___x_1371_, 1);
v_toFunctor_1374_ = lean_ctor_get(v_toApplicative_1372_, 0);
v_toPure_1375_ = lean_ctor_get(v_toApplicative_1372_, 1);
lean_inc_n(v_toBind_1373_, 3);
lean_inc_n(v_toPure_1375_, 5);
v___f_1376_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1376_, 0, v_toPure_1375_);
lean_closure_set(v___f_1376_, 1, v_toBind_1373_);
v___f_1377_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1377_, 0, v_toPure_1375_);
lean_closure_set(v___f_1377_, 1, v_toBind_1373_);
lean_inc_ref(v___f_1376_);
v___f_1378_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1378_, 0, v_toPure_1375_);
lean_closure_set(v___f_1378_, 1, v___f_1376_);
lean_inc_ref_n(v_toFunctor_1374_, 2);
v___f_1379_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1379_, 0, v_toFunctor_1374_);
lean_closure_set(v___f_1379_, 1, v_toPure_1375_);
lean_closure_set(v___f_1379_, 2, v_toBind_1373_);
v___x_1380_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1374_);
v___f_1381_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1381_, 0, v_toPure_1375_);
v___x_1382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___f_1381_);
lean_ctor_set(v___x_1382_, 2, v___f_1379_);
lean_ctor_set(v___x_1382_, 3, v___f_1378_);
lean_ctor_set(v___x_1382_, 4, v___f_1377_);
v___x_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v___f_1376_);
v___x_1384_ = l_ReaderT_instMonad___redArg(v___x_1383_);
v___x_1385_ = l_StateRefT_x27_instMonad___redArg(v___x_1384_);
v___x_1386_ = l_ReaderT_instMonad___redArg(v___x_1385_);
v___x_1387_ = l_ReaderT_instMonad___redArg(v___x_1386_);
lean_inc_ref(v___x_1387_);
v___x_1388_ = l_Lake_EquipT_instMonad___redArg(v___x_1387_);
v_toBuildConfig_1389_ = lean_ctor_get(v_a_1368_, 0);
v_registeredJobs_1390_ = lean_ctor_get(v_a_1368_, 3);
v_verbosity_1391_ = lean_ctor_get_uint8(v_toBuildConfig_1389_, sizeof(void*)*3 + 3);
v___x_1392_ = l_Lake_instDataKindFilePath;
v___x_1393_ = lean_box(v_shouldExport_1363_);
lean_inc_ref(v___x_1388_);
v___f_1394_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1394_, 0, v___x_1393_);
lean_closure_set(v___f_1394_, 1, v___x_1388_);
v___x_1395_ = 2;
v___x_1396_ = l_Lake_instDecidableEqVerbosity(v_verbosity_1391_, v___x_1395_);
v___x_1397_ = 1;
if (v___x_1396_ == 0)
{
lean_object* v___x_1445_; 
v___x_1445_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_1399_ = v___x_1445_;
goto v___jp_1398_;
}
else
{
if (v_shouldExport_1363_ == 0)
{
lean_object* v___x_1446_; 
v___x_1446_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___y_1399_ = v___x_1446_;
goto v___jp_1398_;
}
else
{
lean_object* v___x_1447_; 
v___x_1447_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_1399_ = v___x_1447_;
goto v___jp_1398_;
}
}
v___jp_1398_:
{
lean_object* v_pkg_1400_; lean_object* v_name_1401_; lean_object* v_config_1402_; lean_object* v_keyName_1403_; lean_object* v_dir_1404_; lean_object* v_config_1405_; lean_object* v___f_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___f_1414_; lean_object* v___x_1415_; 
v_pkg_1400_ = lean_ctor_get(v_self_1362_, 0);
v_name_1401_ = lean_ctor_get(v_self_1362_, 1);
lean_inc_n(v_name_1401_, 2);
v_config_1402_ = lean_ctor_get(v_self_1362_, 2);
lean_inc(v_config_1402_);
v_keyName_1403_ = lean_ctor_get(v_pkg_1400_, 2);
v_dir_1404_ = lean_ctor_get(v_pkg_1400_, 4);
lean_inc_ref(v_dir_1404_);
v_config_1405_ = lean_ctor_get(v_pkg_1400_, 6);
lean_inc_ref(v_config_1405_);
lean_inc_ref_n(v_pkg_1400_, 2);
v___f_1406_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(v___f_1406_, 0, v___x_1392_);
lean_closure_set(v___f_1406_, 1, v_pkg_1400_);
v___x_1407_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_1403_);
v___x_1408_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_keyName_1403_);
lean_ctor_set(v___x_1408_, 1, v_name_1401_);
v___x_1409_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_1362_);
v___x_1410_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
lean_ctor_set(v___x_1410_, 2, v_self_1362_);
lean_ctor_set(v___x_1410_, 3, v___x_1407_);
v___x_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1411_, 0, v_pkg_1400_);
v___x_1412_ = lean_box(v_shouldExport_1363_);
v___x_1413_ = lean_box(v___x_1397_);
v___f_1414_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed), 20, 13);
lean_closure_set(v___f_1414_, 0, v___x_1410_);
lean_closure_set(v___f_1414_, 1, v___x_1411_);
lean_closure_set(v___f_1414_, 2, v_config_1405_);
lean_closure_set(v___f_1414_, 3, v_config_1402_);
lean_closure_set(v___f_1414_, 4, v___x_1388_);
lean_closure_set(v___f_1414_, 5, v___f_1406_);
lean_closure_set(v___f_1414_, 6, v___x_1412_);
lean_closure_set(v___f_1414_, 7, v___x_1413_);
lean_closure_set(v___f_1414_, 8, v___x_1387_);
lean_closure_set(v___f_1414_, 9, v___x_1392_);
lean_closure_set(v___f_1414_, 10, v_dir_1404_);
lean_closure_set(v___f_1414_, 11, v_self_1362_);
lean_closure_set(v___f_1414_, 12, v___f_1394_);
v___x_1415_ = l_Lake_ensureJob___redArg(v___x_1392_, v___f_1414_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1444_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_a_1417_ = lean_ctor_get(v___x_1415_, 1);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1419_ = v___x_1415_;
v_isShared_1420_ = v_isSharedCheck_1444_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1444_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v_task_1421_; lean_object* v_kind_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1442_; 
v_task_1421_ = lean_ctor_get(v_a_1416_, 0);
v_kind_1422_ = lean_ctor_get(v_a_1416_, 1);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_a_1416_);
if (v_isSharedCheck_1442_ == 0)
{
lean_object* v_unused_1443_; 
v_unused_1443_ = lean_ctor_get(v_a_1416_, 2);
lean_dec(v_unused_1443_);
v___x_1424_ = v_a_1416_;
v_isShared_1425_ = v_isSharedCheck_1442_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_kind_1422_);
lean_inc(v_task_1421_);
lean_dec(v_a_1416_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1442_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; lean_object* v_job_1433_; 
v___x_1426_ = lean_st_ref_take(v_registeredJobs_1390_);
v___x_1427_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1401_, v___x_1397_);
v___x_1428_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0));
v___x_1429_ = lean_string_append(v___x_1427_, v___x_1428_);
v___x_1430_ = lean_string_append(v___x_1429_, v___y_1399_);
v___x_1431_ = 0;
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 2, v___x_1430_);
v_job_1433_ = v___x_1424_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_task_1421_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_kind_1422_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v___x_1430_);
v_job_1433_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
lean_ctor_set_uint8(v_job_1433_, sizeof(void*)*3, v___x_1431_);
lean_inc_ref(v_job_1433_);
v___x_1434_ = l_Lake_Job_toOpaque___redArg(v_job_1433_);
v___x_1435_ = lean_array_push(v___x_1426_, v___x_1434_);
v___x_1436_ = lean_st_ref_set(v_registeredJobs_1390_, v___x_1435_);
v___x_1437_ = l_Lake_Job_renew___redArg(v_job_1433_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1437_);
v___x_1439_ = v___x_1419_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_a_1417_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
else
{
lean_dec(v_name_1401_);
return v___x_1415_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object* v_self_1448_, lean_object* v_shouldExport_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
uint8_t v_shouldExport_boxed_1457_; lean_object* v_res_1458_; 
v_shouldExport_boxed_1457_ = lean_unbox(v_shouldExport_1449_);
v_res_1458_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1448_, v_shouldExport_boxed_1457_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec(v_a_1452_);
lean_dec(v_a_1451_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t v_fmt_1459_, lean_object* v_a_1460_){
_start:
{
if (v_fmt_1459_ == 0)
{
return v_a_1460_;
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = l_Lake_mkRelPathString(v_a_1460_);
v___x_1462_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
v___x_1463_ = l_Lean_Json_compress(v___x_1462_);
return v___x_1463_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object* v_fmt_1464_, lean_object* v_a_1465_){
_start:
{
uint8_t v_fmt_boxed_1466_; lean_object* v_res_1467_; 
v_fmt_boxed_1466_ = lean_unbox(v_fmt_1464_);
v_res_1467_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_boxed_1466_, v_a_1465_);
return v_res_1467_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2(void){
_start:
{
uint8_t v___x_1470_; lean_object* v_name_1471_; lean_object* v___x_1472_; 
v___x_1470_ = 1;
v_name_1471_ = l_Lake_instDataKindFilePath;
v___x_1472_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1471_, v___x_1470_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* v_defaultPkg_1476_, lean_object* v_self_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_){
_start:
{
uint8_t v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = 1;
lean_inc_ref_n(v_self_1477_, 2);
v___x_1486_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1476_, v_self_1477_, v_self_1477_, v___x_1485_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v_snd_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1529_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_a_1487_);
v_snd_1488_ = lean_ctor_get(v_a_1487_, 1);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_a_1487_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v_a_1487_, 0);
lean_dec(v_unused_1530_);
v___x_1490_ = v_a_1487_;
v_isShared_1491_ = v_isSharedCheck_1529_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_snd_1488_);
lean_dec(v_a_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1529_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1527_; 
v_a_1492_ = lean_ctor_get(v___x_1486_, 1);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; 
v_unused_1528_ = lean_ctor_get(v___x_1486_, 0);
lean_dec(v_unused_1528_);
v___x_1494_ = v___x_1486_;
v_isShared_1495_ = v_isSharedCheck_1527_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1486_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1527_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_kind_1496_; lean_object* v_name_1497_; lean_object* v___y_1499_; uint8_t v___x_1517_; 
v_kind_1496_ = lean_ctor_get(v_snd_1488_, 1);
v_name_1497_ = l_Lake_instDataKindFilePath;
v___x_1517_ = lean_name_eq(v_kind_1496_, v_name_1497_);
if (v___x_1517_ == 0)
{
uint8_t v___x_1518_; 
lean_inc(v_kind_1496_);
lean_del_object(v___x_1490_);
lean_dec(v_snd_1488_);
v___x_1518_ = l_Lean_Name_isAnonymous(v_kind_1496_);
if (v___x_1518_ == 0)
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1519_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1520_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1496_, v___x_1485_);
v___x_1521_ = lean_string_append(v___x_1519_, v___x_1520_);
lean_dec_ref(v___x_1520_);
v___x_1522_ = lean_string_append(v___x_1521_, v___x_1519_);
v___y_1499_ = v___x_1522_;
goto v___jp_1498_;
}
else
{
lean_object* v___x_1523_; 
lean_dec(v_kind_1496_);
v___x_1523_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1499_ = v___x_1523_;
goto v___jp_1498_;
}
}
else
{
lean_object* v___x_1525_; 
lean_del_object(v___x_1494_);
lean_dec_ref(v_self_1477_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v_a_1492_);
lean_ctor_set(v___x_1490_, 0, v_snd_1488_);
v___x_1525_ = v___x_1490_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_snd_1488_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_a_1492_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
v___jp_1498_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1500_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1501_ = l_Lake_PartialBuildKey_toString(v_self_1477_);
v___x_1502_ = lean_string_append(v___x_1500_, v___x_1501_);
lean_dec_ref(v___x_1501_);
v___x_1503_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1504_ = lean_string_append(v___x_1502_, v___x_1503_);
v___x_1505_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
v___x_1506_ = lean_string_append(v___x_1504_, v___x_1505_);
v___x_1507_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1508_ = lean_string_append(v___x_1506_, v___x_1507_);
v___x_1509_ = lean_string_append(v___x_1508_, v___y_1499_);
lean_dec_ref(v___y_1499_);
v___x_1510_ = 3;
v___x_1511_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1511_, 0, v___x_1509_);
lean_ctor_set_uint8(v___x_1511_, sizeof(void*)*1, v___x_1510_);
v___x_1512_ = lean_array_get_size(v_a_1492_);
v___x_1513_ = lean_array_push(v_a_1492_, v___x_1511_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set_tag(v___x_1494_, 1);
lean_ctor_set(v___x_1494_, 1, v___x_1513_);
lean_ctor_set(v___x_1494_, 0, v___x_1512_);
v___x_1515_ = v___x_1494_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec_ref(v_self_1477_);
v_a_1531_ = lean_ctor_get(v___x_1486_, 0);
v_a_1532_ = lean_ctor_get(v___x_1486_, 1);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1486_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_inc(v_a_1531_);
lean_dec(v___x_1486_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1531_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* v_defaultPkg_1540_, lean_object* v_self_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1540_, v_self_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_);
lean_dec_ref(v_a_1546_);
lean_dec(v_a_1545_);
lean_dec(v_a_1544_);
lean_dec(v_a_1543_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* v___x_1550_, size_t v_sz_1551_, size_t v_i_1552_, lean_object* v_bs_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
uint8_t v___x_1561_; 
v___x_1561_ = lean_usize_dec_lt(v_i_1552_, v_sz_1551_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; 
lean_dec_ref(v___y_1554_);
lean_dec_ref(v___x_1550_);
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_bs_1553_);
lean_ctor_set(v___x_1562_, 1, v___y_1559_);
return v___x_1562_;
}
else
{
lean_object* v_v_1563_; lean_object* v___x_1564_; 
v_v_1563_ = lean_array_uget_borrowed(v_bs_1553_, v_i_1552_);
lean_inc_ref(v___y_1554_);
lean_inc(v_v_1563_);
lean_inc_ref(v___x_1550_);
v___x_1564_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1550_, v_v_1563_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v_a_1566_; lean_object* v___x_1567_; lean_object* v_bs_x27_1568_; size_t v___x_1569_; size_t v___x_1570_; lean_object* v___x_1571_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
v_a_1566_ = lean_ctor_get(v___x_1564_, 1);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1564_, 2);
v___x_1567_ = lean_unsigned_to_nat(0u);
v_bs_x27_1568_ = lean_array_uset(v_bs_1553_, v_i_1552_, v___x_1567_);
v___x_1569_ = ((size_t)1ULL);
v___x_1570_ = lean_usize_add(v_i_1552_, v___x_1569_);
v___x_1571_ = lean_array_uset(v_bs_x27_1568_, v_i_1552_, v_a_1565_);
v_i_1552_ = v___x_1570_;
v_bs_1553_ = v___x_1571_;
v___y_1559_ = v_a_1566_;
goto _start;
}
else
{
lean_object* v_a_1573_; lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v___y_1554_);
lean_dec_ref(v_bs_1553_);
lean_dec_ref(v___x_1550_);
v_a_1573_ = lean_ctor_get(v___x_1564_, 0);
v_a_1574_ = lean_ctor_get(v___x_1564_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1564_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_inc(v_a_1573_);
lean_dec(v___x_1564_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1573_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* v___x_1582_, lean_object* v_sz_1583_, lean_object* v_i_1584_, lean_object* v_bs_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
size_t v_sz_boxed_1593_; size_t v_i_boxed_1594_; lean_object* v_res_1595_; 
v_sz_boxed_1593_ = lean_unbox_usize(v_sz_1583_);
lean_dec(v_sz_1583_);
v_i_boxed_1594_ = lean_unbox_usize(v_i_1584_);
lean_dec(v_i_1584_);
v_res_1595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1582_, v_sz_boxed_1593_, v_i_boxed_1594_, v_bs_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec(v___y_1587_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(lean_object* v_a_1596_, lean_object* v_as_1597_, size_t v_i_1598_, size_t v_stop_1599_, lean_object* v_b_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v___x_1603_; 
v___x_1603_ = lean_usize_dec_eq(v_i_1598_, v_stop_1599_);
if (v___x_1603_ == 0)
{
lean_object* v_log_1604_; uint8_t v_action_1605_; uint8_t v_wantsRebuild_1606_; lean_object* v_trace_1607_; lean_object* v_buildTime_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_log_1604_ = lean_ctor_get(v___y_1601_, 0);
v_action_1605_ = lean_ctor_get_uint8(v___y_1601_, sizeof(void*)*3);
v_wantsRebuild_1606_ = lean_ctor_get_uint8(v___y_1601_, sizeof(void*)*3 + 1);
v_trace_1607_ = lean_ctor_get(v___y_1601_, 1);
v_buildTime_1608_ = lean_ctor_get(v___y_1601_, 2);
v___x_1609_ = lean_array_uget_borrowed(v_as_1597_, v_i_1598_);
v___x_1610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
lean_inc(v___x_1609_);
v___x_1611_ = lean_string_append(v___x_1609_, v___x_1610_);
v___x_1612_ = lean_io_prim_handle_put_str(v_a_1596_, v___x_1611_);
lean_dec_ref(v___x_1611_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; size_t v___x_1614_; size_t v___x_1615_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1614_ = ((size_t)1ULL);
v___x_1615_ = lean_usize_add(v_i_1598_, v___x_1614_);
v_i_1598_ = v___x_1615_;
v_b_1600_ = v_a_1613_;
goto _start;
}
else
{
lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1630_; 
lean_inc(v_buildTime_1608_);
lean_inc_ref(v_trace_1607_);
lean_inc_ref(v_log_1604_);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___y_1601_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; lean_object* v_unused_1632_; lean_object* v_unused_1633_; 
v_unused_1631_ = lean_ctor_get(v___y_1601_, 2);
lean_dec(v_unused_1631_);
v_unused_1632_ = lean_ctor_get(v___y_1601_, 1);
lean_dec(v_unused_1632_);
v_unused_1633_ = lean_ctor_get(v___y_1601_, 0);
lean_dec(v_unused_1633_);
v___x_1618_ = v___y_1601_;
v_isShared_1619_ = v_isSharedCheck_1630_;
goto v_resetjp_1617_;
}
else
{
lean_dec(v___y_1601_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1630_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v_a_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
v_a_1620_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1621_ = lean_io_error_to_string(v_a_1620_);
v___x_1622_ = 3;
v___x_1623_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set_uint8(v___x_1623_, sizeof(void*)*1, v___x_1622_);
v___x_1624_ = lean_array_get_size(v_log_1604_);
v___x_1625_ = lean_array_push(v_log_1604_, v___x_1623_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1625_);
v___x_1627_ = v___x_1618_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_trace_1607_);
lean_ctor_set(v_reuseFailAlloc_1629_, 2, v_buildTime_1608_);
lean_ctor_set_uint8(v_reuseFailAlloc_1629_, sizeof(void*)*3, v_action_1605_);
lean_ctor_set_uint8(v_reuseFailAlloc_1629_, sizeof(void*)*3 + 1, v_wantsRebuild_1606_);
v___x_1627_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1628_; 
v___x_1628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1624_);
lean_ctor_set(v___x_1628_, 1, v___x_1627_);
return v___x_1628_;
}
}
}
}
else
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v_b_1600_);
lean_ctor_set(v___x_1634_, 1, v___y_1601_);
return v___x_1634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(lean_object* v_a_1635_, lean_object* v_as_1636_, lean_object* v_i_1637_, lean_object* v_stop_1638_, lean_object* v_b_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
size_t v_i_boxed_1642_; size_t v_stop_boxed_1643_; lean_object* v_res_1644_; 
v_i_boxed_1642_ = lean_unbox_usize(v_i_1637_);
lean_dec(v_i_1637_);
v_stop_boxed_1643_ = lean_unbox_usize(v_stop_1638_);
lean_dec(v_stop_1638_);
v_res_1644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1635_, v_as_1636_, v_i_boxed_1642_, v_stop_boxed_1643_, v_b_1639_, v___y_1640_);
lean_dec_ref(v_as_1636_);
lean_dec(v_a_1635_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(uint8_t v_bootstrap_1645_, lean_object* v___y_1646_, lean_object* v_oFiles_1647_, uint8_t v_shouldExport_1648_, uint8_t v___x_1649_, size_t v___x_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
if (v_bootstrap_1645_ == 0)
{
lean_object* v_toContext_1658_; lean_object* v_lakeEnv_1659_; lean_object* v_lean_1660_; lean_object* v_log_1661_; uint8_t v_action_1662_; uint8_t v_wantsRebuild_1663_; lean_object* v_trace_1664_; lean_object* v_buildTime_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1695_; 
v_toContext_1658_ = lean_ctor_get(v___y_1655_, 1);
v_lakeEnv_1659_ = lean_ctor_get(v_toContext_1658_, 0);
v_lean_1660_ = lean_ctor_get(v_lakeEnv_1659_, 1);
v_log_1661_ = lean_ctor_get(v___y_1656_, 0);
v_action_1662_ = lean_ctor_get_uint8(v___y_1656_, sizeof(void*)*3);
v_wantsRebuild_1663_ = lean_ctor_get_uint8(v___y_1656_, sizeof(void*)*3 + 1);
v_trace_1664_ = lean_ctor_get(v___y_1656_, 1);
v_buildTime_1665_ = lean_ctor_get(v___y_1656_, 2);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___y_1656_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1667_ = v___y_1656_;
v_isShared_1668_ = v_isSharedCheck_1695_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_buildTime_1665_);
lean_inc(v_trace_1664_);
lean_inc(v_log_1661_);
lean_dec(v___y_1656_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1695_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v_ar_1669_; lean_object* v___x_1670_; 
v_ar_1669_ = lean_ctor_get(v_lean_1660_, 13);
lean_inc_ref(v_ar_1669_);
v___x_1670_ = l_Lake_compileStaticLib(v___y_1646_, v_oFiles_1647_, v_ar_1669_, v_bootstrap_1645_, v_log_1661_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1682_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_a_1672_ = lean_ctor_get(v___x_1670_, 1);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1674_ = v___x_1670_;
v_isShared_1675_ = v_isSharedCheck_1682_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1682_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v_a_1672_);
v___x_1677_ = v___x_1667_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1672_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_trace_1664_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_buildTime_1665_);
lean_ctor_set_uint8(v_reuseFailAlloc_1681_, sizeof(void*)*3, v_action_1662_);
lean_ctor_set_uint8(v_reuseFailAlloc_1681_, sizeof(void*)*3 + 1, v_wantsRebuild_1663_);
v___x_1677_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1679_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v___x_1677_);
v___x_1679_ = v___x_1674_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1671_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1694_; 
v_a_1683_ = lean_ctor_get(v___x_1670_, 0);
v_a_1684_ = lean_ctor_get(v___x_1670_, 1);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1686_ = v___x_1670_;
v_isShared_1687_ = v_isSharedCheck_1694_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_inc(v_a_1683_);
lean_dec(v___x_1670_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1694_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 0, v_a_1684_);
v___x_1689_ = v___x_1667_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1684_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_trace_1664_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_buildTime_1665_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*3, v_action_1662_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*3 + 1, v_wantsRebuild_1663_);
v___x_1689_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1691_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v___x_1689_);
v___x_1691_ = v___x_1686_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1683_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
}
}
else
{
uint8_t v___x_1696_; 
v___x_1696_ = l_System_Platform_isOSX;
if (v___x_1696_ == 0)
{
uint8_t v___x_1697_; 
v___x_1697_ = l_System_Platform_isWindows;
if (v___x_1697_ == 0)
{
lean_object* v_toContext_1698_; lean_object* v_lakeEnv_1699_; lean_object* v_lean_1700_; lean_object* v_log_1701_; uint8_t v_action_1702_; uint8_t v_wantsRebuild_1703_; lean_object* v_trace_1704_; lean_object* v_buildTime_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1735_; 
v_toContext_1698_ = lean_ctor_get(v___y_1655_, 1);
v_lakeEnv_1699_ = lean_ctor_get(v_toContext_1698_, 0);
v_lean_1700_ = lean_ctor_get(v_lakeEnv_1699_, 1);
v_log_1701_ = lean_ctor_get(v___y_1656_, 0);
v_action_1702_ = lean_ctor_get_uint8(v___y_1656_, sizeof(void*)*3);
v_wantsRebuild_1703_ = lean_ctor_get_uint8(v___y_1656_, sizeof(void*)*3 + 1);
v_trace_1704_ = lean_ctor_get(v___y_1656_, 1);
v_buildTime_1705_ = lean_ctor_get(v___y_1656_, 2);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___y_1656_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1707_ = v___y_1656_;
v_isShared_1708_ = v_isSharedCheck_1735_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_buildTime_1705_);
lean_inc(v_trace_1704_);
lean_inc(v_log_1701_);
lean_dec(v___y_1656_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1735_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_ar_1709_; lean_object* v___x_1710_; 
v_ar_1709_ = lean_ctor_get(v_lean_1700_, 13);
lean_inc_ref(v_ar_1709_);
v___x_1710_ = l_Lake_compileStaticLib(v___y_1646_, v_oFiles_1647_, v_ar_1709_, v___x_1697_, v_log_1701_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1722_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_a_1712_ = lean_ctor_get(v___x_1710_, 1);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1714_ = v___x_1710_;
v_isShared_1715_ = v_isSharedCheck_1722_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1722_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v_a_1712_);
v___x_1717_ = v___x_1707_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1712_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_trace_1704_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v_buildTime_1705_);
lean_ctor_set_uint8(v_reuseFailAlloc_1721_, sizeof(void*)*3, v_action_1702_);
lean_ctor_set_uint8(v_reuseFailAlloc_1721_, sizeof(void*)*3 + 1, v_wantsRebuild_1703_);
v___x_1717_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v___x_1717_);
v___x_1719_ = v___x_1714_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1711_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1734_; 
v_a_1723_ = lean_ctor_get(v___x_1710_, 0);
v_a_1724_ = lean_ctor_get(v___x_1710_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1726_ = v___x_1710_;
v_isShared_1727_ = v_isSharedCheck_1734_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_inc(v_a_1723_);
lean_dec(v___x_1710_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1734_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v_a_1724_);
v___x_1729_ = v___x_1707_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1724_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_trace_1704_);
lean_ctor_set(v_reuseFailAlloc_1733_, 2, v_buildTime_1705_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*3, v_action_1702_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*3 + 1, v_wantsRebuild_1703_);
v___x_1729_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1731_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v___x_1729_);
v___x_1731_ = v___x_1726_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1723_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1736_; lean_object* v_lakeEnv_1737_; lean_object* v_lean_1738_; lean_object* v_log_1739_; uint8_t v_action_1740_; uint8_t v_wantsRebuild_1741_; lean_object* v_trace_1742_; lean_object* v_buildTime_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1773_; 
v_toContext_1736_ = lean_ctor_get(v___y_1655_, 1);
v_lakeEnv_1737_ = lean_ctor_get(v_toContext_1736_, 0);
v_lean_1738_ = lean_ctor_get(v_lakeEnv_1737_, 1);
v_log_1739_ = lean_ctor_get(v___y_1656_, 0);
v_action_1740_ = lean_ctor_get_uint8(v___y_1656_, sizeof(void*)*3);
v_wantsRebuild_1741_ = lean_ctor_get_uint8(v___y_1656_, sizeof(void*)*3 + 1);
v_trace_1742_ = lean_ctor_get(v___y_1656_, 1);
v_buildTime_1743_ = lean_ctor_get(v___y_1656_, 2);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___y_1656_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1745_ = v___y_1656_;
v_isShared_1746_ = v_isSharedCheck_1773_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_buildTime_1743_);
lean_inc(v_trace_1742_);
lean_inc(v_log_1739_);
lean_dec(v___y_1656_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1773_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v_ar_1747_; lean_object* v___x_1748_; 
v_ar_1747_ = lean_ctor_get(v_lean_1738_, 13);
lean_inc_ref(v_ar_1747_);
v___x_1748_ = l_Lake_compileStaticLib(v___y_1646_, v_oFiles_1647_, v_ar_1747_, v_shouldExport_1648_, v_log_1739_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1760_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_a_1750_ = lean_ctor_get(v___x_1748_, 1);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1752_ = v___x_1748_;
v_isShared_1753_ = v_isSharedCheck_1760_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1760_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v_a_1750_);
v___x_1755_ = v___x_1745_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1750_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_trace_1742_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_buildTime_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1759_, sizeof(void*)*3, v_action_1740_);
lean_ctor_set_uint8(v_reuseFailAlloc_1759_, sizeof(void*)*3 + 1, v_wantsRebuild_1741_);
v___x_1755_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1757_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 1, v___x_1755_);
v___x_1757_ = v___x_1752_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1749_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1772_; 
v_a_1761_ = lean_ctor_get(v___x_1748_, 0);
v_a_1762_ = lean_ctor_get(v___x_1748_, 1);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1764_ = v___x_1748_;
v_isShared_1765_ = v_isSharedCheck_1772_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_inc(v_a_1761_);
lean_dec(v___x_1748_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1772_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v_a_1762_);
v___x_1767_ = v___x_1745_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1762_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_trace_1742_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v_buildTime_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1771_, sizeof(void*)*3, v_action_1740_);
lean_ctor_set_uint8(v_reuseFailAlloc_1771_, sizeof(void*)*3 + 1, v_wantsRebuild_1741_);
v___x_1767_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1769_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 1, v___x_1767_);
v___x_1769_ = v___x_1764_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1761_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1774_; uint8_t v_action_1775_; uint8_t v_wantsRebuild_1776_; lean_object* v_trace_1777_; lean_object* v_buildTime_1778_; lean_object* v___x_1779_; 
v_log_1774_ = lean_ctor_get(v___y_1656_, 0);
v_action_1775_ = lean_ctor_get_uint8(v___y_1656_, sizeof(void*)*3);
v_wantsRebuild_1776_ = lean_ctor_get_uint8(v___y_1656_, sizeof(void*)*3 + 1);
v_trace_1777_ = lean_ctor_get(v___y_1656_, 1);
v_buildTime_1778_ = lean_ctor_get(v___y_1656_, 2);
lean_inc_ref(v___y_1646_);
v___x_1779_ = l_Lake_createParentDirs(v___y_1646_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v_a_1783_; lean_object* v___y_1832_; uint8_t v___x_1834_; lean_object* v___x_1835_; 
lean_dec_ref_known(v___x_1779_, 1);
v___x_1780_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1646_);
v___x_1781_ = l_System_FilePath_addExtension(v___y_1646_, v___x_1780_);
v___x_1834_ = 1;
v___x_1835_ = lean_io_prim_handle_mk(v___x_1781_, v___x_1834_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = lean_unsigned_to_nat(0u);
v___x_1838_ = lean_array_get_size(v_oFiles_1647_);
v___x_1839_ = lean_nat_dec_lt(v___x_1837_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_dec(v_a_1836_);
lean_dec_ref(v_oFiles_1647_);
v_a_1783_ = v___y_1656_;
goto v___jp_1782_;
}
else
{
lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1840_ = lean_box(0);
v___x_1841_ = lean_nat_dec_le(v___x_1838_, v___x_1838_);
if (v___x_1841_ == 0)
{
if (v___x_1839_ == 0)
{
lean_dec(v_a_1836_);
lean_dec_ref(v_oFiles_1647_);
v_a_1783_ = v___y_1656_;
goto v___jp_1782_;
}
else
{
size_t v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = lean_usize_of_nat(v___x_1838_);
v___x_1843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1836_, v_oFiles_1647_, v___x_1650_, v___x_1842_, v___x_1840_, v___y_1656_);
lean_dec_ref(v_oFiles_1647_);
lean_dec(v_a_1836_);
v___y_1832_ = v___x_1843_;
goto v___jp_1831_;
}
}
else
{
size_t v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_usize_of_nat(v___x_1838_);
v___x_1845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1836_, v_oFiles_1647_, v___x_1650_, v___x_1844_, v___x_1840_, v___y_1656_);
lean_dec_ref(v_oFiles_1647_);
lean_dec(v_a_1836_);
v___y_1832_ = v___x_1845_;
goto v___jp_1831_;
}
}
}
else
{
lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1859_; 
lean_inc(v_buildTime_1778_);
lean_inc_ref(v_trace_1777_);
lean_inc_ref(v_log_1774_);
lean_dec_ref(v___x_1781_);
lean_dec_ref(v_oFiles_1647_);
lean_dec_ref(v___y_1646_);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___y_1656_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; lean_object* v_unused_1861_; lean_object* v_unused_1862_; 
v_unused_1860_ = lean_ctor_get(v___y_1656_, 2);
lean_dec(v_unused_1860_);
v_unused_1861_ = lean_ctor_get(v___y_1656_, 1);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v___y_1656_, 0);
lean_dec(v_unused_1862_);
v___x_1847_ = v___y_1656_;
v_isShared_1848_ = v_isSharedCheck_1859_;
goto v_resetjp_1846_;
}
else
{
lean_dec(v___y_1656_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1859_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_a_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v_a_1849_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1850_ = lean_io_error_to_string(v_a_1849_);
v___x_1851_ = 3;
v___x_1852_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set_uint8(v___x_1852_, sizeof(void*)*1, v___x_1851_);
v___x_1853_ = lean_array_get_size(v_log_1774_);
v___x_1854_ = lean_array_push(v_log_1774_, v___x_1852_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1854_);
v___x_1856_ = v___x_1847_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_trace_1777_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_buildTime_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*3, v_action_1775_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*3 + 1, v_wantsRebuild_1776_);
v___x_1856_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1853_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
return v___x_1857_;
}
}
}
v___jp_1782_:
{
lean_object* v___x_1784_; lean_object* v_log_1785_; uint8_t v_action_1786_; uint8_t v_wantsRebuild_1787_; lean_object* v_trace_1788_; lean_object* v_buildTime_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1830_; 
v___x_1784_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1785_ = lean_ctor_get(v_a_1783_, 0);
v_action_1786_ = lean_ctor_get_uint8(v_a_1783_, sizeof(void*)*3);
v_wantsRebuild_1787_ = lean_ctor_get_uint8(v_a_1783_, sizeof(void*)*3 + 1);
v_trace_1788_ = lean_ctor_get(v_a_1783_, 1);
v_buildTime_1789_ = lean_ctor_get(v_a_1783_, 2);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_a_1783_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1791_ = v_a_1783_;
v_isShared_1792_ = v_isSharedCheck_1830_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_buildTime_1789_);
lean_inc(v_trace_1788_);
lean_inc(v_log_1785_);
lean_dec(v_a_1783_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1830_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1793_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1794_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1795_ = lean_unsigned_to_nat(5u);
v___x_1796_ = lean_mk_empty_array_with_capacity(v___x_1795_);
lean_dec_ref(v___x_1796_);
v___x_1797_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1798_ = lean_array_push(v___x_1797_, v___y_1646_);
v___x_1799_ = lean_array_push(v___x_1798_, v___x_1794_);
v___x_1800_ = lean_array_push(v___x_1799_, v___x_1781_);
v___x_1801_ = lean_box(0);
v___x_1802_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1803_ = 0;
v___x_1804_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1804_, 0, v___x_1784_);
lean_ctor_set(v___x_1804_, 1, v___x_1793_);
lean_ctor_set(v___x_1804_, 2, v___x_1800_);
lean_ctor_set(v___x_1804_, 3, v___x_1801_);
lean_ctor_set(v___x_1804_, 4, v___x_1802_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*5, v___x_1649_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*5 + 1, v___x_1803_);
v___x_1805_ = l_Lake_proc(v___x_1804_, v___x_1803_, v___x_1801_, v_log_1785_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1817_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_a_1807_ = lean_ctor_get(v___x_1805_, 1);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1809_ = v___x_1805_;
v_isShared_1810_ = v_isSharedCheck_1817_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1817_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v_a_1807_);
v___x_1812_ = v___x_1791_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1807_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_trace_1788_);
lean_ctor_set(v_reuseFailAlloc_1816_, 2, v_buildTime_1789_);
lean_ctor_set_uint8(v_reuseFailAlloc_1816_, sizeof(void*)*3, v_action_1786_);
lean_ctor_set_uint8(v_reuseFailAlloc_1816_, sizeof(void*)*3 + 1, v_wantsRebuild_1787_);
v___x_1812_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 1, v___x_1812_);
v___x_1814_ = v___x_1809_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1806_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_object* v_a_1818_; lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1829_; 
v_a_1818_ = lean_ctor_get(v___x_1805_, 0);
v_a_1819_ = lean_ctor_get(v___x_1805_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1821_ = v___x_1805_;
v_isShared_1822_ = v_isSharedCheck_1829_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_inc(v_a_1818_);
lean_dec(v___x_1805_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1829_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 0, v_a_1819_);
v___x_1824_ = v___x_1791_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1819_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_trace_1788_);
lean_ctor_set(v_reuseFailAlloc_1828_, 2, v_buildTime_1789_);
lean_ctor_set_uint8(v_reuseFailAlloc_1828_, sizeof(void*)*3, v_action_1786_);
lean_ctor_set_uint8(v_reuseFailAlloc_1828_, sizeof(void*)*3 + 1, v_wantsRebuild_1787_);
v___x_1824_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1826_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 1, v___x_1824_);
v___x_1826_ = v___x_1821_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1818_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
}
v___jp_1831_:
{
if (lean_obj_tag(v___y_1832_) == 0)
{
lean_object* v_a_1833_; 
v_a_1833_ = lean_ctor_get(v___y_1832_, 1);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___y_1832_, 2);
v_a_1783_ = v_a_1833_;
goto v___jp_1782_;
}
else
{
lean_dec_ref(v___x_1781_);
lean_dec_ref(v___y_1646_);
return v___y_1832_;
}
}
}
else
{
lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1876_; 
lean_inc(v_buildTime_1778_);
lean_inc_ref(v_trace_1777_);
lean_inc_ref(v_log_1774_);
lean_dec_ref(v_oFiles_1647_);
lean_dec_ref(v___y_1646_);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___y_1656_);
if (v_isSharedCheck_1876_ == 0)
{
lean_object* v_unused_1877_; lean_object* v_unused_1878_; lean_object* v_unused_1879_; 
v_unused_1877_ = lean_ctor_get(v___y_1656_, 2);
lean_dec(v_unused_1877_);
v_unused_1878_ = lean_ctor_get(v___y_1656_, 1);
lean_dec(v_unused_1878_);
v_unused_1879_ = lean_ctor_get(v___y_1656_, 0);
lean_dec(v_unused_1879_);
v___x_1864_ = v___y_1656_;
v_isShared_1865_ = v_isSharedCheck_1876_;
goto v_resetjp_1863_;
}
else
{
lean_dec(v___y_1656_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1876_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_a_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1873_; 
v_a_1866_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1779_, 1);
v___x_1867_ = lean_io_error_to_string(v_a_1866_);
v___x_1868_ = 3;
v___x_1869_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set_uint8(v___x_1869_, sizeof(void*)*1, v___x_1868_);
v___x_1870_ = lean_array_get_size(v_log_1774_);
v___x_1871_ = lean_array_push(v_log_1774_, v___x_1869_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v___x_1871_);
v___x_1873_ = v___x_1864_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1871_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_trace_1777_);
lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_buildTime_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1875_, sizeof(void*)*3, v_action_1775_);
lean_ctor_set_uint8(v_reuseFailAlloc_1875_, sizeof(void*)*3 + 1, v_wantsRebuild_1776_);
v___x_1873_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1874_; 
v___x_1874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1870_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
return v___x_1874_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object* v_bootstrap_1880_, lean_object* v___y_1881_, lean_object* v_oFiles_1882_, lean_object* v_shouldExport_1883_, lean_object* v___x_1884_, lean_object* v___x_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
uint8_t v_bootstrap_boxed_1893_; uint8_t v_shouldExport_boxed_1894_; uint8_t v___x_6746__boxed_1895_; size_t v___x_6747__boxed_1896_; lean_object* v_res_1897_; 
v_bootstrap_boxed_1893_ = lean_unbox(v_bootstrap_1880_);
v_shouldExport_boxed_1894_ = lean_unbox(v_shouldExport_1883_);
v___x_6746__boxed_1895_ = lean_unbox(v___x_1884_);
v___x_6747__boxed_1896_ = lean_unbox_usize(v___x_1885_);
lean_dec(v___x_1885_);
v_res_1897_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_boxed_1893_, v___y_1881_, v_oFiles_1882_, v_shouldExport_boxed_1894_, v___x_6746__boxed_1895_, v___x_6747__boxed_1896_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t v_bootstrap_1898_, lean_object* v___y_1899_, uint8_t v_shouldExport_1900_, uint8_t v___x_1901_, size_t v___x_1902_, lean_object* v_oFiles_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___y_1915_; uint8_t v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1911_ = lean_box(v_bootstrap_1898_);
v___x_1912_ = lean_box(v_shouldExport_1900_);
v___x_1913_ = lean_box(v___x_1901_);
v___x_1914_ = lean_box_usize(v___x_1902_);
lean_inc_ref(v___y_1899_);
v___y_1915_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed), 13, 6);
lean_closure_set(v___y_1915_, 0, v___x_1911_);
lean_closure_set(v___y_1915_, 1, v___y_1899_);
lean_closure_set(v___y_1915_, 2, v_oFiles_1903_);
lean_closure_set(v___y_1915_, 3, v___x_1912_);
lean_closure_set(v___y_1915_, 4, v___x_1913_);
lean_closure_set(v___y_1915_, 5, v___x_1914_);
v___x_1916_ = 0;
v___x_1917_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1918_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1899_, v___y_1915_, v___x_1916_, v___x_1917_, v___x_1901_, v___x_1916_, v___x_1916_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1928_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_a_1920_ = lean_ctor_get(v___x_1918_, 1);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1922_ = v___x_1918_;
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1928_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v_path_1924_; lean_object* v___x_1926_; 
v_path_1924_ = lean_ctor_get(v_a_1919_, 1);
lean_inc_ref(v_path_1924_);
lean_dec(v_a_1919_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v_path_1924_);
v___x_1926_ = v___x_1922_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_path_1924_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_a_1920_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v_a_1929_ = lean_ctor_get(v___x_1918_, 0);
v_a_1930_ = lean_ctor_get(v___x_1918_, 1);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1918_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_inc(v_a_1929_);
lean_dec(v___x_1918_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1929_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* v_bootstrap_1938_, lean_object* v___y_1939_, lean_object* v_shouldExport_1940_, lean_object* v___x_1941_, lean_object* v___x_1942_, lean_object* v_oFiles_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
uint8_t v_bootstrap_boxed_1951_; uint8_t v_shouldExport_boxed_1952_; uint8_t v___x_7156__boxed_1953_; size_t v___x_7157__boxed_1954_; lean_object* v_res_1955_; 
v_bootstrap_boxed_1951_ = lean_unbox(v_bootstrap_1938_);
v_shouldExport_boxed_1952_ = lean_unbox(v_shouldExport_1940_);
v___x_7156__boxed_1953_ = lean_unbox(v___x_1941_);
v___x_7157__boxed_1954_ = lean_unbox_usize(v___x_1942_);
lean_dec(v___x_1942_);
v_res_1955_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_boxed_1951_, v___y_1939_, v_shouldExport_boxed_1952_, v___x_7156__boxed_1953_, v___x_7157__boxed_1954_, v_oFiles_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec(v___y_1945_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* v_a_1956_, size_t v_sz_1957_, size_t v_i_1958_, lean_object* v_bs_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
uint8_t v___x_1967_; 
v___x_1967_ = lean_usize_dec_lt(v_i_1958_, v_sz_1957_);
if (v___x_1967_ == 0)
{
lean_object* v___x_1968_; 
lean_dec_ref(v___y_1960_);
lean_dec_ref(v_a_1956_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v_bs_1959_);
lean_ctor_set(v___x_1968_, 1, v___y_1965_);
return v___x_1968_;
}
else
{
lean_object* v_v_1969_; lean_object* v___x_1970_; 
v_v_1969_ = lean_array_uget_borrowed(v_bs_1959_, v_i_1958_);
lean_inc_ref(v___y_1960_);
lean_inc_ref(v_a_1956_);
lean_inc(v_v_1969_);
v___x_1970_ = l_Lake_ModuleFacet_fetch___redArg(v_v_1969_, v_a_1956_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v_a_1972_; lean_object* v___x_1973_; lean_object* v_bs_x27_1974_; size_t v___x_1975_; size_t v___x_1976_; lean_object* v___x_1977_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
v_a_1972_ = lean_ctor_get(v___x_1970_, 1);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1970_, 2);
v___x_1973_ = lean_unsigned_to_nat(0u);
v_bs_x27_1974_ = lean_array_uset(v_bs_1959_, v_i_1958_, v___x_1973_);
v___x_1975_ = ((size_t)1ULL);
v___x_1976_ = lean_usize_add(v_i_1958_, v___x_1975_);
v___x_1977_ = lean_array_uset(v_bs_x27_1974_, v_i_1958_, v_a_1971_);
v_i_1958_ = v___x_1976_;
v_bs_1959_ = v___x_1977_;
v___y_1965_ = v_a_1972_;
goto _start;
}
else
{
lean_object* v_a_1979_; lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v___y_1960_);
lean_dec_ref(v_bs_1959_);
lean_dec_ref(v_a_1956_);
v_a_1979_ = lean_ctor_get(v___x_1970_, 0);
v_a_1980_ = lean_ctor_get(v___x_1970_, 1);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1970_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_inc(v_a_1979_);
lean_dec(v___x_1970_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1979_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object* v_a_1988_, lean_object* v_sz_1989_, lean_object* v_i_1990_, lean_object* v_bs_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
size_t v_sz_boxed_1999_; size_t v_i_boxed_2000_; lean_object* v_res_2001_; 
v_sz_boxed_1999_ = lean_unbox_usize(v_sz_1989_);
lean_dec(v_sz_1989_);
v_i_boxed_2000_ = lean_unbox_usize(v_i_1990_);
lean_dec(v_i_1990_);
v_res_2001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_1988_, v_sz_boxed_1999_, v_i_boxed_2000_, v_bs_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec(v___y_1993_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(uint8_t v_shouldExport_2002_, lean_object* v_as_2003_, size_t v_i_2004_, size_t v_stop_2005_, lean_object* v_b_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
uint8_t v___x_2014_; 
v___x_2014_ = lean_usize_dec_eq(v_i_2004_, v_stop_2005_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v_lib_2016_; lean_object* v_config_2017_; lean_object* v_nativeFacets_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; size_t v_sz_2021_; size_t v___x_2022_; lean_object* v___x_2023_; 
v___x_2015_ = lean_array_uget_borrowed(v_as_2003_, v_i_2004_);
v_lib_2016_ = lean_ctor_get(v___x_2015_, 0);
v_config_2017_ = lean_ctor_get(v_lib_2016_, 2);
v_nativeFacets_2018_ = lean_ctor_get(v_config_2017_, 8);
v___x_2019_ = lean_box(v_shouldExport_2002_);
lean_inc_ref(v_nativeFacets_2018_);
v___x_2020_ = lean_apply_1(v_nativeFacets_2018_, v___x_2019_);
v_sz_2021_ = lean_array_size(v___x_2020_);
v___x_2022_ = ((size_t)0ULL);
lean_inc_ref(v___y_2007_);
lean_inc(v___x_2015_);
v___x_2023_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2015_, v_sz_2021_, v___x_2022_, v___x_2020_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v_a_2025_; lean_object* v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
v_a_2025_ = lean_ctor_get(v___x_2023_, 1);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2023_, 2);
v___x_2026_ = l_Array_append___redArg(v_b_2006_, v_a_2024_);
lean_dec(v_a_2024_);
v___x_2027_ = ((size_t)1ULL);
v___x_2028_ = lean_usize_add(v_i_2004_, v___x_2027_);
v_i_2004_ = v___x_2028_;
v_b_2006_ = v___x_2026_;
v___y_2012_ = v_a_2025_;
goto _start;
}
else
{
lean_dec_ref(v___y_2007_);
lean_dec_ref(v_b_2006_);
return v___x_2023_;
}
}
else
{
lean_object* v___x_2030_; 
lean_dec_ref(v___y_2007_);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v_b_2006_);
lean_ctor_set(v___x_2030_, 1, v___y_2012_);
return v___x_2030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(lean_object* v_shouldExport_2031_, lean_object* v_as_2032_, lean_object* v_i_2033_, lean_object* v_stop_2034_, lean_object* v_b_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
uint8_t v_shouldExport_boxed_2043_; size_t v_i_boxed_2044_; size_t v_stop_boxed_2045_; lean_object* v_res_2046_; 
v_shouldExport_boxed_2043_ = lean_unbox(v_shouldExport_2031_);
v_i_boxed_2044_ = lean_unbox_usize(v_i_2033_);
lean_dec(v_i_2033_);
v_stop_boxed_2045_ = lean_unbox_usize(v_stop_2034_);
lean_dec(v_stop_2034_);
v_res_2046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_boxed_2043_, v_as_2032_, v_i_boxed_2044_, v_stop_boxed_2045_, v_b_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v_as_2032_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object* v___x_2047_, lean_object* v___x_2048_, lean_object* v_config_2049_, lean_object* v_config_2050_, lean_object* v_pkg_2051_, uint8_t v_shouldExport_2052_, uint8_t v___x_2053_, lean_object* v___x_2054_, lean_object* v_dir_2055_, lean_object* v_self_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
uint8_t v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; size_t v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v_a_2085_; lean_object* v_a_2086_; lean_object* v___y_2129_; lean_object* v___x_2141_; 
lean_inc_ref(v___y_2057_);
lean_inc_ref(v___y_2061_);
lean_inc(v___y_2060_);
lean_inc(v___y_2059_);
lean_inc(v___x_2048_);
v___x_2141_ = lean_apply_7(v___y_2057_, v___x_2047_, v___x_2048_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, lean_box(0));
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v_a_2143_; lean_object* v___x_2144_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
v_a_2143_ = lean_ctor_get(v___x_2141_, 1);
lean_inc(v_a_2143_);
lean_dec_ref_known(v___x_2141_, 2);
v___x_2144_ = l_Lake_Job_await___redArg(v_a_2142_, v_a_2143_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v_a_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
v_a_2146_ = lean_ctor_get(v___x_2144_, 1);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2144_, 2);
v___x_2147_ = lean_unsigned_to_nat(0u);
v___x_2148_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_2149_ = lean_array_get_size(v_a_2145_);
v___x_2150_ = lean_nat_dec_lt(v___x_2147_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_dec(v_a_2145_);
v_a_2085_ = v___x_2148_;
v_a_2086_ = v_a_2146_;
goto v___jp_2084_;
}
else
{
uint8_t v___x_2151_; 
v___x_2151_ = lean_nat_dec_le(v___x_2149_, v___x_2149_);
if (v___x_2151_ == 0)
{
if (v___x_2150_ == 0)
{
lean_dec(v_a_2145_);
v_a_2085_ = v___x_2148_;
v_a_2086_ = v_a_2146_;
goto v___jp_2084_;
}
else
{
size_t v___x_2152_; size_t v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = ((size_t)0ULL);
v___x_2153_ = lean_usize_of_nat(v___x_2149_);
lean_inc_ref(v___y_2057_);
v___x_2154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2052_, v_a_2145_, v___x_2152_, v___x_2153_, v___x_2148_, v___y_2057_, v___x_2048_, v___y_2059_, v___y_2060_, v___y_2061_, v_a_2146_);
lean_dec(v_a_2145_);
v___y_2129_ = v___x_2154_;
goto v___jp_2128_;
}
}
else
{
size_t v___x_2155_; size_t v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = ((size_t)0ULL);
v___x_2156_ = lean_usize_of_nat(v___x_2149_);
lean_inc_ref(v___y_2057_);
v___x_2157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2052_, v_a_2145_, v___x_2155_, v___x_2156_, v___x_2148_, v___y_2057_, v___x_2048_, v___y_2059_, v___y_2060_, v___y_2061_, v_a_2146_);
lean_dec(v_a_2145_);
v___y_2129_ = v___x_2157_;
goto v___jp_2128_;
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec_ref(v___y_2057_);
lean_dec_ref(v_self_2056_);
lean_dec_ref(v_dir_2055_);
lean_dec(v___x_2054_);
lean_dec_ref(v_pkg_2051_);
lean_dec_ref(v_config_2049_);
lean_dec(v___x_2048_);
v_a_2158_ = lean_ctor_get(v___x_2144_, 0);
v_a_2159_ = lean_ctor_get(v___x_2144_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2144_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_inc(v_a_2158_);
lean_dec(v___x_2144_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2158_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec_ref(v___y_2057_);
lean_dec_ref(v_self_2056_);
lean_dec_ref(v_dir_2055_);
lean_dec(v___x_2054_);
lean_dec_ref(v_pkg_2051_);
lean_dec_ref(v_config_2049_);
lean_dec(v___x_2048_);
v_a_2167_ = lean_ctor_get(v___x_2141_, 0);
v_a_2168_ = lean_ctor_get(v___x_2141_, 1);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2141_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_inc(v_a_2167_);
lean_dec(v___x_2141_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2167_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
v___jp_2064_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___f_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2071_ = lean_box(v___y_2065_);
v___x_2072_ = lean_box(v_shouldExport_2052_);
v___x_2073_ = lean_box(v___x_2053_);
v___x_2074_ = lean_box_usize(v___y_2068_);
v___f_2075_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2075_, 0, v___x_2071_);
lean_closure_set(v___f_2075_, 1, v___y_2070_);
lean_closure_set(v___f_2075_, 2, v___x_2072_);
lean_closure_set(v___f_2075_, 3, v___x_2073_);
lean_closure_set(v___f_2075_, 4, v___x_2074_);
v___x_2076_ = l_Array_append___redArg(v___y_2069_, v___y_2067_);
lean_dec_ref(v___y_2067_);
v___x_2077_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_2078_ = l_Lake_Job_collectArray___redArg(v___x_2076_, v___x_2077_);
lean_dec_ref(v___x_2076_);
v___x_2079_ = lean_unsigned_to_nat(0u);
v___x_2080_ = 0;
v___x_2081_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2082_ = l_Lake_Job_mapM___redArg(v___x_2054_, v___x_2078_, v___f_2075_, v___x_2079_, v___x_2080_, v___y_2057_, v___x_2048_, v___y_2059_, v___y_2060_, v___y_2061_, v___x_2081_);
lean_dec(v___x_2048_);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___y_2066_);
return v___x_2083_;
}
v___jp_2084_:
{
lean_object* v_toLeanConfig_2087_; lean_object* v_toLeanConfig_2088_; uint8_t v_bootstrap_2089_; lean_object* v_buildDir_2090_; lean_object* v_nativeLibDir_2091_; lean_object* v_moreLinkObjs_2092_; lean_object* v_moreLinkObjs_2093_; lean_object* v___x_2094_; size_t v_sz_2095_; size_t v___x_2096_; lean_object* v___x_2097_; 
v_toLeanConfig_2087_ = lean_ctor_get(v_config_2049_, 1);
lean_inc_ref(v_toLeanConfig_2087_);
v_toLeanConfig_2088_ = lean_ctor_get(v_config_2050_, 0);
v_bootstrap_2089_ = lean_ctor_get_uint8(v_config_2049_, sizeof(void*)*27);
v_buildDir_2090_ = lean_ctor_get(v_config_2049_, 5);
lean_inc_ref(v_buildDir_2090_);
v_nativeLibDir_2091_ = lean_ctor_get(v_config_2049_, 7);
lean_inc_ref(v_nativeLibDir_2091_);
lean_dec_ref(v_config_2049_);
v_moreLinkObjs_2092_ = lean_ctor_get(v_toLeanConfig_2087_, 6);
lean_inc_ref(v_moreLinkObjs_2092_);
lean_dec_ref(v_toLeanConfig_2087_);
v_moreLinkObjs_2093_ = lean_ctor_get(v_toLeanConfig_2088_, 6);
v___x_2094_ = l_Array_append___redArg(v_moreLinkObjs_2092_, v_moreLinkObjs_2093_);
v_sz_2095_ = lean_array_size(v___x_2094_);
v___x_2096_ = ((size_t)0ULL);
lean_inc_ref(v___y_2057_);
v___x_2097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_2051_, v_sz_2095_, v___x_2096_, v___x_2094_, v___y_2057_, v___x_2048_, v___y_2059_, v___y_2060_, v___y_2061_, v_a_2086_);
if (lean_obj_tag(v___x_2097_) == 0)
{
if (v_shouldExport_2052_ == 0)
{
lean_object* v_a_2098_; lean_object* v_a_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
v_a_2099_ = lean_ctor_get(v___x_2097_, 1);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2097_, 2);
v___x_2100_ = l_System_FilePath_normalize(v_buildDir_2090_);
v___x_2101_ = l_Lake_joinRelative(v_dir_2055_, v___x_2100_);
v___x_2102_ = l_System_FilePath_normalize(v_nativeLibDir_2091_);
v___x_2103_ = l_Lake_joinRelative(v___x_2101_, v___x_2102_);
v___x_2104_ = l_Lake_LeanLib_libName(v_self_2056_);
v___x_2105_ = l_Lake_nameToStaticLib(v___x_2104_, v_shouldExport_2052_);
v___x_2106_ = l_Lake_joinRelative(v___x_2103_, v___x_2105_);
v___y_2065_ = v_bootstrap_2089_;
v___y_2066_ = v_a_2099_;
v___y_2067_ = v_a_2098_;
v___y_2068_ = v___x_2096_;
v___y_2069_ = v_a_2085_;
v___y_2070_ = v___x_2106_;
goto v___jp_2064_;
}
else
{
lean_object* v_a_2107_; lean_object* v_a_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v_a_2107_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2107_);
v_a_2108_ = lean_ctor_get(v___x_2097_, 1);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2097_, 2);
v___x_2109_ = l_System_FilePath_normalize(v_buildDir_2090_);
v___x_2110_ = l_Lake_joinRelative(v_dir_2055_, v___x_2109_);
v___x_2111_ = l_System_FilePath_normalize(v_nativeLibDir_2091_);
v___x_2112_ = l_Lake_joinRelative(v___x_2110_, v___x_2111_);
v___x_2113_ = l_Lake_LeanLib_libName(v_self_2056_);
v___x_2114_ = 0;
v___x_2115_ = l_Lake_nameToStaticLib(v___x_2113_, v___x_2114_);
v___x_2116_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_2117_ = l_System_FilePath_addExtension(v___x_2115_, v___x_2116_);
v___x_2118_ = l_Lake_joinRelative(v___x_2112_, v___x_2117_);
v___y_2065_ = v_bootstrap_2089_;
v___y_2066_ = v_a_2108_;
v___y_2067_ = v_a_2107_;
v___y_2068_ = v___x_2096_;
v___y_2069_ = v_a_2085_;
v___y_2070_ = v___x_2118_;
goto v___jp_2064_;
}
}
else
{
lean_object* v_a_2119_; lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v_nativeLibDir_2091_);
lean_dec_ref(v_buildDir_2090_);
lean_dec_ref(v_a_2085_);
lean_dec_ref(v___y_2057_);
lean_dec_ref(v_self_2056_);
lean_dec_ref(v_dir_2055_);
lean_dec(v___x_2054_);
lean_dec(v___x_2048_);
v_a_2119_ = lean_ctor_get(v___x_2097_, 0);
v_a_2120_ = lean_ctor_get(v___x_2097_, 1);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2097_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_inc(v_a_2119_);
lean_dec(v___x_2097_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2119_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
v___jp_2128_:
{
if (lean_obj_tag(v___y_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v_a_2131_; 
v_a_2130_ = lean_ctor_get(v___y_2129_, 0);
lean_inc(v_a_2130_);
v_a_2131_ = lean_ctor_get(v___y_2129_, 1);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___y_2129_, 2);
v_a_2085_ = v_a_2130_;
v_a_2086_ = v_a_2131_;
goto v___jp_2084_;
}
else
{
lean_object* v_a_2132_; lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v___y_2057_);
lean_dec_ref(v_self_2056_);
lean_dec_ref(v_dir_2055_);
lean_dec(v___x_2054_);
lean_dec_ref(v_pkg_2051_);
lean_dec_ref(v_config_2049_);
lean_dec(v___x_2048_);
v_a_2132_ = lean_ctor_get(v___y_2129_, 0);
v_a_2133_ = lean_ctor_get(v___y_2129_, 1);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___y_2129_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___y_2129_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_inc(v_a_2132_);
lean_dec(v___y_2129_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2132_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(lean_object** _args){
lean_object* v___x_2176_ = _args[0];
lean_object* v___x_2177_ = _args[1];
lean_object* v_config_2178_ = _args[2];
lean_object* v_config_2179_ = _args[3];
lean_object* v_pkg_2180_ = _args[4];
lean_object* v_shouldExport_2181_ = _args[5];
lean_object* v___x_2182_ = _args[6];
lean_object* v___x_2183_ = _args[7];
lean_object* v_dir_2184_ = _args[8];
lean_object* v_self_2185_ = _args[9];
lean_object* v___y_2186_ = _args[10];
lean_object* v___y_2187_ = _args[11];
lean_object* v___y_2188_ = _args[12];
lean_object* v___y_2189_ = _args[13];
lean_object* v___y_2190_ = _args[14];
lean_object* v___y_2191_ = _args[15];
lean_object* v___y_2192_ = _args[16];
_start:
{
uint8_t v_shouldExport_boxed_2193_; uint8_t v___x_7358__boxed_2194_; lean_object* v_res_2195_; 
v_shouldExport_boxed_2193_ = lean_unbox(v_shouldExport_2181_);
v___x_7358__boxed_2194_ = lean_unbox(v___x_2182_);
v_res_2195_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v___x_2176_, v___x_2177_, v_config_2178_, v_config_2179_, v_pkg_2180_, v_shouldExport_boxed_2193_, v___x_7358__boxed_2194_, v___x_2183_, v_dir_2184_, v_self_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec(v_config_2179_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object* v___y_2196_, lean_object* v_self_2197_, uint8_t v_shouldExport_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v_toBuildConfig_2205_; lean_object* v_registeredJobs_2206_; uint8_t v_verbosity_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; uint8_t v___x_2210_; uint8_t v___x_2211_; lean_object* v___y_2213_; 
v_toBuildConfig_2205_ = lean_ctor_get(v_a_2202_, 0);
v_registeredJobs_2206_ = lean_ctor_get(v_a_2202_, 3);
v_verbosity_2207_ = lean_ctor_get_uint8(v_toBuildConfig_2205_, sizeof(void*)*3 + 3);
v___x_2208_ = l_Lake_instDataKindFilePath;
v___x_2209_ = 2;
v___x_2210_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2207_, v___x_2209_);
v___x_2211_ = 1;
if (v___x_2210_ == 0)
{
lean_object* v___x_2258_; 
v___x_2258_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_2213_ = v___x_2258_;
goto v___jp_2212_;
}
else
{
if (v_shouldExport_2198_ == 0)
{
lean_object* v___x_2259_; 
v___x_2259_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___y_2213_ = v___x_2259_;
goto v___jp_2212_;
}
else
{
lean_object* v___x_2260_; 
v___x_2260_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_2213_ = v___x_2260_;
goto v___jp_2212_;
}
}
v___jp_2212_:
{
lean_object* v_pkg_2214_; lean_object* v_name_2215_; lean_object* v_config_2216_; lean_object* v_keyName_2217_; lean_object* v_dir_2218_; lean_object* v_config_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___f_2227_; lean_object* v___x_2228_; 
v_pkg_2214_ = lean_ctor_get(v_self_2197_, 0);
lean_inc_ref_n(v_pkg_2214_, 2);
v_name_2215_ = lean_ctor_get(v_self_2197_, 1);
lean_inc_n(v_name_2215_, 2);
v_config_2216_ = lean_ctor_get(v_self_2197_, 2);
lean_inc(v_config_2216_);
v_keyName_2217_ = lean_ctor_get(v_pkg_2214_, 2);
v_dir_2218_ = lean_ctor_get(v_pkg_2214_, 4);
lean_inc_ref(v_dir_2218_);
v_config_2219_ = lean_ctor_get(v_pkg_2214_, 6);
lean_inc_ref(v_config_2219_);
v___x_2220_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_2217_);
v___x_2221_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2221_, 0, v_keyName_2217_);
lean_ctor_set(v___x_2221_, 1, v_name_2215_);
v___x_2222_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_2197_);
v___x_2223_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2221_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
lean_ctor_set(v___x_2223_, 2, v_self_2197_);
lean_ctor_set(v___x_2223_, 3, v___x_2220_);
v___x_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2224_, 0, v_pkg_2214_);
v___x_2225_ = lean_box(v_shouldExport_2198_);
v___x_2226_ = lean_box(v___x_2211_);
v___f_2227_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed), 17, 10);
lean_closure_set(v___f_2227_, 0, v___x_2223_);
lean_closure_set(v___f_2227_, 1, v___x_2224_);
lean_closure_set(v___f_2227_, 2, v_config_2219_);
lean_closure_set(v___f_2227_, 3, v_config_2216_);
lean_closure_set(v___f_2227_, 4, v_pkg_2214_);
lean_closure_set(v___f_2227_, 5, v___x_2225_);
lean_closure_set(v___f_2227_, 6, v___x_2226_);
lean_closure_set(v___f_2227_, 7, v___x_2208_);
lean_closure_set(v___f_2227_, 8, v_dir_2218_);
lean_closure_set(v___f_2227_, 9, v_self_2197_);
v___x_2228_ = l_Lake_ensureJob___redArg(v___x_2208_, v___f_2227_, v___y_2196_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2257_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_a_2230_ = lean_ctor_get(v___x_2228_, 1);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2232_ = v___x_2228_;
v_isShared_2233_ = v_isSharedCheck_2257_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2257_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v_task_2234_; lean_object* v_kind_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2255_; 
v_task_2234_ = lean_ctor_get(v_a_2229_, 0);
v_kind_2235_ = lean_ctor_get(v_a_2229_, 1);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_a_2229_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; 
v_unused_2256_ = lean_ctor_get(v_a_2229_, 2);
lean_dec(v_unused_2256_);
v___x_2237_ = v_a_2229_;
v_isShared_2238_ = v_isSharedCheck_2255_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_kind_2235_);
lean_inc(v_task_2234_);
lean_dec(v_a_2229_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2255_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; lean_object* v_job_2246_; 
v___x_2239_ = lean_st_ref_take(v_registeredJobs_2206_);
v___x_2240_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2215_, v___x_2211_);
v___x_2241_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0));
v___x_2242_ = lean_string_append(v___x_2240_, v___x_2241_);
v___x_2243_ = lean_string_append(v___x_2242_, v___y_2213_);
v___x_2244_ = 0;
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 2, v___x_2243_);
v_job_2246_ = v___x_2237_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_task_2234_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_kind_2235_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v___x_2243_);
v_job_2246_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2252_; 
lean_ctor_set_uint8(v_job_2246_, sizeof(void*)*3, v___x_2244_);
lean_inc_ref(v_job_2246_);
v___x_2247_ = l_Lake_Job_toOpaque___redArg(v_job_2246_);
v___x_2248_ = lean_array_push(v___x_2239_, v___x_2247_);
v___x_2249_ = lean_st_ref_set(v_registeredJobs_2206_, v___x_2248_);
v___x_2250_ = l_Lake_Job_renew___redArg(v_job_2246_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2250_);
v___x_2252_ = v___x_2232_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_a_2230_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
else
{
lean_dec(v_name_2215_);
return v___x_2228_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* v___y_2261_, lean_object* v_self_2262_, lean_object* v_shouldExport_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
uint8_t v_shouldExport_boxed_2270_; lean_object* v_res_2271_; 
v_shouldExport_boxed_2270_ = lean_unbox(v_shouldExport_2263_);
v_res_2271_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2261_, v_self_2262_, v_shouldExport_boxed_2270_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_);
lean_dec_ref(v_a_2267_);
lean_dec(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec(v_a_2264_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* v_x_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
uint8_t v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = 0;
v___x_2281_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2273_, v_x_2272_, v___x_2280_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object* v_x_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec(v___y_2284_);
return v_res_2290_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___f_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___f_2293_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2294_ = 1;
v___x_2295_ = l_Lake_instDataKindFilePath;
v___f_2296_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__0));
v___x_2297_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2298_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v___f_2296_);
lean_ctor_set(v___x_2298_, 2, v___x_2295_);
lean_ctor_set(v___x_2298_, 3, v___f_2293_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*4, v___x_2294_);
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*4 + 1, v___x_2294_);
return v___x_2298_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_obj_once(&l_Lake_LeanLib_staticFacetConfig___closed__2, &l_Lake_LeanLib_staticFacetConfig___closed__2_once, _init_l_Lake_LeanLib_staticFacetConfig___closed__2);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(lean_object* v_a_2300_, lean_object* v_as_2301_, size_t v_i_2302_, size_t v_stop_2303_, lean_object* v_b_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2300_, v_as_2301_, v_i_2302_, v_stop_2303_, v_b_2304_, v___y_2310_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* v_a_2313_, lean_object* v_as_2314_, lean_object* v_i_2315_, lean_object* v_stop_2316_, lean_object* v_b_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
size_t v_i_boxed_2325_; size_t v_stop_boxed_2326_; lean_object* v_res_2327_; 
v_i_boxed_2325_ = lean_unbox_usize(v_i_2315_);
lean_dec(v_i_2315_);
v_stop_boxed_2326_ = lean_unbox_usize(v_stop_2316_);
lean_dec(v_stop_2316_);
v_res_2327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_2313_, v_as_2314_, v_i_boxed_2325_, v_stop_boxed_2326_, v_b_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec_ref(v_as_2314_);
lean_dec(v_a_2313_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* v_x_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
uint8_t v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = 1;
v___x_2337_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2329_, v_x_2328_, v___x_2336_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object* v_x_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec(v___y_2340_);
return v_res_2346_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2348_; uint8_t v___x_2349_; lean_object* v___x_2350_; lean_object* v___f_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___f_2348_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2349_ = 1;
v___x_2350_ = l_Lake_instDataKindFilePath;
v___f_2351_ = ((lean_object*)(l_Lake_LeanLib_staticExportFacetConfig___closed__0));
v___x_2352_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2353_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
lean_ctor_set(v___x_2353_, 1, v___f_2351_);
lean_ctor_set(v___x_2353_, 2, v___x_2350_);
lean_ctor_set(v___x_2353_, 3, v___f_2348_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*4, v___x_2349_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*4 + 1, v___x_2349_);
return v___x_2353_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig(void){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_obj_once(&l_Lake_LeanLib_staticExportFacetConfig___closed__1, &l_Lake_LeanLib_staticExportFacetConfig___closed__1_once, _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1);
return v___x_2354_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0(void){
_start:
{
uint8_t v___x_2355_; lean_object* v_name_2356_; lean_object* v___x_2357_; 
v___x_2355_ = 1;
v_name_2356_ = l_Lake_instDataKindDynlib;
v___x_2357_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2356_, v___x_2355_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object* v_defaultPkg_2358_, lean_object* v_self_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
uint8_t v___x_2367_; lean_object* v___x_2368_; 
v___x_2367_ = 1;
lean_inc_ref_n(v_self_2359_, 2);
v___x_2368_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_2358_, v_self_2359_, v_self_2359_, v___x_2367_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v_snd_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2411_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
v_snd_2370_ = lean_ctor_get(v_a_2369_, 1);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_a_2369_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; 
v_unused_2412_ = lean_ctor_get(v_a_2369_, 0);
lean_dec(v_unused_2412_);
v___x_2372_ = v_a_2369_;
v_isShared_2373_ = v_isSharedCheck_2411_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_snd_2370_);
lean_dec(v_a_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2411_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2409_; 
v_a_2374_ = lean_ctor_get(v___x_2368_, 1);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; 
v_unused_2410_ = lean_ctor_get(v___x_2368_, 0);
lean_dec(v_unused_2410_);
v___x_2376_ = v___x_2368_;
v_isShared_2377_ = v_isSharedCheck_2409_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2368_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2409_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v_kind_2378_; lean_object* v_name_2379_; lean_object* v___y_2381_; uint8_t v___x_2399_; 
v_kind_2378_ = lean_ctor_get(v_snd_2370_, 1);
v_name_2379_ = l_Lake_instDataKindDynlib;
v___x_2399_ = lean_name_eq(v_kind_2378_, v_name_2379_);
if (v___x_2399_ == 0)
{
uint8_t v___x_2400_; 
lean_inc(v_kind_2378_);
lean_del_object(v___x_2372_);
lean_dec(v_snd_2370_);
v___x_2400_ = l_Lean_Name_isAnonymous(v_kind_2378_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2401_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_2402_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2378_, v___x_2367_);
v___x_2403_ = lean_string_append(v___x_2401_, v___x_2402_);
lean_dec_ref(v___x_2402_);
v___x_2404_ = lean_string_append(v___x_2403_, v___x_2401_);
v___y_2381_ = v___x_2404_;
goto v___jp_2380_;
}
else
{
lean_object* v___x_2405_; 
lean_dec(v_kind_2378_);
v___x_2405_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_2381_ = v___x_2405_;
goto v___jp_2380_;
}
}
else
{
lean_object* v___x_2407_; 
lean_del_object(v___x_2376_);
lean_dec_ref(v_self_2359_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 1, v_a_2374_);
lean_ctor_set(v___x_2372_, 0, v_snd_2370_);
v___x_2407_ = v___x_2372_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_snd_2370_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v_a_2374_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
v___jp_2380_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2382_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_2383_ = l_Lake_PartialBuildKey_toString(v_self_2359_);
v___x_2384_ = lean_string_append(v___x_2382_, v___x_2383_);
lean_dec_ref(v___x_2383_);
v___x_2385_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_2386_ = lean_string_append(v___x_2384_, v___x_2385_);
v___x_2387_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0);
v___x_2388_ = lean_string_append(v___x_2386_, v___x_2387_);
v___x_2389_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_2390_ = lean_string_append(v___x_2388_, v___x_2389_);
v___x_2391_ = lean_string_append(v___x_2390_, v___y_2381_);
lean_dec_ref(v___y_2381_);
v___x_2392_ = 3;
v___x_2393_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set_uint8(v___x_2393_, sizeof(void*)*1, v___x_2392_);
v___x_2394_ = lean_array_get_size(v_a_2374_);
v___x_2395_ = lean_array_push(v_a_2374_, v___x_2393_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set_tag(v___x_2376_, 1);
lean_ctor_set(v___x_2376_, 1, v___x_2395_);
lean_ctor_set(v___x_2376_, 0, v___x_2394_);
v___x_2397_ = v___x_2376_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
else
{
lean_object* v_a_2413_; lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec_ref(v_self_2359_);
v_a_2413_ = lean_ctor_get(v___x_2368_, 0);
v_a_2414_ = lean_ctor_get(v___x_2368_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2368_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_inc(v_a_2413_);
lean_dec(v___x_2368_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2413_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* v_defaultPkg_2422_, lean_object* v_self_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_2422_, v_self_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec(v_a_2426_);
lean_dec(v_a_2425_);
return v_res_2431_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0));
v___x_2435_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v___x_2434_);
return v___x_2436_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5(void){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object* v___x_2438_, lean_object* v_as_2439_, size_t v_i_2440_, size_t v_stop_2441_, lean_object* v_b_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
uint8_t v___x_2450_; 
v___x_2450_ = lean_usize_dec_eq(v_i_2440_, v_stop_2441_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = lean_array_uget_borrowed(v_as_2439_, v_i_2440_);
lean_inc_ref(v___y_2443_);
lean_inc(v___x_2451_);
lean_inc_ref(v___x_2438_);
v___x_2452_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_2438_, v___x_2451_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v_a_2454_; lean_object* v___x_2455_; size_t v___x_2456_; size_t v___x_2457_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
v_a_2454_ = lean_ctor_get(v___x_2452_, 1);
lean_inc(v_a_2454_);
lean_dec_ref_known(v___x_2452_, 2);
v___x_2455_ = lean_array_push(v_b_2442_, v_a_2453_);
v___x_2456_ = ((size_t)1ULL);
v___x_2457_ = lean_usize_add(v_i_2440_, v___x_2456_);
v_i_2440_ = v___x_2457_;
v_b_2442_ = v___x_2455_;
v___y_2448_ = v_a_2454_;
goto _start;
}
else
{
lean_object* v_a_2459_; lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec_ref(v___y_2443_);
lean_dec_ref(v_b_2442_);
lean_dec_ref(v___x_2438_);
v_a_2459_ = lean_ctor_get(v___x_2452_, 0);
v_a_2460_ = lean_ctor_get(v___x_2452_, 1);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2452_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_inc(v_a_2459_);
lean_dec(v___x_2452_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2459_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
else
{
lean_object* v___x_2468_; 
lean_dec_ref(v___y_2443_);
lean_dec_ref(v___x_2438_);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v_b_2442_);
lean_ctor_set(v___x_2468_, 1, v___y_2448_);
return v___x_2468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* v___x_2469_, lean_object* v_as_2470_, lean_object* v_i_2471_, lean_object* v_stop_2472_, lean_object* v_b_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
size_t v_i_boxed_2481_; size_t v_stop_boxed_2482_; lean_object* v_res_2483_; 
v_i_boxed_2481_ = lean_unbox_usize(v_i_2471_);
lean_dec(v_i_2471_);
v_stop_boxed_2482_ = lean_unbox_usize(v_stop_2472_);
lean_dec(v_stop_2472_);
v_res_2483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_2469_, v_as_2470_, v_i_boxed_2481_, v_stop_boxed_2482_, v_b_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v_as_2470_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object* v_self_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v_toHashSet_2486_; lean_object* v_toArray_2487_; uint8_t v___x_2488_; 
v_toHashSet_2486_ = lean_ctor_get(v_self_2484_, 0);
v_toArray_2487_ = lean_ctor_get(v_self_2484_, 1);
v___x_2488_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_2486_, v_a_2485_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2498_; 
lean_inc_ref(v_toArray_2487_);
lean_inc_ref(v_toHashSet_2486_);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_self_2484_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; lean_object* v_unused_2500_; 
v_unused_2499_ = lean_ctor_get(v_self_2484_, 1);
lean_dec(v_unused_2499_);
v_unused_2500_ = lean_ctor_get(v_self_2484_, 0);
lean_dec(v_unused_2500_);
v___x_2490_ = v_self_2484_;
v_isShared_2491_ = v_isSharedCheck_2498_;
goto v_resetjp_2489_;
}
else
{
lean_dec(v_self_2484_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2498_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2496_; 
v___x_2492_ = lean_box(0);
lean_inc_ref(v_a_2485_);
v___x_2493_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_toHashSet_2486_, v_a_2485_, v___x_2492_);
v___x_2494_ = lean_array_push(v_toArray_2487_, v_a_2485_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 1, v___x_2494_);
lean_ctor_set(v___x_2490_, 0, v___x_2493_);
v___x_2496_ = v___x_2490_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
else
{
lean_dec_ref(v_a_2485_);
return v_self_2484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object* v_as_2501_, size_t v_i_2502_, size_t v_stop_2503_, lean_object* v_b_2504_){
_start:
{
uint8_t v___x_2505_; 
v___x_2505_ = lean_usize_dec_eq(v_i_2502_, v_stop_2503_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; lean_object* v___x_2507_; size_t v___x_2508_; size_t v___x_2509_; 
v___x_2506_ = lean_array_uget_borrowed(v_as_2501_, v_i_2502_);
lean_inc(v___x_2506_);
v___x_2507_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_2504_, v___x_2506_);
v___x_2508_ = ((size_t)1ULL);
v___x_2509_ = lean_usize_add(v_i_2502_, v___x_2508_);
v_i_2502_ = v___x_2509_;
v_b_2504_ = v___x_2507_;
goto _start;
}
else
{
return v_b_2504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object* v_as_2511_, lean_object* v_i_2512_, lean_object* v_stop_2513_, lean_object* v_b_2514_){
_start:
{
size_t v_i_boxed_2515_; size_t v_stop_boxed_2516_; lean_object* v_res_2517_; 
v_i_boxed_2515_ = lean_unbox_usize(v_i_2512_);
lean_dec(v_i_2512_);
v_stop_boxed_2516_ = lean_unbox_usize(v_stop_2513_);
lean_dec(v_stop_2513_);
v_res_2517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_2511_, v_i_boxed_2515_, v_stop_boxed_2516_, v_b_2514_);
lean_dec_ref(v_as_2511_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object* v_self_2518_, lean_object* v_arr_2519_){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
v___x_2520_ = lean_unsigned_to_nat(0u);
v___x_2521_ = lean_array_get_size(v_arr_2519_);
v___x_2522_ = lean_nat_dec_lt(v___x_2520_, v___x_2521_);
if (v___x_2522_ == 0)
{
return v_self_2518_;
}
else
{
uint8_t v___x_2523_; 
v___x_2523_ = lean_nat_dec_le(v___x_2521_, v___x_2521_);
if (v___x_2523_ == 0)
{
if (v___x_2522_ == 0)
{
return v_self_2518_;
}
else
{
size_t v___x_2524_; size_t v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = ((size_t)0ULL);
v___x_2525_ = lean_usize_of_nat(v___x_2521_);
v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2519_, v___x_2524_, v___x_2525_, v_self_2518_);
return v___x_2526_;
}
}
else
{
size_t v___x_2527_; size_t v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = ((size_t)0ULL);
v___x_2528_ = lean_usize_of_nat(v___x_2521_);
v___x_2529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2519_, v___x_2527_, v___x_2528_, v_self_2518_);
return v___x_2529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(lean_object* v_self_2530_, lean_object* v_arr_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_self_2530_, v_arr_2531_);
lean_dec_ref(v_arr_2531_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(lean_object* v_as_2533_, size_t v_i_2534_, size_t v_stop_2535_, lean_object* v_b_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
uint8_t v___x_2544_; 
v___x_2544_ = lean_usize_dec_eq(v_i_2534_, v_stop_2535_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; lean_object* v_lib_2546_; lean_object* v_pkg_2547_; lean_object* v_name_2548_; lean_object* v_keyName_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2545_ = lean_array_uget_borrowed(v_as_2533_, v_i_2534_);
v_lib_2546_ = lean_ctor_get(v___x_2545_, 0);
v_pkg_2547_ = lean_ctor_get(v_lib_2546_, 0);
v_name_2548_ = lean_ctor_get(v___x_2545_, 1);
v_keyName_2549_ = lean_ctor_get(v_pkg_2547_, 2);
v___x_2550_ = l_Lake_Module_transImportsFacet;
lean_inc(v_name_2548_);
lean_inc(v_keyName_2549_);
v___x_2551_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2551_, 0, v_keyName_2549_);
lean_ctor_set(v___x_2551_, 1, v_name_2548_);
v___x_2552_ = l_Lake_Module_keyword;
lean_inc(v___x_2545_);
v___x_2553_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2551_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
lean_ctor_set(v___x_2553_, 2, v___x_2545_);
lean_ctor_set(v___x_2553_, 3, v___x_2550_);
lean_inc_ref(v___y_2537_);
lean_inc_ref(v___y_2541_);
lean_inc(v___y_2540_);
lean_inc(v___y_2539_);
lean_inc(v___y_2538_);
v___x_2554_ = lean_apply_7(v___y_2537_, v___x_2553_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, lean_box(0));
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; lean_object* v_a_2556_; lean_object* v___x_2557_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
v_a_2556_ = lean_ctor_get(v___x_2554_, 1);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2554_, 2);
v___x_2557_ = l_Lake_Job_await___redArg(v_a_2555_, v_a_2556_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v_a_2559_; lean_object* v___x_2560_; size_t v___x_2561_; size_t v___x_2562_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
v_a_2559_ = lean_ctor_get(v___x_2557_, 1);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2557_, 2);
v___x_2560_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_b_2536_, v_a_2558_);
lean_dec(v_a_2558_);
v___x_2561_ = ((size_t)1ULL);
v___x_2562_ = lean_usize_add(v_i_2534_, v___x_2561_);
v_i_2534_ = v___x_2562_;
v_b_2536_ = v___x_2560_;
v___y_2542_ = v_a_2559_;
goto _start;
}
else
{
lean_object* v_a_2564_; lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref(v___y_2537_);
lean_dec_ref(v_b_2536_);
v_a_2564_ = lean_ctor_get(v___x_2557_, 0);
v_a_2565_ = lean_ctor_get(v___x_2557_, 1);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2557_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_inc(v_a_2564_);
lean_dec(v___x_2557_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2564_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec_ref(v___y_2537_);
lean_dec_ref(v_b_2536_);
v_a_2573_ = lean_ctor_get(v___x_2554_, 0);
v_a_2574_ = lean_ctor_get(v___x_2554_, 1);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2554_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_inc(v_a_2573_);
lean_dec(v___x_2554_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2573_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
else
{
lean_object* v___x_2582_; 
lean_dec_ref(v___y_2537_);
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v_b_2536_);
lean_ctor_set(v___x_2582_, 1, v___y_2542_);
return v___x_2582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object* v_as_2583_, lean_object* v_i_2584_, lean_object* v_stop_2585_, lean_object* v_b_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
size_t v_i_boxed_2594_; size_t v_stop_boxed_2595_; lean_object* v_res_2596_; 
v_i_boxed_2594_ = lean_unbox_usize(v_i_2584_);
lean_dec(v_i_2584_);
v_stop_boxed_2595_ = lean_unbox_usize(v_stop_2585_);
lean_dec(v_stop_2585_);
v_res_2596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_as_2583_, v_i_boxed_2594_, v_stop_boxed_2595_, v_b_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v_as_2583_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(lean_object* v_as_2597_, size_t v_i_2598_, size_t v_stop_2599_, lean_object* v_b_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
uint8_t v___x_2608_; 
v___x_2608_ = lean_usize_dec_eq(v_i_2598_, v_stop_2599_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v_pkg_2610_; lean_object* v_name_2611_; lean_object* v_keyName_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2609_ = lean_array_uget_borrowed(v_as_2597_, v_i_2598_);
v_pkg_2610_ = lean_ctor_get(v___x_2609_, 0);
v_name_2611_ = lean_ctor_get(v___x_2609_, 1);
v_keyName_2612_ = lean_ctor_get(v_pkg_2610_, 2);
v___x_2613_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_2611_);
lean_inc(v_keyName_2612_);
v___x_2614_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2614_, 0, v_keyName_2612_);
lean_ctor_set(v___x_2614_, 1, v_name_2611_);
v___x_2615_ = l_Lake_ExternLib_keyword;
lean_inc(v___x_2609_);
v___x_2616_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2614_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
lean_ctor_set(v___x_2616_, 2, v___x_2609_);
lean_ctor_set(v___x_2616_, 3, v___x_2613_);
lean_inc_ref(v___y_2601_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc(v___y_2603_);
lean_inc(v___y_2602_);
v___x_2617_ = lean_apply_7(v___y_2601_, v___x_2616_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, lean_box(0));
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v_a_2619_; lean_object* v___x_2620_; size_t v___x_2621_; size_t v___x_2622_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
v_a_2619_ = lean_ctor_get(v___x_2617_, 1);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2617_, 2);
v___x_2620_ = lean_array_push(v_b_2600_, v_a_2618_);
v___x_2621_ = ((size_t)1ULL);
v___x_2622_ = lean_usize_add(v_i_2598_, v___x_2621_);
v_i_2598_ = v___x_2622_;
v_b_2600_ = v___x_2620_;
v___y_2606_ = v_a_2619_;
goto _start;
}
else
{
lean_object* v_a_2624_; lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v___y_2601_);
lean_dec_ref(v_b_2600_);
v_a_2624_ = lean_ctor_get(v___x_2617_, 0);
v_a_2625_ = lean_ctor_get(v___x_2617_, 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2617_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_inc(v_a_2624_);
lean_dec(v___x_2617_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2624_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
else
{
lean_object* v___x_2633_; 
lean_dec_ref(v___y_2601_);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v_b_2600_);
lean_ctor_set(v___x_2633_, 1, v___y_2606_);
return v___x_2633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(lean_object* v_as_2634_, lean_object* v_i_2635_, lean_object* v_stop_2636_, lean_object* v_b_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
size_t v_i_boxed_2645_; size_t v_stop_boxed_2646_; lean_object* v_res_2647_; 
v_i_boxed_2645_ = lean_unbox_usize(v_i_2635_);
lean_dec(v_i_2635_);
v_stop_boxed_2646_ = lean_unbox_usize(v_stop_2636_);
lean_dec(v_stop_2636_);
v_res_2647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v_as_2634_, v_i_boxed_2645_, v_stop_boxed_2646_, v_b_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v_as_2634_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(lean_object* v_as_2648_, size_t v_i_2649_, size_t v_stop_2650_, lean_object* v_b_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v_a_2660_; lean_object* v_a_2661_; uint8_t v___x_2665_; 
v___x_2665_ = lean_usize_dec_eq(v_i_2649_, v_stop_2650_);
if (v___x_2665_ == 0)
{
lean_object* v_fst_2666_; lean_object* v_snd_2667_; lean_object* v___x_2668_; lean_object* v_lib_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2706_; 
v_fst_2666_ = lean_ctor_get(v_b_2651_, 0);
v_snd_2667_ = lean_ctor_get(v_b_2651_, 1);
v___x_2668_ = lean_array_uget(v_as_2648_, v_i_2649_);
v_lib_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2706_ == 0)
{
lean_object* v_unused_2707_; 
v_unused_2707_ = lean_ctor_get(v___x_2668_, 1);
lean_dec(v_unused_2707_);
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2706_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_lib_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2706_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v_pkg_2673_; lean_object* v_name_2674_; uint8_t v___x_2675_; 
v_pkg_2673_ = lean_ctor_get(v_lib_2669_, 0);
v_name_2674_ = lean_ctor_get(v_lib_2669_, 1);
lean_inc(v_name_2674_);
v___x_2675_ = l_Lean_NameSet_contains(v_fst_2666_, v_name_2674_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2703_; 
lean_inc(v_snd_2667_);
lean_inc(v_fst_2666_);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_b_2651_);
if (v_isSharedCheck_2703_ == 0)
{
lean_object* v_unused_2704_; lean_object* v_unused_2705_; 
v_unused_2704_ = lean_ctor_get(v_b_2651_, 1);
lean_dec(v_unused_2704_);
v_unused_2705_ = lean_ctor_get(v_b_2651_, 0);
lean_dec(v_unused_2705_);
v___x_2677_ = v_b_2651_;
v_isShared_2678_ = v_isSharedCheck_2703_;
goto v_resetjp_2676_;
}
else
{
lean_dec(v_b_2651_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2703_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v_keyName_2679_; lean_object* v___x_2680_; lean_object* v___x_2682_; 
v_keyName_2679_ = lean_ctor_get(v_pkg_2673_, 2);
v___x_2680_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_2674_);
lean_inc(v_keyName_2679_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set_tag(v___x_2671_, 3);
lean_ctor_set(v___x_2671_, 1, v_name_2674_);
lean_ctor_set(v___x_2671_, 0, v_keyName_2679_);
v___x_2682_ = v___x_2671_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_keyName_2679_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_name_2674_);
v___x_2682_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2684_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2682_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
lean_ctor_set(v___x_2684_, 2, v_lib_2669_);
lean_ctor_set(v___x_2684_, 3, v___x_2680_);
lean_inc_ref(v___y_2652_);
lean_inc_ref(v___y_2656_);
lean_inc(v___y_2655_);
lean_inc(v___y_2654_);
lean_inc(v___y_2653_);
v___x_2685_ = lean_apply_7(v___y_2652_, v___x_2684_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, lean_box(0));
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v_a_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
v_a_2687_ = lean_ctor_get(v___x_2685_, 1);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2685_, 2);
v___x_2688_ = lean_array_push(v_snd_2667_, v_a_2686_);
v___x_2689_ = l_Lean_NameSet_insert(v_fst_2666_, v_name_2674_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 1, v___x_2688_);
lean_ctor_set(v___x_2677_, 0, v___x_2689_);
v___x_2691_ = v___x_2677_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___x_2688_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
v_a_2660_ = v___x_2691_;
v_a_2661_ = v_a_2687_;
goto v___jp_2659_;
}
}
else
{
lean_object* v_a_2693_; lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_del_object(v___x_2677_);
lean_dec(v_name_2674_);
lean_dec(v_snd_2667_);
lean_dec(v_fst_2666_);
lean_dec_ref(v___y_2652_);
v_a_2693_ = lean_ctor_get(v___x_2685_, 0);
v_a_2694_ = lean_ctor_get(v___x_2685_, 1);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2685_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_inc(v_a_2693_);
lean_dec(v___x_2685_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2693_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
}
}
else
{
lean_dec(v_name_2674_);
lean_del_object(v___x_2671_);
lean_dec_ref(v_lib_2669_);
v_a_2660_ = v_b_2651_;
v_a_2661_ = v___y_2657_;
goto v___jp_2659_;
}
}
}
else
{
lean_object* v___x_2708_; 
lean_dec_ref(v___y_2652_);
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v_b_2651_);
lean_ctor_set(v___x_2708_, 1, v___y_2657_);
return v___x_2708_;
}
v___jp_2659_:
{
size_t v___x_2662_; size_t v___x_2663_; 
v___x_2662_ = ((size_t)1ULL);
v___x_2663_ = lean_usize_add(v_i_2649_, v___x_2662_);
v_i_2649_ = v___x_2663_;
v_b_2651_ = v_a_2660_;
v___y_2657_ = v_a_2661_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object* v_as_2709_, lean_object* v_i_2710_, lean_object* v_stop_2711_, lean_object* v_b_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
size_t v_i_boxed_2720_; size_t v_stop_boxed_2721_; lean_object* v_res_2722_; 
v_i_boxed_2720_ = lean_unbox_usize(v_i_2710_);
lean_dec(v_i_2710_);
v_stop_boxed_2721_ = lean_unbox_usize(v_stop_2711_);
lean_dec(v_stop_2711_);
v_res_2722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_as_2709_, v_i_boxed_2720_, v_stop_boxed_2721_, v_b_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v_as_2709_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(lean_object* v___x_2723_, lean_object* v_as_2724_, size_t v_i_2725_, size_t v_stop_2726_, lean_object* v_b_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
uint8_t v___x_2735_; 
v___x_2735_ = lean_usize_dec_eq(v_i_2725_, v_stop_2726_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_array_uget_borrowed(v_as_2724_, v_i_2725_);
lean_inc_ref(v___y_2728_);
lean_inc(v___x_2736_);
lean_inc_ref(v___x_2723_);
v___x_2737_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v___x_2723_, v___x_2736_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v_a_2739_; lean_object* v___x_2740_; size_t v___x_2741_; size_t v___x_2742_; 
v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc(v_a_2738_);
v_a_2739_ = lean_ctor_get(v___x_2737_, 1);
lean_inc(v_a_2739_);
lean_dec_ref_known(v___x_2737_, 2);
v___x_2740_ = lean_array_push(v_b_2727_, v_a_2738_);
v___x_2741_ = ((size_t)1ULL);
v___x_2742_ = lean_usize_add(v_i_2725_, v___x_2741_);
v_i_2725_ = v___x_2742_;
v_b_2727_ = v___x_2740_;
v___y_2733_ = v_a_2739_;
goto _start;
}
else
{
lean_object* v_a_2744_; lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec_ref(v___y_2728_);
lean_dec_ref(v_b_2727_);
lean_dec_ref(v___x_2723_);
v_a_2744_ = lean_ctor_get(v___x_2737_, 0);
v_a_2745_ = lean_ctor_get(v___x_2737_, 1);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2737_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_inc(v_a_2744_);
lean_dec(v___x_2737_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2744_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
else
{
lean_object* v___x_2753_; 
lean_dec_ref(v___y_2728_);
lean_dec_ref(v___x_2723_);
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v_b_2727_);
lean_ctor_set(v___x_2753_, 1, v___y_2733_);
return v___x_2753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object* v___x_2754_, lean_object* v_as_2755_, lean_object* v_i_2756_, lean_object* v_stop_2757_, lean_object* v_b_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
size_t v_i_boxed_2766_; size_t v_stop_boxed_2767_; lean_object* v_res_2768_; 
v_i_boxed_2766_ = lean_unbox_usize(v_i_2756_);
lean_dec(v_i_2756_);
v_stop_boxed_2767_ = lean_unbox_usize(v_stop_2757_);
lean_dec(v_stop_2757_);
v_res_2768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v___x_2754_, v_as_2755_, v_i_boxed_2766_, v_stop_boxed_2767_, v_b_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v_as_2755_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(lean_object* v___x_2769_, lean_object* v_as_2770_, size_t v_i_2771_, size_t v_stop_2772_, lean_object* v_b_2773_){
_start:
{
lean_object* v___y_2775_; uint8_t v___x_2779_; 
v___x_2779_ = lean_usize_dec_eq(v_i_2771_, v_stop_2772_);
if (v___x_2779_ == 0)
{
lean_object* v_toConfigDecl_2780_; lean_object* v_name_2781_; lean_object* v_kind_2782_; lean_object* v_config_2783_; lean_object* v___x_2784_; uint8_t v___x_2785_; 
v_toConfigDecl_2780_ = lean_array_uget_borrowed(v_as_2770_, v_i_2771_);
v_name_2781_ = lean_ctor_get(v_toConfigDecl_2780_, 1);
v_kind_2782_ = lean_ctor_get(v_toConfigDecl_2780_, 2);
v_config_2783_ = lean_ctor_get(v_toConfigDecl_2780_, 3);
v___x_2784_ = l_Lake_ExternLib_keyword;
v___x_2785_ = lean_name_eq(v_kind_2782_, v___x_2784_);
if (v___x_2785_ == 0)
{
v___y_2775_ = v_b_2773_;
goto v___jp_2774_;
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_inc(v_config_2783_);
lean_inc(v_name_2781_);
lean_inc_ref(v___x_2769_);
v___x_2786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2769_);
lean_ctor_set(v___x_2786_, 1, v_name_2781_);
lean_ctor_set(v___x_2786_, 2, v_config_2783_);
v___x_2787_ = lean_array_push(v_b_2773_, v___x_2786_);
v___y_2775_ = v___x_2787_;
goto v___jp_2774_;
}
}
else
{
lean_dec_ref(v___x_2769_);
return v_b_2773_;
}
v___jp_2774_:
{
size_t v___x_2776_; size_t v___x_2777_; 
v___x_2776_ = ((size_t)1ULL);
v___x_2777_ = lean_usize_add(v_i_2771_, v___x_2776_);
v_i_2771_ = v___x_2777_;
v_b_2773_ = v___y_2775_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(lean_object* v___x_2788_, lean_object* v_as_2789_, lean_object* v_i_2790_, lean_object* v_stop_2791_, lean_object* v_b_2792_){
_start:
{
size_t v_i_boxed_2793_; size_t v_stop_boxed_2794_; lean_object* v_res_2795_; 
v_i_boxed_2793_ = lean_unbox_usize(v_i_2790_);
lean_dec(v_i_2790_);
v_stop_boxed_2794_ = lean_unbox_usize(v_stop_2791_);
lean_dec(v_stop_2791_);
v_res_2795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v___x_2788_, v_as_2789_, v_i_boxed_2793_, v_stop_boxed_2794_, v_b_2792_);
lean_dec_ref(v_as_2789_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(lean_object* v_as_2796_, size_t v_i_2797_, size_t v_stop_2798_, lean_object* v_b_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
uint8_t v___x_2807_; 
v___x_2807_ = lean_usize_dec_eq(v_i_2797_, v_stop_2798_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; lean_object* v_lib_2809_; lean_object* v_config_2810_; lean_object* v_nativeFacets_2811_; uint8_t v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; size_t v_sz_2815_; size_t v___x_2816_; lean_object* v___x_2817_; 
v___x_2808_ = lean_array_uget_borrowed(v_as_2796_, v_i_2797_);
v_lib_2809_ = lean_ctor_get(v___x_2808_, 0);
v_config_2810_ = lean_ctor_get(v_lib_2809_, 2);
v_nativeFacets_2811_ = lean_ctor_get(v_config_2810_, 8);
v___x_2812_ = 1;
v___x_2813_ = lean_box(v___x_2812_);
lean_inc_ref(v_nativeFacets_2811_);
v___x_2814_ = lean_apply_1(v_nativeFacets_2811_, v___x_2813_);
v_sz_2815_ = lean_array_size(v___x_2814_);
v___x_2816_ = ((size_t)0ULL);
lean_inc_ref(v___y_2800_);
lean_inc(v___x_2808_);
v___x_2817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2808_, v_sz_2815_, v___x_2816_, v___x_2814_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v_a_2819_; lean_object* v___x_2820_; size_t v___x_2821_; size_t v___x_2822_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
v_a_2819_ = lean_ctor_get(v___x_2817_, 1);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2817_, 2);
v___x_2820_ = l_Array_append___redArg(v_b_2799_, v_a_2818_);
lean_dec(v_a_2818_);
v___x_2821_ = ((size_t)1ULL);
v___x_2822_ = lean_usize_add(v_i_2797_, v___x_2821_);
v_i_2797_ = v___x_2822_;
v_b_2799_ = v___x_2820_;
v___y_2805_ = v_a_2819_;
goto _start;
}
else
{
lean_dec_ref(v___y_2800_);
lean_dec_ref(v_b_2799_);
return v___x_2817_;
}
}
else
{
lean_object* v___x_2824_; 
lean_dec_ref(v___y_2800_);
v___x_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2824_, 0, v_b_2799_);
lean_ctor_set(v___x_2824_, 1, v___y_2805_);
return v___x_2824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object* v_as_2825_, lean_object* v_i_2826_, lean_object* v_stop_2827_, lean_object* v_b_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
size_t v_i_boxed_2836_; size_t v_stop_boxed_2837_; lean_object* v_res_2838_; 
v_i_boxed_2836_ = lean_unbox_usize(v_i_2826_);
lean_dec(v_i_2826_);
v_stop_boxed_2837_ = lean_unbox_usize(v_stop_2827_);
lean_dec(v_stop_2827_);
v_res_2838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_as_2825_, v_i_boxed_2836_, v_stop_boxed_2837_, v_b_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec_ref(v_as_2825_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(lean_object* v___x_2839_, lean_object* v___x_2840_, lean_object* v_self_2841_, lean_object* v_dir_2842_, lean_object* v_targetDecls_2843_, lean_object* v_pkg_2844_, lean_object* v_name_2845_, lean_object* v_config_2846_, lean_object* v_config_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v_a_2863_; lean_object* v_a_2864_; lean_object* v_a_2881_; lean_object* v_a_2882_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v_a_2927_; lean_object* v_a_2928_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v_snd_2964_; lean_object* v_a_2965_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v_a_3004_; lean_object* v_a_3005_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___x_3043_; 
lean_inc_ref(v___y_2848_);
lean_inc_ref(v___y_2852_);
lean_inc(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc(v___x_2840_);
v___x_3043_ = lean_apply_7(v___y_2848_, v___x_2839_, v___x_2840_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, lean_box(0));
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v_a_3045_; lean_object* v___x_3046_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
v_a_3045_ = lean_ctor_get(v___x_3043_, 1);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3043_, 2);
v___x_3046_ = l_Lake_Job_await___redArg(v_a_3044_, v_a_3045_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v_a_3048_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v_a_3059_; lean_object* v_a_3060_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v_a_3094_; lean_object* v_a_3095_; lean_object* v___y_3120_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; uint8_t v___x_3135_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
v_a_3048_ = lean_ctor_get(v___x_3046_, 1);
lean_inc(v_a_3048_);
lean_dec_ref_known(v___x_3046_, 2);
v___x_3132_ = lean_unsigned_to_nat(0u);
v___x_3133_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_3134_ = lean_array_get_size(v_a_3047_);
v___x_3135_ = lean_nat_dec_lt(v___x_3132_, v___x_3134_);
if (v___x_3135_ == 0)
{
v_a_3094_ = v___x_3133_;
v_a_3095_ = v_a_3048_;
goto v___jp_3093_;
}
else
{
uint8_t v___x_3136_; 
v___x_3136_ = lean_nat_dec_le(v___x_3134_, v___x_3134_);
if (v___x_3136_ == 0)
{
if (v___x_3135_ == 0)
{
v_a_3094_ = v___x_3133_;
v_a_3095_ = v_a_3048_;
goto v___jp_3093_;
}
else
{
size_t v___x_3137_; size_t v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = ((size_t)0ULL);
v___x_3138_ = lean_usize_of_nat(v___x_3134_);
lean_inc_ref(v___y_2848_);
v___x_3139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3047_, v___x_3137_, v___x_3138_, v___x_3133_, v___y_2848_, v___x_2840_, v___y_2850_, v___y_2851_, v___y_2852_, v_a_3048_);
v___y_3120_ = v___x_3139_;
goto v___jp_3119_;
}
}
else
{
size_t v___x_3140_; size_t v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = ((size_t)0ULL);
v___x_3141_ = lean_usize_of_nat(v___x_3134_);
lean_inc_ref(v___y_2848_);
v___x_3142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3047_, v___x_3140_, v___x_3141_, v___x_3133_, v___y_2848_, v___x_2840_, v___y_2850_, v___y_2851_, v___y_2852_, v_a_3048_);
v___y_3120_ = v___x_3142_;
goto v___jp_3119_;
}
}
v___jp_3049_:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; 
v___x_3061_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
v___x_3062_ = lean_array_get_size(v_a_3047_);
v___x_3063_ = lean_nat_dec_lt(v___y_3055_, v___x_3062_);
if (v___x_3063_ == 0)
{
lean_dec(v_a_3047_);
v___y_2994_ = v___y_3050_;
v___y_2995_ = v___y_3051_;
v___y_2996_ = v_a_3059_;
v___y_2997_ = v___y_3052_;
v___y_2998_ = v___y_3053_;
v___y_2999_ = v___y_3054_;
v___y_3000_ = v___y_3055_;
v___y_3001_ = v___y_3056_;
v___y_3002_ = v___y_3057_;
v___y_3003_ = v___y_3058_;
v_a_3004_ = v___x_3061_;
v_a_3005_ = v_a_3060_;
goto v___jp_2993_;
}
else
{
uint8_t v___x_3064_; 
v___x_3064_ = lean_nat_dec_le(v___x_3062_, v___x_3062_);
if (v___x_3064_ == 0)
{
if (v___x_3063_ == 0)
{
lean_dec(v_a_3047_);
v___y_2994_ = v___y_3050_;
v___y_2995_ = v___y_3051_;
v___y_2996_ = v_a_3059_;
v___y_2997_ = v___y_3052_;
v___y_2998_ = v___y_3053_;
v___y_2999_ = v___y_3054_;
v___y_3000_ = v___y_3055_;
v___y_3001_ = v___y_3056_;
v___y_3002_ = v___y_3057_;
v___y_3003_ = v___y_3058_;
v_a_3004_ = v___x_3061_;
v_a_3005_ = v_a_3060_;
goto v___jp_2993_;
}
else
{
size_t v___x_3065_; size_t v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = ((size_t)0ULL);
v___x_3066_ = lean_usize_of_nat(v___x_3062_);
lean_inc_ref(v___y_2848_);
v___x_3067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3047_, v___x_3065_, v___x_3066_, v___x_3061_, v___y_2848_, v___x_2840_, v___y_2850_, v___y_2851_, v___y_2852_, v_a_3060_);
lean_dec(v_a_3047_);
v___y_3028_ = v___y_3050_;
v___y_3029_ = v___y_3051_;
v___y_3030_ = v___y_3052_;
v___y_3031_ = v_a_3059_;
v___y_3032_ = v___y_3053_;
v___y_3033_ = v___y_3054_;
v___y_3034_ = v___y_3055_;
v___y_3035_ = v___y_3056_;
v___y_3036_ = v___y_3057_;
v___y_3037_ = v___y_3058_;
v___y_3038_ = v___x_3067_;
goto v___jp_3027_;
}
}
else
{
size_t v___x_3068_; size_t v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = ((size_t)0ULL);
v___x_3069_ = lean_usize_of_nat(v___x_3062_);
lean_inc_ref(v___y_2848_);
v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3047_, v___x_3068_, v___x_3069_, v___x_3061_, v___y_2848_, v___x_2840_, v___y_2850_, v___y_2851_, v___y_2852_, v_a_3060_);
lean_dec(v_a_3047_);
v___y_3028_ = v___y_3050_;
v___y_3029_ = v___y_3051_;
v___y_3030_ = v___y_3052_;
v___y_3031_ = v_a_3059_;
v___y_3032_ = v___y_3053_;
v___y_3033_ = v___y_3054_;
v___y_3034_ = v___y_3055_;
v___y_3035_ = v___y_3056_;
v___y_3036_ = v___y_3057_;
v___y_3037_ = v___y_3058_;
v___y_3038_ = v___x_3070_;
goto v___jp_3027_;
}
}
}
v___jp_3071_:
{
if (lean_obj_tag(v___y_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v_a_3083_; 
v_a_3082_ = lean_ctor_get(v___y_3081_, 0);
lean_inc(v_a_3082_);
v_a_3083_ = lean_ctor_get(v___y_3081_, 1);
lean_inc(v_a_3083_);
lean_dec_ref_known(v___y_3081_, 2);
v___y_3050_ = v___y_3072_;
v___y_3051_ = v___y_3073_;
v___y_3052_ = v___y_3074_;
v___y_3053_ = v___y_3075_;
v___y_3054_ = v___y_3076_;
v___y_3055_ = v___y_3077_;
v___y_3056_ = v___y_3078_;
v___y_3057_ = v___y_3079_;
v___y_3058_ = v___y_3080_;
v_a_3059_ = v_a_3082_;
v_a_3060_ = v_a_3083_;
goto v___jp_3049_;
}
else
{
lean_object* v_a_3084_; lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec_ref(v___y_3078_);
lean_dec_ref(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec_ref(v___y_3072_);
lean_dec(v_a_3047_);
lean_dec_ref(v___y_2848_);
lean_dec(v_name_2845_);
lean_dec_ref(v_pkg_2844_);
lean_dec_ref(v_dir_2842_);
lean_dec_ref(v_self_2841_);
lean_dec(v___x_2840_);
v_a_3084_ = lean_ctor_get(v___y_3081_, 0);
v_a_3085_ = lean_ctor_get(v___y_3081_, 1);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___y_3081_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___y_3081_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_inc(v_a_3084_);
lean_dec(v___y_3081_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3084_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
v___jp_3093_:
{
lean_object* v_toLeanConfig_3096_; lean_object* v_toLeanConfig_3097_; lean_object* v_buildDir_3098_; lean_object* v_nativeLibDir_3099_; lean_object* v_moreLinkObjs_3100_; lean_object* v_moreLinkLibs_3101_; lean_object* v_moreLinkArgs_3102_; lean_object* v_weakLinkArgs_3103_; lean_object* v_moreLinkObjs_3104_; lean_object* v_moreLinkLibs_3105_; lean_object* v_moreLinkArgs_3106_; lean_object* v_weakLinkArgs_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v_toLeanConfig_3096_ = lean_ctor_get(v_config_2846_, 1);
lean_inc_ref(v_toLeanConfig_3096_);
v_toLeanConfig_3097_ = lean_ctor_get(v_config_2847_, 0);
v_buildDir_3098_ = lean_ctor_get(v_config_2846_, 5);
lean_inc_ref(v_buildDir_3098_);
v_nativeLibDir_3099_ = lean_ctor_get(v_config_2846_, 7);
lean_inc_ref(v_nativeLibDir_3099_);
lean_dec_ref(v_config_2846_);
v_moreLinkObjs_3100_ = lean_ctor_get(v_toLeanConfig_3096_, 6);
lean_inc_ref(v_moreLinkObjs_3100_);
v_moreLinkLibs_3101_ = lean_ctor_get(v_toLeanConfig_3096_, 7);
lean_inc_ref(v_moreLinkLibs_3101_);
v_moreLinkArgs_3102_ = lean_ctor_get(v_toLeanConfig_3096_, 8);
lean_inc_ref(v_moreLinkArgs_3102_);
v_weakLinkArgs_3103_ = lean_ctor_get(v_toLeanConfig_3096_, 9);
lean_inc_ref(v_weakLinkArgs_3103_);
lean_dec_ref(v_toLeanConfig_3096_);
v_moreLinkObjs_3104_ = lean_ctor_get(v_toLeanConfig_3097_, 6);
v_moreLinkLibs_3105_ = lean_ctor_get(v_toLeanConfig_3097_, 7);
v_moreLinkArgs_3106_ = lean_ctor_get(v_toLeanConfig_3097_, 8);
v_weakLinkArgs_3107_ = lean_ctor_get(v_toLeanConfig_3097_, 9);
v___x_3108_ = l_Array_append___redArg(v_moreLinkObjs_3100_, v_moreLinkObjs_3104_);
v___x_3109_ = lean_unsigned_to_nat(0u);
v___x_3110_ = lean_array_get_size(v___x_3108_);
v___x_3111_ = lean_nat_dec_lt(v___x_3109_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_dec_ref(v___x_3108_);
v___y_3050_ = v_nativeLibDir_3099_;
v___y_3051_ = v_weakLinkArgs_3107_;
v___y_3052_ = v_moreLinkArgs_3102_;
v___y_3053_ = v_weakLinkArgs_3103_;
v___y_3054_ = v_buildDir_3098_;
v___y_3055_ = v___x_3109_;
v___y_3056_ = v_moreLinkLibs_3101_;
v___y_3057_ = v_moreLinkArgs_3106_;
v___y_3058_ = v_moreLinkLibs_3105_;
v_a_3059_ = v_a_3094_;
v_a_3060_ = v_a_3095_;
goto v___jp_3049_;
}
else
{
uint8_t v___x_3112_; 
v___x_3112_ = lean_nat_dec_le(v___x_3110_, v___x_3110_);
if (v___x_3112_ == 0)
{
if (v___x_3111_ == 0)
{
lean_dec_ref(v___x_3108_);
v___y_3050_ = v_nativeLibDir_3099_;
v___y_3051_ = v_weakLinkArgs_3107_;
v___y_3052_ = v_moreLinkArgs_3102_;
v___y_3053_ = v_weakLinkArgs_3103_;
v___y_3054_ = v_buildDir_3098_;
v___y_3055_ = v___x_3109_;
v___y_3056_ = v_moreLinkLibs_3101_;
v___y_3057_ = v_moreLinkArgs_3106_;
v___y_3058_ = v_moreLinkLibs_3105_;
v_a_3059_ = v_a_3094_;
v_a_3060_ = v_a_3095_;
goto v___jp_3049_;
}
else
{
size_t v___x_3113_; size_t v___x_3114_; lean_object* v___x_3115_; 
v___x_3113_ = ((size_t)0ULL);
v___x_3114_ = lean_usize_of_nat(v___x_3110_);
lean_inc_ref(v___y_2848_);
lean_inc_ref(v_pkg_2844_);
v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2844_, v___x_3108_, v___x_3113_, v___x_3114_, v_a_3094_, v___y_2848_, v___x_2840_, v___y_2850_, v___y_2851_, v___y_2852_, v_a_3095_);
lean_dec_ref(v___x_3108_);
v___y_3072_ = v_nativeLibDir_3099_;
v___y_3073_ = v_weakLinkArgs_3107_;
v___y_3074_ = v_moreLinkArgs_3102_;
v___y_3075_ = v_weakLinkArgs_3103_;
v___y_3076_ = v_buildDir_3098_;
v___y_3077_ = v___x_3109_;
v___y_3078_ = v_moreLinkLibs_3101_;
v___y_3079_ = v_moreLinkArgs_3106_;
v___y_3080_ = v_moreLinkLibs_3105_;
v___y_3081_ = v___x_3115_;
goto v___jp_3071_;
}
}
else
{
size_t v___x_3116_; size_t v___x_3117_; lean_object* v___x_3118_; 
v___x_3116_ = ((size_t)0ULL);
v___x_3117_ = lean_usize_of_nat(v___x_3110_);
lean_inc_ref(v___y_2848_);
lean_inc_ref(v_pkg_2844_);
v___x_3118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2844_, v___x_3108_, v___x_3116_, v___x_3117_, v_a_3094_, v___y_2848_, v___x_2840_, v___y_2850_, v___y_2851_, v___y_2852_, v_a_3095_);
lean_dec_ref(v___x_3108_);
v___y_3072_ = v_nativeLibDir_3099_;
v___y_3073_ = v_weakLinkArgs_3107_;
v___y_3074_ = v_moreLinkArgs_3102_;
v___y_3075_ = v_weakLinkArgs_3103_;
v___y_3076_ = v_buildDir_3098_;
v___y_3077_ = v___x_3109_;
v___y_3078_ = v_moreLinkLibs_3101_;
v___y_3079_ = v_moreLinkArgs_3106_;
v___y_3080_ = v_moreLinkLibs_3105_;
v___y_3081_ = v___x_3118_;
goto v___jp_3071_;
}
}
}
v___jp_3119_:
{
if (lean_obj_tag(v___y_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v_a_3122_; 
v_a_3121_ = lean_ctor_get(v___y_3120_, 0);
lean_inc(v_a_3121_);
v_a_3122_ = lean_ctor_get(v___y_3120_, 1);
lean_inc(v_a_3122_);
lean_dec_ref_known(v___y_3120_, 2);
v_a_3094_ = v_a_3121_;
v_a_3095_ = v_a_3122_;
goto v___jp_3093_;
}
else
{
lean_object* v_a_3123_; lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec(v_a_3047_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_config_2846_);
lean_dec(v_name_2845_);
lean_dec_ref(v_pkg_2844_);
lean_dec_ref(v_dir_2842_);
lean_dec_ref(v_self_2841_);
lean_dec(v___x_2840_);
v_a_3123_ = lean_ctor_get(v___y_3120_, 0);
v_a_3124_ = lean_ctor_get(v___y_3120_, 1);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___y_3120_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___y_3120_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_inc(v_a_3123_);
lean_dec(v___y_3120_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3123_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
}
else
{
lean_object* v_a_3143_; lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_config_2846_);
lean_dec(v_name_2845_);
lean_dec_ref(v_pkg_2844_);
lean_dec_ref(v_dir_2842_);
lean_dec_ref(v_self_2841_);
lean_dec(v___x_2840_);
v_a_3143_ = lean_ctor_get(v___x_3046_, 0);
v_a_3144_ = lean_ctor_get(v___x_3046_, 1);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3046_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_inc(v_a_3143_);
lean_dec(v___x_3046_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3143_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_config_2846_);
lean_dec(v_name_2845_);
lean_dec_ref(v_pkg_2844_);
lean_dec_ref(v_dir_2842_);
lean_dec_ref(v_self_2841_);
lean_dec(v___x_2840_);
v_a_3152_ = lean_ctor_get(v___x_3043_, 0);
v_a_3153_ = lean_ctor_get(v___x_3043_, 1);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_3043_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_inc(v_a_3152_);
lean_dec(v___x_3043_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3152_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_a_3153_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
v___jp_2855_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; uint8_t v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; 
lean_inc_ref(v_self_2841_);
v___x_2865_ = l_Lake_LeanLib_libName(v_self_2841_);
v___x_2866_ = l_System_FilePath_normalize(v___y_2861_);
v___x_2867_ = l_Lake_joinRelative(v_dir_2842_, v___x_2866_);
v___x_2868_ = l_System_FilePath_normalize(v___y_2856_);
v___x_2869_ = l_Lake_joinRelative(v___x_2867_, v___x_2868_);
v___x_2870_ = 0;
v___x_2871_ = l_Lake_nameToSharedLib(v___x_2865_, v___x_2870_);
v___x_2872_ = l_Lake_joinRelative(v___x_2869_, v___x_2871_);
v___x_2873_ = l_Array_append___redArg(v___y_2860_, v___y_2857_);
v___x_2874_ = l_Array_append___redArg(v___y_2859_, v___y_2862_);
v___x_2875_ = l_Lake_LeanLib_isPlugin(v_self_2841_);
v___x_2876_ = l_System_Platform_isWindows;
v___x_2877_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2878_ = l_Lake_buildLeanSharedLib(v___x_2865_, v___x_2872_, v___y_2858_, v_a_2863_, v___x_2873_, v___x_2874_, v___x_2875_, v___x_2876_, v___y_2848_, v___x_2840_, v___y_2850_, v___y_2851_, v___y_2852_, v___x_2877_);
lean_dec(v___x_2840_);
lean_dec_ref(v___y_2858_);
v___x_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
lean_ctor_set(v___x_2879_, 1, v_a_2864_);
return v___x_2879_;
}
v___jp_2880_:
{
lean_object* v___x_2883_; 
v___x_2883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2883_, 0, v_a_2881_);
lean_ctor_set(v___x_2883_, 1, v_a_2882_);
return v___x_2883_;
}
v___jp_2884_:
{
if (lean_obj_tag(v___y_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v_a_2894_; 
v_a_2893_ = lean_ctor_get(v___y_2892_, 0);
lean_inc(v_a_2893_);
v_a_2894_ = lean_ctor_get(v___y_2892_, 1);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___y_2892_, 2);
v___y_2856_ = v___y_2885_;
v___y_2857_ = v___y_2886_;
v___y_2858_ = v___y_2888_;
v___y_2859_ = v___y_2887_;
v___y_2860_ = v___y_2889_;
v___y_2861_ = v___y_2890_;
v___y_2862_ = v___y_2891_;
v_a_2863_ = v_a_2893_;
v_a_2864_ = v_a_2894_;
goto v___jp_2855_;
}
else
{
lean_object* v_a_2895_; lean_object* v_a_2896_; 
lean_dec_ref(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec_ref(v___y_2885_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_dir_2842_);
lean_dec_ref(v_self_2841_);
lean_dec(v___x_2840_);
v_a_2895_ = lean_ctor_get(v___y_2892_, 0);
lean_inc(v_a_2895_);
v_a_2896_ = lean_ctor_get(v___y_2892_, 1);
lean_inc(v_a_2896_);
lean_dec_ref_known(v___y_2892_, 2);
v_a_2881_ = v_a_2895_;
v_a_2882_ = v_a_2896_;
goto v___jp_2880_;
}
}
v___jp_2897_:
{
lean_object* v___x_2909_; uint8_t v___x_2910_; 
v___x_2909_ = lean_array_get_size(v___y_2908_);
v___x_2910_ = lean_nat_dec_lt(v___y_2905_, v___x_2909_);
if (v___x_2910_ == 0)
{
lean_dec_ref(v___y_2908_);
v___y_2856_ = v___y_2898_;
v___y_2857_ = v___y_2899_;
v___y_2858_ = v___y_2902_;
v___y_2859_ = v___y_2901_;
v___y_2860_ = v___y_2903_;
v___y_2861_ = v___y_2904_;
v___y_2862_ = v___y_2907_;
v_a_2863_ = v___y_2900_;
v_a_2864_ = v___y_2906_;
goto v___jp_2855_;
}
else
{
uint8_t v___x_2911_; 
v___x_2911_ = lean_nat_dec_le(v___x_2909_, v___x_2909_);
if (v___x_2911_ == 0)
{
if (v___x_2910_ == 0)
{
lean_dec_ref(v___y_2908_);
v___y_2856_ = v___y_2898_;
v___y_2857_ = v___y_2899_;
v___y_2858_ = v___y_2902_;
v___y_2859_ = v___y_2901_;
v___y_2860_ = v___y_2903_;
v___y_2861_ = v___y_2904_;
v___y_2862_ = v___y_2907_;
v_a_2863_ = v___y_2900_;
v_a_2864_ = v___y_2906_;
goto v___jp_2855_;
}
else
{
size_t v___x_2912_; size_t v___x_2913_; lean_object* v___x_2914_; 
v___x_2912_ = ((size_t)0ULL);
v___x_2913_ = lean_usize_of_nat(v___x_2909_);
lean_inc_ref(v___y_2848_);
v___x_2914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2908_, v___x_2912_, v___x_2913_, v___y_2900_, v___y_2848_, v___x_2840_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2906_);
lean_dec_ref(v___y_2908_);
v___y_2885_ = v___y_2898_;
v___y_2886_ = v___y_2899_;
v___y_2887_ = v___y_2901_;
v___y_2888_ = v___y_2902_;
v___y_2889_ = v___y_2903_;
v___y_2890_ = v___y_2904_;
v___y_2891_ = v___y_2907_;
v___y_2892_ = v___x_2914_;
goto v___jp_2884_;
}
}
else
{
size_t v___x_2915_; size_t v___x_2916_; lean_object* v___x_2917_; 
v___x_2915_ = ((size_t)0ULL);
v___x_2916_ = lean_usize_of_nat(v___x_2909_);
lean_inc_ref(v___y_2848_);
v___x_2917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2908_, v___x_2915_, v___x_2916_, v___y_2900_, v___y_2848_, v___x_2840_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2906_);
lean_dec_ref(v___y_2908_);
v___y_2885_ = v___y_2898_;
v___y_2886_ = v___y_2899_;
v___y_2887_ = v___y_2901_;
v___y_2888_ = v___y_2902_;
v___y_2889_ = v___y_2903_;
v___y_2890_ = v___y_2904_;
v___y_2891_ = v___y_2907_;
v___y_2892_ = v___x_2917_;
goto v___jp_2884_;
}
}
}
v___jp_2918_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2929_ = lean_mk_empty_array_with_capacity(v___y_2925_);
v___x_2930_ = lean_array_get_size(v_targetDecls_2843_);
v___x_2931_ = lean_nat_dec_lt(v___y_2925_, v___x_2930_);
if (v___x_2931_ == 0)
{
lean_dec_ref(v_pkg_2844_);
v___y_2898_ = v___y_2919_;
v___y_2899_ = v___y_2920_;
v___y_2900_ = v_a_2927_;
v___y_2901_ = v___y_2922_;
v___y_2902_ = v___y_2921_;
v___y_2903_ = v___y_2923_;
v___y_2904_ = v___y_2924_;
v___y_2905_ = v___y_2925_;
v___y_2906_ = v_a_2928_;
v___y_2907_ = v___y_2926_;
v___y_2908_ = v___x_2929_;
goto v___jp_2897_;
}
else
{
uint8_t v___x_2932_; 
v___x_2932_ = lean_nat_dec_le(v___x_2930_, v___x_2930_);
if (v___x_2932_ == 0)
{
if (v___x_2931_ == 0)
{
lean_dec_ref(v_pkg_2844_);
v___y_2898_ = v___y_2919_;
v___y_2899_ = v___y_2920_;
v___y_2900_ = v_a_2927_;
v___y_2901_ = v___y_2922_;
v___y_2902_ = v___y_2921_;
v___y_2903_ = v___y_2923_;
v___y_2904_ = v___y_2924_;
v___y_2905_ = v___y_2925_;
v___y_2906_ = v_a_2928_;
v___y_2907_ = v___y_2926_;
v___y_2908_ = v___x_2929_;
goto v___jp_2897_;
}
else
{
size_t v___x_2933_; size_t v___x_2934_; lean_object* v___x_2935_; 
v___x_2933_ = ((size_t)0ULL);
v___x_2934_ = lean_usize_of_nat(v___x_2930_);
v___x_2935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2844_, v_targetDecls_2843_, v___x_2933_, v___x_2934_, v___x_2929_);
v___y_2898_ = v___y_2919_;
v___y_2899_ = v___y_2920_;
v___y_2900_ = v_a_2927_;
v___y_2901_ = v___y_2922_;
v___y_2902_ = v___y_2921_;
v___y_2903_ = v___y_2923_;
v___y_2904_ = v___y_2924_;
v___y_2905_ = v___y_2925_;
v___y_2906_ = v_a_2928_;
v___y_2907_ = v___y_2926_;
v___y_2908_ = v___x_2935_;
goto v___jp_2897_;
}
}
else
{
size_t v___x_2936_; size_t v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = ((size_t)0ULL);
v___x_2937_ = lean_usize_of_nat(v___x_2930_);
v___x_2938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2844_, v_targetDecls_2843_, v___x_2936_, v___x_2937_, v___x_2929_);
v___y_2898_ = v___y_2919_;
v___y_2899_ = v___y_2920_;
v___y_2900_ = v_a_2927_;
v___y_2901_ = v___y_2922_;
v___y_2902_ = v___y_2921_;
v___y_2903_ = v___y_2923_;
v___y_2904_ = v___y_2924_;
v___y_2905_ = v___y_2925_;
v___y_2906_ = v_a_2928_;
v___y_2907_ = v___y_2926_;
v___y_2908_ = v___x_2938_;
goto v___jp_2897_;
}
}
}
v___jp_2939_:
{
if (lean_obj_tag(v___y_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v_a_2950_; 
v_a_2949_ = lean_ctor_get(v___y_2948_, 0);
lean_inc(v_a_2949_);
v_a_2950_ = lean_ctor_get(v___y_2948_, 1);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___y_2948_, 2);
v___y_2919_ = v___y_2940_;
v___y_2920_ = v___y_2941_;
v___y_2921_ = v___y_2943_;
v___y_2922_ = v___y_2942_;
v___y_2923_ = v___y_2944_;
v___y_2924_ = v___y_2945_;
v___y_2925_ = v___y_2946_;
v___y_2926_ = v___y_2947_;
v_a_2927_ = v_a_2949_;
v_a_2928_ = v_a_2950_;
goto v___jp_2918_;
}
else
{
lean_object* v_a_2951_; lean_object* v_a_2952_; 
lean_dec_ref(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec_ref(v___y_2940_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_pkg_2844_);
lean_dec_ref(v_dir_2842_);
lean_dec_ref(v_self_2841_);
lean_dec(v___x_2840_);
v_a_2951_ = lean_ctor_get(v___y_2948_, 0);
lean_inc(v_a_2951_);
v_a_2952_ = lean_ctor_get(v___y_2948_, 1);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___y_2948_, 2);
v_a_2881_ = v_a_2951_;
v_a_2882_ = v_a_2952_;
goto v___jp_2880_;
}
}
v___jp_2953_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; 
v___x_2966_ = l_Array_append___redArg(v___y_2961_, v___y_2963_);
v___x_2967_ = lean_array_get_size(v___x_2966_);
v___x_2968_ = lean_nat_dec_lt(v___y_2960_, v___x_2967_);
if (v___x_2968_ == 0)
{
lean_dec_ref(v___x_2966_);
v___y_2919_ = v___y_2954_;
v___y_2920_ = v___y_2955_;
v___y_2921_ = v___y_2957_;
v___y_2922_ = v___y_2956_;
v___y_2923_ = v___y_2958_;
v___y_2924_ = v___y_2959_;
v___y_2925_ = v___y_2960_;
v___y_2926_ = v___y_2962_;
v_a_2927_ = v_snd_2964_;
v_a_2928_ = v_a_2965_;
goto v___jp_2918_;
}
else
{
uint8_t v___x_2969_; 
v___x_2969_ = lean_nat_dec_le(v___x_2967_, v___x_2967_);
if (v___x_2969_ == 0)
{
if (v___x_2968_ == 0)
{
lean_dec_ref(v___x_2966_);
v___y_2919_ = v___y_2954_;
v___y_2920_ = v___y_2955_;
v___y_2921_ = v___y_2957_;
v___y_2922_ = v___y_2956_;
v___y_2923_ = v___y_2958_;
v___y_2924_ = v___y_2959_;
v___y_2925_ = v___y_2960_;
v___y_2926_ = v___y_2962_;
v_a_2927_ = v_snd_2964_;
v_a_2928_ = v_a_2965_;
goto v___jp_2918_;
}
else
{
size_t v___x_2970_; size_t v___x_2971_; lean_object* v___x_2972_; 
v___x_2970_ = ((size_t)0ULL);
v___x_2971_ = lean_usize_of_nat(v___x_2967_);
lean_inc_ref(v___y_2848_);
lean_inc_ref(v_pkg_2844_);
v___x_2972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2844_, v___x_2966_, v___x_2970_, v___x_2971_, v_snd_2964_, v___y_2848_, v___x_2840_, v___y_2850_, v___y_2851_, v___y_2852_, v_a_2965_);
lean_dec_ref(v___x_2966_);
v___y_2940_ = v___y_2954_;
v___y_2941_ = v___y_2955_;
v___y_2942_ = v___y_2956_;
v___y_2943_ = v___y_2957_;
v___y_2944_ = v___y_2958_;
v___y_2945_ = v___y_2959_;
v___y_2946_ = v___y_2960_;
v___y_2947_ = v___y_2962_;
v___y_2948_ = v___x_2972_;
goto v___jp_2939_;
}
}
else
{
size_t v___x_2973_; size_t v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = ((size_t)0ULL);
v___x_2974_ = lean_usize_of_nat(v___x_2967_);
lean_inc_ref(v___y_2848_);
lean_inc_ref(v_pkg_2844_);
v___x_2975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2844_, v___x_2966_, v___x_2973_, v___x_2974_, v_snd_2964_, v___y_2848_, v___x_2840_, v___y_2850_, v___y_2851_, v___y_2852_, v_a_2965_);
lean_dec_ref(v___x_2966_);
v___y_2940_ = v___y_2954_;
v___y_2941_ = v___y_2955_;
v___y_2942_ = v___y_2956_;
v___y_2943_ = v___y_2957_;
v___y_2944_ = v___y_2958_;
v___y_2945_ = v___y_2959_;
v___y_2946_ = v___y_2960_;
v___y_2947_ = v___y_2962_;
v___y_2948_ = v___x_2975_;
goto v___jp_2939_;
}
}
}
v___jp_2976_:
{
if (lean_obj_tag(v___y_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v_a_2989_; lean_object* v_snd_2990_; 
v_a_2988_ = lean_ctor_get(v___y_2987_, 0);
lean_inc(v_a_2988_);
v_a_2989_ = lean_ctor_get(v___y_2987_, 1);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___y_2987_, 2);
v_snd_2990_ = lean_ctor_get(v_a_2988_, 1);
lean_inc(v_snd_2990_);
lean_dec(v_a_2988_);
v___y_2954_ = v___y_2977_;
v___y_2955_ = v___y_2978_;
v___y_2956_ = v___y_2980_;
v___y_2957_ = v___y_2979_;
v___y_2958_ = v___y_2981_;
v___y_2959_ = v___y_2982_;
v___y_2960_ = v___y_2983_;
v___y_2961_ = v___y_2984_;
v___y_2962_ = v___y_2985_;
v___y_2963_ = v___y_2986_;
v_snd_2964_ = v_snd_2990_;
v_a_2965_ = v_a_2989_;
goto v___jp_2953_;
}
else
{
lean_object* v_a_2991_; lean_object* v_a_2992_; 
lean_dec_ref(v___y_2984_);
lean_dec_ref(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec_ref(v___y_2977_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_pkg_2844_);
lean_dec_ref(v_dir_2842_);
lean_dec_ref(v_self_2841_);
lean_dec(v___x_2840_);
v_a_2991_ = lean_ctor_get(v___y_2987_, 0);
lean_inc(v_a_2991_);
v_a_2992_ = lean_ctor_get(v___y_2987_, 1);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___y_2987_, 2);
v_a_2881_ = v_a_2991_;
v_a_2882_ = v_a_2992_;
goto v___jp_2880_;
}
}
v___jp_2993_:
{
lean_object* v_toArray_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3025_; 
v_toArray_3006_ = lean_ctor_get(v_a_3004_, 1);
v_isSharedCheck_3025_ = !lean_is_exclusive(v_a_3004_);
if (v_isSharedCheck_3025_ == 0)
{
lean_object* v_unused_3026_; 
v_unused_3026_ = lean_ctor_get(v_a_3004_, 0);
lean_dec(v_unused_3026_);
v___x_3008_ = v_a_3004_;
v_isShared_3009_ = v_isSharedCheck_3025_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_toArray_3006_);
lean_dec(v_a_3004_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3025_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3010_ = lean_mk_empty_array_with_capacity(v___y_3000_);
v___x_3011_ = lean_array_get_size(v_toArray_3006_);
v___x_3012_ = lean_nat_dec_lt(v___y_3000_, v___x_3011_);
if (v___x_3012_ == 0)
{
lean_del_object(v___x_3008_);
lean_dec_ref(v_toArray_3006_);
lean_dec(v_name_2845_);
v___y_2954_ = v___y_2994_;
v___y_2955_ = v___y_2995_;
v___y_2956_ = v___y_2997_;
v___y_2957_ = v___y_2996_;
v___y_2958_ = v___y_2998_;
v___y_2959_ = v___y_2999_;
v___y_2960_ = v___y_3000_;
v___y_2961_ = v___y_3001_;
v___y_2962_ = v___y_3002_;
v___y_2963_ = v___y_3003_;
v_snd_2964_ = v___x_3010_;
v_a_2965_ = v_a_3005_;
goto v___jp_2953_;
}
else
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3016_; 
v___x_3013_ = l_Lean_NameSet_empty;
v___x_3014_ = l_Lean_NameSet_insert(v___x_3013_, v_name_2845_);
lean_inc_ref(v___x_3010_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 1, v___x_3010_);
lean_ctor_set(v___x_3008_, 0, v___x_3014_);
v___x_3016_ = v___x_3008_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v___x_3014_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v___x_3010_);
v___x_3016_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
uint8_t v___x_3017_; 
v___x_3017_ = lean_nat_dec_le(v___x_3011_, v___x_3011_);
if (v___x_3017_ == 0)
{
if (v___x_3012_ == 0)
{
lean_dec_ref(v___x_3016_);
lean_dec_ref(v_toArray_3006_);
v___y_2954_ = v___y_2994_;
v___y_2955_ = v___y_2995_;
v___y_2956_ = v___y_2997_;
v___y_2957_ = v___y_2996_;
v___y_2958_ = v___y_2998_;
v___y_2959_ = v___y_2999_;
v___y_2960_ = v___y_3000_;
v___y_2961_ = v___y_3001_;
v___y_2962_ = v___y_3002_;
v___y_2963_ = v___y_3003_;
v_snd_2964_ = v___x_3010_;
v_a_2965_ = v_a_3005_;
goto v___jp_2953_;
}
else
{
size_t v___x_3018_; size_t v___x_3019_; lean_object* v___x_3020_; 
lean_dec_ref(v___x_3010_);
v___x_3018_ = ((size_t)0ULL);
v___x_3019_ = lean_usize_of_nat(v___x_3011_);
lean_inc_ref(v___y_2848_);
v___x_3020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_3006_, v___x_3018_, v___x_3019_, v___x_3016_, v___y_2848_, v___x_2840_, v___y_2850_, v___y_2851_, v___y_2852_, v_a_3005_);
lean_dec_ref(v_toArray_3006_);
v___y_2977_ = v___y_2994_;
v___y_2978_ = v___y_2995_;
v___y_2979_ = v___y_2996_;
v___y_2980_ = v___y_2997_;
v___y_2981_ = v___y_2998_;
v___y_2982_ = v___y_2999_;
v___y_2983_ = v___y_3000_;
v___y_2984_ = v___y_3001_;
v___y_2985_ = v___y_3002_;
v___y_2986_ = v___y_3003_;
v___y_2987_ = v___x_3020_;
goto v___jp_2976_;
}
}
else
{
size_t v___x_3021_; size_t v___x_3022_; lean_object* v___x_3023_; 
lean_dec_ref(v___x_3010_);
v___x_3021_ = ((size_t)0ULL);
v___x_3022_ = lean_usize_of_nat(v___x_3011_);
lean_inc_ref(v___y_2848_);
v___x_3023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_3006_, v___x_3021_, v___x_3022_, v___x_3016_, v___y_2848_, v___x_2840_, v___y_2850_, v___y_2851_, v___y_2852_, v_a_3005_);
lean_dec_ref(v_toArray_3006_);
v___y_2977_ = v___y_2994_;
v___y_2978_ = v___y_2995_;
v___y_2979_ = v___y_2996_;
v___y_2980_ = v___y_2997_;
v___y_2981_ = v___y_2998_;
v___y_2982_ = v___y_2999_;
v___y_2983_ = v___y_3000_;
v___y_2984_ = v___y_3001_;
v___y_2985_ = v___y_3002_;
v___y_2986_ = v___y_3003_;
v___y_2987_ = v___x_3023_;
goto v___jp_2976_;
}
}
}
}
}
v___jp_3027_:
{
if (lean_obj_tag(v___y_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v_a_3040_; 
v_a_3039_ = lean_ctor_get(v___y_3038_, 0);
lean_inc(v_a_3039_);
v_a_3040_ = lean_ctor_get(v___y_3038_, 1);
lean_inc(v_a_3040_);
lean_dec_ref_known(v___y_3038_, 2);
v___y_2994_ = v___y_3028_;
v___y_2995_ = v___y_3029_;
v___y_2996_ = v___y_3031_;
v___y_2997_ = v___y_3030_;
v___y_2998_ = v___y_3032_;
v___y_2999_ = v___y_3033_;
v___y_3000_ = v___y_3034_;
v___y_3001_ = v___y_3035_;
v___y_3002_ = v___y_3036_;
v___y_3003_ = v___y_3037_;
v_a_3004_ = v_a_3039_;
v_a_3005_ = v_a_3040_;
goto v___jp_2993_;
}
else
{
lean_object* v_a_3041_; lean_object* v_a_3042_; 
lean_dec_ref(v___y_3035_);
lean_dec_ref(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec_ref(v___y_3028_);
lean_dec_ref(v___y_2848_);
lean_dec(v_name_2845_);
lean_dec_ref(v_pkg_2844_);
lean_dec_ref(v_dir_2842_);
lean_dec_ref(v_self_2841_);
lean_dec(v___x_2840_);
v_a_3041_ = lean_ctor_get(v___y_3038_, 0);
lean_inc(v_a_3041_);
v_a_3042_ = lean_ctor_get(v___y_3038_, 1);
lean_inc(v_a_3042_);
lean_dec_ref_known(v___y_3038_, 2);
v_a_2881_ = v_a_3041_;
v_a_2882_ = v_a_3042_;
goto v___jp_2880_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* v___x_3161_, lean_object* v___x_3162_, lean_object* v_self_3163_, lean_object* v_dir_3164_, lean_object* v_targetDecls_3165_, lean_object* v_pkg_3166_, lean_object* v_name_3167_, lean_object* v_config_3168_, lean_object* v_config_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v___x_3161_, v___x_3162_, v_self_3163_, v_dir_3164_, v_targetDecls_3165_, v_pkg_3166_, v_name_3167_, v_config_3168_, v_config_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec(v_config_3169_);
lean_dec_ref(v_targetDecls_3165_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object* v_self_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_){
_start:
{
lean_object* v_pkg_3187_; lean_object* v_name_3188_; lean_object* v_config_3189_; lean_object* v_keyName_3190_; lean_object* v_dir_3191_; lean_object* v_config_3192_; lean_object* v_targetDecls_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___f_3200_; lean_object* v___x_3201_; 
v_pkg_3187_ = lean_ctor_get(v_self_3179_, 0);
lean_inc_ref_n(v_pkg_3187_, 2);
v_name_3188_ = lean_ctor_get(v_self_3179_, 1);
lean_inc_n(v_name_3188_, 3);
v_config_3189_ = lean_ctor_get(v_self_3179_, 2);
lean_inc(v_config_3189_);
v_keyName_3190_ = lean_ctor_get(v_pkg_3187_, 2);
v_dir_3191_ = lean_ctor_get(v_pkg_3187_, 4);
lean_inc_ref(v_dir_3191_);
v_config_3192_ = lean_ctor_get(v_pkg_3187_, 6);
lean_inc_ref(v_config_3192_);
v_targetDecls_3193_ = lean_ctor_get(v_pkg_3187_, 15);
lean_inc_ref(v_targetDecls_3193_);
v___x_3194_ = l_Lake_instDataKindDynlib;
v___x_3195_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_3190_);
v___x_3196_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3196_, 0, v_keyName_3190_);
lean_ctor_set(v___x_3196_, 1, v_name_3188_);
v___x_3197_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3179_);
v___x_3198_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3196_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
lean_ctor_set(v___x_3198_, 2, v_self_3179_);
lean_ctor_set(v___x_3198_, 3, v___x_3195_);
v___x_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3199_, 0, v_pkg_3187_);
v___f_3200_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3200_, 0, v___x_3198_);
lean_closure_set(v___f_3200_, 1, v___x_3199_);
lean_closure_set(v___f_3200_, 2, v_self_3179_);
lean_closure_set(v___f_3200_, 3, v_dir_3191_);
lean_closure_set(v___f_3200_, 4, v_targetDecls_3193_);
lean_closure_set(v___f_3200_, 5, v_pkg_3187_);
lean_closure_set(v___f_3200_, 6, v_name_3188_);
lean_closure_set(v___f_3200_, 7, v_config_3192_);
lean_closure_set(v___f_3200_, 8, v_config_3189_);
v___x_3201_ = l_Lake_ensureJob___redArg(v___x_3194_, v___f_3200_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3231_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
v_a_3203_ = lean_ctor_get(v___x_3201_, 1);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3205_ = v___x_3201_;
v_isShared_3206_ = v_isSharedCheck_3231_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_inc(v_a_3202_);
lean_dec(v___x_3201_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3231_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v_task_3207_; lean_object* v_kind_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3229_; 
v_task_3207_ = lean_ctor_get(v_a_3202_, 0);
v_kind_3208_ = lean_ctor_get(v_a_3202_, 1);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_a_3202_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v_a_3202_, 2);
lean_dec(v_unused_3230_);
v___x_3210_ = v_a_3202_;
v_isShared_3211_ = v_isSharedCheck_3229_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_kind_3208_);
lean_inc(v_task_3207_);
lean_dec(v_a_3202_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3229_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v_registeredJobs_3212_; lean_object* v___x_3213_; uint8_t v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; uint8_t v___x_3218_; lean_object* v_job_3220_; 
v_registeredJobs_3212_ = lean_ctor_get(v_a_3184_, 3);
v___x_3213_ = lean_st_ref_take(v_registeredJobs_3212_);
v___x_3214_ = 1;
v___x_3215_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3188_, v___x_3214_);
v___x_3216_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0));
v___x_3217_ = lean_string_append(v___x_3215_, v___x_3216_);
v___x_3218_ = 0;
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 2, v___x_3217_);
v_job_3220_ = v___x_3210_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_task_3207_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v_kind_3208_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v___x_3217_);
v_job_3220_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
lean_ctor_set_uint8(v_job_3220_, sizeof(void*)*3, v___x_3218_);
lean_inc_ref(v_job_3220_);
v___x_3221_ = l_Lake_Job_toOpaque___redArg(v_job_3220_);
v___x_3222_ = lean_array_push(v___x_3213_, v___x_3221_);
v___x_3223_ = lean_st_ref_set(v_registeredJobs_3212_, v___x_3222_);
v___x_3224_ = l_Lake_Job_renew___redArg(v_job_3220_);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v___x_3224_);
v___x_3226_ = v___x_3205_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_a_3203_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
}
else
{
lean_dec(v_name_3188_);
return v___x_3201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object* v_self_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
lean_dec_ref(v_a_3237_);
lean_dec(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec(v_a_3234_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t v_fmt_3241_, lean_object* v_a_3242_){
_start:
{
if (v_fmt_3241_ == 0)
{
lean_object* v_path_3243_; 
v_path_3243_ = lean_ctor_get(v_a_3242_, 0);
lean_inc_ref(v_path_3243_);
return v_path_3243_;
}
else
{
lean_object* v_path_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v_path_3244_ = lean_ctor_get(v_a_3242_, 0);
lean_inc_ref(v_path_3244_);
v___x_3245_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3245_, 0, v_path_3244_);
v___x_3246_ = l_Lean_Json_compress(v___x_3245_);
return v___x_3246_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* v_fmt_3247_, lean_object* v_a_3248_){
_start:
{
uint8_t v_fmt_boxed_3249_; lean_object* v_res_3250_; 
v_fmt_boxed_3249_ = lean_unbox(v_fmt_3247_);
v_res_3250_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_boxed_3249_, v_a_3248_);
lean_dec_ref(v_a_3248_);
return v_res_3250_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3253_; uint8_t v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___f_3253_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__0));
v___x_3254_ = 1;
v___x_3255_ = l_Lake_instDataKindDynlib;
v___x_3256_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__1));
v___x_3257_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3258_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
lean_ctor_set(v___x_3258_, 1, v___x_3256_);
lean_ctor_set(v___x_3258_, 2, v___x_3255_);
lean_ctor_set(v___x_3258_, 3, v___f_3253_);
lean_ctor_set_uint8(v___x_3258_, sizeof(void*)*4, v___x_3254_);
lean_ctor_set_uint8(v___x_3258_, sizeof(void*)*4 + 1, v___x_3254_);
return v___x_3258_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = lean_obj_once(&l_Lake_LeanLib_sharedFacetConfig___closed__2, &l_Lake_LeanLib_sharedFacetConfig___closed__2_once, _init_l_Lake_LeanLib_sharedFacetConfig___closed__2);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* v___x_3260_, lean_object* v_as_3261_, size_t v_sz_3262_, size_t v_i_3263_, lean_object* v_b_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
uint8_t v___x_3272_; 
v___x_3272_ = lean_usize_dec_lt(v_i_3263_, v_sz_3262_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; 
lean_dec_ref(v___y_3265_);
lean_dec_ref(v___x_3260_);
v___x_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3273_, 0, v_b_3264_);
lean_ctor_set(v___x_3273_, 1, v___y_3270_);
return v___x_3273_;
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3275_; 
v_a_3274_ = lean_array_uget_borrowed(v_as_3261_, v_i_3263_);
lean_inc_ref(v___y_3265_);
lean_inc_n(v_a_3274_, 2);
lean_inc_ref(v___x_3260_);
v___x_3275_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v___x_3260_, v_a_3274_, v_a_3274_, v___x_3272_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v_a_3277_; lean_object* v_snd_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; size_t v___x_3281_; size_t v___x_3282_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3276_);
v_a_3277_ = lean_ctor_get(v___x_3275_, 1);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3275_, 2);
v_snd_3278_ = lean_ctor_get(v_a_3276_, 1);
lean_inc(v_snd_3278_);
lean_dec(v_a_3276_);
v___x_3279_ = l_Lake_Job_toOpaque___redArg(v_snd_3278_);
v___x_3280_ = l_Lake_Job_mix___redArg(v_b_3264_, v___x_3279_);
v___x_3281_ = ((size_t)1ULL);
v___x_3282_ = lean_usize_add(v_i_3263_, v___x_3281_);
v_i_3263_ = v___x_3282_;
v_b_3264_ = v___x_3280_;
v___y_3270_ = v_a_3277_;
goto _start;
}
else
{
lean_object* v_a_3284_; lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec_ref(v___y_3265_);
lean_dec_ref(v_b_3264_);
lean_dec_ref(v___x_3260_);
v_a_3284_ = lean_ctor_get(v___x_3275_, 0);
v_a_3285_ = lean_ctor_get(v___x_3275_, 1);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3275_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_inc(v_a_3284_);
lean_dec(v___x_3275_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3284_);
lean_ctor_set(v_reuseFailAlloc_3291_, 1, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* v___x_3293_, lean_object* v_as_3294_, lean_object* v_sz_3295_, lean_object* v_i_3296_, lean_object* v_b_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
size_t v_sz_boxed_3305_; size_t v_i_boxed_3306_; lean_object* v_res_3307_; 
v_sz_boxed_3305_ = lean_unbox_usize(v_sz_3295_);
lean_dec(v_sz_3295_);
v_i_boxed_3306_ = lean_unbox_usize(v_i_3296_);
lean_dec(v_i_3296_);
v_res_3307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_3293_, v_as_3294_, v_sz_boxed_3305_, v_i_boxed_3306_, v_b_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v_as_3294_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* v___x_3308_, lean_object* v_as_3309_, size_t v_sz_3310_, size_t v_i_3311_, lean_object* v_b_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
uint8_t v___x_3320_; 
v___x_3320_ = lean_usize_dec_lt(v_i_3311_, v_sz_3310_);
if (v___x_3320_ == 0)
{
lean_object* v___x_3321_; 
lean_dec_ref(v___y_3313_);
lean_dec_ref(v___x_3308_);
v___x_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3321_, 0, v_b_3312_);
lean_ctor_set(v___x_3321_, 1, v___y_3318_);
return v___x_3321_;
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3323_; 
v_a_3322_ = lean_array_uget_borrowed(v_as_3309_, v_i_3311_);
lean_inc_ref(v___y_3313_);
lean_inc(v_a_3322_);
lean_inc_ref(v___x_3308_);
v___x_3323_ = l_Lake_Package_fetchTargetJob(v___x_3308_, v_a_3322_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v_a_3325_; lean_object* v___x_3326_; size_t v___x_3327_; size_t v___x_3328_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
v_a_3325_ = lean_ctor_get(v___x_3323_, 1);
lean_inc(v_a_3325_);
lean_dec_ref_known(v___x_3323_, 2);
v___x_3326_ = l_Lake_Job_mix___redArg(v_b_3312_, v_a_3324_);
v___x_3327_ = ((size_t)1ULL);
v___x_3328_ = lean_usize_add(v_i_3311_, v___x_3327_);
v_i_3311_ = v___x_3328_;
v_b_3312_ = v___x_3326_;
v___y_3318_ = v_a_3325_;
goto _start;
}
else
{
lean_object* v_a_3330_; lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
lean_dec_ref(v___y_3313_);
lean_dec_ref(v_b_3312_);
lean_dec_ref(v___x_3308_);
v_a_3330_ = lean_ctor_get(v___x_3323_, 0);
v_a_3331_ = lean_ctor_get(v___x_3323_, 1);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3323_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_inc(v_a_3330_);
lean_dec(v___x_3323_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3330_);
lean_ctor_set(v_reuseFailAlloc_3337_, 1, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* v___x_3339_, lean_object* v_as_3340_, lean_object* v_sz_3341_, lean_object* v_i_3342_, lean_object* v_b_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
size_t v_sz_boxed_3351_; size_t v_i_boxed_3352_; lean_object* v_res_3353_; 
v_sz_boxed_3351_ = lean_unbox_usize(v_sz_3341_);
lean_dec(v_sz_3341_);
v_i_boxed_3352_ = lean_unbox_usize(v_i_3342_);
lean_dec(v_i_3342_);
v_res_3353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_3339_, v_as_3340_, v_sz_boxed_3351_, v_i_boxed_3352_, v_b_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec_ref(v_as_3340_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object* v_self_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_){
_start:
{
lean_object* v_pkg_3364_; lean_object* v_name_3365_; lean_object* v_config_3366_; lean_object* v_baseName_3367_; lean_object* v_keyName_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v_pkg_3364_ = lean_ctor_get(v_self_3356_, 0);
lean_inc_ref_n(v_pkg_3364_, 2);
v_name_3365_ = lean_ctor_get(v_self_3356_, 1);
lean_inc(v_name_3365_);
v_config_3366_ = lean_ctor_get(v_self_3356_, 2);
lean_inc(v_config_3366_);
lean_dec_ref(v_self_3356_);
v_baseName_3367_ = lean_ctor_get(v_pkg_3364_, 1);
v_keyName_3368_ = lean_ctor_get(v_pkg_3364_, 2);
v___x_3369_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_3368_);
v___x_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3370_, 0, v_keyName_3368_);
v___x_3371_ = l_Lake_Package_keyword;
v___x_3372_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3370_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
lean_ctor_set(v___x_3372_, 2, v_pkg_3364_);
lean_ctor_set(v___x_3372_, 3, v___x_3369_);
lean_inc_ref(v_a_3357_);
lean_inc_ref(v_a_3361_);
lean_inc(v_a_3360_);
lean_inc(v_a_3359_);
lean_inc(v_a_3358_);
v___x_3373_ = lean_apply_7(v_a_3357_, v___x_3372_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, lean_box(0));
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3411_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
v_a_3375_ = lean_ctor_get(v___x_3373_, 1);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3377_ = v___x_3373_;
v_isShared_3378_ = v_isSharedCheck_3411_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_inc(v_a_3374_);
lean_dec(v___x_3373_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3411_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v_needs_3383_; lean_object* v_extraDepTargets_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; uint8_t v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3398_; 
v___x_3379_ = 1;
lean_inc(v_baseName_3367_);
v___x_3380_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3367_, v___x_3379_);
v___x_3381_ = lean_unsigned_to_nat(0u);
v___x_3382_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v_needs_3383_ = lean_ctor_get(v_config_3366_, 5);
lean_inc_ref(v_needs_3383_);
v_extraDepTargets_3384_ = lean_ctor_get(v_config_3366_, 6);
lean_inc_ref(v_extraDepTargets_3384_);
lean_dec(v_config_3366_);
v___x_3385_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0));
v___x_3386_ = lean_string_append(v___x_3380_, v___x_3385_);
v___x_3387_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3365_, v___x_3379_);
v___x_3388_ = lean_string_append(v___x_3386_, v___x_3387_);
lean_dec_ref(v___x_3387_);
v___x_3389_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1));
v___x_3390_ = lean_string_append(v___x_3388_, v___x_3389_);
v___x_3391_ = 0;
v___x_3392_ = 0;
v___x_3393_ = l_Lake_BuildTrace_nil(v___x_3390_);
v___x_3394_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3394_, 0, v___x_3382_);
lean_ctor_set(v___x_3394_, 1, v___x_3393_);
lean_ctor_set(v___x_3394_, 2, v___x_3381_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*3, v___x_3391_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*3 + 1, v___x_3392_);
v___x_3395_ = lean_box(0);
v___x_3396_ = lean_box(0);
if (v_isShared_3378_ == 0)
{
lean_ctor_set(v___x_3377_, 1, v___x_3394_);
lean_ctor_set(v___x_3377_, 0, v___x_3396_);
v___x_3398_ = v___x_3377_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3396_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v___x_3394_);
v___x_3398_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v_job_3401_; lean_object* v___x_3402_; size_t v_sz_3403_; size_t v___x_3404_; lean_object* v___x_3405_; 
v___x_3399_ = lean_task_pure(v___x_3398_);
v___x_3400_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v_job_3401_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_3401_, 0, v___x_3399_);
lean_ctor_set(v_job_3401_, 1, v___x_3395_);
lean_ctor_set(v_job_3401_, 2, v___x_3400_);
lean_ctor_set_uint8(v_job_3401_, sizeof(void*)*3, v___x_3392_);
v___x_3402_ = l_Lake_Job_mix___redArg(v_job_3401_, v_a_3374_);
v_sz_3403_ = lean_array_size(v_extraDepTargets_3384_);
v___x_3404_ = ((size_t)0ULL);
lean_inc_ref(v_a_3357_);
lean_inc_ref(v_pkg_3364_);
v___x_3405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_3364_, v_extraDepTargets_3384_, v_sz_3403_, v___x_3404_, v___x_3402_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3375_);
lean_dec_ref(v_extraDepTargets_3384_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v_a_3407_; size_t v_sz_3408_; lean_object* v___x_3409_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
v_a_3407_ = lean_ctor_get(v___x_3405_, 1);
lean_inc(v_a_3407_);
lean_dec_ref_known(v___x_3405_, 2);
v_sz_3408_ = lean_array_size(v_needs_3383_);
v___x_3409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_3364_, v_needs_3383_, v_sz_3408_, v___x_3404_, v_a_3406_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3407_);
lean_dec_ref(v_needs_3383_);
return v___x_3409_;
}
else
{
lean_dec_ref(v_needs_3383_);
lean_dec_ref(v_pkg_3364_);
lean_dec_ref(v_a_3357_);
return v___x_3405_;
}
}
}
}
else
{
lean_dec(v_config_3366_);
lean_dec(v_name_3365_);
lean_dec_ref(v_pkg_3364_);
lean_dec_ref(v_a_3357_);
return v___x_3373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object* v_self_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
lean_dec_ref(v_a_3417_);
lean_dec(v_a_3416_);
lean_dec(v_a_3415_);
lean_dec(v_a_3414_);
return v_res_3420_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3422_; uint8_t v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___f_3422_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3423_ = 1;
v___x_3424_ = l_Lake_instDataKindUnit;
v___x_3425_ = ((lean_object*)(l_Lake_LeanLib_extraDepFacetConfig___closed__0));
v___x_3426_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3427_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
lean_ctor_set(v___x_3427_, 1, v___x_3425_);
lean_ctor_set(v___x_3427_, 2, v___x_3424_);
lean_ctor_set(v___x_3427_, 3, v___f_3422_);
lean_ctor_set_uint8(v___x_3427_, sizeof(void*)*4, v___x_3423_);
lean_ctor_set_uint8(v___x_3427_, sizeof(void*)*4 + 1, v___x_3423_);
return v___x_3427_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_3428_; 
v___x_3428_ = lean_obj_once(&l_Lake_LeanLib_extraDepFacetConfig___closed__1, &l_Lake_LeanLib_extraDepFacetConfig___closed__1_once, _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* v_self_3429_, size_t v_sz_3430_, size_t v_i_3431_, lean_object* v_bs_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
uint8_t v___x_3440_; 
v___x_3440_ = lean_usize_dec_lt(v_i_3431_, v_sz_3430_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; 
lean_dec_ref(v___y_3433_);
lean_dec_ref(v_self_3429_);
v___x_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3441_, 0, v_bs_3432_);
lean_ctor_set(v___x_3441_, 1, v___y_3438_);
return v___x_3441_;
}
else
{
lean_object* v_pkg_3442_; lean_object* v_name_3443_; lean_object* v_keyName_3444_; lean_object* v_v_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v_pkg_3442_ = lean_ctor_get(v_self_3429_, 0);
v_name_3443_ = lean_ctor_get(v_self_3429_, 1);
v_keyName_3444_ = lean_ctor_get(v_pkg_3442_, 2);
v_v_3445_ = lean_array_uget_borrowed(v_bs_3432_, v_i_3431_);
lean_inc(v_name_3443_);
lean_inc(v_keyName_3444_);
v___x_3446_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3446_, 0, v_keyName_3444_);
lean_ctor_set(v___x_3446_, 1, v_name_3443_);
v___x_3447_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc(v_v_3445_);
lean_inc_ref(v_self_3429_);
v___x_3448_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3446_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
lean_ctor_set(v___x_3448_, 2, v_self_3429_);
lean_ctor_set(v___x_3448_, 3, v_v_3445_);
lean_inc_ref(v___y_3433_);
lean_inc_ref(v___y_3437_);
lean_inc(v___y_3436_);
lean_inc(v___y_3435_);
lean_inc(v___y_3434_);
v___x_3449_ = lean_apply_7(v___y_3433_, v___x_3448_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, lean_box(0));
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v_a_3451_; lean_object* v___x_3452_; lean_object* v_bs_x27_3453_; lean_object* v___x_3454_; size_t v___x_3455_; size_t v___x_3456_; lean_object* v___x_3457_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
v_a_3451_ = lean_ctor_get(v___x_3449_, 1);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3449_, 2);
v___x_3452_ = lean_unsigned_to_nat(0u);
v_bs_x27_3453_ = lean_array_uset(v_bs_3432_, v_i_3431_, v___x_3452_);
v___x_3454_ = l_Lake_Job_toOpaque___redArg(v_a_3450_);
v___x_3455_ = ((size_t)1ULL);
v___x_3456_ = lean_usize_add(v_i_3431_, v___x_3455_);
v___x_3457_ = lean_array_uset(v_bs_x27_3453_, v_i_3431_, v___x_3454_);
v_i_3431_ = v___x_3456_;
v_bs_3432_ = v___x_3457_;
v___y_3438_ = v_a_3451_;
goto _start;
}
else
{
lean_object* v_a_3459_; lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec_ref(v___y_3433_);
lean_dec_ref(v_bs_3432_);
lean_dec_ref(v_self_3429_);
v_a_3459_ = lean_ctor_get(v___x_3449_, 0);
v_a_3460_ = lean_ctor_get(v___x_3449_, 1);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3449_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_inc(v_a_3459_);
lean_dec(v___x_3449_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3459_);
lean_ctor_set(v_reuseFailAlloc_3466_, 1, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* v_self_3468_, lean_object* v_sz_3469_, lean_object* v_i_3470_, lean_object* v_bs_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
size_t v_sz_boxed_3479_; size_t v_i_boxed_3480_; lean_object* v_res_3481_; 
v_sz_boxed_3479_ = lean_unbox_usize(v_sz_3469_);
lean_dec(v_sz_3469_);
v_i_boxed_3480_ = lean_unbox_usize(v_i_3470_);
lean_dec(v_i_3470_);
v_res_3481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3468_, v_sz_boxed_3479_, v_i_boxed_3480_, v_bs_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec(v___y_3473_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object* v_self_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_){
_start:
{
lean_object* v_config_3491_; lean_object* v_defaultFacets_3492_; size_t v_sz_3493_; size_t v___x_3494_; lean_object* v___x_3495_; 
v_config_3491_ = lean_ctor_get(v_self_3483_, 2);
v_defaultFacets_3492_ = lean_ctor_get(v_config_3491_, 7);
lean_inc_ref(v_defaultFacets_3492_);
v_sz_3493_ = lean_array_size(v_defaultFacets_3492_);
v___x_3494_ = ((size_t)0ULL);
v___x_3495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3483_, v_sz_3493_, v___x_3494_, v_defaultFacets_3492_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3506_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
v_a_3497_ = lean_ctor_get(v___x_3495_, 1);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3499_ = v___x_3495_;
v_isShared_3500_ = v_isSharedCheck_3506_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_inc(v_a_3496_);
lean_dec(v___x_3495_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3506_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3504_; 
v___x_3501_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0));
v___x_3502_ = l_Lake_Job_mixArray___redArg(v_a_3496_, v___x_3501_);
lean_dec(v_a_3496_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3502_);
v___x_3504_ = v___x_3499_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_a_3497_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
else
{
lean_object* v_a_3507_; lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
v_a_3507_ = lean_ctor_get(v___x_3495_, 0);
v_a_3508_ = lean_ctor_get(v___x_3495_, 1);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3495_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_inc(v_a_3507_);
lean_dec(v___x_3495_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3507_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object* v_self_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
lean_dec_ref(v_a_3521_);
lean_dec(v_a_3520_);
lean_dec(v_a_3519_);
lean_dec(v_a_3518_);
return v_res_3524_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3526_; uint8_t v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___f_3526_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3527_ = 1;
v___x_3528_ = l_Lake_instDataKindUnit;
v___x_3529_ = ((lean_object*)(l_Lake_LeanLib_defaultFacetConfig___closed__0));
v___x_3530_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3531_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3531_, 0, v___x_3530_);
lean_ctor_set(v___x_3531_, 1, v___x_3529_);
lean_ctor_set(v___x_3531_, 2, v___x_3528_);
lean_ctor_set(v___x_3531_, 3, v___f_3526_);
lean_ctor_set_uint8(v___x_3531_, sizeof(void*)*4, v___x_3527_);
lean_ctor_set_uint8(v___x_3531_, sizeof(void*)*4 + 1, v___x_3527_);
return v___x_3531_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = lean_obj_once(&l_Lake_LeanLib_defaultFacetConfig___closed__1, &l_Lake_LeanLib_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanLib_defaultFacetConfig___closed__1);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_3533_, lean_object* v_v_3534_, lean_object* v_t_3535_){
_start:
{
if (lean_obj_tag(v_t_3535_) == 0)
{
lean_object* v_size_3536_; lean_object* v_k_3537_; lean_object* v_v_3538_; lean_object* v_l_3539_; lean_object* v_r_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3820_; 
v_size_3536_ = lean_ctor_get(v_t_3535_, 0);
v_k_3537_ = lean_ctor_get(v_t_3535_, 1);
v_v_3538_ = lean_ctor_get(v_t_3535_, 2);
v_l_3539_ = lean_ctor_get(v_t_3535_, 3);
v_r_3540_ = lean_ctor_get(v_t_3535_, 4);
v_isSharedCheck_3820_ = !lean_is_exclusive(v_t_3535_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3542_ = v_t_3535_;
v_isShared_3543_ = v_isSharedCheck_3820_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_r_3540_);
lean_inc(v_l_3539_);
lean_inc(v_v_3538_);
lean_inc(v_k_3537_);
lean_inc(v_size_3536_);
lean_dec(v_t_3535_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3820_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
uint8_t v___x_3544_; 
v___x_3544_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3533_, v_k_3537_);
switch(v___x_3544_)
{
case 0:
{
lean_object* v_impl_3545_; lean_object* v___x_3546_; 
lean_dec(v_size_3536_);
v_impl_3545_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3533_, v_v_3534_, v_l_3539_);
v___x_3546_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3540_) == 0)
{
lean_object* v_size_3547_; lean_object* v_size_3548_; lean_object* v_k_3549_; lean_object* v_v_3550_; lean_object* v_l_3551_; lean_object* v_r_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; uint8_t v___x_3555_; 
v_size_3547_ = lean_ctor_get(v_r_3540_, 0);
v_size_3548_ = lean_ctor_get(v_impl_3545_, 0);
lean_inc(v_size_3548_);
v_k_3549_ = lean_ctor_get(v_impl_3545_, 1);
lean_inc(v_k_3549_);
v_v_3550_ = lean_ctor_get(v_impl_3545_, 2);
lean_inc(v_v_3550_);
v_l_3551_ = lean_ctor_get(v_impl_3545_, 3);
lean_inc(v_l_3551_);
v_r_3552_ = lean_ctor_get(v_impl_3545_, 4);
lean_inc(v_r_3552_);
v___x_3553_ = lean_unsigned_to_nat(3u);
v___x_3554_ = lean_nat_mul(v___x_3553_, v_size_3547_);
v___x_3555_ = lean_nat_dec_lt(v___x_3554_, v_size_3548_);
lean_dec(v___x_3554_);
if (v___x_3555_ == 0)
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3559_; 
lean_dec(v_r_3552_);
lean_dec(v_l_3551_);
lean_dec(v_v_3550_);
lean_dec(v_k_3549_);
v___x_3556_ = lean_nat_add(v___x_3546_, v_size_3548_);
lean_dec(v_size_3548_);
v___x_3557_ = lean_nat_add(v___x_3556_, v_size_3547_);
lean_dec(v___x_3556_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 3, v_impl_3545_);
lean_ctor_set(v___x_3542_, 0, v___x_3557_);
v___x_3559_ = v___x_3542_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3560_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3560_, 3, v_impl_3545_);
lean_ctor_set(v_reuseFailAlloc_3560_, 4, v_r_3540_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
else
{
lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3626_; 
v_isSharedCheck_3626_ = !lean_is_exclusive(v_impl_3545_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; lean_object* v_unused_3628_; lean_object* v_unused_3629_; lean_object* v_unused_3630_; lean_object* v_unused_3631_; 
v_unused_3627_ = lean_ctor_get(v_impl_3545_, 4);
lean_dec(v_unused_3627_);
v_unused_3628_ = lean_ctor_get(v_impl_3545_, 3);
lean_dec(v_unused_3628_);
v_unused_3629_ = lean_ctor_get(v_impl_3545_, 2);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v_impl_3545_, 1);
lean_dec(v_unused_3630_);
v_unused_3631_ = lean_ctor_get(v_impl_3545_, 0);
lean_dec(v_unused_3631_);
v___x_3562_ = v_impl_3545_;
v_isShared_3563_ = v_isSharedCheck_3626_;
goto v_resetjp_3561_;
}
else
{
lean_dec(v_impl_3545_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3626_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v_size_3564_; lean_object* v_size_3565_; lean_object* v_k_3566_; lean_object* v_v_3567_; lean_object* v_l_3568_; lean_object* v_r_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; uint8_t v___x_3572_; 
v_size_3564_ = lean_ctor_get(v_l_3551_, 0);
v_size_3565_ = lean_ctor_get(v_r_3552_, 0);
v_k_3566_ = lean_ctor_get(v_r_3552_, 1);
v_v_3567_ = lean_ctor_get(v_r_3552_, 2);
v_l_3568_ = lean_ctor_get(v_r_3552_, 3);
v_r_3569_ = lean_ctor_get(v_r_3552_, 4);
v___x_3570_ = lean_unsigned_to_nat(2u);
v___x_3571_ = lean_nat_mul(v___x_3570_, v_size_3564_);
v___x_3572_ = lean_nat_dec_lt(v_size_3565_, v___x_3571_);
lean_dec(v___x_3571_);
if (v___x_3572_ == 0)
{
lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3601_; 
lean_inc(v_r_3569_);
lean_inc(v_l_3568_);
lean_inc(v_v_3567_);
lean_inc(v_k_3566_);
v_isSharedCheck_3601_ = !lean_is_exclusive(v_r_3552_);
if (v_isSharedCheck_3601_ == 0)
{
lean_object* v_unused_3602_; lean_object* v_unused_3603_; lean_object* v_unused_3604_; lean_object* v_unused_3605_; lean_object* v_unused_3606_; 
v_unused_3602_ = lean_ctor_get(v_r_3552_, 4);
lean_dec(v_unused_3602_);
v_unused_3603_ = lean_ctor_get(v_r_3552_, 3);
lean_dec(v_unused_3603_);
v_unused_3604_ = lean_ctor_get(v_r_3552_, 2);
lean_dec(v_unused_3604_);
v_unused_3605_ = lean_ctor_get(v_r_3552_, 1);
lean_dec(v_unused_3605_);
v_unused_3606_ = lean_ctor_get(v_r_3552_, 0);
lean_dec(v_unused_3606_);
v___x_3574_ = v_r_3552_;
v_isShared_3575_ = v_isSharedCheck_3601_;
goto v_resetjp_3573_;
}
else
{
lean_dec(v_r_3552_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3601_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___x_3589_; lean_object* v___y_3591_; 
v___x_3576_ = lean_nat_add(v___x_3546_, v_size_3548_);
lean_dec(v_size_3548_);
v___x_3577_ = lean_nat_add(v___x_3576_, v_size_3547_);
lean_dec(v___x_3576_);
v___x_3589_ = lean_nat_add(v___x_3546_, v_size_3564_);
if (lean_obj_tag(v_l_3568_) == 0)
{
lean_object* v_size_3599_; 
v_size_3599_ = lean_ctor_get(v_l_3568_, 0);
lean_inc(v_size_3599_);
v___y_3591_ = v_size_3599_;
goto v___jp_3590_;
}
else
{
lean_object* v___x_3600_; 
v___x_3600_ = lean_unsigned_to_nat(0u);
v___y_3591_ = v___x_3600_;
goto v___jp_3590_;
}
v___jp_3578_:
{
lean_object* v___x_3582_; lean_object* v___x_3584_; 
v___x_3582_ = lean_nat_add(v___y_3579_, v___y_3581_);
lean_dec(v___y_3581_);
lean_dec(v___y_3579_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 4, v_r_3540_);
lean_ctor_set(v___x_3574_, 3, v_r_3569_);
lean_ctor_set(v___x_3574_, 2, v_v_3538_);
lean_ctor_set(v___x_3574_, 1, v_k_3537_);
lean_ctor_set(v___x_3574_, 0, v___x_3582_);
v___x_3584_ = v___x_3574_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3588_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3588_, 3, v_r_3569_);
lean_ctor_set(v_reuseFailAlloc_3588_, 4, v_r_3540_);
v___x_3584_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3586_; 
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 4, v___x_3584_);
lean_ctor_set(v___x_3562_, 3, v___y_3580_);
lean_ctor_set(v___x_3562_, 2, v_v_3567_);
lean_ctor_set(v___x_3562_, 1, v_k_3566_);
lean_ctor_set(v___x_3562_, 0, v___x_3577_);
v___x_3586_ = v___x_3562_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3577_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_k_3566_);
lean_ctor_set(v_reuseFailAlloc_3587_, 2, v_v_3567_);
lean_ctor_set(v_reuseFailAlloc_3587_, 3, v___y_3580_);
lean_ctor_set(v_reuseFailAlloc_3587_, 4, v___x_3584_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
v___jp_3590_:
{
lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3592_ = lean_nat_add(v___x_3589_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec(v___x_3589_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 4, v_l_3568_);
lean_ctor_set(v___x_3542_, 3, v_l_3551_);
lean_ctor_set(v___x_3542_, 2, v_v_3550_);
lean_ctor_set(v___x_3542_, 1, v_k_3549_);
lean_ctor_set(v___x_3542_, 0, v___x_3592_);
v___x_3594_ = v___x_3542_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3598_, 1, v_k_3549_);
lean_ctor_set(v_reuseFailAlloc_3598_, 2, v_v_3550_);
lean_ctor_set(v_reuseFailAlloc_3598_, 3, v_l_3551_);
lean_ctor_set(v_reuseFailAlloc_3598_, 4, v_l_3568_);
v___x_3594_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3595_; 
v___x_3595_ = lean_nat_add(v___x_3546_, v_size_3547_);
if (lean_obj_tag(v_r_3569_) == 0)
{
lean_object* v_size_3596_; 
v_size_3596_ = lean_ctor_get(v_r_3569_, 0);
lean_inc(v_size_3596_);
v___y_3579_ = v___x_3595_;
v___y_3580_ = v___x_3594_;
v___y_3581_ = v_size_3596_;
goto v___jp_3578_;
}
else
{
lean_object* v___x_3597_; 
v___x_3597_ = lean_unsigned_to_nat(0u);
v___y_3579_ = v___x_3595_;
v___y_3580_ = v___x_3594_;
v___y_3581_ = v___x_3597_;
goto v___jp_3578_;
}
}
}
}
}
else
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3612_; 
lean_del_object(v___x_3542_);
v___x_3607_ = lean_nat_add(v___x_3546_, v_size_3548_);
lean_dec(v_size_3548_);
v___x_3608_ = lean_nat_add(v___x_3607_, v_size_3547_);
lean_dec(v___x_3607_);
v___x_3609_ = lean_nat_add(v___x_3546_, v_size_3547_);
v___x_3610_ = lean_nat_add(v___x_3609_, v_size_3565_);
lean_dec(v___x_3609_);
lean_inc_ref(v_r_3540_);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 4, v_r_3540_);
lean_ctor_set(v___x_3562_, 3, v_r_3552_);
lean_ctor_set(v___x_3562_, 2, v_v_3538_);
lean_ctor_set(v___x_3562_, 1, v_k_3537_);
lean_ctor_set(v___x_3562_, 0, v___x_3610_);
v___x_3612_ = v___x_3562_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3610_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3625_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3625_, 3, v_r_3552_);
lean_ctor_set(v_reuseFailAlloc_3625_, 4, v_r_3540_);
v___x_3612_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
v_isSharedCheck_3619_ = !lean_is_exclusive(v_r_3540_);
if (v_isSharedCheck_3619_ == 0)
{
lean_object* v_unused_3620_; lean_object* v_unused_3621_; lean_object* v_unused_3622_; lean_object* v_unused_3623_; lean_object* v_unused_3624_; 
v_unused_3620_ = lean_ctor_get(v_r_3540_, 4);
lean_dec(v_unused_3620_);
v_unused_3621_ = lean_ctor_get(v_r_3540_, 3);
lean_dec(v_unused_3621_);
v_unused_3622_ = lean_ctor_get(v_r_3540_, 2);
lean_dec(v_unused_3622_);
v_unused_3623_ = lean_ctor_get(v_r_3540_, 1);
lean_dec(v_unused_3623_);
v_unused_3624_ = lean_ctor_get(v_r_3540_, 0);
lean_dec(v_unused_3624_);
v___x_3614_ = v_r_3540_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_dec(v_r_3540_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 4, v___x_3612_);
lean_ctor_set(v___x_3614_, 3, v_l_3551_);
lean_ctor_set(v___x_3614_, 2, v_v_3550_);
lean_ctor_set(v___x_3614_, 1, v_k_3549_);
lean_ctor_set(v___x_3614_, 0, v___x_3608_);
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3608_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v_k_3549_);
lean_ctor_set(v_reuseFailAlloc_3618_, 2, v_v_3550_);
lean_ctor_set(v_reuseFailAlloc_3618_, 3, v_l_3551_);
lean_ctor_set(v_reuseFailAlloc_3618_, 4, v___x_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3632_; 
v_l_3632_ = lean_ctor_get(v_impl_3545_, 3);
lean_inc(v_l_3632_);
if (lean_obj_tag(v_l_3632_) == 0)
{
lean_object* v_r_3633_; lean_object* v_k_3634_; lean_object* v_v_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3646_; 
v_r_3633_ = lean_ctor_get(v_impl_3545_, 4);
v_k_3634_ = lean_ctor_get(v_impl_3545_, 1);
v_v_3635_ = lean_ctor_get(v_impl_3545_, 2);
v_isSharedCheck_3646_ = !lean_is_exclusive(v_impl_3545_);
if (v_isSharedCheck_3646_ == 0)
{
lean_object* v_unused_3647_; lean_object* v_unused_3648_; 
v_unused_3647_ = lean_ctor_get(v_impl_3545_, 3);
lean_dec(v_unused_3647_);
v_unused_3648_ = lean_ctor_get(v_impl_3545_, 0);
lean_dec(v_unused_3648_);
v___x_3637_ = v_impl_3545_;
v_isShared_3638_ = v_isSharedCheck_3646_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_r_3633_);
lean_inc(v_v_3635_);
lean_inc(v_k_3634_);
lean_dec(v_impl_3545_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3646_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3639_; lean_object* v___x_3641_; 
v___x_3639_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3633_);
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 3, v_r_3633_);
lean_ctor_set(v___x_3637_, 2, v_v_3538_);
lean_ctor_set(v___x_3637_, 1, v_k_3537_);
lean_ctor_set(v___x_3637_, 0, v___x_3546_);
v___x_3641_ = v___x_3637_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3645_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3645_, 3, v_r_3633_);
lean_ctor_set(v_reuseFailAlloc_3645_, 4, v_r_3633_);
v___x_3641_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_object* v___x_3643_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 4, v___x_3641_);
lean_ctor_set(v___x_3542_, 3, v_l_3632_);
lean_ctor_set(v___x_3542_, 2, v_v_3635_);
lean_ctor_set(v___x_3542_, 1, v_k_3634_);
lean_ctor_set(v___x_3542_, 0, v___x_3639_);
v___x_3643_ = v___x_3542_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3639_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_k_3634_);
lean_ctor_set(v_reuseFailAlloc_3644_, 2, v_v_3635_);
lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_l_3632_);
lean_ctor_set(v_reuseFailAlloc_3644_, 4, v___x_3641_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
else
{
lean_object* v_r_3649_; 
v_r_3649_ = lean_ctor_get(v_impl_3545_, 4);
lean_inc(v_r_3649_);
if (lean_obj_tag(v_r_3649_) == 0)
{
lean_object* v_k_3650_; lean_object* v_v_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3674_; 
v_k_3650_ = lean_ctor_get(v_impl_3545_, 1);
v_v_3651_ = lean_ctor_get(v_impl_3545_, 2);
v_isSharedCheck_3674_ = !lean_is_exclusive(v_impl_3545_);
if (v_isSharedCheck_3674_ == 0)
{
lean_object* v_unused_3675_; lean_object* v_unused_3676_; lean_object* v_unused_3677_; 
v_unused_3675_ = lean_ctor_get(v_impl_3545_, 4);
lean_dec(v_unused_3675_);
v_unused_3676_ = lean_ctor_get(v_impl_3545_, 3);
lean_dec(v_unused_3676_);
v_unused_3677_ = lean_ctor_get(v_impl_3545_, 0);
lean_dec(v_unused_3677_);
v___x_3653_ = v_impl_3545_;
v_isShared_3654_ = v_isSharedCheck_3674_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_v_3651_);
lean_inc(v_k_3650_);
lean_dec(v_impl_3545_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3674_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v_k_3655_; lean_object* v_v_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3670_; 
v_k_3655_ = lean_ctor_get(v_r_3649_, 1);
v_v_3656_ = lean_ctor_get(v_r_3649_, 2);
v_isSharedCheck_3670_ = !lean_is_exclusive(v_r_3649_);
if (v_isSharedCheck_3670_ == 0)
{
lean_object* v_unused_3671_; lean_object* v_unused_3672_; lean_object* v_unused_3673_; 
v_unused_3671_ = lean_ctor_get(v_r_3649_, 4);
lean_dec(v_unused_3671_);
v_unused_3672_ = lean_ctor_get(v_r_3649_, 3);
lean_dec(v_unused_3672_);
v_unused_3673_ = lean_ctor_get(v_r_3649_, 0);
lean_dec(v_unused_3673_);
v___x_3658_ = v_r_3649_;
v_isShared_3659_ = v_isSharedCheck_3670_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_v_3656_);
lean_inc(v_k_3655_);
lean_dec(v_r_3649_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3670_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3660_; lean_object* v___x_3662_; 
v___x_3660_ = lean_unsigned_to_nat(3u);
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 4, v_l_3632_);
lean_ctor_set(v___x_3658_, 3, v_l_3632_);
lean_ctor_set(v___x_3658_, 2, v_v_3651_);
lean_ctor_set(v___x_3658_, 1, v_k_3650_);
lean_ctor_set(v___x_3658_, 0, v___x_3546_);
v___x_3662_ = v___x_3658_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_k_3650_);
lean_ctor_set(v_reuseFailAlloc_3669_, 2, v_v_3651_);
lean_ctor_set(v_reuseFailAlloc_3669_, 3, v_l_3632_);
lean_ctor_set(v_reuseFailAlloc_3669_, 4, v_l_3632_);
v___x_3662_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3664_; 
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 4, v_l_3632_);
lean_ctor_set(v___x_3653_, 2, v_v_3538_);
lean_ctor_set(v___x_3653_, 1, v_k_3537_);
lean_ctor_set(v___x_3653_, 0, v___x_3546_);
v___x_3664_ = v___x_3653_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3668_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3668_, 3, v_l_3632_);
lean_ctor_set(v_reuseFailAlloc_3668_, 4, v_l_3632_);
v___x_3664_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3666_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 4, v___x_3664_);
lean_ctor_set(v___x_3542_, 3, v___x_3662_);
lean_ctor_set(v___x_3542_, 2, v_v_3656_);
lean_ctor_set(v___x_3542_, 1, v_k_3655_);
lean_ctor_set(v___x_3542_, 0, v___x_3660_);
v___x_3666_ = v___x_3542_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_k_3655_);
lean_ctor_set(v_reuseFailAlloc_3667_, 2, v_v_3656_);
lean_ctor_set(v_reuseFailAlloc_3667_, 3, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3667_, 4, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
}
}
else
{
lean_object* v___x_3678_; lean_object* v___x_3680_; 
v___x_3678_ = lean_unsigned_to_nat(2u);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 4, v_r_3649_);
lean_ctor_set(v___x_3542_, 3, v_impl_3545_);
lean_ctor_set(v___x_3542_, 0, v___x_3678_);
v___x_3680_ = v___x_3542_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
lean_ctor_set(v_reuseFailAlloc_3681_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3681_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3681_, 3, v_impl_3545_);
lean_ctor_set(v_reuseFailAlloc_3681_, 4, v_r_3649_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3683_; 
lean_dec(v_v_3538_);
lean_dec(v_k_3537_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 2, v_v_3534_);
lean_ctor_set(v___x_3542_, 1, v_k_3533_);
v___x_3683_ = v___x_3542_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_size_3536_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_k_3533_);
lean_ctor_set(v_reuseFailAlloc_3684_, 2, v_v_3534_);
lean_ctor_set(v_reuseFailAlloc_3684_, 3, v_l_3539_);
lean_ctor_set(v_reuseFailAlloc_3684_, 4, v_r_3540_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
default: 
{
lean_object* v_impl_3685_; lean_object* v___x_3686_; 
lean_dec(v_size_3536_);
v_impl_3685_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3533_, v_v_3534_, v_r_3540_);
v___x_3686_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3539_) == 0)
{
lean_object* v_size_3687_; lean_object* v_size_3688_; lean_object* v_k_3689_; lean_object* v_v_3690_; lean_object* v_l_3691_; lean_object* v_r_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; uint8_t v___x_3695_; 
v_size_3687_ = lean_ctor_get(v_l_3539_, 0);
v_size_3688_ = lean_ctor_get(v_impl_3685_, 0);
lean_inc(v_size_3688_);
v_k_3689_ = lean_ctor_get(v_impl_3685_, 1);
lean_inc(v_k_3689_);
v_v_3690_ = lean_ctor_get(v_impl_3685_, 2);
lean_inc(v_v_3690_);
v_l_3691_ = lean_ctor_get(v_impl_3685_, 3);
lean_inc(v_l_3691_);
v_r_3692_ = lean_ctor_get(v_impl_3685_, 4);
lean_inc(v_r_3692_);
v___x_3693_ = lean_unsigned_to_nat(3u);
v___x_3694_ = lean_nat_mul(v___x_3693_, v_size_3687_);
v___x_3695_ = lean_nat_dec_lt(v___x_3694_, v_size_3688_);
lean_dec(v___x_3694_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3699_; 
lean_dec(v_r_3692_);
lean_dec(v_l_3691_);
lean_dec(v_v_3690_);
lean_dec(v_k_3689_);
v___x_3696_ = lean_nat_add(v___x_3686_, v_size_3687_);
v___x_3697_ = lean_nat_add(v___x_3696_, v_size_3688_);
lean_dec(v_size_3688_);
lean_dec(v___x_3696_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 4, v_impl_3685_);
lean_ctor_set(v___x_3542_, 0, v___x_3697_);
v___x_3699_ = v___x_3542_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3697_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3700_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3700_, 3, v_l_3539_);
lean_ctor_set(v_reuseFailAlloc_3700_, 4, v_impl_3685_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
else
{
lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3764_; 
v_isSharedCheck_3764_ = !lean_is_exclusive(v_impl_3685_);
if (v_isSharedCheck_3764_ == 0)
{
lean_object* v_unused_3765_; lean_object* v_unused_3766_; lean_object* v_unused_3767_; lean_object* v_unused_3768_; lean_object* v_unused_3769_; 
v_unused_3765_ = lean_ctor_get(v_impl_3685_, 4);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_impl_3685_, 3);
lean_dec(v_unused_3766_);
v_unused_3767_ = lean_ctor_get(v_impl_3685_, 2);
lean_dec(v_unused_3767_);
v_unused_3768_ = lean_ctor_get(v_impl_3685_, 1);
lean_dec(v_unused_3768_);
v_unused_3769_ = lean_ctor_get(v_impl_3685_, 0);
lean_dec(v_unused_3769_);
v___x_3702_ = v_impl_3685_;
v_isShared_3703_ = v_isSharedCheck_3764_;
goto v_resetjp_3701_;
}
else
{
lean_dec(v_impl_3685_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3764_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v_size_3704_; lean_object* v_k_3705_; lean_object* v_v_3706_; lean_object* v_l_3707_; lean_object* v_r_3708_; lean_object* v_size_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; uint8_t v___x_3712_; 
v_size_3704_ = lean_ctor_get(v_l_3691_, 0);
v_k_3705_ = lean_ctor_get(v_l_3691_, 1);
v_v_3706_ = lean_ctor_get(v_l_3691_, 2);
v_l_3707_ = lean_ctor_get(v_l_3691_, 3);
v_r_3708_ = lean_ctor_get(v_l_3691_, 4);
v_size_3709_ = lean_ctor_get(v_r_3692_, 0);
v___x_3710_ = lean_unsigned_to_nat(2u);
v___x_3711_ = lean_nat_mul(v___x_3710_, v_size_3709_);
v___x_3712_ = lean_nat_dec_lt(v_size_3704_, v___x_3711_);
lean_dec(v___x_3711_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3740_; 
lean_inc(v_r_3708_);
lean_inc(v_l_3707_);
lean_inc(v_v_3706_);
lean_inc(v_k_3705_);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_l_3691_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; lean_object* v_unused_3742_; lean_object* v_unused_3743_; lean_object* v_unused_3744_; lean_object* v_unused_3745_; 
v_unused_3741_ = lean_ctor_get(v_l_3691_, 4);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_l_3691_, 3);
lean_dec(v_unused_3742_);
v_unused_3743_ = lean_ctor_get(v_l_3691_, 2);
lean_dec(v_unused_3743_);
v_unused_3744_ = lean_ctor_get(v_l_3691_, 1);
lean_dec(v_unused_3744_);
v_unused_3745_ = lean_ctor_get(v_l_3691_, 0);
lean_dec(v_unused_3745_);
v___x_3714_ = v_l_3691_;
v_isShared_3715_ = v_isSharedCheck_3740_;
goto v_resetjp_3713_;
}
else
{
lean_dec(v_l_3691_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3740_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3730_; 
v___x_3716_ = lean_nat_add(v___x_3686_, v_size_3687_);
v___x_3717_ = lean_nat_add(v___x_3716_, v_size_3688_);
lean_dec(v_size_3688_);
if (lean_obj_tag(v_l_3707_) == 0)
{
lean_object* v_size_3738_; 
v_size_3738_ = lean_ctor_get(v_l_3707_, 0);
lean_inc(v_size_3738_);
v___y_3730_ = v_size_3738_;
goto v___jp_3729_;
}
else
{
lean_object* v___x_3739_; 
v___x_3739_ = lean_unsigned_to_nat(0u);
v___y_3730_ = v___x_3739_;
goto v___jp_3729_;
}
v___jp_3718_:
{
lean_object* v___x_3722_; lean_object* v___x_3724_; 
v___x_3722_ = lean_nat_add(v___y_3720_, v___y_3721_);
lean_dec(v___y_3721_);
lean_dec(v___y_3720_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 4, v_r_3692_);
lean_ctor_set(v___x_3714_, 3, v_r_3708_);
lean_ctor_set(v___x_3714_, 2, v_v_3690_);
lean_ctor_set(v___x_3714_, 1, v_k_3689_);
lean_ctor_set(v___x_3714_, 0, v___x_3722_);
v___x_3724_ = v___x_3714_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_k_3689_);
lean_ctor_set(v_reuseFailAlloc_3728_, 2, v_v_3690_);
lean_ctor_set(v_reuseFailAlloc_3728_, 3, v_r_3708_);
lean_ctor_set(v_reuseFailAlloc_3728_, 4, v_r_3692_);
v___x_3724_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3726_; 
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 4, v___x_3724_);
lean_ctor_set(v___x_3702_, 3, v___y_3719_);
lean_ctor_set(v___x_3702_, 2, v_v_3706_);
lean_ctor_set(v___x_3702_, 1, v_k_3705_);
lean_ctor_set(v___x_3702_, 0, v___x_3717_);
v___x_3726_ = v___x_3702_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_k_3705_);
lean_ctor_set(v_reuseFailAlloc_3727_, 2, v_v_3706_);
lean_ctor_set(v_reuseFailAlloc_3727_, 3, v___y_3719_);
lean_ctor_set(v_reuseFailAlloc_3727_, 4, v___x_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
v___jp_3729_:
{
lean_object* v___x_3731_; lean_object* v___x_3733_; 
v___x_3731_ = lean_nat_add(v___x_3716_, v___y_3730_);
lean_dec(v___y_3730_);
lean_dec(v___x_3716_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 4, v_l_3707_);
lean_ctor_set(v___x_3542_, 0, v___x_3731_);
v___x_3733_ = v___x_3542_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3737_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3737_, 3, v_l_3539_);
lean_ctor_set(v_reuseFailAlloc_3737_, 4, v_l_3707_);
v___x_3733_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_nat_add(v___x_3686_, v_size_3709_);
if (lean_obj_tag(v_r_3708_) == 0)
{
lean_object* v_size_3735_; 
v_size_3735_ = lean_ctor_get(v_r_3708_, 0);
lean_inc(v_size_3735_);
v___y_3719_ = v___x_3733_;
v___y_3720_ = v___x_3734_;
v___y_3721_ = v_size_3735_;
goto v___jp_3718_;
}
else
{
lean_object* v___x_3736_; 
v___x_3736_ = lean_unsigned_to_nat(0u);
v___y_3719_ = v___x_3733_;
v___y_3720_ = v___x_3734_;
v___y_3721_ = v___x_3736_;
goto v___jp_3718_;
}
}
}
}
}
else
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3750_; 
lean_del_object(v___x_3542_);
v___x_3746_ = lean_nat_add(v___x_3686_, v_size_3687_);
v___x_3747_ = lean_nat_add(v___x_3746_, v_size_3688_);
lean_dec(v_size_3688_);
v___x_3748_ = lean_nat_add(v___x_3746_, v_size_3704_);
lean_dec(v___x_3746_);
lean_inc_ref(v_l_3539_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 4, v_l_3691_);
lean_ctor_set(v___x_3702_, 3, v_l_3539_);
lean_ctor_set(v___x_3702_, 2, v_v_3538_);
lean_ctor_set(v___x_3702_, 1, v_k_3537_);
lean_ctor_set(v___x_3702_, 0, v___x_3748_);
v___x_3750_ = v___x_3702_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3748_);
lean_ctor_set(v_reuseFailAlloc_3763_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3763_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3763_, 3, v_l_3539_);
lean_ctor_set(v_reuseFailAlloc_3763_, 4, v_l_3691_);
v___x_3750_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
v_isSharedCheck_3757_ = !lean_is_exclusive(v_l_3539_);
if (v_isSharedCheck_3757_ == 0)
{
lean_object* v_unused_3758_; lean_object* v_unused_3759_; lean_object* v_unused_3760_; lean_object* v_unused_3761_; lean_object* v_unused_3762_; 
v_unused_3758_ = lean_ctor_get(v_l_3539_, 4);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_l_3539_, 3);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_l_3539_, 2);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_l_3539_, 1);
lean_dec(v_unused_3761_);
v_unused_3762_ = lean_ctor_get(v_l_3539_, 0);
lean_dec(v_unused_3762_);
v___x_3752_ = v_l_3539_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_dec(v_l_3539_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 4, v_r_3692_);
lean_ctor_set(v___x_3752_, 3, v___x_3750_);
lean_ctor_set(v___x_3752_, 2, v_v_3690_);
lean_ctor_set(v___x_3752_, 1, v_k_3689_);
lean_ctor_set(v___x_3752_, 0, v___x_3747_);
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3747_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_k_3689_);
lean_ctor_set(v_reuseFailAlloc_3756_, 2, v_v_3690_);
lean_ctor_set(v_reuseFailAlloc_3756_, 3, v___x_3750_);
lean_ctor_set(v_reuseFailAlloc_3756_, 4, v_r_3692_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3770_; 
v_l_3770_ = lean_ctor_get(v_impl_3685_, 3);
lean_inc(v_l_3770_);
if (lean_obj_tag(v_l_3770_) == 0)
{
lean_object* v_r_3771_; lean_object* v_k_3772_; lean_object* v_v_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3796_; 
v_r_3771_ = lean_ctor_get(v_impl_3685_, 4);
v_k_3772_ = lean_ctor_get(v_impl_3685_, 1);
v_v_3773_ = lean_ctor_get(v_impl_3685_, 2);
v_isSharedCheck_3796_ = !lean_is_exclusive(v_impl_3685_);
if (v_isSharedCheck_3796_ == 0)
{
lean_object* v_unused_3797_; lean_object* v_unused_3798_; 
v_unused_3797_ = lean_ctor_get(v_impl_3685_, 3);
lean_dec(v_unused_3797_);
v_unused_3798_ = lean_ctor_get(v_impl_3685_, 0);
lean_dec(v_unused_3798_);
v___x_3775_ = v_impl_3685_;
v_isShared_3776_ = v_isSharedCheck_3796_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_r_3771_);
lean_inc(v_v_3773_);
lean_inc(v_k_3772_);
lean_dec(v_impl_3685_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3796_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v_k_3777_; lean_object* v_v_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3792_; 
v_k_3777_ = lean_ctor_get(v_l_3770_, 1);
v_v_3778_ = lean_ctor_get(v_l_3770_, 2);
v_isSharedCheck_3792_ = !lean_is_exclusive(v_l_3770_);
if (v_isSharedCheck_3792_ == 0)
{
lean_object* v_unused_3793_; lean_object* v_unused_3794_; lean_object* v_unused_3795_; 
v_unused_3793_ = lean_ctor_get(v_l_3770_, 4);
lean_dec(v_unused_3793_);
v_unused_3794_ = lean_ctor_get(v_l_3770_, 3);
lean_dec(v_unused_3794_);
v_unused_3795_ = lean_ctor_get(v_l_3770_, 0);
lean_dec(v_unused_3795_);
v___x_3780_ = v_l_3770_;
v_isShared_3781_ = v_isSharedCheck_3792_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_v_3778_);
lean_inc(v_k_3777_);
lean_dec(v_l_3770_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3792_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3782_; lean_object* v___x_3784_; 
v___x_3782_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3771_, 2);
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 4, v_r_3771_);
lean_ctor_set(v___x_3780_, 3, v_r_3771_);
lean_ctor_set(v___x_3780_, 2, v_v_3538_);
lean_ctor_set(v___x_3780_, 1, v_k_3537_);
lean_ctor_set(v___x_3780_, 0, v___x_3686_);
v___x_3784_ = v___x_3780_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v___x_3686_);
lean_ctor_set(v_reuseFailAlloc_3791_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3791_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3791_, 3, v_r_3771_);
lean_ctor_set(v_reuseFailAlloc_3791_, 4, v_r_3771_);
v___x_3784_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
lean_object* v___x_3786_; 
lean_inc(v_r_3771_);
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 3, v_r_3771_);
lean_ctor_set(v___x_3775_, 0, v___x_3686_);
v___x_3786_ = v___x_3775_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3686_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_k_3772_);
lean_ctor_set(v_reuseFailAlloc_3790_, 2, v_v_3773_);
lean_ctor_set(v_reuseFailAlloc_3790_, 3, v_r_3771_);
lean_ctor_set(v_reuseFailAlloc_3790_, 4, v_r_3771_);
v___x_3786_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3788_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 4, v___x_3786_);
lean_ctor_set(v___x_3542_, 3, v___x_3784_);
lean_ctor_set(v___x_3542_, 2, v_v_3778_);
lean_ctor_set(v___x_3542_, 1, v_k_3777_);
lean_ctor_set(v___x_3542_, 0, v___x_3782_);
v___x_3788_ = v___x_3542_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_k_3777_);
lean_ctor_set(v_reuseFailAlloc_3789_, 2, v_v_3778_);
lean_ctor_set(v_reuseFailAlloc_3789_, 3, v___x_3784_);
lean_ctor_set(v_reuseFailAlloc_3789_, 4, v___x_3786_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
}
}
else
{
lean_object* v_r_3799_; 
v_r_3799_ = lean_ctor_get(v_impl_3685_, 4);
lean_inc(v_r_3799_);
if (lean_obj_tag(v_r_3799_) == 0)
{
lean_object* v_k_3800_; lean_object* v_v_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3812_; 
v_k_3800_ = lean_ctor_get(v_impl_3685_, 1);
v_v_3801_ = lean_ctor_get(v_impl_3685_, 2);
v_isSharedCheck_3812_ = !lean_is_exclusive(v_impl_3685_);
if (v_isSharedCheck_3812_ == 0)
{
lean_object* v_unused_3813_; lean_object* v_unused_3814_; lean_object* v_unused_3815_; 
v_unused_3813_ = lean_ctor_get(v_impl_3685_, 4);
lean_dec(v_unused_3813_);
v_unused_3814_ = lean_ctor_get(v_impl_3685_, 3);
lean_dec(v_unused_3814_);
v_unused_3815_ = lean_ctor_get(v_impl_3685_, 0);
lean_dec(v_unused_3815_);
v___x_3803_ = v_impl_3685_;
v_isShared_3804_ = v_isSharedCheck_3812_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_v_3801_);
lean_inc(v_k_3800_);
lean_dec(v_impl_3685_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3812_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3805_; lean_object* v___x_3807_; 
v___x_3805_ = lean_unsigned_to_nat(3u);
if (v_isShared_3804_ == 0)
{
lean_ctor_set(v___x_3803_, 4, v_l_3770_);
lean_ctor_set(v___x_3803_, 2, v_v_3538_);
lean_ctor_set(v___x_3803_, 1, v_k_3537_);
lean_ctor_set(v___x_3803_, 0, v___x_3686_);
v___x_3807_ = v___x_3803_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3686_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3811_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3811_, 3, v_l_3770_);
lean_ctor_set(v_reuseFailAlloc_3811_, 4, v_l_3770_);
v___x_3807_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
lean_object* v___x_3809_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 4, v_r_3799_);
lean_ctor_set(v___x_3542_, 3, v___x_3807_);
lean_ctor_set(v___x_3542_, 2, v_v_3801_);
lean_ctor_set(v___x_3542_, 1, v_k_3800_);
lean_ctor_set(v___x_3542_, 0, v___x_3805_);
v___x_3809_ = v___x_3542_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3805_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v_k_3800_);
lean_ctor_set(v_reuseFailAlloc_3810_, 2, v_v_3801_);
lean_ctor_set(v_reuseFailAlloc_3810_, 3, v___x_3807_);
lean_ctor_set(v_reuseFailAlloc_3810_, 4, v_r_3799_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
else
{
lean_object* v___x_3816_; lean_object* v___x_3818_; 
v___x_3816_ = lean_unsigned_to_nat(2u);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 4, v_impl_3685_);
lean_ctor_set(v___x_3542_, 3, v_r_3799_);
lean_ctor_set(v___x_3542_, 0, v___x_3816_);
v___x_3818_ = v___x_3542_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3816_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v_k_3537_);
lean_ctor_set(v_reuseFailAlloc_3819_, 2, v_v_3538_);
lean_ctor_set(v_reuseFailAlloc_3819_, 3, v_r_3799_);
lean_ctor_set(v_reuseFailAlloc_3819_, 4, v_impl_3685_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
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
lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3821_ = lean_unsigned_to_nat(1u);
v___x_3822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
lean_ctor_set(v___x_3822_, 1, v_k_3533_);
lean_ctor_set(v___x_3822_, 2, v_v_3534_);
lean_ctor_set(v___x_3822_, 3, v_t_3535_);
lean_ctor_set(v___x_3822_, 4, v_t_3535_);
return v___x_3822_;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3823_ = lean_box(1);
v___x_3824_ = l_Lake_LeanLib_defaultFacetConfig;
v___x_3825_ = l_Lake_LeanLib_defaultFacet;
v___x_3826_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3825_, v___x_3824_, v___x_3823_);
return v___x_3826_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3827_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__0, &l_Lake_LeanLib_initFacetConfigs___closed__0_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__0);
v___x_3828_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig));
v___x_3829_ = l_Lake_LeanLib_modulesFacet;
v___x_3830_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3829_, v___x_3828_, v___x_3827_);
return v___x_3830_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3831_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__1, &l_Lake_LeanLib_initFacetConfigs___closed__1_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__1);
v___x_3832_ = l_Lake_LeanLib_leanArtsFacetConfig;
v___x_3833_ = l_Lake_LeanLib_leanArtsFacet;
v___x_3834_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3833_, v___x_3832_, v___x_3831_);
return v___x_3834_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v___x_3835_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__2, &l_Lake_LeanLib_initFacetConfigs___closed__2_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__2);
v___x_3836_ = l_Lake_LeanLib_staticFacetConfig;
v___x_3837_ = l_Lake_LeanLib_staticFacet;
v___x_3838_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3837_, v___x_3836_, v___x_3835_);
return v___x_3838_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3839_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__3, &l_Lake_LeanLib_initFacetConfigs___closed__3_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__3);
v___x_3840_ = l_Lake_LeanLib_staticExportFacetConfig;
v___x_3841_ = l_Lake_LeanLib_staticExportFacet;
v___x_3842_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3841_, v___x_3840_, v___x_3839_);
return v___x_3842_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3843_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__4, &l_Lake_LeanLib_initFacetConfigs___closed__4_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__4);
v___x_3844_ = l_Lake_LeanLib_sharedFacetConfig;
v___x_3845_ = l_Lake_LeanLib_sharedFacet;
v___x_3846_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3845_, v___x_3844_, v___x_3843_);
return v___x_3846_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3847_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__5, &l_Lake_LeanLib_initFacetConfigs___closed__5_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__5);
v___x_3848_ = l_Lake_LeanLib_extraDepFacetConfig;
v___x_3849_ = l_Lake_LeanLib_extraDepFacet;
v___x_3850_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3849_, v___x_3848_, v___x_3847_);
return v___x_3850_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__6, &l_Lake_LeanLib_initFacetConfigs___closed__6_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__6);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3852_, lean_object* v_k_3853_, lean_object* v_v_3854_, lean_object* v_t_3855_, lean_object* v_hl_3856_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3853_, v_v_3854_, v_t_3855_);
return v___x_3857_;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs(void){
_start:
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lake_LeanLib_initFacetConfigs;
return v___x_3858_;
}
}
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Targets(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Target_Fetch(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Library(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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
