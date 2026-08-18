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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
extern lean_object* l_Lake_instDataKindDynlib;
lean_object* l_Lake_nameToSharedLib(lean_object*, uint8_t);
uint8_t l_Lake_LeanLib_isPlugin(lean_object*);
lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_dynlibFacet;
extern lean_object* l_Lake_ExternLib_keyword;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_sharedFacet;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
extern lean_object* l_Lake_Module_transImportsFacet;
extern lean_object* l_Lake_Module_keyword;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lake_Target_fetchIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
extern lean_object* l_Lake_instDataKindUnit;
lean_object* l_Lake_Job_mixArray___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_defaultFacet;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__4;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2_spec__3___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_4_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_dec(v_x_5_);
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(2);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_val_9_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v_x_3_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_val_9_);
lean_dec(v_x_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_val_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
else
{
lean_object* v_keyArray_17_; lean_object* v_valueArray_18_; lean_object* v___x_19_; uint8_t v_isSome_20_; 
v_keyArray_17_ = lean_ctor_get(v_m_1_, 1);
v_valueArray_18_ = lean_ctor_get(v_m_1_, 2);
v___x_19_ = lean_array_fget_borrowed(v_keyArray_17_, v_x_5_);
v_isSome_20_ = lean_noption_is_some(v___x_19_);
if (v_isSome_20_ == 0)
{
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_x_5_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_x_5_);
v_val_22_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_x_3_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_val_22_);
lean_dec(v_x_3_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
else
{
lean_object* v_one_30_; lean_object* v_n_31_; lean_object* v___y_33_; 
v_one_30_ = lean_unsigned_to_nat(1u);
v_n_31_ = lean_nat_sub(v_x_4_, v_one_30_);
lean_dec(v_x_4_);
if (v_isSome_20_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_41_; uint8_t v_isSome_42_; 
v___x_41_ = lean_array_fget_borrowed(v_valueArray_18_, v_x_5_);
v_isSome_42_ = lean_noption_is_some(v___x_41_);
if (v_isSome_42_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v_val_43_; lean_object* v_name_44_; lean_object* v_name_45_; uint8_t v___x_46_; 
lean_inc(v___x_19_);
v_val_43_ = lean_noption_get(v___x_19_);
v_name_44_ = lean_ctor_get(v_val_43_, 1);
lean_inc(v_name_44_);
v_name_45_ = lean_ctor_get(v_query_2_, 1);
v___x_46_ = lean_name_eq(v_name_44_, v_name_45_);
lean_dec(v_name_44_);
if (v___x_46_ == 0)
{
lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
lean_dec(v_val_43_);
v___x_47_ = lean_array_get_size(v_keyArray_17_);
v___x_48_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_49_ = lean_nat_dec_lt(v___x_48_, v___x_47_);
if (v___x_49_ == 0)
{
lean_dec(v___x_48_);
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_4_ = v_n_31_;
v_x_5_ = v___x_48_;
goto _start;
}
}
else
{
lean_object* v_val_52_; lean_object* v___x_53_; 
lean_dec(v_n_31_);
lean_dec(v_x_3_);
lean_inc(v___x_41_);
v_val_52_ = lean_noption_get(v___x_41_);
v___x_53_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_53_, 0, v_x_5_);
lean_ctor_set(v___x_53_, 1, v_val_43_);
lean_ctor_set(v___x_53_, 2, v_val_52_);
return v___x_53_;
}
}
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_array_get_size(v_keyArray_17_);
v___x_35_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_36_ = lean_nat_dec_lt(v___x_35_, v___x_34_);
if (v___x_36_ == 0)
{
lean_dec(v___x_35_);
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v___x_35_;
goto _start;
}
}
v___jp_39_:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_40_; 
lean_inc(v_x_5_);
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_x_5_);
v___y_33_ = v___x_40_;
goto v___jp_32_;
}
else
{
v___y_33_ = v_x_3_;
goto v___jp_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2_spec__3___redArg___boxed(lean_object* v_m_54_, lean_object* v_query_55_, lean_object* v_x_56_, lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2_spec__3___redArg(v_m_54_, v_query_55_, v_x_56_, v_x_57_, v_x_58_);
lean_dec_ref(v_query_55_);
lean_dec_ref(v_m_54_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(lean_object* v_m_60_, lean_object* v_query_61_){
_start:
{
lean_object* v_keyArray_62_; lean_object* v_name_63_; lean_object* v___x_64_; uint64_t v___y_66_; 
v_keyArray_62_ = lean_ctor_get(v_m_60_, 1);
v_name_63_ = lean_ctor_get(v_query_61_, 1);
v___x_64_ = lean_array_get_size(v_keyArray_62_);
if (lean_obj_tag(v_name_63_) == 0)
{
uint64_t v___x_81_; 
v___x_81_ = 1723ULL;
v___y_66_ = v___x_81_;
goto v___jp_65_;
}
else
{
uint64_t v_hash_82_; 
v_hash_82_ = lean_ctor_get_uint64(v_name_63_, sizeof(void*)*2);
v___y_66_ = v_hash_82_;
goto v___jp_65_;
}
v___jp_65_:
{
uint64_t v___x_67_; uint64_t v___x_68_; uint64_t v_fold_69_; uint64_t v___x_70_; uint64_t v___x_71_; uint64_t v___x_72_; size_t v___x_73_; size_t v___x_74_; size_t v___x_75_; size_t v___x_76_; size_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_67_ = 32ULL;
v___x_68_ = lean_uint64_shift_right(v___y_66_, v___x_67_);
v_fold_69_ = lean_uint64_xor(v___y_66_, v___x_68_);
v___x_70_ = 16ULL;
v___x_71_ = lean_uint64_shift_right(v_fold_69_, v___x_70_);
v___x_72_ = lean_uint64_xor(v_fold_69_, v___x_71_);
v___x_73_ = lean_uint64_to_usize(v___x_72_);
v___x_74_ = lean_usize_of_nat(v___x_64_);
v___x_75_ = ((size_t)1ULL);
v___x_76_ = lean_usize_sub(v___x_74_, v___x_75_);
v___x_77_ = lean_usize_land(v___x_73_, v___x_76_);
v___x_78_ = lean_usize_to_nat(v___x_77_);
v___x_79_ = lean_box(0);
v___x_80_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2_spec__3___redArg(v_m_60_, v_query_61_, v___x_79_, v___x_64_, v___x_78_);
return v___x_80_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg___boxed(lean_object* v_m_83_, lean_object* v_query_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(v_m_83_, v_query_84_);
lean_dec_ref(v_query_84_);
lean_dec_ref(v_m_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(lean_object* v_m_86_, lean_object* v_query_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(v_m_86_, v_query_87_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_index_89_; lean_object* v_key_90_; lean_object* v_value_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
v_index_89_ = lean_ctor_get(v___x_88_, 0);
v_key_90_ = lean_ctor_get(v___x_88_, 1);
v_value_91_ = lean_ctor_get(v___x_88_, 2);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_88_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_value_91_);
lean_inc(v_key_90_);
lean_inc(v_index_89_);
lean_dec(v___x_88_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_index_89_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_key_90_);
lean_ctor_set(v_reuseFailAlloc_97_, 2, v_value_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
else
{
lean_object* v___x_99_; 
lean_dec(v___x_88_);
v___x_99_ = lean_box(1);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg___boxed(lean_object* v_m_100_, lean_object* v_query_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_m_100_, v_query_101_);
lean_dec_ref(v_query_101_);
lean_dec_ref(v_m_100_);
return v_res_102_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(lean_object* v_m_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_m_103_, v_a_104_);
if (lean_obj_tag(v___x_105_) == 0)
{
uint8_t v___x_106_; 
lean_dec_ref_known(v___x_105_, 3);
v___x_106_ = 1;
return v___x_106_;
}
else
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg___boxed(lean_object* v_m_108_, lean_object* v_a_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_108_, v_a_109_);
lean_dec_ref(v_a_109_);
lean_dec_ref(v_m_108_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5_spec__6___redArg(lean_object* v_b_112_, lean_object* v_acc_113_, lean_object* v_i_114_){
_start:
{
lean_object* v___y_116_; lean_object* v_keyArray_124_; lean_object* v_valueArray_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_keyArray_124_ = lean_ctor_get(v_b_112_, 1);
v_valueArray_125_ = lean_ctor_get(v_b_112_, 2);
v___x_126_ = lean_array_get_size(v_keyArray_124_);
v___x_127_ = lean_nat_dec_lt(v_i_114_, v___x_126_);
if (v___x_127_ == 0)
{
lean_dec(v_i_114_);
return v_acc_113_;
}
else
{
lean_object* v___x_128_; uint8_t v_isSome_129_; 
v___x_128_ = lean_array_fget_borrowed(v_keyArray_124_, v_i_114_);
v_isSome_129_ = lean_noption_is_some(v___x_128_);
if (v_isSome_129_ == 0)
{
goto v___jp_120_;
}
else
{
lean_object* v___x_130_; uint8_t v_isSome_131_; 
v___x_130_ = lean_array_fget_borrowed(v_valueArray_125_, v_i_114_);
v_isSome_131_ = lean_noption_is_some(v___x_130_);
if (v_isSome_131_ == 0)
{
goto v___jp_120_;
}
else
{
lean_object* v_val_132_; lean_object* v_val_133_; lean_object* v_i_135_; lean_object* v___x_140_; 
lean_inc(v___x_128_);
v_val_132_ = lean_noption_get(v___x_128_);
lean_inc(v___x_130_);
v_val_133_ = lean_noption_get(v___x_130_);
v___x_140_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(v_acc_113_, v_val_132_);
switch(lean_obj_tag(v___x_140_))
{
case 0:
{
lean_object* v_index_141_; lean_object* v_size_142_; lean_object* v___x_143_; 
v_index_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_index_141_);
lean_dec_ref_known(v___x_140_, 3);
v_size_142_ = lean_ctor_get(v_acc_113_, 0);
lean_inc(v_size_142_);
v___x_143_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_113_, v_size_142_, v_index_141_, v_val_132_, v_val_133_);
lean_dec(v_index_141_);
v___y_116_ = v___x_143_;
goto v___jp_115_;
}
case 1:
{
lean_object* v_index_144_; 
v_index_144_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_index_144_);
lean_dec_ref_known(v___x_140_, 1);
v_i_135_ = v_index_144_;
goto v___jp_134_;
}
default: 
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_113_, v___x_145_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_index_147_; 
v_index_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_index_147_);
lean_dec_ref_known(v___x_146_, 1);
v_i_135_ = v_index_147_;
goto v___jp_134_;
}
else
{
lean_dec(v_val_133_);
lean_dec(v_val_132_);
v___y_116_ = v_acc_113_;
goto v___jp_115_;
}
}
}
v___jp_134_:
{
lean_object* v_size_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_size_136_ = lean_ctor_get(v_acc_113_, 0);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_nat_add(v_size_136_, v___x_137_);
v___x_139_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_113_, v___x_138_, v_i_135_, v_val_132_, v_val_133_);
lean_dec(v_i_135_);
v___y_116_ = v___x_139_;
goto v___jp_115_;
}
}
}
}
v___jp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_add(v_i_114_, v___x_117_);
lean_dec(v_i_114_);
v_acc_113_ = v___y_116_;
v_i_114_ = v___x_118_;
goto _start;
}
v___jp_120_:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_add(v_i_114_, v___x_121_);
lean_dec(v_i_114_);
v_i_114_ = v___x_122_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_b_148_, lean_object* v_acc_149_, lean_object* v_i_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5_spec__6___redArg(v_b_148_, v_acc_149_, v_i_150_);
lean_dec_ref(v_b_148_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5___redArg(lean_object* v_init_152_, lean_object* v_b_153_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5_spec__6___redArg(v_b_153_, v_init_152_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5___redArg___boxed(lean_object* v_init_156_, lean_object* v_b_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5___redArg(v_init_156_, v_b_157_);
lean_dec_ref(v_b_157_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(lean_object* v_m_159_){
_start:
{
lean_object* v_keyArray_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_cellCount_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_target_167_; lean_object* v___x_168_; 
v_keyArray_160_ = lean_ctor_get(v_m_159_, 1);
v___x_161_ = lean_array_get_size(v_keyArray_160_);
v___x_162_ = lean_unsigned_to_nat(2u);
v_cellCount_163_ = lean_nat_mul(v___x_161_, v___x_162_);
v___x_164_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_163_);
v___x_165_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_163_);
v___x_166_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_163_);
v_target_167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_167_, 0, v___x_164_);
lean_ctor_set(v_target_167_, 1, v___x_165_);
lean_ctor_set(v_target_167_, 2, v___x_166_);
v___x_168_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5___redArg(v_target_167_, v_m_159_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg___boxed(lean_object* v_m_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(v_m_169_);
lean_dec_ref(v_m_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(lean_object* v_self_171_, lean_object* v_root_172_, lean_object* v_col_173_, uint8_t v_viaImport_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_col_183_; lean_object* v___y_184_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v_mods_190_; lean_object* v_modSet_191_; uint8_t v_hasErrors_192_; uint8_t v___x_193_; 
v_mods_190_ = lean_ctor_get(v_col_173_, 0);
v_modSet_191_ = lean_ctor_get(v_col_173_, 1);
v_hasErrors_192_ = lean_ctor_get_uint8(v_col_173_, sizeof(void*)*2);
v___x_193_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_modSet_191_, v_root_172_);
if (v___x_193_ == 0)
{
lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_311_; 
lean_inc_ref(v_modSet_191_);
lean_inc_ref(v_mods_190_);
v_isSharedCheck_311_ = !lean_is_exclusive(v_col_173_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; 
v_unused_312_ = lean_ctor_get(v_col_173_, 1);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_col_173_, 0);
lean_dec(v_unused_313_);
v___x_195_ = v_col_173_;
v_isShared_196_ = v_isSharedCheck_311_;
goto v_resetjp_194_;
}
else
{
lean_dec(v_col_173_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_311_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
uint8_t v___x_197_; lean_object* v___y_199_; lean_object* v___x_249_; lean_object* v___y_251_; lean_object* v_i_252_; lean_object* v___y_258_; lean_object* v___y_268_; lean_object* v_i_269_; lean_object* v___x_284_; 
v___x_197_ = 1;
v___x_249_ = lean_box(0);
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(v_modSet_191_, v_root_172_);
switch(lean_obj_tag(v___x_284_))
{
case 0:
{
lean_dec_ref_known(v___x_284_, 3);
v___y_199_ = v_modSet_191_;
goto v___jp_198_;
}
case 1:
{
lean_object* v_index_285_; lean_object* v_size_286_; lean_object* v_keyArray_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_index_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_index_285_);
lean_dec_ref_known(v___x_284_, 1);
v_size_286_ = lean_ctor_get(v_modSet_191_, 0);
v_keyArray_287_ = lean_ctor_get(v_modSet_191_, 1);
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_add(v_size_286_, v___x_288_);
v___x_290_ = lean_array_get_size(v_keyArray_287_);
v___x_291_ = lean_nat_dec_lt(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_dec(v___x_289_);
lean_dec(v_index_285_);
goto v___jp_274_;
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_292_ = lean_unsigned_to_nat(4u);
v___x_293_ = lean_nat_mul(v___x_289_, v___x_292_);
v___x_294_ = lean_unsigned_to_nat(3u);
v___x_295_ = lean_nat_mul(v___x_290_, v___x_294_);
v___x_296_ = lean_nat_dec_le(v___x_293_, v___x_295_);
lean_dec(v___x_295_);
lean_dec(v___x_293_);
if (v___x_296_ == 0)
{
lean_dec(v___x_289_);
lean_dec(v_index_285_);
goto v___jp_274_;
}
else
{
lean_object* v___x_297_; 
lean_inc_ref(v_root_172_);
v___x_297_ = l_Std_DHashMap_Raw_setEntry___redArg(v_modSet_191_, v___x_289_, v_index_285_, v_root_172_, v___x_249_);
lean_dec(v_index_285_);
v___y_199_ = v___x_297_;
goto v___jp_198_;
}
}
}
default: 
{
lean_object* v_size_298_; lean_object* v_keyArray_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v_size_298_ = lean_ctor_get(v_modSet_191_, 0);
v_keyArray_299_ = lean_ctor_get(v_modSet_191_, 1);
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_add(v_size_298_, v___x_300_);
v___x_302_ = lean_array_get_size(v_keyArray_299_);
v___x_303_ = lean_nat_dec_lt(v___x_301_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
lean_dec(v___x_301_);
v___x_304_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(v_modSet_191_);
lean_dec_ref(v_modSet_191_);
v___y_258_ = v___x_304_;
goto v___jp_257_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_305_ = lean_unsigned_to_nat(4u);
v___x_306_ = lean_nat_mul(v___x_301_, v___x_305_);
lean_dec(v___x_301_);
v___x_307_ = lean_unsigned_to_nat(3u);
v___x_308_ = lean_nat_mul(v___x_302_, v___x_307_);
v___x_309_ = lean_nat_dec_le(v___x_306_, v___x_308_);
lean_dec(v___x_308_);
lean_dec(v___x_306_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; 
v___x_310_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(v_modSet_191_);
lean_dec_ref(v_modSet_191_);
v___y_258_ = v___x_310_;
goto v___jp_257_;
}
else
{
v___y_258_ = v_modSet_191_;
goto v___jp_257_;
}
}
}
}
v___jp_198_:
{
lean_object* v_lib_200_; lean_object* v_pkg_201_; lean_object* v_name_202_; lean_object* v_keyName_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_lib_200_ = lean_ctor_get(v_root_172_, 0);
v_pkg_201_ = lean_ctor_get(v_lib_200_, 0);
v_name_202_ = lean_ctor_get(v_root_172_, 1);
v_keyName_203_ = lean_ctor_get(v_pkg_201_, 2);
v___x_204_ = l_Lake_Module_importsFacet;
lean_inc(v_name_202_);
lean_inc(v_keyName_203_);
v___x_205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_205_, 0, v_keyName_203_);
lean_ctor_set(v___x_205_, 1, v_name_202_);
v___x_206_ = l_Lake_Module_keyword;
lean_inc_ref(v_root_172_);
v___x_207_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
lean_ctor_set(v___x_207_, 2, v_root_172_);
lean_ctor_set(v___x_207_, 3, v___x_204_);
lean_inc_ref(v_a_175_);
lean_inc_ref(v_a_179_);
lean_inc(v_a_178_);
lean_inc(v_a_177_);
lean_inc(v_a_176_);
v___x_208_ = lean_apply_7(v_a_175_, v___x_207_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, lean_box(0));
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v_a_210_; lean_object* v_task_211_; lean_object* v___x_212_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
v_a_210_ = lean_ctor_get(v___x_208_, 1);
lean_inc(v_a_210_);
lean_dec_ref_known(v___x_208_, 2);
v_task_211_ = lean_ctor_get(v_a_209_, 0);
lean_inc_ref(v_task_211_);
lean_dec(v_a_209_);
v___x_212_ = lean_io_wait(v_task_211_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; lean_object* v_col_215_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref_known(v___x_212_, 2);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 1, v___y_199_);
v_col_215_ = v___x_195_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_mods_190_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v___y_199_);
lean_ctor_set_uint8(v_reuseFailAlloc_232_, sizeof(void*)*2, v_hasErrors_192_);
v_col_215_ = v_reuseFailAlloc_232_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
size_t v_sz_216_; size_t v___x_217_; lean_object* v___x_218_; 
v_sz_216_ = lean_array_size(v_a_213_);
v___x_217_ = ((size_t)0ULL);
v___x_218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1(v_self_171_, v_a_213_, v_sz_216_, v___x_217_, v_col_215_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_210_);
lean_dec(v_a_213_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v_a_220_; lean_object* v_mods_221_; lean_object* v_modSet_222_; uint8_t v_hasErrors_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_231_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_a_219_);
v_a_220_ = lean_ctor_get(v___x_218_, 1);
lean_inc(v_a_220_);
lean_dec_ref_known(v___x_218_, 2);
v_mods_221_ = lean_ctor_get(v_a_219_, 0);
v_modSet_222_ = lean_ctor_get(v_a_219_, 1);
v_hasErrors_223_ = lean_ctor_get_uint8(v_a_219_, sizeof(void*)*2);
v_isSharedCheck_231_ = !lean_is_exclusive(v_a_219_);
if (v_isSharedCheck_231_ == 0)
{
v___x_225_ = v_a_219_;
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_modSet_222_);
lean_inc(v_mods_221_);
lean_dec(v_a_219_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = lean_array_push(v_mods_221_, v_root_172_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_227_);
v___x_229_ = v___x_225_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_modSet_222_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*2, v_hasErrors_223_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
v_col_183_ = v___x_229_;
v___y_184_ = v_a_220_;
goto v___jp_182_;
}
}
}
else
{
lean_dec_ref(v_root_172_);
return v___x_218_;
}
}
}
else
{
lean_dec_ref_known(v___x_212_, 2);
lean_dec_ref(v_a_175_);
if (v_viaImport_174_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_233_ = lean_array_push(v_mods_190_, v_root_172_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 1, v___y_199_);
lean_ctor_set(v___x_195_, 0, v___x_233_);
v___x_235_ = v___x_195_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___y_199_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*2, v___x_197_);
v___y_187_ = v_a_210_;
v___y_188_ = v___x_235_;
goto v___jp_186_;
}
}
else
{
lean_object* v___x_238_; 
lean_dec_ref(v_root_172_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 1, v___y_199_);
v___x_238_ = v___x_195_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_mods_190_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___y_199_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_ctor_set_uint8(v___x_238_, sizeof(void*)*2, v___x_197_);
v___y_187_ = v_a_210_;
v___y_188_ = v___x_238_;
goto v___jp_186_;
}
}
}
}
else
{
lean_object* v_a_240_; lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec_ref(v___y_199_);
lean_del_object(v___x_195_);
lean_dec_ref(v_mods_190_);
lean_dec_ref(v_a_175_);
lean_dec_ref(v_root_172_);
v_a_240_ = lean_ctor_get(v___x_208_, 0);
v_a_241_ = lean_ctor_get(v___x_208_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_208_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_inc(v_a_240_);
lean_dec(v___x_208_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_240_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
v___jp_250_:
{
lean_object* v_size_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_size_253_ = lean_ctor_get(v___y_251_, 0);
v___x_254_ = lean_unsigned_to_nat(1u);
v___x_255_ = lean_nat_add(v_size_253_, v___x_254_);
lean_inc_ref(v_root_172_);
v___x_256_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_251_, v___x_255_, v_i_252_, v_root_172_, v___x_249_);
lean_dec(v_i_252_);
v___y_199_ = v___x_256_;
goto v___jp_198_;
}
v___jp_257_:
{
lean_object* v___x_259_; 
v___x_259_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(v___y_258_, v_root_172_);
switch(lean_obj_tag(v___x_259_))
{
case 0:
{
lean_object* v_index_260_; lean_object* v_size_261_; lean_object* v___x_262_; 
v_index_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_index_260_);
lean_dec_ref_known(v___x_259_, 3);
v_size_261_ = lean_ctor_get(v___y_258_, 0);
lean_inc(v_size_261_);
lean_inc_ref(v_root_172_);
v___x_262_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_258_, v_size_261_, v_index_260_, v_root_172_, v___x_249_);
lean_dec(v_index_260_);
v___y_199_ = v___x_262_;
goto v___jp_198_;
}
case 1:
{
lean_object* v_index_263_; 
v_index_263_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_index_263_);
lean_dec_ref_known(v___x_259_, 1);
v___y_251_ = v___y_258_;
v_i_252_ = v_index_263_;
goto v___jp_250_;
}
default: 
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_258_, v___x_264_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_index_266_; 
v_index_266_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_index_266_);
lean_dec_ref_known(v___x_265_, 1);
v___y_251_ = v___y_258_;
v_i_252_ = v_index_266_;
goto v___jp_250_;
}
else
{
v___y_199_ = v___y_258_;
goto v___jp_198_;
}
}
}
}
v___jp_267_:
{
lean_object* v_size_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_size_270_ = lean_ctor_get(v___y_268_, 0);
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_nat_add(v_size_270_, v___x_271_);
lean_inc_ref(v_root_172_);
v___x_273_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_268_, v___x_272_, v_i_269_, v_root_172_, v___x_249_);
lean_dec(v_i_269_);
v___y_199_ = v___x_273_;
goto v___jp_198_;
}
v___jp_274_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(v_modSet_191_);
lean_dec_ref(v_modSet_191_);
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(v___x_275_, v_root_172_);
switch(lean_obj_tag(v___x_276_))
{
case 0:
{
lean_object* v_index_277_; lean_object* v_size_278_; lean_object* v___x_279_; 
v_index_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_index_277_);
lean_dec_ref_known(v___x_276_, 3);
v_size_278_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_size_278_);
lean_inc_ref(v_root_172_);
v___x_279_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_275_, v_size_278_, v_index_277_, v_root_172_, v___x_249_);
lean_dec(v_index_277_);
v___y_199_ = v___x_279_;
goto v___jp_198_;
}
case 1:
{
lean_object* v_index_280_; 
v_index_280_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_index_280_);
lean_dec_ref_known(v___x_276_, 1);
v___y_268_ = v___x_275_;
v_i_269_ = v_index_280_;
goto v___jp_267_;
}
default: 
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_275_, v___x_281_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_index_283_; 
v_index_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_index_283_);
lean_dec_ref_known(v___x_282_, 1);
v___y_268_ = v___x_275_;
v_i_269_ = v_index_283_;
goto v___jp_267_;
}
else
{
v___y_199_ = v___x_275_;
goto v___jp_198_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_a_175_);
lean_dec_ref(v_root_172_);
v_col_183_ = v_col_173_;
v___y_184_ = v_a_180_;
goto v___jp_182_;
}
v___jp_182_:
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_col_183_);
lean_ctor_set(v___x_185_, 1, v___y_184_);
return v___x_185_;
}
v___jp_186_:
{
lean_object* v___x_189_; 
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___y_188_);
lean_ctor_set(v___x_189_, 1, v___y_187_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1(lean_object* v_self_314_, lean_object* v_as_315_, size_t v_sz_316_, size_t v_i_317_, lean_object* v_b_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_a_327_; lean_object* v_a_328_; uint8_t v___x_332_; 
v___x_332_ = lean_usize_dec_lt(v_i_317_, v_sz_316_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
lean_dec_ref(v___y_319_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v_b_318_);
lean_ctor_set(v___x_333_, 1, v___y_324_);
return v___x_333_;
}
else
{
lean_object* v_a_334_; lean_object* v_lib_335_; lean_object* v_name_336_; lean_object* v_name_337_; uint8_t v___x_338_; 
v_a_334_ = lean_array_uget_borrowed(v_as_315_, v_i_317_);
v_lib_335_ = lean_ctor_get(v_a_334_, 0);
v_name_336_ = lean_ctor_get(v_lib_335_, 1);
v_name_337_ = lean_ctor_get(v_self_314_, 1);
v___x_338_ = lean_name_eq(v_name_336_, v_name_337_);
if (v___x_338_ == 0)
{
v_a_327_ = v_b_318_;
v_a_328_ = v___y_324_;
goto v___jp_326_;
}
else
{
lean_object* v___x_339_; 
lean_inc_ref(v___y_319_);
lean_inc(v_a_334_);
v___x_339_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_314_, v_a_334_, v_b_318_, v___x_338_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v_a_341_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
v_a_341_ = lean_ctor_get(v___x_339_, 1);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_339_, 2);
v_a_327_ = v_a_340_;
v_a_328_ = v_a_341_;
goto v___jp_326_;
}
else
{
lean_dec_ref(v___y_319_);
return v___x_339_;
}
}
}
v___jp_326_:
{
size_t v___x_329_; size_t v___x_330_; 
v___x_329_ = ((size_t)1ULL);
v___x_330_ = lean_usize_add(v_i_317_, v___x_329_);
v_i_317_ = v___x_330_;
v_b_318_ = v_a_327_;
v___y_324_ = v_a_328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___boxed(lean_object* v_self_342_, lean_object* v_as_343_, lean_object* v_sz_344_, lean_object* v_i_345_, lean_object* v_b_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
size_t v_sz_boxed_354_; size_t v_i_boxed_355_; lean_object* v_res_356_; 
v_sz_boxed_354_ = lean_unbox_usize(v_sz_344_);
lean_dec(v_sz_344_);
v_i_boxed_355_ = lean_unbox_usize(v_i_345_);
lean_dec(v_i_345_);
v_res_356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1(v_self_342_, v_as_343_, v_sz_boxed_354_, v_i_boxed_355_, v_b_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v_as_343_);
lean_dec_ref(v_self_342_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object* v_self_357_, lean_object* v_root_358_, lean_object* v_col_359_, lean_object* v_viaImport_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
uint8_t v_viaImport_boxed_368_; lean_object* v_res_369_; 
v_viaImport_boxed_368_ = lean_unbox(v_viaImport_360_);
v_res_369_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_357_, v_root_358_, v_col_359_, v_viaImport_boxed_368_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_self_357_);
return v_res_369_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_object* v_00_u03b2_370_, lean_object* v_m_371_, lean_object* v_a_372_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_371_, v_a_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(lean_object* v_00_u03b2_374_, lean_object* v_m_375_, lean_object* v_a_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(v_00_u03b2_374_, v_m_375_, v_a_376_);
lean_dec_ref(v_a_376_);
lean_dec_ref(v_m_375_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(lean_object* v_00_u03b2_379_, lean_object* v_m_380_, lean_object* v_query_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(v_m_380_, v_query_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(lean_object* v_00_u03b2_383_, lean_object* v_m_384_, lean_object* v_query_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_00_u03b2_383_, v_m_384_, v_query_385_);
lean_dec_ref(v_query_385_);
lean_dec_ref(v_m_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3(lean_object* v_00_u03b2_387_, lean_object* v_m_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(v_m_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3___boxed(lean_object* v_00_u03b2_390_, lean_object* v_m_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3(v_00_u03b2_390_, v_m_391_);
lean_dec_ref(v_m_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(lean_object* v_00_u03b2_393_, lean_object* v_m_394_, lean_object* v_query_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_m_394_, v_query_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_397_, lean_object* v_m_398_, lean_object* v_query_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(v_00_u03b2_397_, v_m_398_, v_query_399_);
lean_dec_ref(v_query_399_);
lean_dec_ref(v_m_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2_spec__3(lean_object* v_00_u03b2_401_, lean_object* v_m_402_, lean_object* v_query_403_, lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2_spec__3___redArg(v_m_402_, v_query_403_, v_x_404_, v_x_405_, v_x_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2_spec__3___boxed(lean_object* v_00_u03b2_409_, lean_object* v_m_410_, lean_object* v_query_411_, lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2_spec__3(v_00_u03b2_409_, v_m_410_, v_query_411_, v_x_412_, v_x_413_, v_x_414_, v_x_415_);
lean_dec_ref(v_query_411_);
lean_dec_ref(v_m_410_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5(lean_object* v_00_u03b2_417_, lean_object* v_init_418_, lean_object* v_b_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5___redArg(v_init_418_, v_b_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5___boxed(lean_object* v_00_u03b2_421_, lean_object* v_init_422_, lean_object* v_b_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5(v_00_u03b2_421_, v_init_422_, v_b_423_);
lean_dec_ref(v_b_423_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_425_, lean_object* v_b_426_, lean_object* v_acc_427_, lean_object* v_i_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5_spec__6___redArg(v_b_426_, v_acc_427_, v_i_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_430_, lean_object* v_b_431_, lean_object* v_acc_432_, lean_object* v_i_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3_spec__5_spec__6(v_00_u03b2_430_, v_b_431_, v_acc_432_, v_i_433_);
lean_dec_ref(v_b_431_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(lean_object* v_self_435_, lean_object* v_as_436_, size_t v_sz_437_, size_t v_i_438_, lean_object* v_b_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
uint8_t v___x_447_; 
v___x_447_ = lean_usize_dec_lt(v_i_438_, v_sz_437_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
lean_dec_ref(v___y_440_);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_b_439_);
lean_ctor_set(v___x_448_, 1, v___y_445_);
return v___x_448_;
}
else
{
uint8_t v___x_449_; lean_object* v_a_450_; lean_object* v___x_451_; 
v___x_449_ = 0;
v_a_450_ = lean_array_uget_borrowed(v_as_436_, v_i_438_);
lean_inc_ref(v___y_440_);
lean_inc(v_a_450_);
v___x_451_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_435_, v_a_450_, v_b_439_, v___x_449_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v_a_453_; size_t v___x_454_; size_t v___x_455_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
v_a_453_ = lean_ctor_get(v___x_451_, 1);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_451_, 2);
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_add(v_i_438_, v___x_454_);
v_i_438_ = v___x_455_;
v_b_439_ = v_a_452_;
v___y_445_ = v_a_453_;
goto _start;
}
else
{
lean_dec_ref(v___y_440_);
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0___boxed(lean_object* v_self_457_, lean_object* v_as_458_, lean_object* v_sz_459_, lean_object* v_i_460_, lean_object* v_b_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
size_t v_sz_boxed_469_; size_t v_i_boxed_470_; lean_object* v_res_471_; 
v_sz_boxed_469_ = lean_unbox_usize(v_sz_459_);
lean_dec(v_sz_459_);
v_i_boxed_470_ = lean_unbox_usize(v_i_460_);
lean_dec(v_i_460_);
v_res_471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_457_, v_as_458_, v_sz_boxed_469_, v_i_boxed_470_, v_b_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v_as_458_);
lean_dec_ref(v_self_457_);
return v_res_471_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1));
v___x_475_ = l_Lake_BuildTrace_nil(v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(lean_object* v_self_477_, lean_object* v_col_478_, lean_object* v___x_479_, uint8_t v___x_480_, lean_object* v___x_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; 
lean_inc_ref(v_self_477_);
v___x_489_ = l_Lake_LeanLib_getModuleArray(v_self_477_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; size_t v_sz_491_; size_t v___x_492_; lean_object* v___x_493_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
v_sz_491_ = lean_array_size(v_a_490_);
v___x_492_ = ((size_t)0ULL);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_477_, v_a_490_, v_sz_491_, v___x_492_, v_col_478_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v_a_490_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_521_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_a_495_ = lean_ctor_get(v___x_493_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_521_ == 0)
{
v___x_497_ = v___x_493_;
v_isShared_498_ = v_isSharedCheck_521_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_521_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_mods_499_; uint8_t v_hasErrors_500_; lean_object* v___y_502_; 
v_mods_499_ = lean_ctor_get(v_a_494_, 0);
lean_inc_ref(v_mods_499_);
v_hasErrors_500_ = lean_ctor_get_uint8(v_a_494_, sizeof(void*)*2);
lean_dec(v_a_494_);
if (v_hasErrors_500_ == 0)
{
lean_dec_ref(v_self_477_);
v___y_502_ = v_a_495_;
goto v___jp_501_;
}
else
{
lean_object* v_name_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_name_514_ = lean_ctor_get(v_self_477_, 1);
lean_inc(v_name_514_);
lean_dec_ref(v_self_477_);
v___x_515_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_514_, v_hasErrors_500_);
v___x_516_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__3));
v___x_517_ = lean_string_append(v___x_515_, v___x_516_);
v___x_518_ = 3;
v___x_519_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*1, v___x_518_);
v___x_520_ = lean_array_push(v_a_495_, v___x_519_);
v___y_502_ = v___x_520_;
goto v___jp_501_;
}
v___jp_501_:
{
lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_503_ = lean_mk_empty_array_with_capacity(v___x_479_);
v___x_504_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_505_ = 0;
v___x_506_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_507_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_507_, 0, v___x_503_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
lean_ctor_set(v___x_507_, 2, v___x_479_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*3, v___x_505_);
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*3 + 1, v___x_480_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v___x_507_);
lean_ctor_set(v___x_497_, 0, v_mods_499_);
v___x_509_ = v___x_497_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_mods_499_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v___x_507_);
v___x_509_ = v_reuseFailAlloc_513_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_510_ = lean_task_pure(v___x_509_);
v___x_511_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v___x_481_);
lean_ctor_set(v___x_511_, 2, v___x_504_);
lean_ctor_set_uint8(v___x_511_, sizeof(void*)*3, v___x_480_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v___y_502_);
return v___x_512_;
}
}
}
}
else
{
lean_object* v_a_522_; lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec(v___x_481_);
lean_dec(v___x_479_);
lean_dec_ref(v_self_477_);
v_a_522_ = lean_ctor_get(v___x_493_, 0);
v_a_523_ = lean_ctor_get(v___x_493_, 1);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_493_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_inc(v_a_522_);
lean_dec(v___x_493_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_522_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_532_; uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref(v___y_482_);
lean_dec(v___x_481_);
lean_dec(v___x_479_);
lean_dec_ref(v_col_478_);
lean_dec_ref(v_self_477_);
v_a_531_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_489_, 1);
v___x_532_ = lean_io_error_to_string(v_a_531_);
v___x_533_ = 3;
v___x_534_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*1, v___x_533_);
v___x_535_ = lean_array_get_size(v___y_487_);
v___x_536_ = lean_array_push(v___y_487_, v___x_534_);
v___x_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed(lean_object* v_self_538_, lean_object* v_col_539_, lean_object* v___x_540_, lean_object* v___x_541_, lean_object* v___x_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
uint8_t v___x_7763__boxed_550_; lean_object* v_res_551_; 
v___x_7763__boxed_550_ = lean_unbox(v___x_541_);
v_res_551_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(v_self_538_, v_col_539_, v___x_540_, v___x_7763__boxed_550_, v___x_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec(v___y_545_);
lean_dec(v___y_544_);
return v_res_551_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1(void){
_start:
{
lean_object* v_cellCount_554_; lean_object* v___x_555_; 
v_cellCount_554_ = lean_unsigned_to_nat(16u);
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_554_);
return v___x_555_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2(void){
_start:
{
lean_object* v_cellCount_556_; lean_object* v___x_557_; 
v_cellCount_556_ = lean_unsigned_to_nat(16u);
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_556_);
return v___x_557_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_558_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_559_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1);
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___x_559_);
lean_ctor_set(v___x_561_, 2, v___x_558_);
return v___x_561_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__4(void){
_start:
{
uint8_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_col_565_; 
v___x_562_ = 0;
v___x_563_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3);
v___x_564_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0));
v_col_565_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_col_565_, 0, v___x_564_);
lean_ctor_set(v_col_565_, 1, v___x_563_);
lean_ctor_set_uint8(v_col_565_, sizeof(void*)*2, v___x_562_);
return v_col_565_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(lean_object* v_self_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; lean_object* v_col_577_; lean_object* v___x_578_; lean_object* v___f_579_; lean_object* v___x_580_; 
v___x_574_ = lean_box(0);
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = 0;
v_col_577_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__4);
v___x_578_ = lean_box(v___x_576_);
v___f_579_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed), 12, 5);
lean_closure_set(v___f_579_, 0, v_self_566_);
lean_closure_set(v___f_579_, 1, v_col_577_);
lean_closure_set(v___f_579_, 2, v___x_575_);
lean_closure_set(v___f_579_, 3, v___x_578_);
lean_closure_set(v___f_579_, 4, v___x_574_);
v___x_580_ = l_Lake_ensureJob___redArg(v___x_574_, v___f_579_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___boxed(lean_object* v_self_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(v_self_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
lean_dec(v_a_584_);
lean_dec(v_a_583_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(lean_object* v_as_591_, size_t v_i_592_, size_t v_stop_593_, lean_object* v_b_594_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = lean_usize_dec_eq(v_i_592_, v_stop_593_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v_name_597_; uint8_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; size_t v___x_603_; size_t v___x_604_; 
v___x_596_ = lean_array_uget_borrowed(v_as_591_, v_i_592_);
v_name_597_ = lean_ctor_get(v___x_596_, 1);
v___x_598_ = 1;
lean_inc(v_name_597_);
v___x_599_ = l_Lean_Name_toString(v_name_597_, v___x_598_);
v___x_600_ = lean_string_append(v_b_594_, v___x_599_);
lean_dec_ref(v___x_599_);
v___x_601_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_602_ = lean_string_append(v___x_600_, v___x_601_);
v___x_603_ = ((size_t)1ULL);
v___x_604_ = lean_usize_add(v_i_592_, v___x_603_);
v_i_592_ = v___x_604_;
v_b_594_ = v___x_602_;
goto _start;
}
else
{
return v_b_594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_606_, lean_object* v_i_607_, lean_object* v_stop_608_, lean_object* v_b_609_){
_start:
{
size_t v_i_boxed_610_; size_t v_stop_boxed_611_; lean_object* v_res_612_; 
v_i_boxed_610_ = lean_unbox_usize(v_i_607_);
lean_dec(v_i_607_);
v_stop_boxed_611_ = lean_unbox_usize(v_stop_608_);
lean_dec(v_stop_608_);
v_res_612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_as_606_, v_i_boxed_610_, v_stop_boxed_611_, v_b_609_);
lean_dec_ref(v_as_606_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(size_t v_sz_613_, size_t v_i_614_, lean_object* v_bs_615_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = lean_usize_dec_lt(v_i_614_, v_sz_613_);
if (v___x_616_ == 0)
{
return v_bs_615_;
}
else
{
lean_object* v_v_617_; lean_object* v_name_618_; lean_object* v___x_619_; lean_object* v_bs_x27_620_; lean_object* v___x_621_; lean_object* v___x_622_; size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; 
v_v_617_ = lean_array_uget_borrowed(v_bs_615_, v_i_614_);
v_name_618_ = lean_ctor_get(v_v_617_, 1);
lean_inc(v_name_618_);
v___x_619_ = lean_unsigned_to_nat(0u);
v_bs_x27_620_ = lean_array_uset(v_bs_615_, v_i_614_, v___x_619_);
v___x_621_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_618_, v___x_616_);
v___x_622_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
v___x_623_ = ((size_t)1ULL);
v___x_624_ = lean_usize_add(v_i_614_, v___x_623_);
v___x_625_ = lean_array_uset(v_bs_x27_620_, v_i_614_, v___x_622_);
v_i_614_ = v___x_624_;
v_bs_615_ = v___x_625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_627_, lean_object* v_i_628_, lean_object* v_bs_629_){
_start:
{
size_t v_sz_boxed_630_; size_t v_i_boxed_631_; lean_object* v_res_632_; 
v_sz_boxed_630_ = lean_unbox_usize(v_sz_627_);
lean_dec(v_sz_627_);
v_i_boxed_631_ = lean_unbox_usize(v_i_628_);
lean_dec(v_i_628_);
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_630_, v_i_boxed_631_, v_bs_629_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(lean_object* v_a_633_){
_start:
{
size_t v_sz_634_; size_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_sz_634_ = lean_array_size(v_a_633_);
v___x_635_ = ((size_t)0ULL);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_634_, v___x_635_, v_a_633_);
v___x_637_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(uint8_t v_fmt_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___y_641_; 
if (v_fmt_638_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_648_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_array_get_size(v_a_639_);
v___x_651_ = lean_nat_dec_lt(v___x_649_, v___x_650_);
if (v___x_651_ == 0)
{
lean_dec_ref(v_a_639_);
v___y_641_ = v___x_648_;
goto v___jp_640_;
}
else
{
uint8_t v___x_652_; 
v___x_652_ = lean_nat_dec_le(v___x_650_, v___x_650_);
if (v___x_652_ == 0)
{
if (v___x_651_ == 0)
{
lean_dec_ref(v_a_639_);
v___y_641_ = v___x_648_;
goto v___jp_640_;
}
else
{
size_t v___x_653_; size_t v___x_654_; lean_object* v___x_655_; 
v___x_653_ = ((size_t)0ULL);
v___x_654_ = lean_usize_of_nat(v___x_650_);
v___x_655_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_639_, v___x_653_, v___x_654_, v___x_648_);
lean_dec_ref(v_a_639_);
v___y_641_ = v___x_655_;
goto v___jp_640_;
}
}
else
{
size_t v___x_656_; size_t v___x_657_; lean_object* v___x_658_; 
v___x_656_ = ((size_t)0ULL);
v___x_657_ = lean_usize_of_nat(v___x_650_);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_639_, v___x_656_, v___x_657_, v___x_648_);
lean_dec_ref(v_a_639_);
v___y_641_ = v___x_658_;
goto v___jp_640_;
}
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(v_a_639_);
v___x_660_ = l_Lean_Json_compress(v___x_659_);
return v___x_660_;
}
v___jp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_string_utf8_byte_size(v___y_641_);
lean_inc_ref(v___y_641_);
v___x_645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_645_, 0, v___y_641_);
lean_ctor_set(v___x_645_, 1, v___x_643_);
lean_ctor_set(v___x_645_, 2, v___x_644_);
v___x_646_ = l_String_Slice_Pos_prevn(v___x_645_, v___x_644_, v___x_642_);
lean_dec_ref_known(v___x_645_, 3);
v___x_647_ = lean_string_utf8_extract_fast(v___y_641_, v___x_643_, v___x_646_);
lean_dec(v___x_646_);
lean_dec_ref(v___y_641_);
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0___boxed(lean_object* v_fmt_661_, lean_object* v_a_662_){
_start:
{
uint8_t v_fmt_boxed_663_; lean_object* v_res_664_; 
v_fmt_boxed_663_ = lean_unbox(v_fmt_661_);
v_res_664_ = l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(v_fmt_boxed_663_, v_a_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(lean_object* v_as_678_, size_t v_i_679_, size_t v_stop_680_, lean_object* v_b_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
uint8_t v___x_689_; 
v___x_689_ = lean_usize_dec_eq(v_i_679_, v_stop_680_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v_lib_691_; lean_object* v_pkg_692_; lean_object* v_name_693_; lean_object* v_keyName_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_690_ = lean_array_uget_borrowed(v_as_678_, v_i_679_);
v_lib_691_ = lean_ctor_get(v___x_690_, 0);
v_pkg_692_ = lean_ctor_get(v_lib_691_, 0);
v_name_693_ = lean_ctor_get(v___x_690_, 1);
v_keyName_694_ = lean_ctor_get(v_pkg_692_, 2);
v___x_695_ = l_Lake_Module_leanArtsFacet;
lean_inc(v_name_693_);
lean_inc(v_keyName_694_);
v___x_696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_696_, 0, v_keyName_694_);
lean_ctor_set(v___x_696_, 1, v_name_693_);
v___x_697_ = l_Lake_Module_keyword;
lean_inc(v___x_690_);
v___x_698_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
lean_ctor_set(v___x_698_, 2, v___x_690_);
lean_ctor_set(v___x_698_, 3, v___x_695_);
lean_inc_ref(v___y_682_);
lean_inc_ref(v___y_686_);
lean_inc(v___y_685_);
lean_inc(v___y_684_);
lean_inc(v___y_683_);
v___x_699_ = lean_apply_7(v___y_682_, v___x_698_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, lean_box(0));
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v_a_701_; lean_object* v___x_702_; size_t v___x_703_; size_t v___x_704_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
v_a_701_ = lean_ctor_get(v___x_699_, 1);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_699_, 2);
v___x_702_ = l_Lake_Job_mix___redArg(v_b_681_, v_a_700_);
v___x_703_ = ((size_t)1ULL);
v___x_704_ = lean_usize_add(v_i_679_, v___x_703_);
v_i_679_ = v___x_704_;
v_b_681_ = v___x_702_;
v___y_687_ = v_a_701_;
goto _start;
}
else
{
lean_object* v_a_706_; lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref(v___y_682_);
lean_dec_ref(v_b_681_);
v_a_706_ = lean_ctor_get(v___x_699_, 0);
v_a_707_ = lean_ctor_get(v___x_699_, 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_699_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_inc(v_a_706_);
lean_dec(v___x_699_);
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
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_706_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v_a_707_);
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
else
{
lean_object* v___x_715_; 
lean_dec_ref(v___y_682_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v_b_681_);
lean_ctor_set(v___x_715_, 1, v___y_687_);
return v___x_715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0___boxed(lean_object* v_as_716_, lean_object* v_i_717_, lean_object* v_stop_718_, lean_object* v_b_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
size_t v_i_boxed_727_; size_t v_stop_boxed_728_; lean_object* v_res_729_; 
v_i_boxed_727_ = lean_unbox_usize(v_i_717_);
lean_dec(v_i_717_);
v_stop_boxed_728_ = lean_unbox_usize(v_stop_718_);
lean_dec(v_stop_718_);
v_res_729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_as_716_, v_i_boxed_727_, v_stop_boxed_728_, v_b_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v_as_716_);
return v_res_729_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; uint8_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_734_ = 0;
v___x_735_ = 0;
v___x_736_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v___x_737_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v___x_733_);
lean_ctor_set(v___x_737_, 2, v___x_732_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*3, v___x_735_);
lean_ctor_set_uint8(v___x_737_, sizeof(void*)*3 + 1, v___x_734_);
return v___x_737_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1);
v___x_739_ = lean_box(0);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v___x_738_);
return v___x_740_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2);
v___x_742_ = lean_task_pure(v___x_741_);
return v___x_742_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4(void){
_start:
{
uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_743_ = 0;
v___x_744_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_745_ = lean_box(0);
v___x_746_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3);
v___x_747_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v___x_745_);
lean_ctor_set(v___x_747_, 2, v___x_744_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*3, v___x_743_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(lean_object* v_self_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_pkg_756_; lean_object* v_name_757_; lean_object* v_keyName_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_pkg_756_ = lean_ctor_get(v_self_748_, 0);
v_name_757_ = lean_ctor_get(v_self_748_, 1);
v_keyName_758_ = lean_ctor_get(v_pkg_756_, 2);
v___x_759_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_757_);
lean_inc(v_keyName_758_);
v___x_760_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_760_, 0, v_keyName_758_);
lean_ctor_set(v___x_760_, 1, v_name_757_);
v___x_761_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_762_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
lean_ctor_set(v___x_762_, 2, v_self_748_);
lean_ctor_set(v___x_762_, 3, v___x_759_);
lean_inc_ref(v_a_749_);
lean_inc_ref(v_a_753_);
lean_inc(v_a_752_);
lean_inc(v_a_751_);
lean_inc(v_a_750_);
v___x_763_ = lean_apply_7(v_a_749_, v___x_762_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, lean_box(0));
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v_a_765_; lean_object* v___x_766_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
v_a_765_ = lean_ctor_get(v___x_763_, 1);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_763_, 2);
v___x_766_ = l_Lake_Job_await___redArg(v_a_764_, v_a_765_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_789_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_a_768_ = lean_ctor_get(v___x_766_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_789_ == 0)
{
v___x_770_ = v___x_766_;
v_isShared_771_ = v_isSharedCheck_789_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_789_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4);
v___x_774_ = lean_array_get_size(v_a_767_);
v___x_775_ = lean_nat_dec_lt(v___x_772_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_777_; 
lean_dec(v_a_767_);
lean_dec_ref(v_a_749_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_773_);
v___x_777_ = v___x_770_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_a_768_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
else
{
uint8_t v___x_779_; 
v___x_779_ = lean_nat_dec_le(v___x_774_, v___x_774_);
if (v___x_779_ == 0)
{
if (v___x_775_ == 0)
{
lean_object* v___x_781_; 
lean_dec(v_a_767_);
lean_dec_ref(v_a_749_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_773_);
v___x_781_ = v___x_770_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_a_768_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
else
{
size_t v___x_783_; size_t v___x_784_; lean_object* v___x_785_; 
lean_del_object(v___x_770_);
v___x_783_ = ((size_t)0ULL);
v___x_784_ = lean_usize_of_nat(v___x_774_);
v___x_785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_767_, v___x_783_, v___x_784_, v___x_773_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_768_);
lean_dec(v_a_767_);
return v___x_785_;
}
}
else
{
size_t v___x_786_; size_t v___x_787_; lean_object* v___x_788_; 
lean_del_object(v___x_770_);
v___x_786_ = ((size_t)0ULL);
v___x_787_ = lean_usize_of_nat(v___x_774_);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_767_, v___x_786_, v___x_787_, v___x_773_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_768_);
lean_dec(v_a_767_);
return v___x_788_;
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v_a_749_);
v_a_790_ = lean_ctor_get(v___x_766_, 0);
v_a_791_ = lean_ctor_get(v___x_766_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_766_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_inc(v_a_790_);
lean_dec(v___x_766_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_790_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v_a_749_);
v_a_799_ = lean_ctor_get(v___x_763_, 0);
v_a_800_ = lean_ctor_get(v___x_763_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_763_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_inc(v_a_799_);
lean_dec(v___x_763_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_799_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___boxed(lean_object* v_self_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(v_self_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec(v_a_811_);
lean_dec(v_a_810_);
return v_res_816_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_box(0);
v___x_818_ = l_Lean_Json_compress(v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(uint8_t v_fmt_819_){
_start:
{
if (v_fmt_819_ == 0)
{
lean_object* v___x_820_; 
v___x_820_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
return v___x_820_;
}
else
{
lean_object* v___x_821_; 
v___x_821_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_822_){
_start:
{
uint8_t v_fmt_boxed_823_; lean_object* v_res_824_; 
v_fmt_boxed_823_ = lean_unbox(v_fmt_822_);
v_res_824_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_boxed_823_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(uint8_t v_fmt_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___boxed(lean_object* v_fmt_828_, lean_object* v_a_829_){
_start:
{
uint8_t v_fmt_boxed_830_; lean_object* v_res_831_; 
v_fmt_boxed_830_ = lean_unbox(v_fmt_828_);
v_res_831_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(v_fmt_boxed_830_, v_a_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0(uint8_t v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v___y_832_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
uint8_t v___y_68__boxed_837_; lean_object* v_res_838_; 
v___y_68__boxed_837_ = lean_unbox(v___y_835_);
v_res_838_ = l_Lake_LeanLib_leanArtsFacetConfig___lam__0(v___y_68__boxed_837_, v___y_836_);
return v_res_838_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_841_; uint8_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___f_841_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_842_ = 1;
v___x_843_ = l_Lake_instDataKindUnit;
v___x_844_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__1));
v___x_845_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_846_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_846_, 0, v___x_845_);
lean_ctor_set(v___x_846_, 1, v___x_844_);
lean_ctor_set(v___x_846_, 2, v___x_843_);
lean_ctor_set(v___x_846_, 3, v___f_841_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*4, v___x_842_);
lean_ctor_set_uint8(v___x_846_, sizeof(void*)*4 + 1, v___x_842_);
return v___x_846_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig(void){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = lean_obj_once(&l_Lake_LeanLib_leanArtsFacetConfig___closed__2, &l_Lake_LeanLib_leanArtsFacetConfig___closed__2_once, _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(lean_object* v_a_848_, lean_object* v_x_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lake_ModuleFacet_fetch___redArg(v_x_849_, v_a_848_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object* v_a_858_, lean_object* v_x_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(v_a_858_, v_x_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
lean_dec(v___y_862_);
lean_dec(v___y_861_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(uint8_t v_shouldExport_868_, lean_object* v___x_869_, lean_object* v_bs_870_, lean_object* v_a_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_lib_879_; lean_object* v_config_880_; lean_object* v_nativeFacets_881_; lean_object* v___f_882_; lean_object* v___x_883_; lean_object* v___x_884_; size_t v_sz_885_; size_t v___x_886_; lean_object* v___x_197263__overap_887_; lean_object* v___x_888_; 
v_lib_879_ = lean_ctor_get(v_a_871_, 0);
v_config_880_ = lean_ctor_get(v_lib_879_, 2);
v_nativeFacets_881_ = lean_ctor_get(v_config_880_, 8);
lean_inc_ref(v_nativeFacets_881_);
v___f_882_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed), 9, 1);
lean_closure_set(v___f_882_, 0, v_a_871_);
v___x_883_ = lean_box(v_shouldExport_868_);
v___x_884_ = lean_apply_1(v_nativeFacets_881_, v___x_883_);
v_sz_885_ = lean_array_size(v___x_884_);
v___x_886_ = ((size_t)0ULL);
v___x_197263__overap_887_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_869_, v___f_882_, v_sz_885_, v___x_886_, v___x_884_);
lean_inc_ref(v___y_876_);
lean_inc(v___y_875_);
lean_inc(v___y_874_);
lean_inc(v___y_873_);
v___x_888_ = lean_apply_7(v___x_197263__overap_887_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, lean_box(0));
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_898_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_a_890_ = lean_ctor_get(v___x_888_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_898_ == 0)
{
v___x_892_ = v___x_888_;
v_isShared_893_ = v_isSharedCheck_898_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_898_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_894_ = l_Array_append___redArg(v_bs_870_, v_a_889_);
lean_dec(v_a_889_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_894_);
v___x_896_ = v___x_892_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_a_890_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
else
{
lean_dec_ref(v_bs_870_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed(lean_object* v_shouldExport_899_, lean_object* v___x_900_, lean_object* v_bs_901_, lean_object* v_a_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
uint8_t v_shouldExport_boxed_910_; lean_object* v_res_911_; 
v_shouldExport_boxed_910_ = lean_unbox(v_shouldExport_899_);
v_res_911_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(v_shouldExport_boxed_910_, v___x_900_, v_bs_901_, v_a_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec(v___y_905_);
lean_dec(v___y_904_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(lean_object* v___x_912_, lean_object* v_pkg_913_, lean_object* v_x_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lake_Target_fetchIn___redArg(v___x_912_, v_pkg_913_, v_x_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object* v___x_923_, lean_object* v_pkg_924_, lean_object* v_x_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(v___x_923_, v_pkg_924_, v_x_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec(v___y_928_);
lean_dec(v___y_927_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object* v_a_934_, lean_object* v_x_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_log_944_; uint8_t v_action_945_; uint8_t v_wantsRebuild_946_; lean_object* v_trace_947_; lean_object* v_buildTime_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_log_944_ = lean_ctor_get(v___y_942_, 0);
v_action_945_ = lean_ctor_get_uint8(v___y_942_, sizeof(void*)*3);
v_wantsRebuild_946_ = lean_ctor_get_uint8(v___y_942_, sizeof(void*)*3 + 1);
v_trace_947_ = lean_ctor_get(v___y_942_, 1);
v_buildTime_948_ = lean_ctor_get(v___y_942_, 2);
v___x_949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_950_ = lean_string_append(v___y_936_, v___x_949_);
v___x_951_ = lean_io_prim_handle_put_str(v_a_934_, v___x_950_);
lean_dec_ref(v___x_950_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_953_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_a_952_);
lean_ctor_set(v___x_953_, 1, v___y_942_);
return v___x_953_;
}
else
{
lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_967_; 
lean_inc(v_buildTime_948_);
lean_inc_ref(v_trace_947_);
lean_inc_ref(v_log_944_);
v_isSharedCheck_967_ = !lean_is_exclusive(v___y_942_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; lean_object* v_unused_969_; lean_object* v_unused_970_; 
v_unused_968_ = lean_ctor_get(v___y_942_, 2);
lean_dec(v_unused_968_);
v_unused_969_ = lean_ctor_get(v___y_942_, 1);
lean_dec(v_unused_969_);
v_unused_970_ = lean_ctor_get(v___y_942_, 0);
lean_dec(v_unused_970_);
v___x_955_ = v___y_942_;
v_isShared_956_ = v_isSharedCheck_967_;
goto v_resetjp_954_;
}
else
{
lean_dec(v___y_942_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_967_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v_a_957_; lean_object* v___x_958_; uint8_t v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v_a_957_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_951_, 1);
v___x_958_ = lean_io_error_to_string(v_a_957_);
v___x_959_ = 3;
v___x_960_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set_uint8(v___x_960_, sizeof(void*)*1, v___x_959_);
v___x_961_ = lean_array_get_size(v_log_944_);
v___x_962_ = lean_array_push(v_log_944_, v___x_960_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_962_);
v___x_964_ = v___x_955_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_trace_947_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_buildTime_948_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3, v_action_945_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3 + 1, v_wantsRebuild_946_);
v___x_964_ = v_reuseFailAlloc_966_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; 
v___x_965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_961_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
return v___x_965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object* v_a_971_, lean_object* v_x_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(v_a_971_, v_x_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v_a_971_);
return v_res_981_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_989_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3));
v___x_990_ = lean_unsigned_to_nat(5u);
v___x_991_ = lean_mk_empty_array_with_capacity(v___x_990_);
v___x_992_ = lean_array_push(v___x_991_, v___x_989_);
return v___x_992_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4));
v___x_994_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6);
v___x_995_ = lean_array_push(v___x_994_, v___x_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(uint8_t v_bootstrap_998_, lean_object* v___y_999_, lean_object* v_oFiles_1000_, uint8_t v_shouldExport_1001_, uint8_t v___x_1002_, lean_object* v___x_1003_, size_t v___x_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
if (v_bootstrap_998_ == 0)
{
lean_object* v_toContext_1012_; lean_object* v_lakeEnv_1013_; lean_object* v_lean_1014_; lean_object* v_log_1015_; uint8_t v_action_1016_; uint8_t v_wantsRebuild_1017_; lean_object* v_trace_1018_; lean_object* v_buildTime_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v___y_1005_);
lean_dec_ref(v___x_1003_);
v_toContext_1012_ = lean_ctor_get(v___y_1009_, 1);
v_lakeEnv_1013_ = lean_ctor_get(v_toContext_1012_, 0);
v_lean_1014_ = lean_ctor_get(v_lakeEnv_1013_, 1);
v_log_1015_ = lean_ctor_get(v___y_1010_, 0);
v_action_1016_ = lean_ctor_get_uint8(v___y_1010_, sizeof(void*)*3);
v_wantsRebuild_1017_ = lean_ctor_get_uint8(v___y_1010_, sizeof(void*)*3 + 1);
v_trace_1018_ = lean_ctor_get(v___y_1010_, 1);
v_buildTime_1019_ = lean_ctor_get(v___y_1010_, 2);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___y_1010_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1021_ = v___y_1010_;
v_isShared_1022_ = v_isSharedCheck_1049_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_buildTime_1019_);
lean_inc(v_trace_1018_);
lean_inc(v_log_1015_);
lean_dec(v___y_1010_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1049_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v_ar_1023_; lean_object* v___x_1024_; 
v_ar_1023_ = lean_ctor_get(v_lean_1014_, 13);
lean_inc_ref(v_ar_1023_);
v___x_1024_ = l_Lake_compileStaticLib(v___y_999_, v_oFiles_1000_, v_ar_1023_, v_bootstrap_998_, v_log_1015_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1036_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_a_1026_ = lean_ctor_get(v___x_1024_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1028_ = v___x_1024_;
v_isShared_1029_ = v_isSharedCheck_1036_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1036_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v_a_1026_);
v___x_1031_ = v___x_1021_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1026_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_trace_1018_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v_buildTime_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*3, v_action_1016_);
lean_ctor_set_uint8(v_reuseFailAlloc_1035_, sizeof(void*)*3 + 1, v_wantsRebuild_1017_);
v___x_1031_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
lean_object* v___x_1033_; 
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 1, v___x_1031_);
v___x_1033_ = v___x_1028_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1025_);
lean_ctor_set(v_reuseFailAlloc_1034_, 1, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1048_; 
v_a_1037_ = lean_ctor_get(v___x_1024_, 0);
v_a_1038_ = lean_ctor_get(v___x_1024_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1040_ = v___x_1024_;
v_isShared_1041_ = v_isSharedCheck_1048_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_inc(v_a_1037_);
lean_dec(v___x_1024_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1048_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v_a_1038_);
v___x_1043_ = v___x_1021_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1038_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_trace_1018_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_buildTime_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1047_, sizeof(void*)*3, v_action_1016_);
lean_ctor_set_uint8(v_reuseFailAlloc_1047_, sizeof(void*)*3 + 1, v_wantsRebuild_1017_);
v___x_1043_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1045_; 
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v___x_1043_);
v___x_1045_ = v___x_1040_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1037_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
}
else
{
uint8_t v___x_1050_; 
v___x_1050_ = l_System_Platform_isOSX;
if (v___x_1050_ == 0)
{
uint8_t v___x_1051_; 
lean_dec_ref(v___y_1005_);
lean_dec_ref(v___x_1003_);
v___x_1051_ = l_System_Platform_isWindows;
if (v___x_1051_ == 0)
{
lean_object* v_toContext_1052_; lean_object* v_lakeEnv_1053_; lean_object* v_lean_1054_; lean_object* v_log_1055_; uint8_t v_action_1056_; uint8_t v_wantsRebuild_1057_; lean_object* v_trace_1058_; lean_object* v_buildTime_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1089_; 
v_toContext_1052_ = lean_ctor_get(v___y_1009_, 1);
v_lakeEnv_1053_ = lean_ctor_get(v_toContext_1052_, 0);
v_lean_1054_ = lean_ctor_get(v_lakeEnv_1053_, 1);
v_log_1055_ = lean_ctor_get(v___y_1010_, 0);
v_action_1056_ = lean_ctor_get_uint8(v___y_1010_, sizeof(void*)*3);
v_wantsRebuild_1057_ = lean_ctor_get_uint8(v___y_1010_, sizeof(void*)*3 + 1);
v_trace_1058_ = lean_ctor_get(v___y_1010_, 1);
v_buildTime_1059_ = lean_ctor_get(v___y_1010_, 2);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___y_1010_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1061_ = v___y_1010_;
v_isShared_1062_ = v_isSharedCheck_1089_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_buildTime_1059_);
lean_inc(v_trace_1058_);
lean_inc(v_log_1055_);
lean_dec(v___y_1010_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1089_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v_ar_1063_; lean_object* v___x_1064_; 
v_ar_1063_ = lean_ctor_get(v_lean_1054_, 13);
lean_inc_ref(v_ar_1063_);
v___x_1064_ = l_Lake_compileStaticLib(v___y_999_, v_oFiles_1000_, v_ar_1063_, v___x_1051_, v_log_1055_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1076_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
v_a_1066_ = lean_ctor_get(v___x_1064_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1068_ = v___x_1064_;
v_isShared_1069_ = v_isSharedCheck_1076_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_inc(v_a_1065_);
lean_dec(v___x_1064_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1076_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v_a_1066_);
v___x_1071_ = v___x_1061_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1066_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_trace_1058_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_buildTime_1059_);
lean_ctor_set_uint8(v_reuseFailAlloc_1075_, sizeof(void*)*3, v_action_1056_);
lean_ctor_set_uint8(v_reuseFailAlloc_1075_, sizeof(void*)*3 + 1, v_wantsRebuild_1057_);
v___x_1071_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1073_; 
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 1, v___x_1071_);
v___x_1073_ = v___x_1068_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1065_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1088_; 
v_a_1077_ = lean_ctor_get(v___x_1064_, 0);
v_a_1078_ = lean_ctor_get(v___x_1064_, 1);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1080_ = v___x_1064_;
v_isShared_1081_ = v_isSharedCheck_1088_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_inc(v_a_1077_);
lean_dec(v___x_1064_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1088_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v_a_1078_);
v___x_1083_ = v___x_1061_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1078_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v_trace_1058_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_buildTime_1059_);
lean_ctor_set_uint8(v_reuseFailAlloc_1087_, sizeof(void*)*3, v_action_1056_);
lean_ctor_set_uint8(v_reuseFailAlloc_1087_, sizeof(void*)*3 + 1, v_wantsRebuild_1057_);
v___x_1083_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1085_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v___x_1083_);
v___x_1085_ = v___x_1080_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1077_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1090_; lean_object* v_lakeEnv_1091_; lean_object* v_lean_1092_; lean_object* v_log_1093_; uint8_t v_action_1094_; uint8_t v_wantsRebuild_1095_; lean_object* v_trace_1096_; lean_object* v_buildTime_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1127_; 
v_toContext_1090_ = lean_ctor_get(v___y_1009_, 1);
v_lakeEnv_1091_ = lean_ctor_get(v_toContext_1090_, 0);
v_lean_1092_ = lean_ctor_get(v_lakeEnv_1091_, 1);
v_log_1093_ = lean_ctor_get(v___y_1010_, 0);
v_action_1094_ = lean_ctor_get_uint8(v___y_1010_, sizeof(void*)*3);
v_wantsRebuild_1095_ = lean_ctor_get_uint8(v___y_1010_, sizeof(void*)*3 + 1);
v_trace_1096_ = lean_ctor_get(v___y_1010_, 1);
v_buildTime_1097_ = lean_ctor_get(v___y_1010_, 2);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___y_1010_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1099_ = v___y_1010_;
v_isShared_1100_ = v_isSharedCheck_1127_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_buildTime_1097_);
lean_inc(v_trace_1096_);
lean_inc(v_log_1093_);
lean_dec(v___y_1010_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1127_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_ar_1101_; lean_object* v___x_1102_; 
v_ar_1101_ = lean_ctor_get(v_lean_1092_, 13);
lean_inc_ref(v_ar_1101_);
v___x_1102_ = l_Lake_compileStaticLib(v___y_999_, v_oFiles_1000_, v_ar_1101_, v_shouldExport_1001_, v_log_1093_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1114_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_a_1104_ = lean_ctor_get(v___x_1102_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1106_ = v___x_1102_;
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1114_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v_a_1104_);
v___x_1109_ = v___x_1099_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1104_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_trace_1096_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_buildTime_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, sizeof(void*)*3, v_action_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, sizeof(void*)*3 + 1, v_wantsRebuild_1095_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1111_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 1, v___x_1109_);
v___x_1111_ = v___x_1106_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1103_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___x_1109_);
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
lean_object* v_a_1115_; lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1126_; 
v_a_1115_ = lean_ctor_get(v___x_1102_, 0);
v_a_1116_ = lean_ctor_get(v___x_1102_, 1);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1118_ = v___x_1102_;
v_isShared_1119_ = v_isSharedCheck_1126_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_inc(v_a_1115_);
lean_dec(v___x_1102_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1126_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v_a_1116_);
v___x_1121_ = v___x_1099_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1116_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_trace_1096_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v_buildTime_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1125_, sizeof(void*)*3, v_action_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1125_, sizeof(void*)*3 + 1, v_wantsRebuild_1095_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1123_; 
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 1, v___x_1121_);
v___x_1123_ = v___x_1118_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1115_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1128_; uint8_t v_action_1129_; uint8_t v_wantsRebuild_1130_; lean_object* v_trace_1131_; lean_object* v_buildTime_1132_; lean_object* v___x_1133_; 
v_log_1128_ = lean_ctor_get(v___y_1010_, 0);
v_action_1129_ = lean_ctor_get_uint8(v___y_1010_, sizeof(void*)*3);
v_wantsRebuild_1130_ = lean_ctor_get_uint8(v___y_1010_, sizeof(void*)*3 + 1);
v_trace_1131_ = lean_ctor_get(v___y_1010_, 1);
v_buildTime_1132_ = lean_ctor_get(v___y_1010_, 2);
lean_inc_ref(v___y_999_);
v___x_1133_ = l_Lake_createParentDirs(v___y_999_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v_a_1137_; lean_object* v___y_1184_; uint8_t v___x_1186_; lean_object* v___x_1187_; 
lean_dec_ref_known(v___x_1133_, 1);
v___x_1134_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_999_);
v___x_1135_ = l_System_FilePath_addExtension(v___y_999_, v___x_1134_);
v___x_1186_ = 1;
v___x_1187_ = lean_io_prim_handle_mk(v___x_1135_, v___x_1186_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
v___x_1189_ = l_Lake_EquipT_instMonad___redArg(v___x_1003_);
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_array_get_size(v_oFiles_1000_);
v___x_1192_ = lean_nat_dec_lt(v___x_1190_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_dec_ref(v___x_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v___y_1005_);
lean_dec_ref(v_oFiles_1000_);
v_a_1137_ = v___y_1010_;
goto v___jp_1136_;
}
else
{
lean_object* v___f_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___f_1193_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1193_, 0, v_a_1188_);
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_nat_dec_le(v___x_1191_, v___x_1191_);
if (v___x_1195_ == 0)
{
if (v___x_1192_ == 0)
{
lean_dec_ref(v___f_1193_);
lean_dec_ref(v___x_1189_);
lean_dec_ref(v___y_1005_);
lean_dec_ref(v_oFiles_1000_);
v_a_1137_ = v___y_1010_;
goto v___jp_1136_;
}
else
{
size_t v___x_1196_; lean_object* v___x_197422__overap_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_usize_of_nat(v___x_1191_);
v___x_197422__overap_1197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1189_, v___f_1193_, v_oFiles_1000_, v___x_1004_, v___x_1196_, v___x_1194_);
lean_inc_ref(v___y_1009_);
lean_inc(v___y_1008_);
lean_inc(v___y_1007_);
lean_inc(v___y_1006_);
v___x_1198_ = lean_apply_7(v___x_197422__overap_1197_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, lean_box(0));
v___y_1184_ = v___x_1198_;
goto v___jp_1183_;
}
}
else
{
size_t v___x_1199_; lean_object* v___x_197424__overap_1200_; lean_object* v___x_1201_; 
v___x_1199_ = lean_usize_of_nat(v___x_1191_);
v___x_197424__overap_1200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1189_, v___f_1193_, v_oFiles_1000_, v___x_1004_, v___x_1199_, v___x_1194_);
lean_inc_ref(v___y_1009_);
lean_inc(v___y_1008_);
lean_inc(v___y_1007_);
lean_inc(v___y_1006_);
v___x_1201_ = lean_apply_7(v___x_197424__overap_1200_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, lean_box(0));
v___y_1184_ = v___x_1201_;
goto v___jp_1183_;
}
}
}
else
{
lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1215_; 
lean_inc(v_buildTime_1132_);
lean_inc_ref(v_trace_1131_);
lean_inc_ref(v_log_1128_);
lean_dec_ref(v___x_1135_);
lean_dec_ref(v___y_1005_);
lean_dec_ref(v___x_1003_);
lean_dec_ref(v_oFiles_1000_);
lean_dec_ref(v___y_999_);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___y_1010_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; lean_object* v_unused_1217_; lean_object* v_unused_1218_; 
v_unused_1216_ = lean_ctor_get(v___y_1010_, 2);
lean_dec(v_unused_1216_);
v_unused_1217_ = lean_ctor_get(v___y_1010_, 1);
lean_dec(v_unused_1217_);
v_unused_1218_ = lean_ctor_get(v___y_1010_, 0);
lean_dec(v_unused_1218_);
v___x_1203_ = v___y_1010_;
v_isShared_1204_ = v_isSharedCheck_1215_;
goto v_resetjp_1202_;
}
else
{
lean_dec(v___y_1010_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1215_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_a_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v_a_1205_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1187_, 1);
v___x_1206_ = lean_io_error_to_string(v_a_1205_);
v___x_1207_ = 3;
v___x_1208_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1208_, 0, v___x_1206_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*1, v___x_1207_);
v___x_1209_ = lean_array_get_size(v_log_1128_);
v___x_1210_ = lean_array_push(v_log_1128_, v___x_1208_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1210_);
v___x_1212_ = v___x_1203_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_trace_1131_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_buildTime_1132_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3, v_action_1129_);
lean_ctor_set_uint8(v_reuseFailAlloc_1214_, sizeof(void*)*3 + 1, v_wantsRebuild_1130_);
v___x_1212_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1209_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
return v___x_1213_;
}
}
}
v___jp_1136_:
{
lean_object* v___x_1138_; lean_object* v_log_1139_; uint8_t v_action_1140_; uint8_t v_wantsRebuild_1141_; lean_object* v_trace_1142_; lean_object* v_buildTime_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1182_; 
v___x_1138_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1139_ = lean_ctor_get(v_a_1137_, 0);
v_action_1140_ = lean_ctor_get_uint8(v_a_1137_, sizeof(void*)*3);
v_wantsRebuild_1141_ = lean_ctor_get_uint8(v_a_1137_, sizeof(void*)*3 + 1);
v_trace_1142_ = lean_ctor_get(v_a_1137_, 1);
v_buildTime_1143_ = lean_ctor_get(v_a_1137_, 2);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_a_1137_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1145_ = v_a_1137_;
v_isShared_1146_ = v_isSharedCheck_1182_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_buildTime_1143_);
lean_inc(v_trace_1142_);
lean_inc(v_log_1139_);
lean_dec(v_a_1137_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1182_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1147_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1148_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1149_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1150_ = lean_array_push(v___x_1149_, v___y_999_);
v___x_1151_ = lean_array_push(v___x_1150_, v___x_1148_);
v___x_1152_ = lean_array_push(v___x_1151_, v___x_1135_);
v___x_1153_ = lean_box(0);
v___x_1154_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1155_ = 0;
v___x_1156_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1156_, 0, v___x_1138_);
lean_ctor_set(v___x_1156_, 1, v___x_1147_);
lean_ctor_set(v___x_1156_, 2, v___x_1152_);
lean_ctor_set(v___x_1156_, 3, v___x_1153_);
lean_ctor_set(v___x_1156_, 4, v___x_1154_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*5, v___x_1002_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*5 + 1, v___x_1155_);
v___x_1157_ = l_Lake_proc(v___x_1156_, v___x_1155_, v___x_1153_, v_log_1139_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1169_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_a_1159_ = lean_ctor_get(v___x_1157_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1161_ = v___x_1157_;
v_isShared_1162_ = v_isSharedCheck_1169_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1169_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v_a_1159_);
v___x_1164_ = v___x_1145_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1159_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_trace_1142_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_buildTime_1143_);
lean_ctor_set_uint8(v_reuseFailAlloc_1168_, sizeof(void*)*3, v_action_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1168_, sizeof(void*)*3 + 1, v_wantsRebuild_1141_);
v___x_1164_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1166_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 1, v___x_1164_);
v___x_1166_ = v___x_1161_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1158_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1181_; 
v_a_1170_ = lean_ctor_get(v___x_1157_, 0);
v_a_1171_ = lean_ctor_get(v___x_1157_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1173_ = v___x_1157_;
v_isShared_1174_ = v_isSharedCheck_1181_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_inc(v_a_1170_);
lean_dec(v___x_1157_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1181_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v_a_1171_);
v___x_1176_ = v___x_1145_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1171_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_trace_1142_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_buildTime_1143_);
lean_ctor_set_uint8(v_reuseFailAlloc_1180_, sizeof(void*)*3, v_action_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1180_, sizeof(void*)*3 + 1, v_wantsRebuild_1141_);
v___x_1176_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1178_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 1, v___x_1176_);
v___x_1178_ = v___x_1173_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1170_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
v___jp_1183_:
{
if (lean_obj_tag(v___y_1184_) == 0)
{
lean_object* v_a_1185_; 
v_a_1185_ = lean_ctor_get(v___y_1184_, 1);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___y_1184_, 2);
v_a_1137_ = v_a_1185_;
goto v___jp_1136_;
}
else
{
lean_dec_ref(v___x_1135_);
lean_dec_ref(v___y_999_);
return v___y_1184_;
}
}
}
else
{
lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1232_; 
lean_inc(v_buildTime_1132_);
lean_inc_ref(v_trace_1131_);
lean_inc_ref(v_log_1128_);
lean_dec_ref(v___y_1005_);
lean_dec_ref(v___x_1003_);
lean_dec_ref(v_oFiles_1000_);
lean_dec_ref(v___y_999_);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___y_1010_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; lean_object* v_unused_1234_; lean_object* v_unused_1235_; 
v_unused_1233_ = lean_ctor_get(v___y_1010_, 2);
lean_dec(v_unused_1233_);
v_unused_1234_ = lean_ctor_get(v___y_1010_, 1);
lean_dec(v_unused_1234_);
v_unused_1235_ = lean_ctor_get(v___y_1010_, 0);
lean_dec(v_unused_1235_);
v___x_1220_ = v___y_1010_;
v_isShared_1221_ = v_isSharedCheck_1232_;
goto v_resetjp_1219_;
}
else
{
lean_dec(v___y_1010_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1232_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_a_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1229_; 
v_a_1222_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1133_, 1);
v___x_1223_ = lean_io_error_to_string(v_a_1222_);
v___x_1224_ = 3;
v___x_1225_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1225_, 0, v___x_1223_);
lean_ctor_set_uint8(v___x_1225_, sizeof(void*)*1, v___x_1224_);
v___x_1226_ = lean_array_get_size(v_log_1128_);
v___x_1227_ = lean_array_push(v_log_1128_, v___x_1225_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1227_);
v___x_1229_ = v___x_1220_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_trace_1131_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_buildTime_1132_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*3, v_action_1129_);
lean_ctor_set_uint8(v_reuseFailAlloc_1231_, sizeof(void*)*3 + 1, v_wantsRebuild_1130_);
v___x_1229_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1226_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
return v___x_1230_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object* v_bootstrap_1236_, lean_object* v___y_1237_, lean_object* v_oFiles_1238_, lean_object* v_shouldExport_1239_, lean_object* v___x_1240_, lean_object* v___x_1241_, lean_object* v___x_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
uint8_t v_bootstrap_boxed_1250_; uint8_t v_shouldExport_boxed_1251_; uint8_t v___x_197796__boxed_1252_; size_t v___x_197798__boxed_1253_; lean_object* v_res_1254_; 
v_bootstrap_boxed_1250_ = lean_unbox(v_bootstrap_1236_);
v_shouldExport_boxed_1251_ = lean_unbox(v_shouldExport_1239_);
v___x_197796__boxed_1252_ = lean_unbox(v___x_1240_);
v___x_197798__boxed_1253_ = lean_unbox_usize(v___x_1242_);
lean_dec(v___x_1242_);
v_res_1254_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(v_bootstrap_boxed_1250_, v___y_1237_, v_oFiles_1238_, v_shouldExport_boxed_1251_, v___x_197796__boxed_1252_, v___x_1241_, v___x_197798__boxed_1253_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec(v___y_1244_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(uint8_t v_bootstrap_1256_, lean_object* v___y_1257_, uint8_t v_shouldExport_1258_, uint8_t v___x_1259_, lean_object* v___x_1260_, size_t v___x_1261_, lean_object* v_oFiles_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___y_1274_; uint8_t v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1270_ = lean_box(v_bootstrap_1256_);
v___x_1271_ = lean_box(v_shouldExport_1258_);
v___x_1272_ = lean_box(v___x_1259_);
v___x_1273_ = lean_box_usize(v___x_1261_);
lean_inc_ref(v___y_1257_);
v___y_1274_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed), 14, 7);
lean_closure_set(v___y_1274_, 0, v___x_1270_);
lean_closure_set(v___y_1274_, 1, v___y_1257_);
lean_closure_set(v___y_1274_, 2, v_oFiles_1262_);
lean_closure_set(v___y_1274_, 3, v___x_1271_);
lean_closure_set(v___y_1274_, 4, v___x_1272_);
lean_closure_set(v___y_1274_, 5, v___x_1260_);
lean_closure_set(v___y_1274_, 6, v___x_1273_);
v___x_1275_ = 0;
v___x_1276_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1277_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1257_, v___y_1274_, v___x_1275_, v___x_1276_, v___x_1259_, v___x_1275_, v___x_1275_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1287_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_a_1279_ = lean_ctor_get(v___x_1277_, 1);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1281_ = v___x_1277_;
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_path_1283_; lean_object* v___x_1285_; 
v_path_1283_ = lean_ctor_get(v_a_1278_, 1);
lean_inc_ref(v_path_1283_);
lean_dec(v_a_1278_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v_path_1283_);
v___x_1285_ = v___x_1281_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_path_1283_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_a_1279_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_a_1288_ = lean_ctor_get(v___x_1277_, 0);
v_a_1289_ = lean_ctor_get(v___x_1277_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1277_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_inc(v_a_1288_);
lean_dec(v___x_1277_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1288_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object* v_bootstrap_1297_, lean_object* v___y_1298_, lean_object* v_shouldExport_1299_, lean_object* v___x_1300_, lean_object* v___x_1301_, lean_object* v___x_1302_, lean_object* v_oFiles_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
uint8_t v_bootstrap_boxed_1311_; uint8_t v_shouldExport_boxed_1312_; uint8_t v___x_198221__boxed_1313_; size_t v___x_198223__boxed_1314_; lean_object* v_res_1315_; 
v_bootstrap_boxed_1311_ = lean_unbox(v_bootstrap_1297_);
v_shouldExport_boxed_1312_ = lean_unbox(v_shouldExport_1299_);
v___x_198221__boxed_1313_ = lean_unbox(v___x_1300_);
v___x_198223__boxed_1314_ = lean_unbox_usize(v___x_1302_);
lean_dec(v___x_1302_);
v_res_1315_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(v_bootstrap_boxed_1311_, v___y_1298_, v_shouldExport_boxed_1312_, v___x_198221__boxed_1313_, v___x_1301_, v___x_198223__boxed_1314_, v_oFiles_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec(v___y_1305_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object* v___x_1320_, lean_object* v___x_1321_, lean_object* v_config_1322_, lean_object* v_config_1323_, lean_object* v___x_1324_, lean_object* v___f_1325_, uint8_t v_shouldExport_1326_, uint8_t v___x_1327_, lean_object* v___x_1328_, lean_object* v___x_1329_, lean_object* v_dir_1330_, lean_object* v_self_1331_, lean_object* v___f_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
size_t v___y_1341_; lean_object* v___y_1342_; uint8_t v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v_a_1361_; lean_object* v_a_1362_; lean_object* v___y_1406_; lean_object* v___x_1418_; 
lean_inc_ref(v___y_1333_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc(v___x_1321_);
v___x_1418_ = lean_apply_7(v___y_1333_, v___x_1320_, v___x_1321_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, lean_box(0));
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v_a_1420_; lean_object* v___x_1421_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
v_a_1420_ = lean_ctor_get(v___x_1418_, 1);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1418_, 2);
v___x_1421_ = l_Lake_Job_await___redArg(v_a_1419_, v_a_1420_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v_a_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
v_a_1423_ = lean_ctor_get(v___x_1421_, 1);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1421_, 2);
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_1426_ = lean_array_get_size(v_a_1422_);
v___x_1427_ = lean_nat_dec_lt(v___x_1424_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_dec(v_a_1422_);
lean_dec_ref(v___f_1332_);
v_a_1361_ = v___x_1425_;
v_a_1362_ = v_a_1423_;
goto v___jp_1360_;
}
else
{
uint8_t v___x_1428_; 
v___x_1428_ = lean_nat_dec_le(v___x_1426_, v___x_1426_);
if (v___x_1428_ == 0)
{
if (v___x_1427_ == 0)
{
lean_dec(v_a_1422_);
lean_dec_ref(v___f_1332_);
v_a_1361_ = v___x_1425_;
v_a_1362_ = v_a_1423_;
goto v___jp_1360_;
}
else
{
size_t v___x_1429_; size_t v___x_1430_; lean_object* v___x_197561__overap_1431_; lean_object* v___x_1432_; 
v___x_1429_ = ((size_t)0ULL);
v___x_1430_ = lean_usize_of_nat(v___x_1426_);
lean_inc_ref(v___x_1324_);
v___x_197561__overap_1431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1324_, v___f_1332_, v_a_1422_, v___x_1429_, v___x_1430_, v___x_1425_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc(v___x_1321_);
lean_inc_ref(v___y_1333_);
v___x_1432_ = lean_apply_7(v___x_197561__overap_1431_, v___y_1333_, v___x_1321_, v___y_1335_, v___y_1336_, v___y_1337_, v_a_1423_, lean_box(0));
v___y_1406_ = v___x_1432_;
goto v___jp_1405_;
}
}
else
{
size_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_197564__overap_1435_; lean_object* v___x_1436_; 
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = lean_usize_of_nat(v___x_1426_);
lean_inc_ref(v___x_1324_);
v___x_197564__overap_1435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1324_, v___f_1332_, v_a_1422_, v___x_1433_, v___x_1434_, v___x_1425_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc(v___x_1321_);
lean_inc_ref(v___y_1333_);
v___x_1436_ = lean_apply_7(v___x_197564__overap_1435_, v___y_1333_, v___x_1321_, v___y_1335_, v___y_1336_, v___y_1337_, v_a_1423_, lean_box(0));
v___y_1406_ = v___x_1436_;
goto v___jp_1405_;
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec_ref(v___y_1333_);
lean_dec_ref(v___f_1332_);
lean_dec_ref(v_self_1331_);
lean_dec_ref(v_dir_1330_);
lean_dec(v___x_1329_);
lean_dec_ref(v___x_1328_);
lean_dec_ref(v___f_1325_);
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_config_1322_);
lean_dec(v___x_1321_);
v_a_1437_ = lean_ctor_get(v___x_1421_, 0);
v_a_1438_ = lean_ctor_get(v___x_1421_, 1);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1421_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_inc(v_a_1437_);
lean_dec(v___x_1421_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1437_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec_ref(v___y_1333_);
lean_dec_ref(v___f_1332_);
lean_dec_ref(v_self_1331_);
lean_dec_ref(v_dir_1330_);
lean_dec(v___x_1329_);
lean_dec_ref(v___x_1328_);
lean_dec_ref(v___f_1325_);
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_config_1322_);
lean_dec(v___x_1321_);
v_a_1446_ = lean_ctor_get(v___x_1418_, 0);
v_a_1447_ = lean_ctor_get(v___x_1418_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1418_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_inc(v_a_1446_);
lean_dec(v___x_1418_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1446_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
v___jp_1340_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___f_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; uint8_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1347_ = lean_box(v___y_1343_);
v___x_1348_ = lean_box(v_shouldExport_1326_);
v___x_1349_ = lean_box(v___x_1327_);
v___x_1350_ = lean_box_usize(v___y_1341_);
v___f_1351_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed), 14, 6);
lean_closure_set(v___f_1351_, 0, v___x_1347_);
lean_closure_set(v___f_1351_, 1, v___y_1346_);
lean_closure_set(v___f_1351_, 2, v___x_1348_);
lean_closure_set(v___f_1351_, 3, v___x_1349_);
lean_closure_set(v___f_1351_, 4, v___x_1328_);
lean_closure_set(v___f_1351_, 5, v___x_1350_);
v___x_1352_ = l_Array_append___redArg(v___y_1345_, v___y_1344_);
lean_dec_ref(v___y_1344_);
v___x_1353_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_1354_ = l_Lake_Job_collectArray___redArg(v___x_1352_, v___x_1353_);
lean_dec_ref(v___x_1352_);
v___x_1355_ = lean_unsigned_to_nat(0u);
v___x_1356_ = 0;
v___x_1357_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_1358_ = l_Lake_Job_mapM___redArg(v___x_1329_, v___x_1354_, v___f_1351_, v___x_1355_, v___x_1356_, v___y_1333_, v___x_1321_, v___y_1335_, v___y_1336_, v___y_1337_, v___x_1357_);
lean_dec(v___x_1321_);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v___y_1342_);
return v___x_1359_;
}
v___jp_1360_:
{
lean_object* v_toLeanConfig_1363_; lean_object* v_toLeanConfig_1364_; uint8_t v_bootstrap_1365_; lean_object* v_buildDir_1366_; lean_object* v_nativeLibDir_1367_; lean_object* v_moreLinkObjs_1368_; lean_object* v_moreLinkObjs_1369_; lean_object* v___x_1370_; size_t v_sz_1371_; size_t v___x_1372_; lean_object* v___x_197501__overap_1373_; lean_object* v___x_1374_; 
v_toLeanConfig_1363_ = lean_ctor_get(v_config_1322_, 1);
lean_inc_ref(v_toLeanConfig_1363_);
v_toLeanConfig_1364_ = lean_ctor_get(v_config_1323_, 0);
v_bootstrap_1365_ = lean_ctor_get_uint8(v_config_1322_, sizeof(void*)*27);
v_buildDir_1366_ = lean_ctor_get(v_config_1322_, 5);
lean_inc_ref(v_buildDir_1366_);
v_nativeLibDir_1367_ = lean_ctor_get(v_config_1322_, 7);
lean_inc_ref(v_nativeLibDir_1367_);
lean_dec_ref(v_config_1322_);
v_moreLinkObjs_1368_ = lean_ctor_get(v_toLeanConfig_1363_, 6);
lean_inc_ref(v_moreLinkObjs_1368_);
lean_dec_ref(v_toLeanConfig_1363_);
v_moreLinkObjs_1369_ = lean_ctor_get(v_toLeanConfig_1364_, 6);
v___x_1370_ = l_Array_append___redArg(v_moreLinkObjs_1368_, v_moreLinkObjs_1369_);
v_sz_1371_ = lean_array_size(v___x_1370_);
v___x_1372_ = ((size_t)0ULL);
v___x_197501__overap_1373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1324_, v___f_1325_, v_sz_1371_, v___x_1372_, v___x_1370_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc(v___x_1321_);
lean_inc_ref(v___y_1333_);
v___x_1374_ = lean_apply_7(v___x_197501__overap_1373_, v___y_1333_, v___x_1321_, v___y_1335_, v___y_1336_, v___y_1337_, v_a_1362_, lean_box(0));
if (lean_obj_tag(v___x_1374_) == 0)
{
if (v_shouldExport_1326_ == 0)
{
lean_object* v_a_1375_; lean_object* v_a_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
v_a_1376_ = lean_ctor_get(v___x_1374_, 1);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1374_, 2);
v___x_1377_ = l_System_FilePath_normalize(v_buildDir_1366_);
v___x_1378_ = l_Lake_joinRelative(v_dir_1330_, v___x_1377_);
v___x_1379_ = l_System_FilePath_normalize(v_nativeLibDir_1367_);
v___x_1380_ = l_Lake_joinRelative(v___x_1378_, v___x_1379_);
v___x_1381_ = l_Lake_LeanLib_libName(v_self_1331_);
v___x_1382_ = l_Lake_nameToStaticLib(v___x_1381_, v_shouldExport_1326_);
v___x_1383_ = l_Lake_joinRelative(v___x_1380_, v___x_1382_);
v___y_1341_ = v___x_1372_;
v___y_1342_ = v_a_1376_;
v___y_1343_ = v_bootstrap_1365_;
v___y_1344_ = v_a_1375_;
v___y_1345_ = v_a_1361_;
v___y_1346_ = v___x_1383_;
goto v___jp_1340_;
}
else
{
lean_object* v_a_1384_; lean_object* v_a_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v_a_1384_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1384_);
v_a_1385_ = lean_ctor_get(v___x_1374_, 1);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1374_, 2);
v___x_1386_ = l_System_FilePath_normalize(v_buildDir_1366_);
v___x_1387_ = l_Lake_joinRelative(v_dir_1330_, v___x_1386_);
v___x_1388_ = l_System_FilePath_normalize(v_nativeLibDir_1367_);
v___x_1389_ = l_Lake_joinRelative(v___x_1387_, v___x_1388_);
v___x_1390_ = l_Lake_LeanLib_libName(v_self_1331_);
v___x_1391_ = 0;
v___x_1392_ = l_Lake_nameToStaticLib(v___x_1390_, v___x_1391_);
v___x_1393_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_1394_ = l_System_FilePath_addExtension(v___x_1392_, v___x_1393_);
v___x_1395_ = l_Lake_joinRelative(v___x_1389_, v___x_1394_);
v___y_1341_ = v___x_1372_;
v___y_1342_ = v_a_1385_;
v___y_1343_ = v_bootstrap_1365_;
v___y_1344_ = v_a_1384_;
v___y_1345_ = v_a_1361_;
v___y_1346_ = v___x_1395_;
goto v___jp_1340_;
}
}
else
{
lean_object* v_a_1396_; lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec_ref(v_nativeLibDir_1367_);
lean_dec_ref(v_buildDir_1366_);
lean_dec_ref(v_a_1361_);
lean_dec_ref(v___y_1333_);
lean_dec_ref(v_self_1331_);
lean_dec_ref(v_dir_1330_);
lean_dec(v___x_1329_);
lean_dec_ref(v___x_1328_);
lean_dec(v___x_1321_);
v_a_1396_ = lean_ctor_get(v___x_1374_, 0);
v_a_1397_ = lean_ctor_get(v___x_1374_, 1);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1374_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_inc(v_a_1396_);
lean_dec(v___x_1374_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1396_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
v___jp_1405_:
{
if (lean_obj_tag(v___y_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v_a_1408_; 
v_a_1407_ = lean_ctor_get(v___y_1406_, 0);
lean_inc(v_a_1407_);
v_a_1408_ = lean_ctor_get(v___y_1406_, 1);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___y_1406_, 2);
v_a_1361_ = v_a_1407_;
v_a_1362_ = v_a_1408_;
goto v___jp_1360_;
}
else
{
lean_object* v_a_1409_; lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_dec_ref(v___y_1333_);
lean_dec_ref(v_self_1331_);
lean_dec_ref(v_dir_1330_);
lean_dec(v___x_1329_);
lean_dec_ref(v___x_1328_);
lean_dec_ref(v___f_1325_);
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_config_1322_);
lean_dec(v___x_1321_);
v_a_1409_ = lean_ctor_get(v___y_1406_, 0);
v_a_1410_ = lean_ctor_get(v___y_1406_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___y_1406_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___y_1406_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_inc(v_a_1409_);
lean_dec(v___y_1406_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1409_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_a_1410_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed(lean_object** _args){
lean_object* v___x_1455_ = _args[0];
lean_object* v___x_1456_ = _args[1];
lean_object* v_config_1457_ = _args[2];
lean_object* v_config_1458_ = _args[3];
lean_object* v___x_1459_ = _args[4];
lean_object* v___f_1460_ = _args[5];
lean_object* v_shouldExport_1461_ = _args[6];
lean_object* v___x_1462_ = _args[7];
lean_object* v___x_1463_ = _args[8];
lean_object* v___x_1464_ = _args[9];
lean_object* v_dir_1465_ = _args[10];
lean_object* v_self_1466_ = _args[11];
lean_object* v___f_1467_ = _args[12];
lean_object* v___y_1468_ = _args[13];
lean_object* v___y_1469_ = _args[14];
lean_object* v___y_1470_ = _args[15];
lean_object* v___y_1471_ = _args[16];
lean_object* v___y_1472_ = _args[17];
lean_object* v___y_1473_ = _args[18];
lean_object* v___y_1474_ = _args[19];
_start:
{
uint8_t v_shouldExport_boxed_1475_; uint8_t v___x_198325__boxed_1476_; lean_object* v_res_1477_; 
v_shouldExport_boxed_1475_ = lean_unbox(v_shouldExport_1461_);
v___x_198325__boxed_1476_ = lean_unbox(v___x_1462_);
v_res_1477_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(v___x_1455_, v___x_1456_, v_config_1457_, v_config_1458_, v___x_1459_, v___f_1460_, v_shouldExport_boxed_1475_, v___x_198325__boxed_1476_, v___x_1463_, v___x_1464_, v_dir_1465_, v_self_1466_, v___f_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec(v_config_1458_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object* v_self_1481_, uint8_t v_shouldExport_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v___x_1490_; lean_object* v_toApplicative_1491_; lean_object* v_toBind_1492_; lean_object* v_toFunctor_1493_; lean_object* v_toPure_1494_; lean_object* v___f_1495_; lean_object* v___f_1496_; lean_object* v___f_1497_; lean_object* v___f_1498_; lean_object* v___x_1499_; lean_object* v___f_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v_toBuildConfig_1508_; lean_object* v_registeredJobs_1509_; uint8_t v_verbosity_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___f_1513_; uint8_t v___x_1514_; uint8_t v___x_1515_; uint8_t v___x_1516_; lean_object* v___y_1518_; 
v___x_1490_ = l_instMonadBaseIO;
v_toApplicative_1491_ = lean_ctor_get(v___x_1490_, 0);
v_toBind_1492_ = lean_ctor_get(v___x_1490_, 1);
v_toFunctor_1493_ = lean_ctor_get(v_toApplicative_1491_, 0);
v_toPure_1494_ = lean_ctor_get(v_toApplicative_1491_, 1);
lean_inc_n(v_toBind_1492_, 3);
lean_inc_n(v_toPure_1494_, 5);
v___f_1495_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1495_, 0, v_toPure_1494_);
lean_closure_set(v___f_1495_, 1, v_toBind_1492_);
v___f_1496_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1496_, 0, v_toPure_1494_);
lean_closure_set(v___f_1496_, 1, v_toBind_1492_);
lean_inc_ref(v___f_1495_);
v___f_1497_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1497_, 0, v_toPure_1494_);
lean_closure_set(v___f_1497_, 1, v___f_1495_);
lean_inc_ref_n(v_toFunctor_1493_, 2);
v___f_1498_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1498_, 0, v_toFunctor_1493_);
lean_closure_set(v___f_1498_, 1, v_toPure_1494_);
lean_closure_set(v___f_1498_, 2, v_toBind_1492_);
v___x_1499_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1493_);
v___f_1500_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1500_, 0, v_toPure_1494_);
v___x_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1499_);
lean_ctor_set(v___x_1501_, 1, v___f_1500_);
lean_ctor_set(v___x_1501_, 2, v___f_1498_);
lean_ctor_set(v___x_1501_, 3, v___f_1497_);
lean_ctor_set(v___x_1501_, 4, v___f_1496_);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
lean_ctor_set(v___x_1502_, 1, v___f_1495_);
v___x_1503_ = l_ReaderT_instMonad___redArg(v___x_1502_);
v___x_1504_ = l_StateRefT_x27_instMonad___redArg(v___x_1503_);
v___x_1505_ = l_ReaderT_instMonad___redArg(v___x_1504_);
v___x_1506_ = l_ReaderT_instMonad___redArg(v___x_1505_);
lean_inc_ref(v___x_1506_);
v___x_1507_ = l_Lake_EquipT_instMonad___redArg(v___x_1506_);
v_toBuildConfig_1508_ = lean_ctor_get(v_a_1487_, 0);
v_registeredJobs_1509_ = lean_ctor_get(v_a_1487_, 3);
v_verbosity_1510_ = lean_ctor_get_uint8(v_toBuildConfig_1508_, sizeof(void*)*4 + 3);
v___x_1511_ = l_Lake_instDataKindFilePath;
v___x_1512_ = lean_box(v_shouldExport_1482_);
lean_inc_ref(v___x_1507_);
v___f_1513_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1513_, 0, v___x_1512_);
lean_closure_set(v___f_1513_, 1, v___x_1507_);
v___x_1514_ = 2;
v___x_1515_ = l_Lake_instDecidableEqVerbosity(v_verbosity_1510_, v___x_1514_);
v___x_1516_ = 1;
if (v___x_1515_ == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_1518_ = v___x_1564_;
goto v___jp_1517_;
}
else
{
if (v_shouldExport_1482_ == 0)
{
lean_object* v___x_1565_; 
v___x_1565_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___y_1518_ = v___x_1565_;
goto v___jp_1517_;
}
else
{
lean_object* v___x_1566_; 
v___x_1566_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_1518_ = v___x_1566_;
goto v___jp_1517_;
}
}
v___jp_1517_:
{
lean_object* v_pkg_1519_; lean_object* v_name_1520_; lean_object* v_config_1521_; lean_object* v_keyName_1522_; lean_object* v_dir_1523_; lean_object* v_config_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___f_1533_; lean_object* v___x_1534_; 
v_pkg_1519_ = lean_ctor_get(v_self_1481_, 0);
v_name_1520_ = lean_ctor_get(v_self_1481_, 1);
lean_inc_n(v_name_1520_, 2);
v_config_1521_ = lean_ctor_get(v_self_1481_, 2);
lean_inc(v_config_1521_);
v_keyName_1522_ = lean_ctor_get(v_pkg_1519_, 2);
v_dir_1523_ = lean_ctor_get(v_pkg_1519_, 4);
lean_inc_ref(v_dir_1523_);
v_config_1524_ = lean_ctor_get(v_pkg_1519_, 6);
lean_inc_ref(v_config_1524_);
lean_inc_ref_n(v_pkg_1519_, 2);
v___f_1525_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(v___f_1525_, 0, v___x_1511_);
lean_closure_set(v___f_1525_, 1, v_pkg_1519_);
v___x_1526_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_1522_);
v___x_1527_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1527_, 0, v_keyName_1522_);
lean_ctor_set(v___x_1527_, 1, v_name_1520_);
v___x_1528_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_1481_);
v___x_1529_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1527_);
lean_ctor_set(v___x_1529_, 1, v___x_1528_);
lean_ctor_set(v___x_1529_, 2, v_self_1481_);
lean_ctor_set(v___x_1529_, 3, v___x_1526_);
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_pkg_1519_);
v___x_1531_ = lean_box(v_shouldExport_1482_);
v___x_1532_ = lean_box(v___x_1516_);
v___f_1533_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed), 20, 13);
lean_closure_set(v___f_1533_, 0, v___x_1529_);
lean_closure_set(v___f_1533_, 1, v___x_1530_);
lean_closure_set(v___f_1533_, 2, v_config_1524_);
lean_closure_set(v___f_1533_, 3, v_config_1521_);
lean_closure_set(v___f_1533_, 4, v___x_1507_);
lean_closure_set(v___f_1533_, 5, v___f_1525_);
lean_closure_set(v___f_1533_, 6, v___x_1531_);
lean_closure_set(v___f_1533_, 7, v___x_1532_);
lean_closure_set(v___f_1533_, 8, v___x_1506_);
lean_closure_set(v___f_1533_, 9, v___x_1511_);
lean_closure_set(v___f_1533_, 10, v_dir_1523_);
lean_closure_set(v___f_1533_, 11, v_self_1481_);
lean_closure_set(v___f_1533_, 12, v___f_1513_);
v___x_1534_ = l_Lake_ensureJob___redArg(v___x_1511_, v___f_1533_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1563_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_a_1536_ = lean_ctor_get(v___x_1534_, 1);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1538_ = v___x_1534_;
v_isShared_1539_ = v_isSharedCheck_1563_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1563_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v_task_1540_; lean_object* v_kind_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1561_; 
v_task_1540_ = lean_ctor_get(v_a_1535_, 0);
v_kind_1541_ = lean_ctor_get(v_a_1535_, 1);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_a_1535_);
if (v_isSharedCheck_1561_ == 0)
{
lean_object* v_unused_1562_; 
v_unused_1562_ = lean_ctor_get(v_a_1535_, 2);
lean_dec(v_unused_1562_);
v___x_1543_ = v_a_1535_;
v_isShared_1544_ = v_isSharedCheck_1561_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_kind_1541_);
lean_inc(v_task_1540_);
lean_dec(v_a_1535_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1561_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; lean_object* v_job_1552_; 
v___x_1545_ = lean_st_ref_take(v_registeredJobs_1509_);
v___x_1546_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1520_, v___x_1516_);
v___x_1547_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0));
v___x_1548_ = lean_string_append(v___x_1546_, v___x_1547_);
v___x_1549_ = lean_string_append(v___x_1548_, v___y_1518_);
v___x_1550_ = 0;
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 2, v___x_1549_);
v_job_1552_ = v___x_1543_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_task_1540_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_kind_1541_);
lean_ctor_set(v_reuseFailAlloc_1560_, 2, v___x_1549_);
v_job_1552_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
lean_ctor_set_uint8(v_job_1552_, sizeof(void*)*3, v___x_1550_);
lean_inc_ref(v_job_1552_);
v___x_1553_ = l_Lake_Job_toOpaque___redArg(v_job_1552_);
v___x_1554_ = lean_array_push(v___x_1545_, v___x_1553_);
v___x_1555_ = lean_st_ref_put(v_registeredJobs_1509_, v___x_1554_);
v___x_1556_ = l_Lake_Job_renew___redArg(v_job_1552_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1556_);
v___x_1558_ = v___x_1538_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_a_1536_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
else
{
lean_dec(v_name_1520_);
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object* v_self_1567_, lean_object* v_shouldExport_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
uint8_t v_shouldExport_boxed_1576_; lean_object* v_res_1577_; 
v_shouldExport_boxed_1576_ = lean_unbox(v_shouldExport_1568_);
v_res_1577_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1567_, v_shouldExport_boxed_1576_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
lean_dec(v_a_1571_);
lean_dec(v_a_1570_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t v_fmt_1578_, lean_object* v_a_1579_){
_start:
{
if (v_fmt_1578_ == 0)
{
return v_a_1579_;
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = l_Lake_mkRelPathString(v_a_1579_);
v___x_1581_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
v___x_1582_ = l_Lean_Json_compress(v___x_1581_);
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object* v_fmt_1583_, lean_object* v_a_1584_){
_start:
{
uint8_t v_fmt_boxed_1585_; lean_object* v_res_1586_; 
v_fmt_boxed_1585_ = lean_unbox(v_fmt_1583_);
v_res_1586_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_boxed_1585_, v_a_1584_);
return v_res_1586_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2(void){
_start:
{
uint8_t v___x_1589_; lean_object* v_name_1590_; lean_object* v___x_1591_; 
v___x_1589_ = 1;
v_name_1590_ = l_Lake_instDataKindFilePath;
v___x_1591_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1590_, v___x_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* v_defaultPkg_1595_, lean_object* v_self_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
uint8_t v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = 1;
lean_inc_ref_n(v_self_1596_, 2);
v___x_1605_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1595_, v_self_1596_, v_self_1596_, v___x_1604_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v_snd_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1648_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
v_snd_1607_ = lean_ctor_get(v_a_1606_, 1);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_a_1606_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; 
v_unused_1649_ = lean_ctor_get(v_a_1606_, 0);
lean_dec(v_unused_1649_);
v___x_1609_ = v_a_1606_;
v_isShared_1610_ = v_isSharedCheck_1648_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_snd_1607_);
lean_dec(v_a_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1648_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1646_; 
v_a_1611_ = lean_ctor_get(v___x_1605_, 1);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v___x_1605_, 0);
lean_dec(v_unused_1647_);
v___x_1613_ = v___x_1605_;
v_isShared_1614_ = v_isSharedCheck_1646_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1605_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1646_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_kind_1615_; lean_object* v_name_1616_; lean_object* v___y_1618_; uint8_t v___x_1636_; 
v_kind_1615_ = lean_ctor_get(v_snd_1607_, 1);
v_name_1616_ = l_Lake_instDataKindFilePath;
v___x_1636_ = lean_name_eq(v_kind_1615_, v_name_1616_);
if (v___x_1636_ == 0)
{
uint8_t v___x_1637_; 
lean_inc(v_kind_1615_);
lean_del_object(v___x_1609_);
lean_dec(v_snd_1607_);
v___x_1637_ = l_Lean_Name_isAnonymous(v_kind_1615_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1638_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1639_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1615_, v___x_1604_);
v___x_1640_ = lean_string_append(v___x_1638_, v___x_1639_);
lean_dec_ref(v___x_1639_);
v___x_1641_ = lean_string_append(v___x_1640_, v___x_1638_);
v___y_1618_ = v___x_1641_;
goto v___jp_1617_;
}
else
{
lean_object* v___x_1642_; 
lean_dec(v_kind_1615_);
v___x_1642_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1618_ = v___x_1642_;
goto v___jp_1617_;
}
}
else
{
lean_object* v___x_1644_; 
lean_del_object(v___x_1613_);
lean_dec_ref(v_self_1596_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 1, v_a_1611_);
lean_ctor_set(v___x_1609_, 0, v_snd_1607_);
v___x_1644_ = v___x_1609_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_snd_1607_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_a_1611_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
v___jp_1617_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1619_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1620_ = l_Lake_PartialBuildKey_toString(v_self_1596_);
v___x_1621_ = lean_string_append(v___x_1619_, v___x_1620_);
lean_dec_ref(v___x_1620_);
v___x_1622_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1623_ = lean_string_append(v___x_1621_, v___x_1622_);
v___x_1624_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
v___x_1625_ = lean_string_append(v___x_1623_, v___x_1624_);
v___x_1626_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1627_ = lean_string_append(v___x_1625_, v___x_1626_);
v___x_1628_ = lean_string_append(v___x_1627_, v___y_1618_);
lean_dec_ref(v___y_1618_);
v___x_1629_ = 3;
v___x_1630_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*1, v___x_1629_);
v___x_1631_ = lean_array_get_size(v_a_1611_);
v___x_1632_ = lean_array_push(v_a_1611_, v___x_1630_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set_tag(v___x_1613_, 1);
lean_ctor_set(v___x_1613_, 1, v___x_1632_);
lean_ctor_set(v___x_1613_, 0, v___x_1631_);
v___x_1634_ = v___x_1613_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec_ref(v_self_1596_);
v_a_1650_ = lean_ctor_get(v___x_1605_, 0);
v_a_1651_ = lean_ctor_get(v___x_1605_, 1);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1605_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_inc(v_a_1650_);
lean_dec(v___x_1605_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1650_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* v_defaultPkg_1659_, lean_object* v_self_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1659_, v_self_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec(v_a_1662_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* v___x_1669_, size_t v_sz_1670_, size_t v_i_1671_, lean_object* v_bs_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
uint8_t v___x_1680_; 
v___x_1680_ = lean_usize_dec_lt(v_i_1671_, v_sz_1670_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; 
lean_dec_ref(v___y_1673_);
lean_dec_ref(v___x_1669_);
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v_bs_1672_);
lean_ctor_set(v___x_1681_, 1, v___y_1678_);
return v___x_1681_;
}
else
{
lean_object* v_v_1682_; lean_object* v___x_1683_; 
v_v_1682_ = lean_array_uget_borrowed(v_bs_1672_, v_i_1671_);
lean_inc_ref(v___y_1673_);
lean_inc(v_v_1682_);
lean_inc_ref(v___x_1669_);
v___x_1683_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1669_, v_v_1682_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v_a_1685_; lean_object* v___x_1686_; lean_object* v_bs_x27_1687_; size_t v___x_1688_; size_t v___x_1689_; lean_object* v___x_1690_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
v_a_1685_ = lean_ctor_get(v___x_1683_, 1);
lean_inc(v_a_1685_);
lean_dec_ref_known(v___x_1683_, 2);
v___x_1686_ = lean_unsigned_to_nat(0u);
v_bs_x27_1687_ = lean_array_uset(v_bs_1672_, v_i_1671_, v___x_1686_);
v___x_1688_ = ((size_t)1ULL);
v___x_1689_ = lean_usize_add(v_i_1671_, v___x_1688_);
v___x_1690_ = lean_array_uset(v_bs_x27_1687_, v_i_1671_, v_a_1684_);
v_i_1671_ = v___x_1689_;
v_bs_1672_ = v___x_1690_;
v___y_1678_ = v_a_1685_;
goto _start;
}
else
{
lean_object* v_a_1692_; lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec_ref(v___y_1673_);
lean_dec_ref(v_bs_1672_);
lean_dec_ref(v___x_1669_);
v_a_1692_ = lean_ctor_get(v___x_1683_, 0);
v_a_1693_ = lean_ctor_get(v___x_1683_, 1);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1683_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_inc(v_a_1692_);
lean_dec(v___x_1683_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1692_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* v___x_1701_, lean_object* v_sz_1702_, lean_object* v_i_1703_, lean_object* v_bs_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
size_t v_sz_boxed_1712_; size_t v_i_boxed_1713_; lean_object* v_res_1714_; 
v_sz_boxed_1712_ = lean_unbox_usize(v_sz_1702_);
lean_dec(v_sz_1702_);
v_i_boxed_1713_ = lean_unbox_usize(v_i_1703_);
lean_dec(v_i_1703_);
v_res_1714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1701_, v_sz_boxed_1712_, v_i_boxed_1713_, v_bs_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec(v___y_1706_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(lean_object* v_a_1715_, lean_object* v_as_1716_, size_t v_i_1717_, size_t v_stop_1718_, lean_object* v_b_1719_, lean_object* v___y_1720_){
_start:
{
uint8_t v___x_1722_; 
v___x_1722_ = lean_usize_dec_eq(v_i_1717_, v_stop_1718_);
if (v___x_1722_ == 0)
{
lean_object* v_log_1723_; uint8_t v_action_1724_; uint8_t v_wantsRebuild_1725_; lean_object* v_trace_1726_; lean_object* v_buildTime_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_log_1723_ = lean_ctor_get(v___y_1720_, 0);
v_action_1724_ = lean_ctor_get_uint8(v___y_1720_, sizeof(void*)*3);
v_wantsRebuild_1725_ = lean_ctor_get_uint8(v___y_1720_, sizeof(void*)*3 + 1);
v_trace_1726_ = lean_ctor_get(v___y_1720_, 1);
v_buildTime_1727_ = lean_ctor_get(v___y_1720_, 2);
v___x_1728_ = lean_array_uget_borrowed(v_as_1716_, v_i_1717_);
v___x_1729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
lean_inc(v___x_1728_);
v___x_1730_ = lean_string_append(v___x_1728_, v___x_1729_);
v___x_1731_ = lean_io_prim_handle_put_str(v_a_1715_, v___x_1730_);
lean_dec_ref(v___x_1730_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; size_t v___x_1733_; size_t v___x_1734_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1732_);
lean_dec_ref_known(v___x_1731_, 1);
v___x_1733_ = ((size_t)1ULL);
v___x_1734_ = lean_usize_add(v_i_1717_, v___x_1733_);
v_i_1717_ = v___x_1734_;
v_b_1719_ = v_a_1732_;
goto _start;
}
else
{
lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1749_; 
lean_inc(v_buildTime_1727_);
lean_inc_ref(v_trace_1726_);
lean_inc_ref(v_log_1723_);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___y_1720_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; lean_object* v_unused_1751_; lean_object* v_unused_1752_; 
v_unused_1750_ = lean_ctor_get(v___y_1720_, 2);
lean_dec(v_unused_1750_);
v_unused_1751_ = lean_ctor_get(v___y_1720_, 1);
lean_dec(v_unused_1751_);
v_unused_1752_ = lean_ctor_get(v___y_1720_, 0);
lean_dec(v_unused_1752_);
v___x_1737_ = v___y_1720_;
v_isShared_1738_ = v_isSharedCheck_1749_;
goto v_resetjp_1736_;
}
else
{
lean_dec(v___y_1720_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1749_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v_a_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1746_; 
v_a_1739_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1731_, 1);
v___x_1740_ = lean_io_error_to_string(v_a_1739_);
v___x_1741_ = 3;
v___x_1742_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
lean_ctor_set_uint8(v___x_1742_, sizeof(void*)*1, v___x_1741_);
v___x_1743_ = lean_array_get_size(v_log_1723_);
v___x_1744_ = lean_array_push(v_log_1723_, v___x_1742_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 0, v___x_1744_);
v___x_1746_ = v___x_1737_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_trace_1726_);
lean_ctor_set(v_reuseFailAlloc_1748_, 2, v_buildTime_1727_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, sizeof(void*)*3, v_action_1724_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, sizeof(void*)*3 + 1, v_wantsRebuild_1725_);
v___x_1746_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1743_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
return v___x_1747_;
}
}
}
}
else
{
lean_object* v___x_1753_; 
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v_b_1719_);
lean_ctor_set(v___x_1753_, 1, v___y_1720_);
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(lean_object* v_a_1754_, lean_object* v_as_1755_, lean_object* v_i_1756_, lean_object* v_stop_1757_, lean_object* v_b_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
size_t v_i_boxed_1761_; size_t v_stop_boxed_1762_; lean_object* v_res_1763_; 
v_i_boxed_1761_ = lean_unbox_usize(v_i_1756_);
lean_dec(v_i_1756_);
v_stop_boxed_1762_ = lean_unbox_usize(v_stop_1757_);
lean_dec(v_stop_1757_);
v_res_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1754_, v_as_1755_, v_i_boxed_1761_, v_stop_boxed_1762_, v_b_1758_, v___y_1759_);
lean_dec_ref(v_as_1755_);
lean_dec(v_a_1754_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(uint8_t v_bootstrap_1764_, lean_object* v___y_1765_, lean_object* v_oFiles_1766_, uint8_t v_shouldExport_1767_, uint8_t v___x_1768_, size_t v___x_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
if (v_bootstrap_1764_ == 0)
{
lean_object* v_toContext_1777_; lean_object* v_lakeEnv_1778_; lean_object* v_lean_1779_; lean_object* v_log_1780_; uint8_t v_action_1781_; uint8_t v_wantsRebuild_1782_; lean_object* v_trace_1783_; lean_object* v_buildTime_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1814_; 
v_toContext_1777_ = lean_ctor_get(v___y_1774_, 1);
v_lakeEnv_1778_ = lean_ctor_get(v_toContext_1777_, 0);
v_lean_1779_ = lean_ctor_get(v_lakeEnv_1778_, 1);
v_log_1780_ = lean_ctor_get(v___y_1775_, 0);
v_action_1781_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*3);
v_wantsRebuild_1782_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*3 + 1);
v_trace_1783_ = lean_ctor_get(v___y_1775_, 1);
v_buildTime_1784_ = lean_ctor_get(v___y_1775_, 2);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___y_1775_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1786_ = v___y_1775_;
v_isShared_1787_ = v_isSharedCheck_1814_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_buildTime_1784_);
lean_inc(v_trace_1783_);
lean_inc(v_log_1780_);
lean_dec(v___y_1775_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1814_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v_ar_1788_; lean_object* v___x_1789_; 
v_ar_1788_ = lean_ctor_get(v_lean_1779_, 13);
lean_inc_ref(v_ar_1788_);
v___x_1789_ = l_Lake_compileStaticLib(v___y_1765_, v_oFiles_1766_, v_ar_1788_, v_bootstrap_1764_, v_log_1780_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1801_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_a_1791_ = lean_ctor_get(v___x_1789_, 1);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1793_ = v___x_1789_;
v_isShared_1794_ = v_isSharedCheck_1801_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1801_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v_a_1791_);
v___x_1796_ = v___x_1786_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1791_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_trace_1783_);
lean_ctor_set(v_reuseFailAlloc_1800_, 2, v_buildTime_1784_);
lean_ctor_set_uint8(v_reuseFailAlloc_1800_, sizeof(void*)*3, v_action_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1800_, sizeof(void*)*3 + 1, v_wantsRebuild_1782_);
v___x_1796_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1798_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v___x_1796_);
v___x_1798_ = v___x_1793_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1790_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v___x_1796_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1813_; 
v_a_1802_ = lean_ctor_get(v___x_1789_, 0);
v_a_1803_ = lean_ctor_get(v___x_1789_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1805_ = v___x_1789_;
v_isShared_1806_ = v_isSharedCheck_1813_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_inc(v_a_1802_);
lean_dec(v___x_1789_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1813_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v_a_1803_);
v___x_1808_ = v___x_1786_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1803_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v_trace_1783_);
lean_ctor_set(v_reuseFailAlloc_1812_, 2, v_buildTime_1784_);
lean_ctor_set_uint8(v_reuseFailAlloc_1812_, sizeof(void*)*3, v_action_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1812_, sizeof(void*)*3 + 1, v_wantsRebuild_1782_);
v___x_1808_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1810_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___x_1808_);
v___x_1810_ = v___x_1805_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1802_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
}
else
{
uint8_t v___x_1815_; 
v___x_1815_ = l_System_Platform_isOSX;
if (v___x_1815_ == 0)
{
uint8_t v___x_1816_; 
v___x_1816_ = l_System_Platform_isWindows;
if (v___x_1816_ == 0)
{
lean_object* v_toContext_1817_; lean_object* v_lakeEnv_1818_; lean_object* v_lean_1819_; lean_object* v_log_1820_; uint8_t v_action_1821_; uint8_t v_wantsRebuild_1822_; lean_object* v_trace_1823_; lean_object* v_buildTime_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1854_; 
v_toContext_1817_ = lean_ctor_get(v___y_1774_, 1);
v_lakeEnv_1818_ = lean_ctor_get(v_toContext_1817_, 0);
v_lean_1819_ = lean_ctor_get(v_lakeEnv_1818_, 1);
v_log_1820_ = lean_ctor_get(v___y_1775_, 0);
v_action_1821_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*3);
v_wantsRebuild_1822_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*3 + 1);
v_trace_1823_ = lean_ctor_get(v___y_1775_, 1);
v_buildTime_1824_ = lean_ctor_get(v___y_1775_, 2);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___y_1775_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1826_ = v___y_1775_;
v_isShared_1827_ = v_isSharedCheck_1854_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_buildTime_1824_);
lean_inc(v_trace_1823_);
lean_inc(v_log_1820_);
lean_dec(v___y_1775_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1854_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_ar_1828_; lean_object* v___x_1829_; 
v_ar_1828_ = lean_ctor_get(v_lean_1819_, 13);
lean_inc_ref(v_ar_1828_);
v___x_1829_ = l_Lake_compileStaticLib(v___y_1765_, v_oFiles_1766_, v_ar_1828_, v___x_1816_, v_log_1820_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1841_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_a_1831_ = lean_ctor_get(v___x_1829_, 1);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1833_ = v___x_1829_;
v_isShared_1834_ = v_isSharedCheck_1841_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1841_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v_a_1831_);
v___x_1836_ = v___x_1826_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1831_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_trace_1823_);
lean_ctor_set(v_reuseFailAlloc_1840_, 2, v_buildTime_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1840_, sizeof(void*)*3, v_action_1821_);
lean_ctor_set_uint8(v_reuseFailAlloc_1840_, sizeof(void*)*3 + 1, v_wantsRebuild_1822_);
v___x_1836_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1838_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v___x_1836_);
v___x_1838_ = v___x_1833_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1830_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
else
{
lean_object* v_a_1842_; lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1853_; 
v_a_1842_ = lean_ctor_get(v___x_1829_, 0);
v_a_1843_ = lean_ctor_get(v___x_1829_, 1);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1845_ = v___x_1829_;
v_isShared_1846_ = v_isSharedCheck_1853_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_inc(v_a_1842_);
lean_dec(v___x_1829_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1853_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v_a_1843_);
v___x_1848_ = v___x_1826_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1843_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_trace_1823_);
lean_ctor_set(v_reuseFailAlloc_1852_, 2, v_buildTime_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1852_, sizeof(void*)*3, v_action_1821_);
lean_ctor_set_uint8(v_reuseFailAlloc_1852_, sizeof(void*)*3 + 1, v_wantsRebuild_1822_);
v___x_1848_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1850_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 1, v___x_1848_);
v___x_1850_ = v___x_1845_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1842_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1855_; lean_object* v_lakeEnv_1856_; lean_object* v_lean_1857_; lean_object* v_log_1858_; uint8_t v_action_1859_; uint8_t v_wantsRebuild_1860_; lean_object* v_trace_1861_; lean_object* v_buildTime_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1892_; 
v_toContext_1855_ = lean_ctor_get(v___y_1774_, 1);
v_lakeEnv_1856_ = lean_ctor_get(v_toContext_1855_, 0);
v_lean_1857_ = lean_ctor_get(v_lakeEnv_1856_, 1);
v_log_1858_ = lean_ctor_get(v___y_1775_, 0);
v_action_1859_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*3);
v_wantsRebuild_1860_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*3 + 1);
v_trace_1861_ = lean_ctor_get(v___y_1775_, 1);
v_buildTime_1862_ = lean_ctor_get(v___y_1775_, 2);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___y_1775_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1864_ = v___y_1775_;
v_isShared_1865_ = v_isSharedCheck_1892_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_buildTime_1862_);
lean_inc(v_trace_1861_);
lean_inc(v_log_1858_);
lean_dec(v___y_1775_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1892_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v_ar_1866_; lean_object* v___x_1867_; 
v_ar_1866_ = lean_ctor_get(v_lean_1857_, 13);
lean_inc_ref(v_ar_1866_);
v___x_1867_ = l_Lake_compileStaticLib(v___y_1765_, v_oFiles_1766_, v_ar_1866_, v_shouldExport_1767_, v_log_1858_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1879_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
v_a_1869_ = lean_ctor_get(v___x_1867_, 1);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1871_ = v___x_1867_;
v_isShared_1872_ = v_isSharedCheck_1879_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_inc(v_a_1868_);
lean_dec(v___x_1867_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1879_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v_a_1869_);
v___x_1874_ = v___x_1864_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1869_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v_trace_1861_);
lean_ctor_set(v_reuseFailAlloc_1878_, 2, v_buildTime_1862_);
lean_ctor_set_uint8(v_reuseFailAlloc_1878_, sizeof(void*)*3, v_action_1859_);
lean_ctor_set_uint8(v_reuseFailAlloc_1878_, sizeof(void*)*3 + 1, v_wantsRebuild_1860_);
v___x_1874_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1876_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 1, v___x_1874_);
v___x_1876_ = v___x_1871_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1868_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1891_; 
v_a_1880_ = lean_ctor_get(v___x_1867_, 0);
v_a_1881_ = lean_ctor_get(v___x_1867_, 1);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1883_ = v___x_1867_;
v_isShared_1884_ = v_isSharedCheck_1891_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_inc(v_a_1880_);
lean_dec(v___x_1867_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1891_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v_a_1881_);
v___x_1886_ = v___x_1864_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1881_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_trace_1861_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_buildTime_1862_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*3, v_action_1859_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*3 + 1, v_wantsRebuild_1860_);
v___x_1886_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1888_; 
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 1, v___x_1886_);
v___x_1888_ = v___x_1883_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1880_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1893_; uint8_t v_action_1894_; uint8_t v_wantsRebuild_1895_; lean_object* v_trace_1896_; lean_object* v_buildTime_1897_; lean_object* v___x_1898_; 
v_log_1893_ = lean_ctor_get(v___y_1775_, 0);
v_action_1894_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*3);
v_wantsRebuild_1895_ = lean_ctor_get_uint8(v___y_1775_, sizeof(void*)*3 + 1);
v_trace_1896_ = lean_ctor_get(v___y_1775_, 1);
v_buildTime_1897_ = lean_ctor_get(v___y_1775_, 2);
lean_inc_ref(v___y_1765_);
v___x_1898_ = l_Lake_createParentDirs(v___y_1765_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v_a_1902_; lean_object* v___y_1951_; uint8_t v___x_1953_; lean_object* v___x_1954_; 
lean_dec_ref_known(v___x_1898_, 1);
v___x_1899_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1765_);
v___x_1900_ = l_System_FilePath_addExtension(v___y_1765_, v___x_1899_);
v___x_1953_ = 1;
v___x_1954_ = lean_io_prim_handle_mk(v___x_1900_, v___x_1953_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1957_ = lean_array_get_size(v_oFiles_1766_);
v___x_1958_ = lean_nat_dec_lt(v___x_1956_, v___x_1957_);
if (v___x_1958_ == 0)
{
lean_dec(v_a_1955_);
lean_dec_ref(v_oFiles_1766_);
v_a_1902_ = v___y_1775_;
goto v___jp_1901_;
}
else
{
lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1959_ = lean_box(0);
v___x_1960_ = lean_nat_dec_le(v___x_1957_, v___x_1957_);
if (v___x_1960_ == 0)
{
if (v___x_1958_ == 0)
{
lean_dec(v_a_1955_);
lean_dec_ref(v_oFiles_1766_);
v_a_1902_ = v___y_1775_;
goto v___jp_1901_;
}
else
{
size_t v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_usize_of_nat(v___x_1957_);
v___x_1962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1955_, v_oFiles_1766_, v___x_1769_, v___x_1961_, v___x_1959_, v___y_1775_);
lean_dec_ref(v_oFiles_1766_);
lean_dec(v_a_1955_);
v___y_1951_ = v___x_1962_;
goto v___jp_1950_;
}
}
else
{
size_t v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = lean_usize_of_nat(v___x_1957_);
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1955_, v_oFiles_1766_, v___x_1769_, v___x_1963_, v___x_1959_, v___y_1775_);
lean_dec_ref(v_oFiles_1766_);
lean_dec(v_a_1955_);
v___y_1951_ = v___x_1964_;
goto v___jp_1950_;
}
}
}
else
{
lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1978_; 
lean_inc(v_buildTime_1897_);
lean_inc_ref(v_trace_1896_);
lean_inc_ref(v_log_1893_);
lean_dec_ref(v___x_1900_);
lean_dec_ref(v_oFiles_1766_);
lean_dec_ref(v___y_1765_);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___y_1775_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; lean_object* v_unused_1980_; lean_object* v_unused_1981_; 
v_unused_1979_ = lean_ctor_get(v___y_1775_, 2);
lean_dec(v_unused_1979_);
v_unused_1980_ = lean_ctor_get(v___y_1775_, 1);
lean_dec(v_unused_1980_);
v_unused_1981_ = lean_ctor_get(v___y_1775_, 0);
lean_dec(v_unused_1981_);
v___x_1966_ = v___y_1775_;
v_isShared_1967_ = v_isSharedCheck_1978_;
goto v_resetjp_1965_;
}
else
{
lean_dec(v___y_1775_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1978_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v_a_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1975_; 
v_a_1968_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1969_ = lean_io_error_to_string(v_a_1968_);
v___x_1970_ = 3;
v___x_1971_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set_uint8(v___x_1971_, sizeof(void*)*1, v___x_1970_);
v___x_1972_ = lean_array_get_size(v_log_1893_);
v___x_1973_ = lean_array_push(v_log_1893_, v___x_1971_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1973_);
v___x_1975_ = v___x_1966_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_trace_1896_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_buildTime_1897_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*3, v_action_1894_);
lean_ctor_set_uint8(v_reuseFailAlloc_1977_, sizeof(void*)*3 + 1, v_wantsRebuild_1895_);
v___x_1975_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1972_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
return v___x_1976_;
}
}
}
v___jp_1901_:
{
lean_object* v___x_1903_; lean_object* v_log_1904_; uint8_t v_action_1905_; uint8_t v_wantsRebuild_1906_; lean_object* v_trace_1907_; lean_object* v_buildTime_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1949_; 
v___x_1903_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1904_ = lean_ctor_get(v_a_1902_, 0);
v_action_1905_ = lean_ctor_get_uint8(v_a_1902_, sizeof(void*)*3);
v_wantsRebuild_1906_ = lean_ctor_get_uint8(v_a_1902_, sizeof(void*)*3 + 1);
v_trace_1907_ = lean_ctor_get(v_a_1902_, 1);
v_buildTime_1908_ = lean_ctor_get(v_a_1902_, 2);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_a_1902_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1910_ = v_a_1902_;
v_isShared_1911_ = v_isSharedCheck_1949_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_buildTime_1908_);
lean_inc(v_trace_1907_);
lean_inc(v_log_1904_);
lean_dec(v_a_1902_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1949_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1912_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1913_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1914_ = lean_unsigned_to_nat(5u);
v___x_1915_ = lean_mk_empty_array_with_capacity(v___x_1914_);
lean_dec_ref(v___x_1915_);
v___x_1916_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1917_ = lean_array_push(v___x_1916_, v___y_1765_);
v___x_1918_ = lean_array_push(v___x_1917_, v___x_1913_);
v___x_1919_ = lean_array_push(v___x_1918_, v___x_1900_);
v___x_1920_ = lean_box(0);
v___x_1921_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1922_ = 0;
v___x_1923_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1923_, 0, v___x_1903_);
lean_ctor_set(v___x_1923_, 1, v___x_1912_);
lean_ctor_set(v___x_1923_, 2, v___x_1919_);
lean_ctor_set(v___x_1923_, 3, v___x_1920_);
lean_ctor_set(v___x_1923_, 4, v___x_1921_);
lean_ctor_set_uint8(v___x_1923_, sizeof(void*)*5, v___x_1768_);
lean_ctor_set_uint8(v___x_1923_, sizeof(void*)*5 + 1, v___x_1922_);
v___x_1924_ = l_Lake_proc(v___x_1923_, v___x_1922_, v___x_1920_, v_log_1904_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1936_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_a_1926_ = lean_ctor_get(v___x_1924_, 1);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1928_ = v___x_1924_;
v_isShared_1929_ = v_isSharedCheck_1936_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1936_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v_a_1926_);
v___x_1931_ = v___x_1910_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1926_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_trace_1907_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_buildTime_1908_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*3, v_action_1905_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*3 + 1, v_wantsRebuild_1906_);
v___x_1931_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1933_; 
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v___x_1931_);
v___x_1933_ = v___x_1928_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1925_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1948_; 
v_a_1937_ = lean_ctor_get(v___x_1924_, 0);
v_a_1938_ = lean_ctor_get(v___x_1924_, 1);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1940_ = v___x_1924_;
v_isShared_1941_ = v_isSharedCheck_1948_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_inc(v_a_1937_);
lean_dec(v___x_1924_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1948_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v_a_1938_);
v___x_1943_ = v___x_1910_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1938_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_trace_1907_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_buildTime_1908_);
lean_ctor_set_uint8(v_reuseFailAlloc_1947_, sizeof(void*)*3, v_action_1905_);
lean_ctor_set_uint8(v_reuseFailAlloc_1947_, sizeof(void*)*3 + 1, v_wantsRebuild_1906_);
v___x_1943_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1945_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 1, v___x_1943_);
v___x_1945_ = v___x_1940_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1937_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
}
}
v___jp_1950_:
{
if (lean_obj_tag(v___y_1951_) == 0)
{
lean_object* v_a_1952_; 
v_a_1952_ = lean_ctor_get(v___y_1951_, 1);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___y_1951_, 2);
v_a_1902_ = v_a_1952_;
goto v___jp_1901_;
}
else
{
lean_dec_ref(v___x_1900_);
lean_dec_ref(v___y_1765_);
return v___y_1951_;
}
}
}
else
{
lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1995_; 
lean_inc(v_buildTime_1897_);
lean_inc_ref(v_trace_1896_);
lean_inc_ref(v_log_1893_);
lean_dec_ref(v_oFiles_1766_);
lean_dec_ref(v___y_1765_);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___y_1775_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; lean_object* v_unused_1997_; lean_object* v_unused_1998_; 
v_unused_1996_ = lean_ctor_get(v___y_1775_, 2);
lean_dec(v_unused_1996_);
v_unused_1997_ = lean_ctor_get(v___y_1775_, 1);
lean_dec(v_unused_1997_);
v_unused_1998_ = lean_ctor_get(v___y_1775_, 0);
lean_dec(v_unused_1998_);
v___x_1983_ = v___y_1775_;
v_isShared_1984_ = v_isSharedCheck_1995_;
goto v_resetjp_1982_;
}
else
{
lean_dec(v___y_1775_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1995_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_a_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1992_; 
v_a_1985_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1898_, 1);
v___x_1986_ = lean_io_error_to_string(v_a_1985_);
v___x_1987_ = 3;
v___x_1988_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set_uint8(v___x_1988_, sizeof(void*)*1, v___x_1987_);
v___x_1989_ = lean_array_get_size(v_log_1893_);
v___x_1990_ = lean_array_push(v_log_1893_, v___x_1988_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1990_);
v___x_1992_ = v___x_1983_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_trace_1896_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_buildTime_1897_);
lean_ctor_set_uint8(v_reuseFailAlloc_1994_, sizeof(void*)*3, v_action_1894_);
lean_ctor_set_uint8(v_reuseFailAlloc_1994_, sizeof(void*)*3 + 1, v_wantsRebuild_1895_);
v___x_1992_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1989_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
return v___x_1993_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object* v_bootstrap_1999_, lean_object* v___y_2000_, lean_object* v_oFiles_2001_, lean_object* v_shouldExport_2002_, lean_object* v___x_2003_, lean_object* v___x_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
uint8_t v_bootstrap_boxed_2012_; uint8_t v_shouldExport_boxed_2013_; uint8_t v___x_6746__boxed_2014_; size_t v___x_6747__boxed_2015_; lean_object* v_res_2016_; 
v_bootstrap_boxed_2012_ = lean_unbox(v_bootstrap_1999_);
v_shouldExport_boxed_2013_ = lean_unbox(v_shouldExport_2002_);
v___x_6746__boxed_2014_ = lean_unbox(v___x_2003_);
v___x_6747__boxed_2015_ = lean_unbox_usize(v___x_2004_);
lean_dec(v___x_2004_);
v_res_2016_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_boxed_2012_, v___y_2000_, v_oFiles_2001_, v_shouldExport_boxed_2013_, v___x_6746__boxed_2014_, v___x_6747__boxed_2015_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t v_bootstrap_2017_, lean_object* v___y_2018_, uint8_t v_shouldExport_2019_, uint8_t v___x_2020_, size_t v___x_2021_, lean_object* v_oFiles_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___y_2034_; uint8_t v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2030_ = lean_box(v_bootstrap_2017_);
v___x_2031_ = lean_box(v_shouldExport_2019_);
v___x_2032_ = lean_box(v___x_2020_);
v___x_2033_ = lean_box_usize(v___x_2021_);
lean_inc_ref(v___y_2018_);
v___y_2034_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed), 13, 6);
lean_closure_set(v___y_2034_, 0, v___x_2030_);
lean_closure_set(v___y_2034_, 1, v___y_2018_);
lean_closure_set(v___y_2034_, 2, v_oFiles_2022_);
lean_closure_set(v___y_2034_, 3, v___x_2031_);
lean_closure_set(v___y_2034_, 4, v___x_2032_);
lean_closure_set(v___y_2034_, 5, v___x_2033_);
v___x_2035_ = 0;
v___x_2036_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_2037_ = l_Lake_buildArtifactUnlessUpToDate(v___y_2018_, v___y_2034_, v___x_2035_, v___x_2036_, v___x_2020_, v___x_2035_, v___x_2035_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2047_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_a_2039_ = lean_ctor_get(v___x_2037_, 1);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2041_ = v___x_2037_;
v_isShared_2042_ = v_isSharedCheck_2047_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2047_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v_path_2043_; lean_object* v___x_2045_; 
v_path_2043_ = lean_ctor_get(v_a_2038_, 1);
lean_inc_ref(v_path_2043_);
lean_dec(v_a_2038_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v_path_2043_);
v___x_2045_ = v___x_2041_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_path_2043_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_a_2039_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
v_a_2048_ = lean_ctor_get(v___x_2037_, 0);
v_a_2049_ = lean_ctor_get(v___x_2037_, 1);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2037_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_inc(v_a_2048_);
lean_dec(v___x_2037_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2048_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* v_bootstrap_2057_, lean_object* v___y_2058_, lean_object* v_shouldExport_2059_, lean_object* v___x_2060_, lean_object* v___x_2061_, lean_object* v_oFiles_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
uint8_t v_bootstrap_boxed_2070_; uint8_t v_shouldExport_boxed_2071_; uint8_t v___x_7156__boxed_2072_; size_t v___x_7157__boxed_2073_; lean_object* v_res_2074_; 
v_bootstrap_boxed_2070_ = lean_unbox(v_bootstrap_2057_);
v_shouldExport_boxed_2071_ = lean_unbox(v_shouldExport_2059_);
v___x_7156__boxed_2072_ = lean_unbox(v___x_2060_);
v___x_7157__boxed_2073_ = lean_unbox_usize(v___x_2061_);
lean_dec(v___x_2061_);
v_res_2074_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_boxed_2070_, v___y_2058_, v_shouldExport_boxed_2071_, v___x_7156__boxed_2072_, v___x_7157__boxed_2073_, v_oFiles_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec(v___y_2064_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* v_a_2075_, size_t v_sz_2076_, size_t v_i_2077_, lean_object* v_bs_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
uint8_t v___x_2086_; 
v___x_2086_ = lean_usize_dec_lt(v_i_2077_, v_sz_2076_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; 
lean_dec_ref(v___y_2079_);
lean_dec_ref(v_a_2075_);
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v_bs_2078_);
lean_ctor_set(v___x_2087_, 1, v___y_2084_);
return v___x_2087_;
}
else
{
lean_object* v_v_2088_; lean_object* v___x_2089_; 
v_v_2088_ = lean_array_uget_borrowed(v_bs_2078_, v_i_2077_);
lean_inc_ref(v___y_2079_);
lean_inc_ref(v_a_2075_);
lean_inc(v_v_2088_);
v___x_2089_ = l_Lake_ModuleFacet_fetch___redArg(v_v_2088_, v_a_2075_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v_a_2091_; lean_object* v___x_2092_; lean_object* v_bs_x27_2093_; size_t v___x_2094_; size_t v___x_2095_; lean_object* v___x_2096_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
v_a_2091_ = lean_ctor_get(v___x_2089_, 1);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2089_, 2);
v___x_2092_ = lean_unsigned_to_nat(0u);
v_bs_x27_2093_ = lean_array_uset(v_bs_2078_, v_i_2077_, v___x_2092_);
v___x_2094_ = ((size_t)1ULL);
v___x_2095_ = lean_usize_add(v_i_2077_, v___x_2094_);
v___x_2096_ = lean_array_uset(v_bs_x27_2093_, v_i_2077_, v_a_2090_);
v_i_2077_ = v___x_2095_;
v_bs_2078_ = v___x_2096_;
v___y_2084_ = v_a_2091_;
goto _start;
}
else
{
lean_object* v_a_2098_; lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec_ref(v___y_2079_);
lean_dec_ref(v_bs_2078_);
lean_dec_ref(v_a_2075_);
v_a_2098_ = lean_ctor_get(v___x_2089_, 0);
v_a_2099_ = lean_ctor_get(v___x_2089_, 1);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2089_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_inc(v_a_2098_);
lean_dec(v___x_2089_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2098_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object* v_a_2107_, lean_object* v_sz_2108_, lean_object* v_i_2109_, lean_object* v_bs_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
size_t v_sz_boxed_2118_; size_t v_i_boxed_2119_; lean_object* v_res_2120_; 
v_sz_boxed_2118_ = lean_unbox_usize(v_sz_2108_);
lean_dec(v_sz_2108_);
v_i_boxed_2119_ = lean_unbox_usize(v_i_2109_);
lean_dec(v_i_2109_);
v_res_2120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_2107_, v_sz_boxed_2118_, v_i_boxed_2119_, v_bs_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec(v___y_2112_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(uint8_t v_shouldExport_2121_, lean_object* v_as_2122_, size_t v_i_2123_, size_t v_stop_2124_, lean_object* v_b_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
uint8_t v___x_2133_; 
v___x_2133_ = lean_usize_dec_eq(v_i_2123_, v_stop_2124_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; lean_object* v_lib_2135_; lean_object* v_config_2136_; lean_object* v_nativeFacets_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; size_t v_sz_2140_; size_t v___x_2141_; lean_object* v___x_2142_; 
v___x_2134_ = lean_array_uget_borrowed(v_as_2122_, v_i_2123_);
v_lib_2135_ = lean_ctor_get(v___x_2134_, 0);
v_config_2136_ = lean_ctor_get(v_lib_2135_, 2);
v_nativeFacets_2137_ = lean_ctor_get(v_config_2136_, 8);
v___x_2138_ = lean_box(v_shouldExport_2121_);
lean_inc_ref(v_nativeFacets_2137_);
v___x_2139_ = lean_apply_1(v_nativeFacets_2137_, v___x_2138_);
v_sz_2140_ = lean_array_size(v___x_2139_);
v___x_2141_ = ((size_t)0ULL);
lean_inc_ref(v___y_2126_);
lean_inc(v___x_2134_);
v___x_2142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2134_, v_sz_2140_, v___x_2141_, v___x_2139_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v_a_2144_; lean_object* v___x_2145_; size_t v___x_2146_; size_t v___x_2147_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
v_a_2144_ = lean_ctor_get(v___x_2142_, 1);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2142_, 2);
v___x_2145_ = l_Array_append___redArg(v_b_2125_, v_a_2143_);
lean_dec(v_a_2143_);
v___x_2146_ = ((size_t)1ULL);
v___x_2147_ = lean_usize_add(v_i_2123_, v___x_2146_);
v_i_2123_ = v___x_2147_;
v_b_2125_ = v___x_2145_;
v___y_2131_ = v_a_2144_;
goto _start;
}
else
{
lean_dec_ref(v___y_2126_);
lean_dec_ref(v_b_2125_);
return v___x_2142_;
}
}
else
{
lean_object* v___x_2149_; 
lean_dec_ref(v___y_2126_);
v___x_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2149_, 0, v_b_2125_);
lean_ctor_set(v___x_2149_, 1, v___y_2131_);
return v___x_2149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(lean_object* v_shouldExport_2150_, lean_object* v_as_2151_, lean_object* v_i_2152_, lean_object* v_stop_2153_, lean_object* v_b_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
uint8_t v_shouldExport_boxed_2162_; size_t v_i_boxed_2163_; size_t v_stop_boxed_2164_; lean_object* v_res_2165_; 
v_shouldExport_boxed_2162_ = lean_unbox(v_shouldExport_2150_);
v_i_boxed_2163_ = lean_unbox_usize(v_i_2152_);
lean_dec(v_i_2152_);
v_stop_boxed_2164_ = lean_unbox_usize(v_stop_2153_);
lean_dec(v_stop_2153_);
v_res_2165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_boxed_2162_, v_as_2151_, v_i_boxed_2163_, v_stop_boxed_2164_, v_b_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v_as_2151_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object* v___x_2166_, lean_object* v___x_2167_, lean_object* v_config_2168_, lean_object* v_config_2169_, lean_object* v_pkg_2170_, uint8_t v_shouldExport_2171_, uint8_t v___x_2172_, lean_object* v___x_2173_, lean_object* v_dir_2174_, lean_object* v_self_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
size_t v___y_2184_; uint8_t v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v_a_2204_; lean_object* v_a_2205_; lean_object* v___y_2248_; lean_object* v___x_2260_; 
lean_inc_ref(v___y_2176_);
lean_inc_ref(v___y_2180_);
lean_inc(v___y_2179_);
lean_inc(v___y_2178_);
lean_inc(v___x_2167_);
v___x_2260_ = lean_apply_7(v___y_2176_, v___x_2166_, v___x_2167_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, lean_box(0));
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v_a_2262_; lean_object* v___x_2263_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
v_a_2262_ = lean_ctor_get(v___x_2260_, 1);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2260_, 2);
v___x_2263_ = l_Lake_Job_await___redArg(v_a_2261_, v_a_2262_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v_a_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
v_a_2265_ = lean_ctor_get(v___x_2263_, 1);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2263_, 2);
v___x_2266_ = lean_unsigned_to_nat(0u);
v___x_2267_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_2268_ = lean_array_get_size(v_a_2264_);
v___x_2269_ = lean_nat_dec_lt(v___x_2266_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_dec(v_a_2264_);
v_a_2204_ = v___x_2267_;
v_a_2205_ = v_a_2265_;
goto v___jp_2203_;
}
else
{
uint8_t v___x_2270_; 
v___x_2270_ = lean_nat_dec_le(v___x_2268_, v___x_2268_);
if (v___x_2270_ == 0)
{
if (v___x_2269_ == 0)
{
lean_dec(v_a_2264_);
v_a_2204_ = v___x_2267_;
v_a_2205_ = v_a_2265_;
goto v___jp_2203_;
}
else
{
size_t v___x_2271_; size_t v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = ((size_t)0ULL);
v___x_2272_ = lean_usize_of_nat(v___x_2268_);
lean_inc_ref(v___y_2176_);
v___x_2273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2171_, v_a_2264_, v___x_2271_, v___x_2272_, v___x_2267_, v___y_2176_, v___x_2167_, v___y_2178_, v___y_2179_, v___y_2180_, v_a_2265_);
lean_dec(v_a_2264_);
v___y_2248_ = v___x_2273_;
goto v___jp_2247_;
}
}
else
{
size_t v___x_2274_; size_t v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = ((size_t)0ULL);
v___x_2275_ = lean_usize_of_nat(v___x_2268_);
lean_inc_ref(v___y_2176_);
v___x_2276_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2171_, v_a_2264_, v___x_2274_, v___x_2275_, v___x_2267_, v___y_2176_, v___x_2167_, v___y_2178_, v___y_2179_, v___y_2180_, v_a_2265_);
lean_dec(v_a_2264_);
v___y_2248_ = v___x_2276_;
goto v___jp_2247_;
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v___y_2176_);
lean_dec_ref(v_self_2175_);
lean_dec_ref(v_dir_2174_);
lean_dec(v___x_2173_);
lean_dec_ref(v_pkg_2170_);
lean_dec_ref(v_config_2168_);
lean_dec(v___x_2167_);
v_a_2277_ = lean_ctor_get(v___x_2263_, 0);
v_a_2278_ = lean_ctor_get(v___x_2263_, 1);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2263_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_inc(v_a_2277_);
lean_dec(v___x_2263_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2277_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref(v___y_2176_);
lean_dec_ref(v_self_2175_);
lean_dec_ref(v_dir_2174_);
lean_dec(v___x_2173_);
lean_dec_ref(v_pkg_2170_);
lean_dec_ref(v_config_2168_);
lean_dec(v___x_2167_);
v_a_2286_ = lean_ctor_get(v___x_2260_, 0);
v_a_2287_ = lean_ctor_get(v___x_2260_, 1);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2260_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_inc(v_a_2286_);
lean_dec(v___x_2260_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2286_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
v___jp_2183_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___f_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; uint8_t v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2190_ = lean_box(v___y_2185_);
v___x_2191_ = lean_box(v_shouldExport_2171_);
v___x_2192_ = lean_box(v___x_2172_);
v___x_2193_ = lean_box_usize(v___y_2184_);
v___f_2194_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2194_, 0, v___x_2190_);
lean_closure_set(v___f_2194_, 1, v___y_2189_);
lean_closure_set(v___f_2194_, 2, v___x_2191_);
lean_closure_set(v___f_2194_, 3, v___x_2192_);
lean_closure_set(v___f_2194_, 4, v___x_2193_);
v___x_2195_ = l_Array_append___redArg(v___y_2188_, v___y_2187_);
lean_dec_ref(v___y_2187_);
v___x_2196_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_2197_ = l_Lake_Job_collectArray___redArg(v___x_2195_, v___x_2196_);
lean_dec_ref(v___x_2195_);
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = 0;
v___x_2200_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2201_ = l_Lake_Job_mapM___redArg(v___x_2173_, v___x_2197_, v___f_2194_, v___x_2198_, v___x_2199_, v___y_2176_, v___x_2167_, v___y_2178_, v___y_2179_, v___y_2180_, v___x_2200_);
lean_dec(v___x_2167_);
v___x_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v___y_2186_);
return v___x_2202_;
}
v___jp_2203_:
{
lean_object* v_toLeanConfig_2206_; lean_object* v_toLeanConfig_2207_; uint8_t v_bootstrap_2208_; lean_object* v_buildDir_2209_; lean_object* v_nativeLibDir_2210_; lean_object* v_moreLinkObjs_2211_; lean_object* v_moreLinkObjs_2212_; lean_object* v___x_2213_; size_t v_sz_2214_; size_t v___x_2215_; lean_object* v___x_2216_; 
v_toLeanConfig_2206_ = lean_ctor_get(v_config_2168_, 1);
lean_inc_ref(v_toLeanConfig_2206_);
v_toLeanConfig_2207_ = lean_ctor_get(v_config_2169_, 0);
v_bootstrap_2208_ = lean_ctor_get_uint8(v_config_2168_, sizeof(void*)*27);
v_buildDir_2209_ = lean_ctor_get(v_config_2168_, 5);
lean_inc_ref(v_buildDir_2209_);
v_nativeLibDir_2210_ = lean_ctor_get(v_config_2168_, 7);
lean_inc_ref(v_nativeLibDir_2210_);
lean_dec_ref(v_config_2168_);
v_moreLinkObjs_2211_ = lean_ctor_get(v_toLeanConfig_2206_, 6);
lean_inc_ref(v_moreLinkObjs_2211_);
lean_dec_ref(v_toLeanConfig_2206_);
v_moreLinkObjs_2212_ = lean_ctor_get(v_toLeanConfig_2207_, 6);
v___x_2213_ = l_Array_append___redArg(v_moreLinkObjs_2211_, v_moreLinkObjs_2212_);
v_sz_2214_ = lean_array_size(v___x_2213_);
v___x_2215_ = ((size_t)0ULL);
lean_inc_ref(v___y_2176_);
v___x_2216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_2170_, v_sz_2214_, v___x_2215_, v___x_2213_, v___y_2176_, v___x_2167_, v___y_2178_, v___y_2179_, v___y_2180_, v_a_2205_);
if (lean_obj_tag(v___x_2216_) == 0)
{
if (v_shouldExport_2171_ == 0)
{
lean_object* v_a_2217_; lean_object* v_a_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
v_a_2218_ = lean_ctor_get(v___x_2216_, 1);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2216_, 2);
v___x_2219_ = l_System_FilePath_normalize(v_buildDir_2209_);
v___x_2220_ = l_Lake_joinRelative(v_dir_2174_, v___x_2219_);
v___x_2221_ = l_System_FilePath_normalize(v_nativeLibDir_2210_);
v___x_2222_ = l_Lake_joinRelative(v___x_2220_, v___x_2221_);
v___x_2223_ = l_Lake_LeanLib_libName(v_self_2175_);
v___x_2224_ = l_Lake_nameToStaticLib(v___x_2223_, v_shouldExport_2171_);
v___x_2225_ = l_Lake_joinRelative(v___x_2222_, v___x_2224_);
v___y_2184_ = v___x_2215_;
v___y_2185_ = v_bootstrap_2208_;
v___y_2186_ = v_a_2218_;
v___y_2187_ = v_a_2217_;
v___y_2188_ = v_a_2204_;
v___y_2189_ = v___x_2225_;
goto v___jp_2183_;
}
else
{
lean_object* v_a_2226_; lean_object* v_a_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v_a_2226_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2226_);
v_a_2227_ = lean_ctor_get(v___x_2216_, 1);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2216_, 2);
v___x_2228_ = l_System_FilePath_normalize(v_buildDir_2209_);
v___x_2229_ = l_Lake_joinRelative(v_dir_2174_, v___x_2228_);
v___x_2230_ = l_System_FilePath_normalize(v_nativeLibDir_2210_);
v___x_2231_ = l_Lake_joinRelative(v___x_2229_, v___x_2230_);
v___x_2232_ = l_Lake_LeanLib_libName(v_self_2175_);
v___x_2233_ = 0;
v___x_2234_ = l_Lake_nameToStaticLib(v___x_2232_, v___x_2233_);
v___x_2235_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_2236_ = l_System_FilePath_addExtension(v___x_2234_, v___x_2235_);
v___x_2237_ = l_Lake_joinRelative(v___x_2231_, v___x_2236_);
v___y_2184_ = v___x_2215_;
v___y_2185_ = v_bootstrap_2208_;
v___y_2186_ = v_a_2227_;
v___y_2187_ = v_a_2226_;
v___y_2188_ = v_a_2204_;
v___y_2189_ = v___x_2237_;
goto v___jp_2183_;
}
}
else
{
lean_object* v_a_2238_; lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v_nativeLibDir_2210_);
lean_dec_ref(v_buildDir_2209_);
lean_dec_ref(v_a_2204_);
lean_dec_ref(v___y_2176_);
lean_dec_ref(v_self_2175_);
lean_dec_ref(v_dir_2174_);
lean_dec(v___x_2173_);
lean_dec(v___x_2167_);
v_a_2238_ = lean_ctor_get(v___x_2216_, 0);
v_a_2239_ = lean_ctor_get(v___x_2216_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2216_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_inc(v_a_2238_);
lean_dec(v___x_2216_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2238_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_a_2239_);
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
v___jp_2247_:
{
if (lean_obj_tag(v___y_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v_a_2250_; 
v_a_2249_ = lean_ctor_get(v___y_2248_, 0);
lean_inc(v_a_2249_);
v_a_2250_ = lean_ctor_get(v___y_2248_, 1);
lean_inc(v_a_2250_);
lean_dec_ref_known(v___y_2248_, 2);
v_a_2204_ = v_a_2249_;
v_a_2205_ = v_a_2250_;
goto v___jp_2203_;
}
else
{
lean_object* v_a_2251_; lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec_ref(v___y_2176_);
lean_dec_ref(v_self_2175_);
lean_dec_ref(v_dir_2174_);
lean_dec(v___x_2173_);
lean_dec_ref(v_pkg_2170_);
lean_dec_ref(v_config_2168_);
lean_dec(v___x_2167_);
v_a_2251_ = lean_ctor_get(v___y_2248_, 0);
v_a_2252_ = lean_ctor_get(v___y_2248_, 1);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___y_2248_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___y_2248_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_inc(v_a_2251_);
lean_dec(v___y_2248_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2251_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(lean_object** _args){
lean_object* v___x_2295_ = _args[0];
lean_object* v___x_2296_ = _args[1];
lean_object* v_config_2297_ = _args[2];
lean_object* v_config_2298_ = _args[3];
lean_object* v_pkg_2299_ = _args[4];
lean_object* v_shouldExport_2300_ = _args[5];
lean_object* v___x_2301_ = _args[6];
lean_object* v___x_2302_ = _args[7];
lean_object* v_dir_2303_ = _args[8];
lean_object* v_self_2304_ = _args[9];
lean_object* v___y_2305_ = _args[10];
lean_object* v___y_2306_ = _args[11];
lean_object* v___y_2307_ = _args[12];
lean_object* v___y_2308_ = _args[13];
lean_object* v___y_2309_ = _args[14];
lean_object* v___y_2310_ = _args[15];
lean_object* v___y_2311_ = _args[16];
_start:
{
uint8_t v_shouldExport_boxed_2312_; uint8_t v___x_7358__boxed_2313_; lean_object* v_res_2314_; 
v_shouldExport_boxed_2312_ = lean_unbox(v_shouldExport_2300_);
v___x_7358__boxed_2313_ = lean_unbox(v___x_2301_);
v_res_2314_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v___x_2295_, v___x_2296_, v_config_2297_, v_config_2298_, v_pkg_2299_, v_shouldExport_boxed_2312_, v___x_7358__boxed_2313_, v___x_2302_, v_dir_2303_, v_self_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec(v_config_2298_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object* v___y_2315_, lean_object* v_self_2316_, uint8_t v_shouldExport_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_toBuildConfig_2324_; lean_object* v_registeredJobs_2325_; uint8_t v_verbosity_2326_; lean_object* v___x_2327_; uint8_t v___x_2328_; uint8_t v___x_2329_; uint8_t v___x_2330_; lean_object* v___y_2332_; 
v_toBuildConfig_2324_ = lean_ctor_get(v_a_2321_, 0);
v_registeredJobs_2325_ = lean_ctor_get(v_a_2321_, 3);
v_verbosity_2326_ = lean_ctor_get_uint8(v_toBuildConfig_2324_, sizeof(void*)*4 + 3);
v___x_2327_ = l_Lake_instDataKindFilePath;
v___x_2328_ = 2;
v___x_2329_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2326_, v___x_2328_);
v___x_2330_ = 1;
if (v___x_2329_ == 0)
{
lean_object* v___x_2377_; 
v___x_2377_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_2332_ = v___x_2377_;
goto v___jp_2331_;
}
else
{
if (v_shouldExport_2317_ == 0)
{
lean_object* v___x_2378_; 
v___x_2378_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___y_2332_ = v___x_2378_;
goto v___jp_2331_;
}
else
{
lean_object* v___x_2379_; 
v___x_2379_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_2332_ = v___x_2379_;
goto v___jp_2331_;
}
}
v___jp_2331_:
{
lean_object* v_pkg_2333_; lean_object* v_name_2334_; lean_object* v_config_2335_; lean_object* v_keyName_2336_; lean_object* v_dir_2337_; lean_object* v_config_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___f_2346_; lean_object* v___x_2347_; 
v_pkg_2333_ = lean_ctor_get(v_self_2316_, 0);
lean_inc_ref_n(v_pkg_2333_, 2);
v_name_2334_ = lean_ctor_get(v_self_2316_, 1);
lean_inc_n(v_name_2334_, 2);
v_config_2335_ = lean_ctor_get(v_self_2316_, 2);
lean_inc(v_config_2335_);
v_keyName_2336_ = lean_ctor_get(v_pkg_2333_, 2);
v_dir_2337_ = lean_ctor_get(v_pkg_2333_, 4);
lean_inc_ref(v_dir_2337_);
v_config_2338_ = lean_ctor_get(v_pkg_2333_, 6);
lean_inc_ref(v_config_2338_);
v___x_2339_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_2336_);
v___x_2340_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2340_, 0, v_keyName_2336_);
lean_ctor_set(v___x_2340_, 1, v_name_2334_);
v___x_2341_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_2316_);
v___x_2342_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
lean_ctor_set(v___x_2342_, 2, v_self_2316_);
lean_ctor_set(v___x_2342_, 3, v___x_2339_);
v___x_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2343_, 0, v_pkg_2333_);
v___x_2344_ = lean_box(v_shouldExport_2317_);
v___x_2345_ = lean_box(v___x_2330_);
v___f_2346_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed), 17, 10);
lean_closure_set(v___f_2346_, 0, v___x_2342_);
lean_closure_set(v___f_2346_, 1, v___x_2343_);
lean_closure_set(v___f_2346_, 2, v_config_2338_);
lean_closure_set(v___f_2346_, 3, v_config_2335_);
lean_closure_set(v___f_2346_, 4, v_pkg_2333_);
lean_closure_set(v___f_2346_, 5, v___x_2344_);
lean_closure_set(v___f_2346_, 6, v___x_2345_);
lean_closure_set(v___f_2346_, 7, v___x_2327_);
lean_closure_set(v___f_2346_, 8, v_dir_2337_);
lean_closure_set(v___f_2346_, 9, v_self_2316_);
v___x_2347_ = l_Lake_ensureJob___redArg(v___x_2327_, v___f_2346_, v___y_2315_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2376_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_a_2349_ = lean_ctor_get(v___x_2347_, 1);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2351_ = v___x_2347_;
v_isShared_2352_ = v_isSharedCheck_2376_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2376_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v_task_2353_; lean_object* v_kind_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2374_; 
v_task_2353_ = lean_ctor_get(v_a_2348_, 0);
v_kind_2354_ = lean_ctor_get(v_a_2348_, 1);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_a_2348_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; 
v_unused_2375_ = lean_ctor_get(v_a_2348_, 2);
lean_dec(v_unused_2375_);
v___x_2356_ = v_a_2348_;
v_isShared_2357_ = v_isSharedCheck_2374_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_kind_2354_);
lean_inc(v_task_2353_);
lean_dec(v_a_2348_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2374_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; lean_object* v_job_2365_; 
v___x_2358_ = lean_st_ref_take(v_registeredJobs_2325_);
v___x_2359_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2334_, v___x_2330_);
v___x_2360_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0));
v___x_2361_ = lean_string_append(v___x_2359_, v___x_2360_);
v___x_2362_ = lean_string_append(v___x_2361_, v___y_2332_);
v___x_2363_ = 0;
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 2, v___x_2362_);
v_job_2365_ = v___x_2356_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_task_2353_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v_kind_2354_);
lean_ctor_set(v_reuseFailAlloc_2373_, 2, v___x_2362_);
v_job_2365_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
lean_ctor_set_uint8(v_job_2365_, sizeof(void*)*3, v___x_2363_);
lean_inc_ref(v_job_2365_);
v___x_2366_ = l_Lake_Job_toOpaque___redArg(v_job_2365_);
v___x_2367_ = lean_array_push(v___x_2358_, v___x_2366_);
v___x_2368_ = lean_st_ref_put(v_registeredJobs_2325_, v___x_2367_);
v___x_2369_ = l_Lake_Job_renew___redArg(v_job_2365_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2369_);
v___x_2371_ = v___x_2351_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_a_2349_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
else
{
lean_dec(v_name_2334_);
return v___x_2347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* v___y_2380_, lean_object* v_self_2381_, lean_object* v_shouldExport_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
uint8_t v_shouldExport_boxed_2389_; lean_object* v_res_2390_; 
v_shouldExport_boxed_2389_ = lean_unbox(v_shouldExport_2382_);
v_res_2390_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2380_, v_self_2381_, v_shouldExport_boxed_2389_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
lean_dec_ref(v_a_2386_);
lean_dec(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec(v_a_2383_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* v_x_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
uint8_t v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = 0;
v___x_2400_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2392_, v_x_2391_, v___x_2399_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object* v_x_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec(v___y_2403_);
return v_res_2409_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2412_; uint8_t v___x_2413_; lean_object* v___x_2414_; lean_object* v___f_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___f_2412_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2413_ = 1;
v___x_2414_ = l_Lake_instDataKindFilePath;
v___f_2415_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__0));
v___x_2416_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2417_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
lean_ctor_set(v___x_2417_, 1, v___f_2415_);
lean_ctor_set(v___x_2417_, 2, v___x_2414_);
lean_ctor_set(v___x_2417_, 3, v___f_2412_);
lean_ctor_set_uint8(v___x_2417_, sizeof(void*)*4, v___x_2413_);
lean_ctor_set_uint8(v___x_2417_, sizeof(void*)*4 + 1, v___x_2413_);
return v___x_2417_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_obj_once(&l_Lake_LeanLib_staticFacetConfig___closed__2, &l_Lake_LeanLib_staticFacetConfig___closed__2_once, _init_l_Lake_LeanLib_staticFacetConfig___closed__2);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(lean_object* v_a_2419_, lean_object* v_as_2420_, size_t v_i_2421_, size_t v_stop_2422_, lean_object* v_b_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2419_, v_as_2420_, v_i_2421_, v_stop_2422_, v_b_2423_, v___y_2429_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* v_a_2432_, lean_object* v_as_2433_, lean_object* v_i_2434_, lean_object* v_stop_2435_, lean_object* v_b_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
size_t v_i_boxed_2444_; size_t v_stop_boxed_2445_; lean_object* v_res_2446_; 
v_i_boxed_2444_ = lean_unbox_usize(v_i_2434_);
lean_dec(v_i_2434_);
v_stop_boxed_2445_ = lean_unbox_usize(v_stop_2435_);
lean_dec(v_stop_2435_);
v_res_2446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_2432_, v_as_2433_, v_i_boxed_2444_, v_stop_boxed_2445_, v_b_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec_ref(v_as_2433_);
lean_dec(v_a_2432_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* v_x_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
uint8_t v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = 1;
v___x_2456_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2448_, v_x_2447_, v___x_2455_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object* v_x_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec(v___y_2459_);
return v_res_2465_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___f_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___f_2467_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2468_ = 1;
v___x_2469_ = l_Lake_instDataKindFilePath;
v___f_2470_ = ((lean_object*)(l_Lake_LeanLib_staticExportFacetConfig___closed__0));
v___x_2471_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2472_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
lean_ctor_set(v___x_2472_, 1, v___f_2470_);
lean_ctor_set(v___x_2472_, 2, v___x_2469_);
lean_ctor_set(v___x_2472_, 3, v___f_2467_);
lean_ctor_set_uint8(v___x_2472_, sizeof(void*)*4, v___x_2468_);
lean_ctor_set_uint8(v___x_2472_, sizeof(void*)*4 + 1, v___x_2468_);
return v___x_2472_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig(void){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_obj_once(&l_Lake_LeanLib_staticExportFacetConfig___closed__1, &l_Lake_LeanLib_staticExportFacetConfig___closed__1_once, _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1);
return v___x_2473_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0(void){
_start:
{
uint8_t v___x_2474_; lean_object* v_name_2475_; lean_object* v___x_2476_; 
v___x_2474_ = 1;
v_name_2475_ = l_Lake_instDataKindDynlib;
v___x_2476_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2475_, v___x_2474_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object* v_defaultPkg_2477_, lean_object* v_self_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
uint8_t v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = 1;
lean_inc_ref_n(v_self_2478_, 2);
v___x_2487_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_2477_, v_self_2478_, v_self_2478_, v___x_2486_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v_snd_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2530_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
v_snd_2489_ = lean_ctor_get(v_a_2488_, 1);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_a_2488_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v_a_2488_, 0);
lean_dec(v_unused_2531_);
v___x_2491_ = v_a_2488_;
v_isShared_2492_ = v_isSharedCheck_2530_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_snd_2489_);
lean_dec(v_a_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2530_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2528_; 
v_a_2493_ = lean_ctor_get(v___x_2487_, 1);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; 
v_unused_2529_ = lean_ctor_get(v___x_2487_, 0);
lean_dec(v_unused_2529_);
v___x_2495_ = v___x_2487_;
v_isShared_2496_ = v_isSharedCheck_2528_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2487_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2528_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v_kind_2497_; lean_object* v_name_2498_; lean_object* v___y_2500_; uint8_t v___x_2518_; 
v_kind_2497_ = lean_ctor_get(v_snd_2489_, 1);
v_name_2498_ = l_Lake_instDataKindDynlib;
v___x_2518_ = lean_name_eq(v_kind_2497_, v_name_2498_);
if (v___x_2518_ == 0)
{
uint8_t v___x_2519_; 
lean_inc(v_kind_2497_);
lean_del_object(v___x_2491_);
lean_dec(v_snd_2489_);
v___x_2519_ = l_Lean_Name_isAnonymous(v_kind_2497_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2520_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_2521_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2497_, v___x_2486_);
v___x_2522_ = lean_string_append(v___x_2520_, v___x_2521_);
lean_dec_ref(v___x_2521_);
v___x_2523_ = lean_string_append(v___x_2522_, v___x_2520_);
v___y_2500_ = v___x_2523_;
goto v___jp_2499_;
}
else
{
lean_object* v___x_2524_; 
lean_dec(v_kind_2497_);
v___x_2524_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_2500_ = v___x_2524_;
goto v___jp_2499_;
}
}
else
{
lean_object* v___x_2526_; 
lean_del_object(v___x_2495_);
lean_dec_ref(v_self_2478_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 1, v_a_2493_);
lean_ctor_set(v___x_2491_, 0, v_snd_2489_);
v___x_2526_ = v___x_2491_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_snd_2489_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v_a_2493_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
v___jp_2499_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
v___x_2501_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_2502_ = l_Lake_PartialBuildKey_toString(v_self_2478_);
v___x_2503_ = lean_string_append(v___x_2501_, v___x_2502_);
lean_dec_ref(v___x_2502_);
v___x_2504_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_2505_ = lean_string_append(v___x_2503_, v___x_2504_);
v___x_2506_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0);
v___x_2507_ = lean_string_append(v___x_2505_, v___x_2506_);
v___x_2508_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_2509_ = lean_string_append(v___x_2507_, v___x_2508_);
v___x_2510_ = lean_string_append(v___x_2509_, v___y_2500_);
lean_dec_ref(v___y_2500_);
v___x_2511_ = 3;
v___x_2512_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2512_, 0, v___x_2510_);
lean_ctor_set_uint8(v___x_2512_, sizeof(void*)*1, v___x_2511_);
v___x_2513_ = lean_array_get_size(v_a_2493_);
v___x_2514_ = lean_array_push(v_a_2493_, v___x_2512_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set_tag(v___x_2495_, 1);
lean_ctor_set(v___x_2495_, 1, v___x_2514_);
lean_ctor_set(v___x_2495_, 0, v___x_2513_);
v___x_2516_ = v___x_2495_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v___x_2514_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec_ref(v_self_2478_);
v_a_2532_ = lean_ctor_get(v___x_2487_, 0);
v_a_2533_ = lean_ctor_get(v___x_2487_, 1);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2487_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_inc(v_a_2532_);
lean_dec(v___x_2487_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2532_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* v_defaultPkg_2541_, lean_object* v_self_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_2541_, v_self_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec(v_a_2544_);
return v_res_2550_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2553_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0));
v___x_2554_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3);
v___x_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
lean_ctor_set(v___x_2555_, 1, v___x_2553_);
return v___x_2555_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5(void){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object* v___x_2557_, lean_object* v_as_2558_, size_t v_i_2559_, size_t v_stop_2560_, lean_object* v_b_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
uint8_t v___x_2569_; 
v___x_2569_ = lean_usize_dec_eq(v_i_2559_, v_stop_2560_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = lean_array_uget_borrowed(v_as_2558_, v_i_2559_);
lean_inc_ref(v___y_2562_);
lean_inc(v___x_2570_);
lean_inc_ref(v___x_2557_);
v___x_2571_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_2557_, v___x_2570_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v_a_2573_; lean_object* v___x_2574_; size_t v___x_2575_; size_t v___x_2576_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
v_a_2573_ = lean_ctor_get(v___x_2571_, 1);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2571_, 2);
v___x_2574_ = lean_array_push(v_b_2561_, v_a_2572_);
v___x_2575_ = ((size_t)1ULL);
v___x_2576_ = lean_usize_add(v_i_2559_, v___x_2575_);
v_i_2559_ = v___x_2576_;
v_b_2561_ = v___x_2574_;
v___y_2567_ = v_a_2573_;
goto _start;
}
else
{
lean_object* v_a_2578_; lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec_ref(v___y_2562_);
lean_dec_ref(v_b_2561_);
lean_dec_ref(v___x_2557_);
v_a_2578_ = lean_ctor_get(v___x_2571_, 0);
v_a_2579_ = lean_ctor_get(v___x_2571_, 1);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2571_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_inc(v_a_2578_);
lean_dec(v___x_2571_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2578_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
else
{
lean_object* v___x_2587_; 
lean_dec_ref(v___y_2562_);
lean_dec_ref(v___x_2557_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v_b_2561_);
lean_ctor_set(v___x_2587_, 1, v___y_2567_);
return v___x_2587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* v___x_2588_, lean_object* v_as_2589_, lean_object* v_i_2590_, lean_object* v_stop_2591_, lean_object* v_b_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
size_t v_i_boxed_2600_; size_t v_stop_boxed_2601_; lean_object* v_res_2602_; 
v_i_boxed_2600_ = lean_unbox_usize(v_i_2590_);
lean_dec(v_i_2590_);
v_stop_boxed_2601_ = lean_unbox_usize(v_stop_2591_);
lean_dec(v_stop_2591_);
v_res_2602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_2588_, v_as_2589_, v_i_boxed_2600_, v_stop_boxed_2601_, v_b_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v_as_2589_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(lean_object* v_as_2603_, size_t v_i_2604_, size_t v_stop_2605_, lean_object* v_b_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
uint8_t v___x_2614_; 
v___x_2614_ = lean_usize_dec_eq(v_i_2604_, v_stop_2605_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v_pkg_2616_; lean_object* v_name_2617_; lean_object* v_keyName_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2615_ = lean_array_uget_borrowed(v_as_2603_, v_i_2604_);
v_pkg_2616_ = lean_ctor_get(v___x_2615_, 0);
v_name_2617_ = lean_ctor_get(v___x_2615_, 1);
v_keyName_2618_ = lean_ctor_get(v_pkg_2616_, 2);
v___x_2619_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_2617_);
lean_inc(v_keyName_2618_);
v___x_2620_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2620_, 0, v_keyName_2618_);
lean_ctor_set(v___x_2620_, 1, v_name_2617_);
v___x_2621_ = l_Lake_ExternLib_keyword;
lean_inc(v___x_2615_);
v___x_2622_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2620_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
lean_ctor_set(v___x_2622_, 2, v___x_2615_);
lean_ctor_set(v___x_2622_, 3, v___x_2619_);
lean_inc_ref(v___y_2607_);
lean_inc_ref(v___y_2611_);
lean_inc(v___y_2610_);
lean_inc(v___y_2609_);
lean_inc(v___y_2608_);
v___x_2623_ = lean_apply_7(v___y_2607_, v___x_2622_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, lean_box(0));
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v_a_2625_; lean_object* v___x_2626_; size_t v___x_2627_; size_t v___x_2628_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
v_a_2625_ = lean_ctor_get(v___x_2623_, 1);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2623_, 2);
v___x_2626_ = lean_array_push(v_b_2606_, v_a_2624_);
v___x_2627_ = ((size_t)1ULL);
v___x_2628_ = lean_usize_add(v_i_2604_, v___x_2627_);
v_i_2604_ = v___x_2628_;
v_b_2606_ = v___x_2626_;
v___y_2612_ = v_a_2625_;
goto _start;
}
else
{
lean_object* v_a_2630_; lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec_ref(v___y_2607_);
lean_dec_ref(v_b_2606_);
v_a_2630_ = lean_ctor_get(v___x_2623_, 0);
v_a_2631_ = lean_ctor_get(v___x_2623_, 1);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2623_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_inc(v_a_2630_);
lean_dec(v___x_2623_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2630_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
else
{
lean_object* v___x_2639_; 
lean_dec_ref(v___y_2607_);
v___x_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2639_, 0, v_b_2606_);
lean_ctor_set(v___x_2639_, 1, v___y_2612_);
return v___x_2639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(lean_object* v_as_2640_, lean_object* v_i_2641_, lean_object* v_stop_2642_, lean_object* v_b_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
size_t v_i_boxed_2651_; size_t v_stop_boxed_2652_; lean_object* v_res_2653_; 
v_i_boxed_2651_ = lean_unbox_usize(v_i_2641_);
lean_dec(v_i_2641_);
v_stop_boxed_2652_ = lean_unbox_usize(v_stop_2642_);
lean_dec(v_stop_2642_);
v_res_2653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v_as_2640_, v_i_boxed_2651_, v_stop_boxed_2652_, v_b_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v_as_2640_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(lean_object* v___x_2654_, lean_object* v_as_2655_, size_t v_i_2656_, size_t v_stop_2657_, lean_object* v_b_2658_){
_start:
{
lean_object* v___y_2660_; uint8_t v___x_2664_; 
v___x_2664_ = lean_usize_dec_eq(v_i_2656_, v_stop_2657_);
if (v___x_2664_ == 0)
{
lean_object* v_toConfigDecl_2665_; lean_object* v_name_2666_; lean_object* v_kind_2667_; lean_object* v_config_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v_toConfigDecl_2665_ = lean_array_uget_borrowed(v_as_2655_, v_i_2656_);
v_name_2666_ = lean_ctor_get(v_toConfigDecl_2665_, 1);
v_kind_2667_ = lean_ctor_get(v_toConfigDecl_2665_, 2);
v_config_2668_ = lean_ctor_get(v_toConfigDecl_2665_, 3);
v___x_2669_ = l_Lake_ExternLib_keyword;
v___x_2670_ = lean_name_eq(v_kind_2667_, v___x_2669_);
if (v___x_2670_ == 0)
{
v___y_2660_ = v_b_2658_;
goto v___jp_2659_;
}
else
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_inc(v_config_2668_);
lean_inc(v_name_2666_);
lean_inc_ref(v___x_2654_);
v___x_2671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2654_);
lean_ctor_set(v___x_2671_, 1, v_name_2666_);
lean_ctor_set(v___x_2671_, 2, v_config_2668_);
v___x_2672_ = lean_array_push(v_b_2658_, v___x_2671_);
v___y_2660_ = v___x_2672_;
goto v___jp_2659_;
}
}
else
{
lean_dec_ref(v___x_2654_);
return v_b_2658_;
}
v___jp_2659_:
{
size_t v___x_2661_; size_t v___x_2662_; 
v___x_2661_ = ((size_t)1ULL);
v___x_2662_ = lean_usize_add(v_i_2656_, v___x_2661_);
v_i_2656_ = v___x_2662_;
v_b_2658_ = v___y_2660_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(lean_object* v___x_2673_, lean_object* v_as_2674_, lean_object* v_i_2675_, lean_object* v_stop_2676_, lean_object* v_b_2677_){
_start:
{
size_t v_i_boxed_2678_; size_t v_stop_boxed_2679_; lean_object* v_res_2680_; 
v_i_boxed_2678_ = lean_unbox_usize(v_i_2675_);
lean_dec(v_i_2675_);
v_stop_boxed_2679_ = lean_unbox_usize(v_stop_2676_);
lean_dec(v_stop_2676_);
v_res_2680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v___x_2673_, v_as_2674_, v_i_boxed_2678_, v_stop_boxed_2679_, v_b_2677_);
lean_dec_ref(v_as_2674_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(lean_object* v___x_2681_, lean_object* v_as_2682_, size_t v_i_2683_, size_t v_stop_2684_, lean_object* v_b_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
uint8_t v___x_2693_; 
v___x_2693_ = lean_usize_dec_eq(v_i_2683_, v_stop_2684_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = lean_array_uget_borrowed(v_as_2682_, v_i_2683_);
lean_inc_ref(v___y_2686_);
lean_inc(v___x_2694_);
lean_inc_ref(v___x_2681_);
v___x_2695_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v___x_2681_, v___x_2694_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v_a_2697_; lean_object* v___x_2698_; size_t v___x_2699_; size_t v___x_2700_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
v_a_2697_ = lean_ctor_get(v___x_2695_, 1);
lean_inc(v_a_2697_);
lean_dec_ref_known(v___x_2695_, 2);
v___x_2698_ = lean_array_push(v_b_2685_, v_a_2696_);
v___x_2699_ = ((size_t)1ULL);
v___x_2700_ = lean_usize_add(v_i_2683_, v___x_2699_);
v_i_2683_ = v___x_2700_;
v_b_2685_ = v___x_2698_;
v___y_2691_ = v_a_2697_;
goto _start;
}
else
{
lean_object* v_a_2702_; lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec_ref(v___y_2686_);
lean_dec_ref(v_b_2685_);
lean_dec_ref(v___x_2681_);
v_a_2702_ = lean_ctor_get(v___x_2695_, 0);
v_a_2703_ = lean_ctor_get(v___x_2695_, 1);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2695_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_inc(v_a_2702_);
lean_dec(v___x_2695_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2702_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
else
{
lean_object* v___x_2711_; 
lean_dec_ref(v___y_2686_);
lean_dec_ref(v___x_2681_);
v___x_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2711_, 0, v_b_2685_);
lean_ctor_set(v___x_2711_, 1, v___y_2691_);
return v___x_2711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object* v___x_2712_, lean_object* v_as_2713_, lean_object* v_i_2714_, lean_object* v_stop_2715_, lean_object* v_b_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
size_t v_i_boxed_2724_; size_t v_stop_boxed_2725_; lean_object* v_res_2726_; 
v_i_boxed_2724_ = lean_unbox_usize(v_i_2714_);
lean_dec(v_i_2714_);
v_stop_boxed_2725_ = lean_unbox_usize(v_stop_2715_);
lean_dec(v_stop_2715_);
v_res_2726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v___x_2712_, v_as_2713_, v_i_boxed_2724_, v_stop_boxed_2725_, v_b_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v_as_2713_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(lean_object* v_as_2727_, size_t v_i_2728_, size_t v_stop_2729_, lean_object* v_b_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_a_2739_; lean_object* v_a_2740_; uint8_t v___x_2744_; 
v___x_2744_ = lean_usize_dec_eq(v_i_2728_, v_stop_2729_);
if (v___x_2744_ == 0)
{
lean_object* v_fst_2745_; lean_object* v_snd_2746_; lean_object* v___x_2747_; lean_object* v_lib_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2785_; 
v_fst_2745_ = lean_ctor_get(v_b_2730_, 0);
v_snd_2746_ = lean_ctor_get(v_b_2730_, 1);
v___x_2747_ = lean_array_uget(v_as_2727_, v_i_2728_);
v_lib_2748_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; 
v_unused_2786_ = lean_ctor_get(v___x_2747_, 1);
lean_dec(v_unused_2786_);
v___x_2750_ = v___x_2747_;
v_isShared_2751_ = v_isSharedCheck_2785_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_lib_2748_);
lean_dec(v___x_2747_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2785_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v_pkg_2752_; lean_object* v_name_2753_; uint8_t v___x_2754_; 
v_pkg_2752_ = lean_ctor_get(v_lib_2748_, 0);
v_name_2753_ = lean_ctor_get(v_lib_2748_, 1);
lean_inc(v_name_2753_);
v___x_2754_ = l_Lean_NameSet_contains(v_fst_2745_, v_name_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2782_; 
lean_inc(v_snd_2746_);
lean_inc(v_fst_2745_);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_b_2730_);
if (v_isSharedCheck_2782_ == 0)
{
lean_object* v_unused_2783_; lean_object* v_unused_2784_; 
v_unused_2783_ = lean_ctor_get(v_b_2730_, 1);
lean_dec(v_unused_2783_);
v_unused_2784_ = lean_ctor_get(v_b_2730_, 0);
lean_dec(v_unused_2784_);
v___x_2756_ = v_b_2730_;
v_isShared_2757_ = v_isSharedCheck_2782_;
goto v_resetjp_2755_;
}
else
{
lean_dec(v_b_2730_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2782_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v_keyName_2758_; lean_object* v___x_2759_; lean_object* v___x_2761_; 
v_keyName_2758_ = lean_ctor_get(v_pkg_2752_, 2);
v___x_2759_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_2753_);
lean_inc(v_keyName_2758_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set_tag(v___x_2750_, 3);
lean_ctor_set(v___x_2750_, 1, v_name_2753_);
lean_ctor_set(v___x_2750_, 0, v_keyName_2758_);
v___x_2761_ = v___x_2750_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_keyName_2758_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v_name_2753_);
v___x_2761_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2762_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2763_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
lean_ctor_set(v___x_2763_, 2, v_lib_2748_);
lean_ctor_set(v___x_2763_, 3, v___x_2759_);
lean_inc_ref(v___y_2731_);
lean_inc_ref(v___y_2735_);
lean_inc(v___y_2734_);
lean_inc(v___y_2733_);
lean_inc(v___y_2732_);
v___x_2764_ = lean_apply_7(v___y_2731_, v___x_2763_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, lean_box(0));
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v_a_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
v_a_2766_ = lean_ctor_get(v___x_2764_, 1);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2764_, 2);
v___x_2767_ = lean_array_push(v_snd_2746_, v_a_2765_);
v___x_2768_ = l_Lean_NameSet_insert(v_fst_2745_, v_name_2753_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 1, v___x_2767_);
lean_ctor_set(v___x_2756_, 0, v___x_2768_);
v___x_2770_ = v___x_2756_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v___x_2767_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
v_a_2739_ = v___x_2770_;
v_a_2740_ = v_a_2766_;
goto v___jp_2738_;
}
}
else
{
lean_object* v_a_2772_; lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_del_object(v___x_2756_);
lean_dec(v_name_2753_);
lean_dec(v_snd_2746_);
lean_dec(v_fst_2745_);
lean_dec_ref(v___y_2731_);
v_a_2772_ = lean_ctor_get(v___x_2764_, 0);
v_a_2773_ = lean_ctor_get(v___x_2764_, 1);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2764_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_inc(v_a_2772_);
lean_dec(v___x_2764_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2772_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
}
else
{
lean_dec(v_name_2753_);
lean_del_object(v___x_2750_);
lean_dec_ref(v_lib_2748_);
v_a_2739_ = v_b_2730_;
v_a_2740_ = v___y_2736_;
goto v___jp_2738_;
}
}
}
else
{
lean_object* v___x_2787_; 
lean_dec_ref(v___y_2731_);
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v_b_2730_);
lean_ctor_set(v___x_2787_, 1, v___y_2736_);
return v___x_2787_;
}
v___jp_2738_:
{
size_t v___x_2741_; size_t v___x_2742_; 
v___x_2741_ = ((size_t)1ULL);
v___x_2742_ = lean_usize_add(v_i_2728_, v___x_2741_);
v_i_2728_ = v___x_2742_;
v_b_2730_ = v_a_2739_;
v___y_2736_ = v_a_2740_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object* v_as_2788_, lean_object* v_i_2789_, lean_object* v_stop_2790_, lean_object* v_b_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
size_t v_i_boxed_2799_; size_t v_stop_boxed_2800_; lean_object* v_res_2801_; 
v_i_boxed_2799_ = lean_unbox_usize(v_i_2789_);
lean_dec(v_i_2789_);
v_stop_boxed_2800_ = lean_unbox_usize(v_stop_2790_);
lean_dec(v_stop_2790_);
v_res_2801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_as_2788_, v_i_boxed_2799_, v_stop_boxed_2800_, v_b_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v_as_2788_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object* v_self_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v_toHashSet_2804_; lean_object* v_toArray_2805_; lean_object* v___y_2807_; uint8_t v___x_2810_; 
v_toHashSet_2804_ = lean_ctor_get(v_self_2802_, 0);
v_toArray_2805_ = lean_ctor_get(v_self_2802_, 1);
v___x_2810_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_2804_, v_a_2803_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; lean_object* v___y_2813_; lean_object* v_i_2814_; lean_object* v___y_2820_; lean_object* v___y_2830_; lean_object* v_i_2831_; lean_object* v___x_2846_; 
lean_inc_ref(v_toArray_2805_);
lean_inc_ref(v_toHashSet_2804_);
lean_dec_ref(v_self_2802_);
v___x_2811_ = lean_box(0);
v___x_2846_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(v_toHashSet_2804_, v_a_2803_);
switch(lean_obj_tag(v___x_2846_))
{
case 0:
{
lean_dec_ref_known(v___x_2846_, 3);
v___y_2807_ = v_toHashSet_2804_;
goto v___jp_2806_;
}
case 1:
{
lean_object* v_index_2847_; lean_object* v_size_2848_; lean_object* v_keyArray_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v_index_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_index_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v_size_2848_ = lean_ctor_get(v_toHashSet_2804_, 0);
v_keyArray_2849_ = lean_ctor_get(v_toHashSet_2804_, 1);
v___x_2850_ = lean_unsigned_to_nat(1u);
v___x_2851_ = lean_nat_add(v_size_2848_, v___x_2850_);
v___x_2852_ = lean_array_get_size(v_keyArray_2849_);
v___x_2853_ = lean_nat_dec_lt(v___x_2851_, v___x_2852_);
if (v___x_2853_ == 0)
{
lean_dec(v___x_2851_);
lean_dec(v_index_2847_);
goto v___jp_2836_;
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2854_ = lean_unsigned_to_nat(4u);
v___x_2855_ = lean_nat_mul(v___x_2851_, v___x_2854_);
v___x_2856_ = lean_unsigned_to_nat(3u);
v___x_2857_ = lean_nat_mul(v___x_2852_, v___x_2856_);
v___x_2858_ = lean_nat_dec_le(v___x_2855_, v___x_2857_);
lean_dec(v___x_2857_);
lean_dec(v___x_2855_);
if (v___x_2858_ == 0)
{
lean_dec(v___x_2851_);
lean_dec(v_index_2847_);
goto v___jp_2836_;
}
else
{
lean_object* v___x_2859_; 
lean_inc_ref(v_a_2803_);
v___x_2859_ = l_Std_DHashMap_Raw_setEntry___redArg(v_toHashSet_2804_, v___x_2851_, v_index_2847_, v_a_2803_, v___x_2811_);
lean_dec(v_index_2847_);
v___y_2807_ = v___x_2859_;
goto v___jp_2806_;
}
}
}
default: 
{
lean_object* v_size_2860_; lean_object* v_keyArray_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
v_size_2860_ = lean_ctor_get(v_toHashSet_2804_, 0);
v_keyArray_2861_ = lean_ctor_get(v_toHashSet_2804_, 1);
v___x_2862_ = lean_unsigned_to_nat(1u);
v___x_2863_ = lean_nat_add(v_size_2860_, v___x_2862_);
v___x_2864_ = lean_array_get_size(v_keyArray_2861_);
v___x_2865_ = lean_nat_dec_lt(v___x_2863_, v___x_2864_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; 
lean_dec(v___x_2863_);
v___x_2866_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(v_toHashSet_2804_);
lean_dec_ref(v_toHashSet_2804_);
v___y_2820_ = v___x_2866_;
goto v___jp_2819_;
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2867_ = lean_unsigned_to_nat(4u);
v___x_2868_ = lean_nat_mul(v___x_2863_, v___x_2867_);
lean_dec(v___x_2863_);
v___x_2869_ = lean_unsigned_to_nat(3u);
v___x_2870_ = lean_nat_mul(v___x_2864_, v___x_2869_);
v___x_2871_ = lean_nat_dec_le(v___x_2868_, v___x_2870_);
lean_dec(v___x_2870_);
lean_dec(v___x_2868_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(v_toHashSet_2804_);
lean_dec_ref(v_toHashSet_2804_);
v___y_2820_ = v___x_2872_;
goto v___jp_2819_;
}
else
{
v___y_2820_ = v_toHashSet_2804_;
goto v___jp_2819_;
}
}
}
}
v___jp_2812_:
{
lean_object* v_size_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v_size_2815_ = lean_ctor_get(v___y_2813_, 0);
v___x_2816_ = lean_unsigned_to_nat(1u);
v___x_2817_ = lean_nat_add(v_size_2815_, v___x_2816_);
lean_inc_ref(v_a_2803_);
v___x_2818_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2813_, v___x_2817_, v_i_2814_, v_a_2803_, v___x_2811_);
lean_dec(v_i_2814_);
v___y_2807_ = v___x_2818_;
goto v___jp_2806_;
}
v___jp_2819_:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(v___y_2820_, v_a_2803_);
switch(lean_obj_tag(v___x_2821_))
{
case 0:
{
lean_object* v_index_2822_; lean_object* v_size_2823_; lean_object* v___x_2824_; 
v_index_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_index_2822_);
lean_dec_ref_known(v___x_2821_, 3);
v_size_2823_ = lean_ctor_get(v___y_2820_, 0);
lean_inc(v_size_2823_);
lean_inc_ref(v_a_2803_);
v___x_2824_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2820_, v_size_2823_, v_index_2822_, v_a_2803_, v___x_2811_);
lean_dec(v_index_2822_);
v___y_2807_ = v___x_2824_;
goto v___jp_2806_;
}
case 1:
{
lean_object* v_index_2825_; 
v_index_2825_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_index_2825_);
lean_dec_ref_known(v___x_2821_, 1);
v___y_2813_ = v___y_2820_;
v_i_2814_ = v_index_2825_;
goto v___jp_2812_;
}
default: 
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_unsigned_to_nat(0u);
v___x_2827_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2820_, v___x_2826_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_index_2828_; 
v_index_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_index_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v___y_2813_ = v___y_2820_;
v_i_2814_ = v_index_2828_;
goto v___jp_2812_;
}
else
{
v___y_2807_ = v___y_2820_;
goto v___jp_2806_;
}
}
}
}
v___jp_2829_:
{
lean_object* v_size_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
v_size_2832_ = lean_ctor_get(v___y_2830_, 0);
v___x_2833_ = lean_unsigned_to_nat(1u);
v___x_2834_ = lean_nat_add(v_size_2832_, v___x_2833_);
lean_inc_ref(v_a_2803_);
v___x_2835_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2830_, v___x_2834_, v_i_2831_, v_a_2803_, v___x_2811_);
lean_dec(v_i_2831_);
v___y_2807_ = v___x_2835_;
goto v___jp_2806_;
}
v___jp_2836_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__3___redArg(v_toHashSet_2804_);
lean_dec_ref(v_toHashSet_2804_);
v___x_2838_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___redArg(v___x_2837_, v_a_2803_);
switch(lean_obj_tag(v___x_2838_))
{
case 0:
{
lean_object* v_index_2839_; lean_object* v_size_2840_; lean_object* v___x_2841_; 
v_index_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_index_2839_);
lean_dec_ref_known(v___x_2838_, 3);
v_size_2840_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_size_2840_);
lean_inc_ref(v_a_2803_);
v___x_2841_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2837_, v_size_2840_, v_index_2839_, v_a_2803_, v___x_2811_);
lean_dec(v_index_2839_);
v___y_2807_ = v___x_2841_;
goto v___jp_2806_;
}
case 1:
{
lean_object* v_index_2842_; 
v_index_2842_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_index_2842_);
lean_dec_ref_known(v___x_2838_, 1);
v___y_2830_ = v___x_2837_;
v_i_2831_ = v_index_2842_;
goto v___jp_2829_;
}
default: 
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_unsigned_to_nat(0u);
v___x_2844_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2837_, v___x_2843_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_index_2845_; 
v_index_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_index_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v___y_2830_ = v___x_2837_;
v_i_2831_ = v_index_2845_;
goto v___jp_2829_;
}
else
{
v___y_2807_ = v___x_2837_;
goto v___jp_2806_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_2803_);
return v_self_2802_;
}
v___jp_2806_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = lean_array_push(v_toArray_2805_, v_a_2803_);
v___x_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___y_2807_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
return v___x_2809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object* v_as_2873_, size_t v_i_2874_, size_t v_stop_2875_, lean_object* v_b_2876_){
_start:
{
uint8_t v___x_2877_; 
v___x_2877_ = lean_usize_dec_eq(v_i_2874_, v_stop_2875_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; lean_object* v___x_2879_; size_t v___x_2880_; size_t v___x_2881_; 
v___x_2878_ = lean_array_uget_borrowed(v_as_2873_, v_i_2874_);
lean_inc(v___x_2878_);
v___x_2879_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_2876_, v___x_2878_);
v___x_2880_ = ((size_t)1ULL);
v___x_2881_ = lean_usize_add(v_i_2874_, v___x_2880_);
v_i_2874_ = v___x_2881_;
v_b_2876_ = v___x_2879_;
goto _start;
}
else
{
return v_b_2876_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object* v_as_2883_, lean_object* v_i_2884_, lean_object* v_stop_2885_, lean_object* v_b_2886_){
_start:
{
size_t v_i_boxed_2887_; size_t v_stop_boxed_2888_; lean_object* v_res_2889_; 
v_i_boxed_2887_ = lean_unbox_usize(v_i_2884_);
lean_dec(v_i_2884_);
v_stop_boxed_2888_ = lean_unbox_usize(v_stop_2885_);
lean_dec(v_stop_2885_);
v_res_2889_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_2883_, v_i_boxed_2887_, v_stop_boxed_2888_, v_b_2886_);
lean_dec_ref(v_as_2883_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object* v_self_2890_, lean_object* v_arr_2891_){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; 
v___x_2892_ = lean_unsigned_to_nat(0u);
v___x_2893_ = lean_array_get_size(v_arr_2891_);
v___x_2894_ = lean_nat_dec_lt(v___x_2892_, v___x_2893_);
if (v___x_2894_ == 0)
{
return v_self_2890_;
}
else
{
uint8_t v___x_2895_; 
v___x_2895_ = lean_nat_dec_le(v___x_2893_, v___x_2893_);
if (v___x_2895_ == 0)
{
if (v___x_2894_ == 0)
{
return v_self_2890_;
}
else
{
size_t v___x_2896_; size_t v___x_2897_; lean_object* v___x_2898_; 
v___x_2896_ = ((size_t)0ULL);
v___x_2897_ = lean_usize_of_nat(v___x_2893_);
v___x_2898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2891_, v___x_2896_, v___x_2897_, v_self_2890_);
return v___x_2898_;
}
}
else
{
size_t v___x_2899_; size_t v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = ((size_t)0ULL);
v___x_2900_ = lean_usize_of_nat(v___x_2893_);
v___x_2901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2891_, v___x_2899_, v___x_2900_, v_self_2890_);
return v___x_2901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(lean_object* v_self_2902_, lean_object* v_arr_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_self_2902_, v_arr_2903_);
lean_dec_ref(v_arr_2903_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(lean_object* v_as_2905_, size_t v_i_2906_, size_t v_stop_2907_, lean_object* v_b_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
uint8_t v___x_2916_; 
v___x_2916_ = lean_usize_dec_eq(v_i_2906_, v_stop_2907_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v_lib_2918_; lean_object* v_pkg_2919_; lean_object* v_name_2920_; lean_object* v_keyName_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2917_ = lean_array_uget_borrowed(v_as_2905_, v_i_2906_);
v_lib_2918_ = lean_ctor_get(v___x_2917_, 0);
v_pkg_2919_ = lean_ctor_get(v_lib_2918_, 0);
v_name_2920_ = lean_ctor_get(v___x_2917_, 1);
v_keyName_2921_ = lean_ctor_get(v_pkg_2919_, 2);
v___x_2922_ = l_Lake_Module_transImportsFacet;
lean_inc(v_name_2920_);
lean_inc(v_keyName_2921_);
v___x_2923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2923_, 0, v_keyName_2921_);
lean_ctor_set(v___x_2923_, 1, v_name_2920_);
v___x_2924_ = l_Lake_Module_keyword;
lean_inc(v___x_2917_);
v___x_2925_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2923_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
lean_ctor_set(v___x_2925_, 2, v___x_2917_);
lean_ctor_set(v___x_2925_, 3, v___x_2922_);
lean_inc_ref(v___y_2909_);
lean_inc_ref(v___y_2913_);
lean_inc(v___y_2912_);
lean_inc(v___y_2911_);
lean_inc(v___y_2910_);
v___x_2926_ = lean_apply_7(v___y_2909_, v___x_2925_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, lean_box(0));
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v_a_2928_; lean_object* v___x_2929_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
v_a_2928_ = lean_ctor_get(v___x_2926_, 1);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2926_, 2);
v___x_2929_ = l_Lake_Job_await___redArg(v_a_2927_, v_a_2928_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v_a_2931_; lean_object* v___x_2932_; size_t v___x_2933_; size_t v___x_2934_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
v_a_2931_ = lean_ctor_get(v___x_2929_, 1);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2929_, 2);
v___x_2932_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_b_2908_, v_a_2930_);
lean_dec(v_a_2930_);
v___x_2933_ = ((size_t)1ULL);
v___x_2934_ = lean_usize_add(v_i_2906_, v___x_2933_);
v_i_2906_ = v___x_2934_;
v_b_2908_ = v___x_2932_;
v___y_2914_ = v_a_2931_;
goto _start;
}
else
{
lean_object* v_a_2936_; lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec_ref(v___y_2909_);
lean_dec_ref(v_b_2908_);
v_a_2936_ = lean_ctor_get(v___x_2929_, 0);
v_a_2937_ = lean_ctor_get(v___x_2929_, 1);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2929_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_inc(v_a_2936_);
lean_dec(v___x_2929_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2936_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_dec_ref(v___y_2909_);
lean_dec_ref(v_b_2908_);
v_a_2945_ = lean_ctor_get(v___x_2926_, 0);
v_a_2946_ = lean_ctor_get(v___x_2926_, 1);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2926_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_inc(v_a_2945_);
lean_dec(v___x_2926_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2945_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
else
{
lean_object* v___x_2954_; 
lean_dec_ref(v___y_2909_);
v___x_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2954_, 0, v_b_2908_);
lean_ctor_set(v___x_2954_, 1, v___y_2914_);
return v___x_2954_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object* v_as_2955_, lean_object* v_i_2956_, lean_object* v_stop_2957_, lean_object* v_b_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
size_t v_i_boxed_2966_; size_t v_stop_boxed_2967_; lean_object* v_res_2968_; 
v_i_boxed_2966_ = lean_unbox_usize(v_i_2956_);
lean_dec(v_i_2956_);
v_stop_boxed_2967_ = lean_unbox_usize(v_stop_2957_);
lean_dec(v_stop_2957_);
v_res_2968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_as_2955_, v_i_boxed_2966_, v_stop_boxed_2967_, v_b_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec_ref(v_as_2955_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(lean_object* v_as_2969_, size_t v_i_2970_, size_t v_stop_2971_, lean_object* v_b_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
uint8_t v___x_2980_; 
v___x_2980_ = lean_usize_dec_eq(v_i_2970_, v_stop_2971_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2981_; lean_object* v_lib_2982_; lean_object* v_config_2983_; lean_object* v_nativeFacets_2984_; uint8_t v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; size_t v_sz_2988_; size_t v___x_2989_; lean_object* v___x_2990_; 
v___x_2981_ = lean_array_uget_borrowed(v_as_2969_, v_i_2970_);
v_lib_2982_ = lean_ctor_get(v___x_2981_, 0);
v_config_2983_ = lean_ctor_get(v_lib_2982_, 2);
v_nativeFacets_2984_ = lean_ctor_get(v_config_2983_, 8);
v___x_2985_ = 1;
v___x_2986_ = lean_box(v___x_2985_);
lean_inc_ref(v_nativeFacets_2984_);
v___x_2987_ = lean_apply_1(v_nativeFacets_2984_, v___x_2986_);
v_sz_2988_ = lean_array_size(v___x_2987_);
v___x_2989_ = ((size_t)0ULL);
lean_inc_ref(v___y_2973_);
lean_inc(v___x_2981_);
v___x_2990_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2981_, v_sz_2988_, v___x_2989_, v___x_2987_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v_a_2992_; lean_object* v___x_2993_; size_t v___x_2994_; size_t v___x_2995_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
v_a_2992_ = lean_ctor_get(v___x_2990_, 1);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2990_, 2);
v___x_2993_ = l_Array_append___redArg(v_b_2972_, v_a_2991_);
lean_dec(v_a_2991_);
v___x_2994_ = ((size_t)1ULL);
v___x_2995_ = lean_usize_add(v_i_2970_, v___x_2994_);
v_i_2970_ = v___x_2995_;
v_b_2972_ = v___x_2993_;
v___y_2978_ = v_a_2992_;
goto _start;
}
else
{
lean_dec_ref(v___y_2973_);
lean_dec_ref(v_b_2972_);
return v___x_2990_;
}
}
else
{
lean_object* v___x_2997_; 
lean_dec_ref(v___y_2973_);
v___x_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2997_, 0, v_b_2972_);
lean_ctor_set(v___x_2997_, 1, v___y_2978_);
return v___x_2997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object* v_as_2998_, lean_object* v_i_2999_, lean_object* v_stop_3000_, lean_object* v_b_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
size_t v_i_boxed_3009_; size_t v_stop_boxed_3010_; lean_object* v_res_3011_; 
v_i_boxed_3009_ = lean_unbox_usize(v_i_2999_);
lean_dec(v_i_2999_);
v_stop_boxed_3010_ = lean_unbox_usize(v_stop_3000_);
lean_dec(v_stop_3000_);
v_res_3011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_as_2998_, v_i_boxed_3009_, v_stop_boxed_3010_, v_b_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v_as_2998_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(lean_object* v___x_3012_, lean_object* v___x_3013_, lean_object* v_self_3014_, lean_object* v_dir_3015_, lean_object* v_targetDecls_3016_, lean_object* v_pkg_3017_, lean_object* v_name_3018_, lean_object* v_config_3019_, lean_object* v_config_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v_a_3036_; lean_object* v_a_3037_; lean_object* v_a_3055_; lean_object* v_a_3056_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v_a_3101_; lean_object* v_a_3102_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v_snd_3138_; lean_object* v_a_3139_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v_a_3178_; lean_object* v_a_3179_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___x_3217_; 
lean_inc_ref(v___y_3021_);
lean_inc_ref(v___y_3025_);
lean_inc(v___y_3024_);
lean_inc(v___y_3023_);
lean_inc(v___x_3013_);
v___x_3217_ = lean_apply_7(v___y_3021_, v___x_3012_, v___x_3013_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, lean_box(0));
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v_a_3219_; lean_object* v___x_3220_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
v_a_3219_ = lean_ctor_get(v___x_3217_, 1);
lean_inc(v_a_3219_);
lean_dec_ref_known(v___x_3217_, 2);
v___x_3220_ = l_Lake_Job_await___redArg(v_a_3218_, v_a_3219_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v_a_3222_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v_a_3233_; lean_object* v_a_3234_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v_a_3268_; lean_object* v_a_3269_; lean_object* v___y_3294_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; uint8_t v___x_3309_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
v_a_3222_ = lean_ctor_get(v___x_3220_, 1);
lean_inc(v_a_3222_);
lean_dec_ref_known(v___x_3220_, 2);
v___x_3306_ = lean_unsigned_to_nat(0u);
v___x_3307_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_3308_ = lean_array_get_size(v_a_3221_);
v___x_3309_ = lean_nat_dec_lt(v___x_3306_, v___x_3308_);
if (v___x_3309_ == 0)
{
v_a_3268_ = v___x_3307_;
v_a_3269_ = v_a_3222_;
goto v___jp_3267_;
}
else
{
uint8_t v___x_3310_; 
v___x_3310_ = lean_nat_dec_le(v___x_3308_, v___x_3308_);
if (v___x_3310_ == 0)
{
if (v___x_3309_ == 0)
{
v_a_3268_ = v___x_3307_;
v_a_3269_ = v_a_3222_;
goto v___jp_3267_;
}
else
{
size_t v___x_3311_; size_t v___x_3312_; lean_object* v___x_3313_; 
v___x_3311_ = ((size_t)0ULL);
v___x_3312_ = lean_usize_of_nat(v___x_3308_);
lean_inc_ref(v___y_3021_);
v___x_3313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3221_, v___x_3311_, v___x_3312_, v___x_3307_, v___y_3021_, v___x_3013_, v___y_3023_, v___y_3024_, v___y_3025_, v_a_3222_);
v___y_3294_ = v___x_3313_;
goto v___jp_3293_;
}
}
else
{
size_t v___x_3314_; size_t v___x_3315_; lean_object* v___x_3316_; 
v___x_3314_ = ((size_t)0ULL);
v___x_3315_ = lean_usize_of_nat(v___x_3308_);
lean_inc_ref(v___y_3021_);
v___x_3316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3221_, v___x_3314_, v___x_3315_, v___x_3307_, v___y_3021_, v___x_3013_, v___y_3023_, v___y_3024_, v___y_3025_, v_a_3222_);
v___y_3294_ = v___x_3316_;
goto v___jp_3293_;
}
}
v___jp_3223_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; uint8_t v___x_3237_; 
v___x_3235_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
v___x_3236_ = lean_array_get_size(v_a_3221_);
v___x_3237_ = lean_nat_dec_lt(v___y_3232_, v___x_3236_);
if (v___x_3237_ == 0)
{
lean_dec(v_a_3221_);
v___y_3168_ = v___y_3224_;
v___y_3169_ = v___y_3225_;
v___y_3170_ = v___y_3226_;
v___y_3171_ = v___y_3227_;
v___y_3172_ = v_a_3233_;
v___y_3173_ = v___y_3228_;
v___y_3174_ = v___y_3229_;
v___y_3175_ = v___y_3230_;
v___y_3176_ = v___y_3231_;
v___y_3177_ = v___y_3232_;
v_a_3178_ = v___x_3235_;
v_a_3179_ = v_a_3234_;
goto v___jp_3167_;
}
else
{
uint8_t v___x_3238_; 
v___x_3238_ = lean_nat_dec_le(v___x_3236_, v___x_3236_);
if (v___x_3238_ == 0)
{
if (v___x_3237_ == 0)
{
lean_dec(v_a_3221_);
v___y_3168_ = v___y_3224_;
v___y_3169_ = v___y_3225_;
v___y_3170_ = v___y_3226_;
v___y_3171_ = v___y_3227_;
v___y_3172_ = v_a_3233_;
v___y_3173_ = v___y_3228_;
v___y_3174_ = v___y_3229_;
v___y_3175_ = v___y_3230_;
v___y_3176_ = v___y_3231_;
v___y_3177_ = v___y_3232_;
v_a_3178_ = v___x_3235_;
v_a_3179_ = v_a_3234_;
goto v___jp_3167_;
}
else
{
size_t v___x_3239_; size_t v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = ((size_t)0ULL);
v___x_3240_ = lean_usize_of_nat(v___x_3236_);
lean_inc_ref(v___y_3021_);
v___x_3241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3221_, v___x_3239_, v___x_3240_, v___x_3235_, v___y_3021_, v___x_3013_, v___y_3023_, v___y_3024_, v___y_3025_, v_a_3234_);
lean_dec(v_a_3221_);
v___y_3202_ = v___y_3224_;
v___y_3203_ = v___y_3225_;
v___y_3204_ = v___y_3226_;
v___y_3205_ = v___y_3227_;
v___y_3206_ = v_a_3233_;
v___y_3207_ = v___y_3228_;
v___y_3208_ = v___y_3229_;
v___y_3209_ = v___y_3230_;
v___y_3210_ = v___y_3231_;
v___y_3211_ = v___y_3232_;
v___y_3212_ = v___x_3241_;
goto v___jp_3201_;
}
}
else
{
size_t v___x_3242_; size_t v___x_3243_; lean_object* v___x_3244_; 
v___x_3242_ = ((size_t)0ULL);
v___x_3243_ = lean_usize_of_nat(v___x_3236_);
lean_inc_ref(v___y_3021_);
v___x_3244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3221_, v___x_3242_, v___x_3243_, v___x_3235_, v___y_3021_, v___x_3013_, v___y_3023_, v___y_3024_, v___y_3025_, v_a_3234_);
lean_dec(v_a_3221_);
v___y_3202_ = v___y_3224_;
v___y_3203_ = v___y_3225_;
v___y_3204_ = v___y_3226_;
v___y_3205_ = v___y_3227_;
v___y_3206_ = v_a_3233_;
v___y_3207_ = v___y_3228_;
v___y_3208_ = v___y_3229_;
v___y_3209_ = v___y_3230_;
v___y_3210_ = v___y_3231_;
v___y_3211_ = v___y_3232_;
v___y_3212_ = v___x_3244_;
goto v___jp_3201_;
}
}
}
v___jp_3245_:
{
if (lean_obj_tag(v___y_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v_a_3257_; 
v_a_3256_ = lean_ctor_get(v___y_3255_, 0);
lean_inc(v_a_3256_);
v_a_3257_ = lean_ctor_get(v___y_3255_, 1);
lean_inc(v_a_3257_);
lean_dec_ref_known(v___y_3255_, 2);
v___y_3224_ = v___y_3246_;
v___y_3225_ = v___y_3247_;
v___y_3226_ = v___y_3248_;
v___y_3227_ = v___y_3249_;
v___y_3228_ = v___y_3250_;
v___y_3229_ = v___y_3251_;
v___y_3230_ = v___y_3252_;
v___y_3231_ = v___y_3253_;
v___y_3232_ = v___y_3254_;
v_a_3233_ = v_a_3256_;
v_a_3234_ = v_a_3257_;
goto v___jp_3223_;
}
else
{
lean_object* v_a_3258_; lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec_ref(v___y_3252_);
lean_dec_ref(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec_ref(v___y_3246_);
lean_dec(v_a_3221_);
lean_dec_ref(v___y_3021_);
lean_dec(v_name_3018_);
lean_dec_ref(v_pkg_3017_);
lean_dec_ref(v_dir_3015_);
lean_dec_ref(v_self_3014_);
lean_dec(v___x_3013_);
v_a_3258_ = lean_ctor_get(v___y_3255_, 0);
v_a_3259_ = lean_ctor_get(v___y_3255_, 1);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___y_3255_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___y_3255_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_inc(v_a_3258_);
lean_dec(v___y_3255_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3258_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
v___jp_3267_:
{
lean_object* v_toLeanConfig_3270_; lean_object* v_toLeanConfig_3271_; lean_object* v_buildDir_3272_; lean_object* v_nativeLibDir_3273_; lean_object* v_moreLinkObjs_3274_; lean_object* v_moreLinkLibs_3275_; lean_object* v_moreLinkArgs_3276_; lean_object* v_weakLinkArgs_3277_; lean_object* v_moreLinkObjs_3278_; lean_object* v_moreLinkLibs_3279_; lean_object* v_moreLinkArgs_3280_; lean_object* v_weakLinkArgs_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v_toLeanConfig_3270_ = lean_ctor_get(v_config_3019_, 1);
lean_inc_ref(v_toLeanConfig_3270_);
v_toLeanConfig_3271_ = lean_ctor_get(v_config_3020_, 0);
v_buildDir_3272_ = lean_ctor_get(v_config_3019_, 5);
lean_inc_ref(v_buildDir_3272_);
v_nativeLibDir_3273_ = lean_ctor_get(v_config_3019_, 7);
lean_inc_ref(v_nativeLibDir_3273_);
lean_dec_ref(v_config_3019_);
v_moreLinkObjs_3274_ = lean_ctor_get(v_toLeanConfig_3270_, 6);
lean_inc_ref(v_moreLinkObjs_3274_);
v_moreLinkLibs_3275_ = lean_ctor_get(v_toLeanConfig_3270_, 7);
lean_inc_ref(v_moreLinkLibs_3275_);
v_moreLinkArgs_3276_ = lean_ctor_get(v_toLeanConfig_3270_, 8);
lean_inc_ref(v_moreLinkArgs_3276_);
v_weakLinkArgs_3277_ = lean_ctor_get(v_toLeanConfig_3270_, 9);
lean_inc_ref(v_weakLinkArgs_3277_);
lean_dec_ref(v_toLeanConfig_3270_);
v_moreLinkObjs_3278_ = lean_ctor_get(v_toLeanConfig_3271_, 6);
v_moreLinkLibs_3279_ = lean_ctor_get(v_toLeanConfig_3271_, 7);
v_moreLinkArgs_3280_ = lean_ctor_get(v_toLeanConfig_3271_, 8);
v_weakLinkArgs_3281_ = lean_ctor_get(v_toLeanConfig_3271_, 9);
v___x_3282_ = l_Array_append___redArg(v_moreLinkObjs_3274_, v_moreLinkObjs_3278_);
v___x_3283_ = lean_unsigned_to_nat(0u);
v___x_3284_ = lean_array_get_size(v___x_3282_);
v___x_3285_ = lean_nat_dec_lt(v___x_3283_, v___x_3284_);
if (v___x_3285_ == 0)
{
lean_dec_ref(v___x_3282_);
v___y_3224_ = v_nativeLibDir_3273_;
v___y_3225_ = v_weakLinkArgs_3281_;
v___y_3226_ = v_buildDir_3272_;
v___y_3227_ = v_weakLinkArgs_3277_;
v___y_3228_ = v_moreLinkLibs_3275_;
v___y_3229_ = v_moreLinkLibs_3279_;
v___y_3230_ = v_moreLinkArgs_3276_;
v___y_3231_ = v_moreLinkArgs_3280_;
v___y_3232_ = v___x_3283_;
v_a_3233_ = v_a_3268_;
v_a_3234_ = v_a_3269_;
goto v___jp_3223_;
}
else
{
uint8_t v___x_3286_; 
v___x_3286_ = lean_nat_dec_le(v___x_3284_, v___x_3284_);
if (v___x_3286_ == 0)
{
if (v___x_3285_ == 0)
{
lean_dec_ref(v___x_3282_);
v___y_3224_ = v_nativeLibDir_3273_;
v___y_3225_ = v_weakLinkArgs_3281_;
v___y_3226_ = v_buildDir_3272_;
v___y_3227_ = v_weakLinkArgs_3277_;
v___y_3228_ = v_moreLinkLibs_3275_;
v___y_3229_ = v_moreLinkLibs_3279_;
v___y_3230_ = v_moreLinkArgs_3276_;
v___y_3231_ = v_moreLinkArgs_3280_;
v___y_3232_ = v___x_3283_;
v_a_3233_ = v_a_3268_;
v_a_3234_ = v_a_3269_;
goto v___jp_3223_;
}
else
{
size_t v___x_3287_; size_t v___x_3288_; lean_object* v___x_3289_; 
v___x_3287_ = ((size_t)0ULL);
v___x_3288_ = lean_usize_of_nat(v___x_3284_);
lean_inc_ref(v___y_3021_);
lean_inc_ref(v_pkg_3017_);
v___x_3289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_3017_, v___x_3282_, v___x_3287_, v___x_3288_, v_a_3268_, v___y_3021_, v___x_3013_, v___y_3023_, v___y_3024_, v___y_3025_, v_a_3269_);
lean_dec_ref(v___x_3282_);
v___y_3246_ = v_nativeLibDir_3273_;
v___y_3247_ = v_weakLinkArgs_3281_;
v___y_3248_ = v_buildDir_3272_;
v___y_3249_ = v_weakLinkArgs_3277_;
v___y_3250_ = v_moreLinkLibs_3275_;
v___y_3251_ = v_moreLinkLibs_3279_;
v___y_3252_ = v_moreLinkArgs_3276_;
v___y_3253_ = v_moreLinkArgs_3280_;
v___y_3254_ = v___x_3283_;
v___y_3255_ = v___x_3289_;
goto v___jp_3245_;
}
}
else
{
size_t v___x_3290_; size_t v___x_3291_; lean_object* v___x_3292_; 
v___x_3290_ = ((size_t)0ULL);
v___x_3291_ = lean_usize_of_nat(v___x_3284_);
lean_inc_ref(v___y_3021_);
lean_inc_ref(v_pkg_3017_);
v___x_3292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_3017_, v___x_3282_, v___x_3290_, v___x_3291_, v_a_3268_, v___y_3021_, v___x_3013_, v___y_3023_, v___y_3024_, v___y_3025_, v_a_3269_);
lean_dec_ref(v___x_3282_);
v___y_3246_ = v_nativeLibDir_3273_;
v___y_3247_ = v_weakLinkArgs_3281_;
v___y_3248_ = v_buildDir_3272_;
v___y_3249_ = v_weakLinkArgs_3277_;
v___y_3250_ = v_moreLinkLibs_3275_;
v___y_3251_ = v_moreLinkLibs_3279_;
v___y_3252_ = v_moreLinkArgs_3276_;
v___y_3253_ = v_moreLinkArgs_3280_;
v___y_3254_ = v___x_3283_;
v___y_3255_ = v___x_3292_;
goto v___jp_3245_;
}
}
}
v___jp_3293_:
{
if (lean_obj_tag(v___y_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v_a_3296_; 
v_a_3295_ = lean_ctor_get(v___y_3294_, 0);
lean_inc(v_a_3295_);
v_a_3296_ = lean_ctor_get(v___y_3294_, 1);
lean_inc(v_a_3296_);
lean_dec_ref_known(v___y_3294_, 2);
v_a_3268_ = v_a_3295_;
v_a_3269_ = v_a_3296_;
goto v___jp_3267_;
}
else
{
lean_object* v_a_3297_; lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec(v_a_3221_);
lean_dec_ref(v___y_3021_);
lean_dec_ref(v_config_3019_);
lean_dec(v_name_3018_);
lean_dec_ref(v_pkg_3017_);
lean_dec_ref(v_dir_3015_);
lean_dec_ref(v_self_3014_);
lean_dec(v___x_3013_);
v_a_3297_ = lean_ctor_get(v___y_3294_, 0);
v_a_3298_ = lean_ctor_get(v___y_3294_, 1);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___y_3294_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___y_3294_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_inc(v_a_3297_);
lean_dec(v___y_3294_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3297_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec_ref(v___y_3021_);
lean_dec_ref(v_config_3019_);
lean_dec(v_name_3018_);
lean_dec_ref(v_pkg_3017_);
lean_dec_ref(v_dir_3015_);
lean_dec_ref(v_self_3014_);
lean_dec(v___x_3013_);
v_a_3317_ = lean_ctor_get(v___x_3220_, 0);
v_a_3318_ = lean_ctor_get(v___x_3220_, 1);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3220_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_inc(v_a_3317_);
lean_dec(v___x_3220_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3317_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
lean_dec_ref(v___y_3021_);
lean_dec_ref(v_config_3019_);
lean_dec(v_name_3018_);
lean_dec_ref(v_pkg_3017_);
lean_dec_ref(v_dir_3015_);
lean_dec_ref(v_self_3014_);
lean_dec(v___x_3013_);
v_a_3326_ = lean_ctor_get(v___x_3217_, 0);
v_a_3327_ = lean_ctor_get(v___x_3217_, 1);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3217_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_inc(v_a_3326_);
lean_dec(v___x_3217_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3326_);
lean_ctor_set(v_reuseFailAlloc_3333_, 1, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
v___jp_3028_:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; uint8_t v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; uint8_t v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
lean_inc_ref(v_self_3014_);
v___x_3038_ = l_Lake_LeanLib_libName(v_self_3014_);
v___x_3039_ = l_System_FilePath_normalize(v___y_3031_);
v___x_3040_ = l_Lake_joinRelative(v_dir_3015_, v___x_3039_);
v___x_3041_ = l_System_FilePath_normalize(v___y_3029_);
v___x_3042_ = l_Lake_joinRelative(v___x_3040_, v___x_3041_);
v___x_3043_ = 0;
v___x_3044_ = l_Lake_nameToSharedLib(v___x_3038_, v___x_3043_);
v___x_3045_ = l_Lake_joinRelative(v___x_3042_, v___x_3044_);
v___x_3046_ = l_Array_append___redArg(v___y_3032_, v___y_3030_);
v___x_3047_ = l_Array_append___redArg(v___y_3034_, v___y_3035_);
v___x_3048_ = l_Lake_LeanLib_isPlugin(v_self_3014_);
v___x_3049_ = l_System_Platform_isWindows;
v___x_3050_ = lean_box(0);
v___x_3051_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_3052_ = l_Lake_buildLeanSharedLib(v___x_3038_, v___x_3045_, v___y_3033_, v_a_3036_, v___x_3046_, v___x_3047_, v___x_3048_, v___x_3049_, v___x_3050_, v___y_3021_, v___x_3013_, v___y_3023_, v___y_3024_, v___y_3025_, v___x_3051_);
lean_dec(v___x_3013_);
lean_dec_ref(v___y_3033_);
v___x_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set(v___x_3053_, 1, v_a_3037_);
return v___x_3053_;
}
v___jp_3054_:
{
lean_object* v___x_3057_; 
v___x_3057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3057_, 0, v_a_3055_);
lean_ctor_set(v___x_3057_, 1, v_a_3056_);
return v___x_3057_;
}
v___jp_3058_:
{
if (lean_obj_tag(v___y_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v_a_3068_; 
v_a_3067_ = lean_ctor_get(v___y_3066_, 0);
lean_inc(v_a_3067_);
v_a_3068_ = lean_ctor_get(v___y_3066_, 1);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___y_3066_, 2);
v___y_3029_ = v___y_3059_;
v___y_3030_ = v___y_3060_;
v___y_3031_ = v___y_3061_;
v___y_3032_ = v___y_3062_;
v___y_3033_ = v___y_3063_;
v___y_3034_ = v___y_3064_;
v___y_3035_ = v___y_3065_;
v_a_3036_ = v_a_3067_;
v_a_3037_ = v_a_3068_;
goto v___jp_3028_;
}
else
{
lean_object* v_a_3069_; lean_object* v_a_3070_; 
lean_dec_ref(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec_ref(v___y_3059_);
lean_dec_ref(v___y_3021_);
lean_dec_ref(v_dir_3015_);
lean_dec_ref(v_self_3014_);
lean_dec(v___x_3013_);
v_a_3069_ = lean_ctor_get(v___y_3066_, 0);
lean_inc(v_a_3069_);
v_a_3070_ = lean_ctor_get(v___y_3066_, 1);
lean_inc(v_a_3070_);
lean_dec_ref_known(v___y_3066_, 2);
v_a_3055_ = v_a_3069_;
v_a_3056_ = v_a_3070_;
goto v___jp_3054_;
}
}
v___jp_3071_:
{
lean_object* v___x_3083_; uint8_t v___x_3084_; 
v___x_3083_ = lean_array_get_size(v___y_3082_);
v___x_3084_ = lean_nat_dec_lt(v___y_3081_, v___x_3083_);
if (v___x_3084_ == 0)
{
lean_dec_ref(v___y_3082_);
v___y_3029_ = v___y_3073_;
v___y_3030_ = v___y_3074_;
v___y_3031_ = v___y_3075_;
v___y_3032_ = v___y_3076_;
v___y_3033_ = v___y_3077_;
v___y_3034_ = v___y_3078_;
v___y_3035_ = v___y_3080_;
v_a_3036_ = v___y_3079_;
v_a_3037_ = v___y_3072_;
goto v___jp_3028_;
}
else
{
uint8_t v___x_3085_; 
v___x_3085_ = lean_nat_dec_le(v___x_3083_, v___x_3083_);
if (v___x_3085_ == 0)
{
if (v___x_3084_ == 0)
{
lean_dec_ref(v___y_3082_);
v___y_3029_ = v___y_3073_;
v___y_3030_ = v___y_3074_;
v___y_3031_ = v___y_3075_;
v___y_3032_ = v___y_3076_;
v___y_3033_ = v___y_3077_;
v___y_3034_ = v___y_3078_;
v___y_3035_ = v___y_3080_;
v_a_3036_ = v___y_3079_;
v_a_3037_ = v___y_3072_;
goto v___jp_3028_;
}
else
{
size_t v___x_3086_; size_t v___x_3087_; lean_object* v___x_3088_; 
v___x_3086_ = ((size_t)0ULL);
v___x_3087_ = lean_usize_of_nat(v___x_3083_);
lean_inc_ref(v___y_3021_);
v___x_3088_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_3082_, v___x_3086_, v___x_3087_, v___y_3079_, v___y_3021_, v___x_3013_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3072_);
lean_dec_ref(v___y_3082_);
v___y_3059_ = v___y_3073_;
v___y_3060_ = v___y_3074_;
v___y_3061_ = v___y_3075_;
v___y_3062_ = v___y_3076_;
v___y_3063_ = v___y_3077_;
v___y_3064_ = v___y_3078_;
v___y_3065_ = v___y_3080_;
v___y_3066_ = v___x_3088_;
goto v___jp_3058_;
}
}
else
{
size_t v___x_3089_; size_t v___x_3090_; lean_object* v___x_3091_; 
v___x_3089_ = ((size_t)0ULL);
v___x_3090_ = lean_usize_of_nat(v___x_3083_);
lean_inc_ref(v___y_3021_);
v___x_3091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_3082_, v___x_3089_, v___x_3090_, v___y_3079_, v___y_3021_, v___x_3013_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3072_);
lean_dec_ref(v___y_3082_);
v___y_3059_ = v___y_3073_;
v___y_3060_ = v___y_3074_;
v___y_3061_ = v___y_3075_;
v___y_3062_ = v___y_3076_;
v___y_3063_ = v___y_3077_;
v___y_3064_ = v___y_3078_;
v___y_3065_ = v___y_3080_;
v___y_3066_ = v___x_3091_;
goto v___jp_3058_;
}
}
}
v___jp_3092_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3103_ = lean_mk_empty_array_with_capacity(v___y_3100_);
v___x_3104_ = lean_array_get_size(v_targetDecls_3016_);
v___x_3105_ = lean_nat_dec_lt(v___y_3100_, v___x_3104_);
if (v___x_3105_ == 0)
{
lean_dec_ref(v_pkg_3017_);
v___y_3072_ = v_a_3102_;
v___y_3073_ = v___y_3093_;
v___y_3074_ = v___y_3094_;
v___y_3075_ = v___y_3095_;
v___y_3076_ = v___y_3096_;
v___y_3077_ = v___y_3097_;
v___y_3078_ = v___y_3098_;
v___y_3079_ = v_a_3101_;
v___y_3080_ = v___y_3099_;
v___y_3081_ = v___y_3100_;
v___y_3082_ = v___x_3103_;
goto v___jp_3071_;
}
else
{
uint8_t v___x_3106_; 
v___x_3106_ = lean_nat_dec_le(v___x_3104_, v___x_3104_);
if (v___x_3106_ == 0)
{
if (v___x_3105_ == 0)
{
lean_dec_ref(v_pkg_3017_);
v___y_3072_ = v_a_3102_;
v___y_3073_ = v___y_3093_;
v___y_3074_ = v___y_3094_;
v___y_3075_ = v___y_3095_;
v___y_3076_ = v___y_3096_;
v___y_3077_ = v___y_3097_;
v___y_3078_ = v___y_3098_;
v___y_3079_ = v_a_3101_;
v___y_3080_ = v___y_3099_;
v___y_3081_ = v___y_3100_;
v___y_3082_ = v___x_3103_;
goto v___jp_3071_;
}
else
{
size_t v___x_3107_; size_t v___x_3108_; lean_object* v___x_3109_; 
v___x_3107_ = ((size_t)0ULL);
v___x_3108_ = lean_usize_of_nat(v___x_3104_);
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_3017_, v_targetDecls_3016_, v___x_3107_, v___x_3108_, v___x_3103_);
v___y_3072_ = v_a_3102_;
v___y_3073_ = v___y_3093_;
v___y_3074_ = v___y_3094_;
v___y_3075_ = v___y_3095_;
v___y_3076_ = v___y_3096_;
v___y_3077_ = v___y_3097_;
v___y_3078_ = v___y_3098_;
v___y_3079_ = v_a_3101_;
v___y_3080_ = v___y_3099_;
v___y_3081_ = v___y_3100_;
v___y_3082_ = v___x_3109_;
goto v___jp_3071_;
}
}
else
{
size_t v___x_3110_; size_t v___x_3111_; lean_object* v___x_3112_; 
v___x_3110_ = ((size_t)0ULL);
v___x_3111_ = lean_usize_of_nat(v___x_3104_);
v___x_3112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_3017_, v_targetDecls_3016_, v___x_3110_, v___x_3111_, v___x_3103_);
v___y_3072_ = v_a_3102_;
v___y_3073_ = v___y_3093_;
v___y_3074_ = v___y_3094_;
v___y_3075_ = v___y_3095_;
v___y_3076_ = v___y_3096_;
v___y_3077_ = v___y_3097_;
v___y_3078_ = v___y_3098_;
v___y_3079_ = v_a_3101_;
v___y_3080_ = v___y_3099_;
v___y_3081_ = v___y_3100_;
v___y_3082_ = v___x_3112_;
goto v___jp_3071_;
}
}
}
v___jp_3113_:
{
if (lean_obj_tag(v___y_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v_a_3124_; 
v_a_3123_ = lean_ctor_get(v___y_3122_, 0);
lean_inc(v_a_3123_);
v_a_3124_ = lean_ctor_get(v___y_3122_, 1);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___y_3122_, 2);
v___y_3093_ = v___y_3114_;
v___y_3094_ = v___y_3115_;
v___y_3095_ = v___y_3116_;
v___y_3096_ = v___y_3117_;
v___y_3097_ = v___y_3118_;
v___y_3098_ = v___y_3119_;
v___y_3099_ = v___y_3120_;
v___y_3100_ = v___y_3121_;
v_a_3101_ = v_a_3123_;
v_a_3102_ = v_a_3124_;
goto v___jp_3092_;
}
else
{
lean_object* v_a_3125_; lean_object* v_a_3126_; 
lean_dec_ref(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec_ref(v___y_3114_);
lean_dec_ref(v___y_3021_);
lean_dec_ref(v_pkg_3017_);
lean_dec_ref(v_dir_3015_);
lean_dec_ref(v_self_3014_);
lean_dec(v___x_3013_);
v_a_3125_ = lean_ctor_get(v___y_3122_, 0);
lean_inc(v_a_3125_);
v_a_3126_ = lean_ctor_get(v___y_3122_, 1);
lean_inc(v_a_3126_);
lean_dec_ref_known(v___y_3122_, 2);
v_a_3055_ = v_a_3125_;
v_a_3056_ = v_a_3126_;
goto v___jp_3054_;
}
}
v___jp_3127_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v___x_3140_ = l_Array_append___redArg(v___y_3133_, v___y_3134_);
v___x_3141_ = lean_array_get_size(v___x_3140_);
v___x_3142_ = lean_nat_dec_lt(v___y_3137_, v___x_3141_);
if (v___x_3142_ == 0)
{
lean_dec_ref(v___x_3140_);
v___y_3093_ = v___y_3128_;
v___y_3094_ = v___y_3129_;
v___y_3095_ = v___y_3130_;
v___y_3096_ = v___y_3131_;
v___y_3097_ = v___y_3132_;
v___y_3098_ = v___y_3135_;
v___y_3099_ = v___y_3136_;
v___y_3100_ = v___y_3137_;
v_a_3101_ = v_snd_3138_;
v_a_3102_ = v_a_3139_;
goto v___jp_3092_;
}
else
{
uint8_t v___x_3143_; 
v___x_3143_ = lean_nat_dec_le(v___x_3141_, v___x_3141_);
if (v___x_3143_ == 0)
{
if (v___x_3142_ == 0)
{
lean_dec_ref(v___x_3140_);
v___y_3093_ = v___y_3128_;
v___y_3094_ = v___y_3129_;
v___y_3095_ = v___y_3130_;
v___y_3096_ = v___y_3131_;
v___y_3097_ = v___y_3132_;
v___y_3098_ = v___y_3135_;
v___y_3099_ = v___y_3136_;
v___y_3100_ = v___y_3137_;
v_a_3101_ = v_snd_3138_;
v_a_3102_ = v_a_3139_;
goto v___jp_3092_;
}
else
{
size_t v___x_3144_; size_t v___x_3145_; lean_object* v___x_3146_; 
v___x_3144_ = ((size_t)0ULL);
v___x_3145_ = lean_usize_of_nat(v___x_3141_);
lean_inc_ref(v___y_3021_);
lean_inc_ref(v_pkg_3017_);
v___x_3146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_3017_, v___x_3140_, v___x_3144_, v___x_3145_, v_snd_3138_, v___y_3021_, v___x_3013_, v___y_3023_, v___y_3024_, v___y_3025_, v_a_3139_);
lean_dec_ref(v___x_3140_);
v___y_3114_ = v___y_3128_;
v___y_3115_ = v___y_3129_;
v___y_3116_ = v___y_3130_;
v___y_3117_ = v___y_3131_;
v___y_3118_ = v___y_3132_;
v___y_3119_ = v___y_3135_;
v___y_3120_ = v___y_3136_;
v___y_3121_ = v___y_3137_;
v___y_3122_ = v___x_3146_;
goto v___jp_3113_;
}
}
else
{
size_t v___x_3147_; size_t v___x_3148_; lean_object* v___x_3149_; 
v___x_3147_ = ((size_t)0ULL);
v___x_3148_ = lean_usize_of_nat(v___x_3141_);
lean_inc_ref(v___y_3021_);
lean_inc_ref(v_pkg_3017_);
v___x_3149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_3017_, v___x_3140_, v___x_3147_, v___x_3148_, v_snd_3138_, v___y_3021_, v___x_3013_, v___y_3023_, v___y_3024_, v___y_3025_, v_a_3139_);
lean_dec_ref(v___x_3140_);
v___y_3114_ = v___y_3128_;
v___y_3115_ = v___y_3129_;
v___y_3116_ = v___y_3130_;
v___y_3117_ = v___y_3131_;
v___y_3118_ = v___y_3132_;
v___y_3119_ = v___y_3135_;
v___y_3120_ = v___y_3136_;
v___y_3121_ = v___y_3137_;
v___y_3122_ = v___x_3149_;
goto v___jp_3113_;
}
}
}
v___jp_3150_:
{
if (lean_obj_tag(v___y_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v_a_3163_; lean_object* v_snd_3164_; 
v_a_3162_ = lean_ctor_get(v___y_3161_, 0);
lean_inc(v_a_3162_);
v_a_3163_ = lean_ctor_get(v___y_3161_, 1);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___y_3161_, 2);
v_snd_3164_ = lean_ctor_get(v_a_3162_, 1);
lean_inc(v_snd_3164_);
lean_dec(v_a_3162_);
v___y_3128_ = v___y_3151_;
v___y_3129_ = v___y_3152_;
v___y_3130_ = v___y_3153_;
v___y_3131_ = v___y_3154_;
v___y_3132_ = v___y_3155_;
v___y_3133_ = v___y_3156_;
v___y_3134_ = v___y_3157_;
v___y_3135_ = v___y_3158_;
v___y_3136_ = v___y_3159_;
v___y_3137_ = v___y_3160_;
v_snd_3138_ = v_snd_3164_;
v_a_3139_ = v_a_3163_;
goto v___jp_3127_;
}
else
{
lean_object* v_a_3165_; lean_object* v_a_3166_; 
lean_dec_ref(v___y_3158_);
lean_dec_ref(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec_ref(v___y_3151_);
lean_dec_ref(v___y_3021_);
lean_dec_ref(v_pkg_3017_);
lean_dec_ref(v_dir_3015_);
lean_dec_ref(v_self_3014_);
lean_dec(v___x_3013_);
v_a_3165_ = lean_ctor_get(v___y_3161_, 0);
lean_inc(v_a_3165_);
v_a_3166_ = lean_ctor_get(v___y_3161_, 1);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___y_3161_, 2);
v_a_3055_ = v_a_3165_;
v_a_3056_ = v_a_3166_;
goto v___jp_3054_;
}
}
v___jp_3167_:
{
lean_object* v_toArray_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3199_; 
v_toArray_3180_ = lean_ctor_get(v_a_3178_, 1);
v_isSharedCheck_3199_ = !lean_is_exclusive(v_a_3178_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; 
v_unused_3200_ = lean_ctor_get(v_a_3178_, 0);
lean_dec(v_unused_3200_);
v___x_3182_ = v_a_3178_;
v_isShared_3183_ = v_isSharedCheck_3199_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_toArray_3180_);
lean_dec(v_a_3178_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3199_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; uint8_t v___x_3186_; 
v___x_3184_ = lean_mk_empty_array_with_capacity(v___y_3177_);
v___x_3185_ = lean_array_get_size(v_toArray_3180_);
v___x_3186_ = lean_nat_dec_lt(v___y_3177_, v___x_3185_);
if (v___x_3186_ == 0)
{
lean_del_object(v___x_3182_);
lean_dec_ref(v_toArray_3180_);
lean_dec(v_name_3018_);
v___y_3128_ = v___y_3168_;
v___y_3129_ = v___y_3169_;
v___y_3130_ = v___y_3170_;
v___y_3131_ = v___y_3171_;
v___y_3132_ = v___y_3172_;
v___y_3133_ = v___y_3173_;
v___y_3134_ = v___y_3174_;
v___y_3135_ = v___y_3175_;
v___y_3136_ = v___y_3176_;
v___y_3137_ = v___y_3177_;
v_snd_3138_ = v___x_3184_;
v_a_3139_ = v_a_3179_;
goto v___jp_3127_;
}
else
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3187_ = l_Lean_NameSet_empty;
v___x_3188_ = l_Lean_NameSet_insert(v___x_3187_, v_name_3018_);
lean_inc_ref(v___x_3184_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 1, v___x_3184_);
lean_ctor_set(v___x_3182_, 0, v___x_3188_);
v___x_3190_ = v___x_3182_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v___x_3184_);
v___x_3190_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
uint8_t v___x_3191_; 
v___x_3191_ = lean_nat_dec_le(v___x_3185_, v___x_3185_);
if (v___x_3191_ == 0)
{
if (v___x_3186_ == 0)
{
lean_dec_ref(v___x_3190_);
lean_dec_ref(v_toArray_3180_);
v___y_3128_ = v___y_3168_;
v___y_3129_ = v___y_3169_;
v___y_3130_ = v___y_3170_;
v___y_3131_ = v___y_3171_;
v___y_3132_ = v___y_3172_;
v___y_3133_ = v___y_3173_;
v___y_3134_ = v___y_3174_;
v___y_3135_ = v___y_3175_;
v___y_3136_ = v___y_3176_;
v___y_3137_ = v___y_3177_;
v_snd_3138_ = v___x_3184_;
v_a_3139_ = v_a_3179_;
goto v___jp_3127_;
}
else
{
size_t v___x_3192_; size_t v___x_3193_; lean_object* v___x_3194_; 
lean_dec_ref(v___x_3184_);
v___x_3192_ = ((size_t)0ULL);
v___x_3193_ = lean_usize_of_nat(v___x_3185_);
lean_inc_ref(v___y_3021_);
v___x_3194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_3180_, v___x_3192_, v___x_3193_, v___x_3190_, v___y_3021_, v___x_3013_, v___y_3023_, v___y_3024_, v___y_3025_, v_a_3179_);
lean_dec_ref(v_toArray_3180_);
v___y_3151_ = v___y_3168_;
v___y_3152_ = v___y_3169_;
v___y_3153_ = v___y_3170_;
v___y_3154_ = v___y_3171_;
v___y_3155_ = v___y_3172_;
v___y_3156_ = v___y_3173_;
v___y_3157_ = v___y_3174_;
v___y_3158_ = v___y_3175_;
v___y_3159_ = v___y_3176_;
v___y_3160_ = v___y_3177_;
v___y_3161_ = v___x_3194_;
goto v___jp_3150_;
}
}
else
{
size_t v___x_3195_; size_t v___x_3196_; lean_object* v___x_3197_; 
lean_dec_ref(v___x_3184_);
v___x_3195_ = ((size_t)0ULL);
v___x_3196_ = lean_usize_of_nat(v___x_3185_);
lean_inc_ref(v___y_3021_);
v___x_3197_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_3180_, v___x_3195_, v___x_3196_, v___x_3190_, v___y_3021_, v___x_3013_, v___y_3023_, v___y_3024_, v___y_3025_, v_a_3179_);
lean_dec_ref(v_toArray_3180_);
v___y_3151_ = v___y_3168_;
v___y_3152_ = v___y_3169_;
v___y_3153_ = v___y_3170_;
v___y_3154_ = v___y_3171_;
v___y_3155_ = v___y_3172_;
v___y_3156_ = v___y_3173_;
v___y_3157_ = v___y_3174_;
v___y_3158_ = v___y_3175_;
v___y_3159_ = v___y_3176_;
v___y_3160_ = v___y_3177_;
v___y_3161_ = v___x_3197_;
goto v___jp_3150_;
}
}
}
}
}
v___jp_3201_:
{
if (lean_obj_tag(v___y_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v_a_3214_; 
v_a_3213_ = lean_ctor_get(v___y_3212_, 0);
lean_inc(v_a_3213_);
v_a_3214_ = lean_ctor_get(v___y_3212_, 1);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___y_3212_, 2);
v___y_3168_ = v___y_3202_;
v___y_3169_ = v___y_3203_;
v___y_3170_ = v___y_3204_;
v___y_3171_ = v___y_3205_;
v___y_3172_ = v___y_3206_;
v___y_3173_ = v___y_3207_;
v___y_3174_ = v___y_3208_;
v___y_3175_ = v___y_3209_;
v___y_3176_ = v___y_3210_;
v___y_3177_ = v___y_3211_;
v_a_3178_ = v_a_3213_;
v_a_3179_ = v_a_3214_;
goto v___jp_3167_;
}
else
{
lean_object* v_a_3215_; lean_object* v_a_3216_; 
lean_dec_ref(v___y_3209_);
lean_dec_ref(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec_ref(v___y_3202_);
lean_dec_ref(v___y_3021_);
lean_dec(v_name_3018_);
lean_dec_ref(v_pkg_3017_);
lean_dec_ref(v_dir_3015_);
lean_dec_ref(v_self_3014_);
lean_dec(v___x_3013_);
v_a_3215_ = lean_ctor_get(v___y_3212_, 0);
lean_inc(v_a_3215_);
v_a_3216_ = lean_ctor_get(v___y_3212_, 1);
lean_inc(v_a_3216_);
lean_dec_ref_known(v___y_3212_, 2);
v_a_3055_ = v_a_3215_;
v_a_3056_ = v_a_3216_;
goto v___jp_3054_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* v___x_3335_, lean_object* v___x_3336_, lean_object* v_self_3337_, lean_object* v_dir_3338_, lean_object* v_targetDecls_3339_, lean_object* v_pkg_3340_, lean_object* v_name_3341_, lean_object* v_config_3342_, lean_object* v_config_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v___x_3335_, v___x_3336_, v_self_3337_, v_dir_3338_, v_targetDecls_3339_, v_pkg_3340_, v_name_3341_, v_config_3342_, v_config_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec(v_config_3343_);
lean_dec_ref(v_targetDecls_3339_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object* v_self_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v_pkg_3361_; lean_object* v_name_3362_; lean_object* v_config_3363_; lean_object* v_keyName_3364_; lean_object* v_dir_3365_; lean_object* v_config_3366_; lean_object* v_targetDecls_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___f_3374_; lean_object* v___x_3375_; 
v_pkg_3361_ = lean_ctor_get(v_self_3353_, 0);
lean_inc_ref_n(v_pkg_3361_, 2);
v_name_3362_ = lean_ctor_get(v_self_3353_, 1);
lean_inc_n(v_name_3362_, 3);
v_config_3363_ = lean_ctor_get(v_self_3353_, 2);
lean_inc(v_config_3363_);
v_keyName_3364_ = lean_ctor_get(v_pkg_3361_, 2);
v_dir_3365_ = lean_ctor_get(v_pkg_3361_, 4);
lean_inc_ref(v_dir_3365_);
v_config_3366_ = lean_ctor_get(v_pkg_3361_, 6);
lean_inc_ref(v_config_3366_);
v_targetDecls_3367_ = lean_ctor_get(v_pkg_3361_, 15);
lean_inc_ref(v_targetDecls_3367_);
v___x_3368_ = l_Lake_instDataKindDynlib;
v___x_3369_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_3364_);
v___x_3370_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3370_, 0, v_keyName_3364_);
lean_ctor_set(v___x_3370_, 1, v_name_3362_);
v___x_3371_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3353_);
v___x_3372_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3370_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
lean_ctor_set(v___x_3372_, 2, v_self_3353_);
lean_ctor_set(v___x_3372_, 3, v___x_3369_);
v___x_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3373_, 0, v_pkg_3361_);
v___f_3374_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3374_, 0, v___x_3372_);
lean_closure_set(v___f_3374_, 1, v___x_3373_);
lean_closure_set(v___f_3374_, 2, v_self_3353_);
lean_closure_set(v___f_3374_, 3, v_dir_3365_);
lean_closure_set(v___f_3374_, 4, v_targetDecls_3367_);
lean_closure_set(v___f_3374_, 5, v_pkg_3361_);
lean_closure_set(v___f_3374_, 6, v_name_3362_);
lean_closure_set(v___f_3374_, 7, v_config_3366_);
lean_closure_set(v___f_3374_, 8, v_config_3363_);
v___x_3375_ = l_Lake_ensureJob___redArg(v___x_3368_, v___f_3374_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3405_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
v_a_3377_ = lean_ctor_get(v___x_3375_, 1);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3379_ = v___x_3375_;
v_isShared_3380_ = v_isSharedCheck_3405_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_inc(v_a_3376_);
lean_dec(v___x_3375_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3405_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v_task_3381_; lean_object* v_kind_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3403_; 
v_task_3381_ = lean_ctor_get(v_a_3376_, 0);
v_kind_3382_ = lean_ctor_get(v_a_3376_, 1);
v_isSharedCheck_3403_ = !lean_is_exclusive(v_a_3376_);
if (v_isSharedCheck_3403_ == 0)
{
lean_object* v_unused_3404_; 
v_unused_3404_ = lean_ctor_get(v_a_3376_, 2);
lean_dec(v_unused_3404_);
v___x_3384_ = v_a_3376_;
v_isShared_3385_ = v_isSharedCheck_3403_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_kind_3382_);
lean_inc(v_task_3381_);
lean_dec(v_a_3376_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3403_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v_registeredJobs_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; lean_object* v_job_3394_; 
v_registeredJobs_3386_ = lean_ctor_get(v_a_3358_, 3);
v___x_3387_ = lean_st_ref_take(v_registeredJobs_3386_);
v___x_3388_ = 1;
v___x_3389_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3362_, v___x_3388_);
v___x_3390_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0));
v___x_3391_ = lean_string_append(v___x_3389_, v___x_3390_);
v___x_3392_ = 0;
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 2, v___x_3391_);
v_job_3394_ = v___x_3384_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_task_3381_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_kind_3382_);
lean_ctor_set(v_reuseFailAlloc_3402_, 2, v___x_3391_);
v_job_3394_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3400_; 
lean_ctor_set_uint8(v_job_3394_, sizeof(void*)*3, v___x_3392_);
lean_inc_ref(v_job_3394_);
v___x_3395_ = l_Lake_Job_toOpaque___redArg(v_job_3394_);
v___x_3396_ = lean_array_push(v___x_3387_, v___x_3395_);
v___x_3397_ = lean_st_ref_put(v_registeredJobs_3386_, v___x_3396_);
v___x_3398_ = l_Lake_Job_renew___redArg(v_job_3394_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3398_);
v___x_3400_ = v___x_3379_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3398_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v_a_3377_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
}
else
{
lean_dec(v_name_3362_);
return v___x_3375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object* v_self_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_);
lean_dec_ref(v_a_3411_);
lean_dec(v_a_3410_);
lean_dec(v_a_3409_);
lean_dec(v_a_3408_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t v_fmt_3415_, lean_object* v_a_3416_){
_start:
{
if (v_fmt_3415_ == 0)
{
lean_object* v_path_3417_; 
v_path_3417_ = lean_ctor_get(v_a_3416_, 0);
lean_inc_ref(v_path_3417_);
return v_path_3417_;
}
else
{
lean_object* v_path_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v_path_3418_ = lean_ctor_get(v_a_3416_, 0);
lean_inc_ref(v_path_3418_);
v___x_3419_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3419_, 0, v_path_3418_);
v___x_3420_ = l_Lean_Json_compress(v___x_3419_);
return v___x_3420_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* v_fmt_3421_, lean_object* v_a_3422_){
_start:
{
uint8_t v_fmt_boxed_3423_; lean_object* v_res_3424_; 
v_fmt_boxed_3423_ = lean_unbox(v_fmt_3421_);
v_res_3424_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_boxed_3423_, v_a_3422_);
lean_dec_ref(v_a_3422_);
return v_res_3424_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3427_; uint8_t v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___f_3427_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__0));
v___x_3428_ = 1;
v___x_3429_ = l_Lake_instDataKindDynlib;
v___x_3430_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__1));
v___x_3431_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3432_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
lean_ctor_set(v___x_3432_, 1, v___x_3430_);
lean_ctor_set(v___x_3432_, 2, v___x_3429_);
lean_ctor_set(v___x_3432_, 3, v___f_3427_);
lean_ctor_set_uint8(v___x_3432_, sizeof(void*)*4, v___x_3428_);
lean_ctor_set_uint8(v___x_3432_, sizeof(void*)*4 + 1, v___x_3428_);
return v___x_3432_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = lean_obj_once(&l_Lake_LeanLib_sharedFacetConfig___closed__2, &l_Lake_LeanLib_sharedFacetConfig___closed__2_once, _init_l_Lake_LeanLib_sharedFacetConfig___closed__2);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* v___x_3434_, lean_object* v_as_3435_, size_t v_sz_3436_, size_t v_i_3437_, lean_object* v_b_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_usize_dec_lt(v_i_3437_, v_sz_3436_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; 
lean_dec_ref(v___y_3439_);
lean_dec_ref(v___x_3434_);
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v_b_3438_);
lean_ctor_set(v___x_3447_, 1, v___y_3444_);
return v___x_3447_;
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3449_; 
v_a_3448_ = lean_array_uget_borrowed(v_as_3435_, v_i_3437_);
lean_inc_ref(v___y_3439_);
lean_inc_n(v_a_3448_, 2);
lean_inc_ref(v___x_3434_);
v___x_3449_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v___x_3434_, v_a_3448_, v_a_3448_, v___x_3446_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v_a_3451_; lean_object* v_snd_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; size_t v___x_3455_; size_t v___x_3456_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
v_a_3451_ = lean_ctor_get(v___x_3449_, 1);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3449_, 2);
v_snd_3452_ = lean_ctor_get(v_a_3450_, 1);
lean_inc(v_snd_3452_);
lean_dec(v_a_3450_);
v___x_3453_ = l_Lake_Job_toOpaque___redArg(v_snd_3452_);
v___x_3454_ = l_Lake_Job_mix___redArg(v_b_3438_, v___x_3453_);
v___x_3455_ = ((size_t)1ULL);
v___x_3456_ = lean_usize_add(v_i_3437_, v___x_3455_);
v_i_3437_ = v___x_3456_;
v_b_3438_ = v___x_3454_;
v___y_3444_ = v_a_3451_;
goto _start;
}
else
{
lean_object* v_a_3458_; lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v___y_3439_);
lean_dec_ref(v_b_3438_);
lean_dec_ref(v___x_3434_);
v_a_3458_ = lean_ctor_get(v___x_3449_, 0);
v_a_3459_ = lean_ctor_get(v___x_3449_, 1);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3449_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_inc(v_a_3458_);
lean_dec(v___x_3449_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3458_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* v___x_3467_, lean_object* v_as_3468_, lean_object* v_sz_3469_, lean_object* v_i_3470_, lean_object* v_b_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_){
_start:
{
size_t v_sz_boxed_3479_; size_t v_i_boxed_3480_; lean_object* v_res_3481_; 
v_sz_boxed_3479_ = lean_unbox_usize(v_sz_3469_);
lean_dec(v_sz_3469_);
v_i_boxed_3480_ = lean_unbox_usize(v_i_3470_);
lean_dec(v_i_3470_);
v_res_3481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_3467_, v_as_3468_, v_sz_boxed_3479_, v_i_boxed_3480_, v_b_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
lean_dec_ref(v___y_3476_);
lean_dec(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v_as_3468_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* v___x_3482_, lean_object* v_as_3483_, size_t v_sz_3484_, size_t v_i_3485_, lean_object* v_b_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
uint8_t v___x_3494_; 
v___x_3494_ = lean_usize_dec_lt(v_i_3485_, v_sz_3484_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; 
lean_dec_ref(v___y_3487_);
lean_dec_ref(v___x_3482_);
v___x_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3495_, 0, v_b_3486_);
lean_ctor_set(v___x_3495_, 1, v___y_3492_);
return v___x_3495_;
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3497_; 
v_a_3496_ = lean_array_uget_borrowed(v_as_3483_, v_i_3485_);
lean_inc_ref(v___y_3487_);
lean_inc(v_a_3496_);
lean_inc_ref(v___x_3482_);
v___x_3497_ = l_Lake_Package_fetchTargetJob(v___x_3482_, v_a_3496_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v_a_3499_; lean_object* v___x_3500_; size_t v___x_3501_; size_t v___x_3502_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
v_a_3499_ = lean_ctor_get(v___x_3497_, 1);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3497_, 2);
v___x_3500_ = l_Lake_Job_mix___redArg(v_b_3486_, v_a_3498_);
v___x_3501_ = ((size_t)1ULL);
v___x_3502_ = lean_usize_add(v_i_3485_, v___x_3501_);
v_i_3485_ = v___x_3502_;
v_b_3486_ = v___x_3500_;
v___y_3492_ = v_a_3499_;
goto _start;
}
else
{
lean_object* v_a_3504_; lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec_ref(v___y_3487_);
lean_dec_ref(v_b_3486_);
lean_dec_ref(v___x_3482_);
v_a_3504_ = lean_ctor_get(v___x_3497_, 0);
v_a_3505_ = lean_ctor_get(v___x_3497_, 1);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3497_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_inc(v_a_3504_);
lean_dec(v___x_3497_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3504_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* v___x_3513_, lean_object* v_as_3514_, lean_object* v_sz_3515_, lean_object* v_i_3516_, lean_object* v_b_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
size_t v_sz_boxed_3525_; size_t v_i_boxed_3526_; lean_object* v_res_3527_; 
v_sz_boxed_3525_ = lean_unbox_usize(v_sz_3515_);
lean_dec(v_sz_3515_);
v_i_boxed_3526_ = lean_unbox_usize(v_i_3516_);
lean_dec(v_i_3516_);
v_res_3527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_3513_, v_as_3514_, v_sz_boxed_3525_, v_i_boxed_3526_, v_b_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v_as_3514_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object* v_self_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v_pkg_3538_; lean_object* v_name_3539_; lean_object* v_config_3540_; lean_object* v_baseName_3541_; lean_object* v_keyName_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v_pkg_3538_ = lean_ctor_get(v_self_3530_, 0);
lean_inc_ref_n(v_pkg_3538_, 2);
v_name_3539_ = lean_ctor_get(v_self_3530_, 1);
lean_inc(v_name_3539_);
v_config_3540_ = lean_ctor_get(v_self_3530_, 2);
lean_inc(v_config_3540_);
lean_dec_ref(v_self_3530_);
v_baseName_3541_ = lean_ctor_get(v_pkg_3538_, 1);
v_keyName_3542_ = lean_ctor_get(v_pkg_3538_, 2);
v___x_3543_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_3542_);
v___x_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3544_, 0, v_keyName_3542_);
v___x_3545_ = l_Lake_Package_keyword;
v___x_3546_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3544_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
lean_ctor_set(v___x_3546_, 2, v_pkg_3538_);
lean_ctor_set(v___x_3546_, 3, v___x_3543_);
lean_inc_ref(v_a_3531_);
lean_inc_ref(v_a_3535_);
lean_inc(v_a_3534_);
lean_inc(v_a_3533_);
lean_inc(v_a_3532_);
v___x_3547_ = lean_apply_7(v_a_3531_, v___x_3546_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, lean_box(0));
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3585_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
v_a_3549_ = lean_ctor_get(v___x_3547_, 1);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3551_ = v___x_3547_;
v_isShared_3552_ = v_isSharedCheck_3585_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_inc(v_a_3548_);
lean_dec(v___x_3547_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3585_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
uint8_t v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v_needs_3557_; lean_object* v_extraDepTargets_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; uint8_t v___x_3565_; uint8_t v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3553_ = 1;
lean_inc(v_baseName_3541_);
v___x_3554_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3541_, v___x_3553_);
v___x_3555_ = lean_unsigned_to_nat(0u);
v___x_3556_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v_needs_3557_ = lean_ctor_get(v_config_3540_, 5);
lean_inc_ref(v_needs_3557_);
v_extraDepTargets_3558_ = lean_ctor_get(v_config_3540_, 6);
lean_inc_ref(v_extraDepTargets_3558_);
lean_dec(v_config_3540_);
v___x_3559_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0));
v___x_3560_ = lean_string_append(v___x_3554_, v___x_3559_);
v___x_3561_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3539_, v___x_3553_);
v___x_3562_ = lean_string_append(v___x_3560_, v___x_3561_);
lean_dec_ref(v___x_3561_);
v___x_3563_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1));
v___x_3564_ = lean_string_append(v___x_3562_, v___x_3563_);
v___x_3565_ = 0;
v___x_3566_ = 0;
v___x_3567_ = l_Lake_BuildTrace_nil(v___x_3564_);
v___x_3568_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3568_, 0, v___x_3556_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
lean_ctor_set(v___x_3568_, 2, v___x_3555_);
lean_ctor_set_uint8(v___x_3568_, sizeof(void*)*3, v___x_3565_);
lean_ctor_set_uint8(v___x_3568_, sizeof(void*)*3 + 1, v___x_3566_);
v___x_3569_ = lean_box(0);
v___x_3570_ = lean_box(0);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 1, v___x_3568_);
lean_ctor_set(v___x_3551_, 0, v___x_3570_);
v___x_3572_ = v___x_3551_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3570_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v___x_3568_);
v___x_3572_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v_job_3575_; lean_object* v___x_3576_; size_t v_sz_3577_; size_t v___x_3578_; lean_object* v___x_3579_; 
v___x_3573_ = lean_task_pure(v___x_3572_);
v___x_3574_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v_job_3575_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_3575_, 0, v___x_3573_);
lean_ctor_set(v_job_3575_, 1, v___x_3569_);
lean_ctor_set(v_job_3575_, 2, v___x_3574_);
lean_ctor_set_uint8(v_job_3575_, sizeof(void*)*3, v___x_3566_);
v___x_3576_ = l_Lake_Job_mix___redArg(v_job_3575_, v_a_3548_);
v_sz_3577_ = lean_array_size(v_extraDepTargets_3558_);
v___x_3578_ = ((size_t)0ULL);
lean_inc_ref(v_a_3531_);
lean_inc_ref(v_pkg_3538_);
v___x_3579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_3538_, v_extraDepTargets_3558_, v_sz_3577_, v___x_3578_, v___x_3576_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3549_);
lean_dec_ref(v_extraDepTargets_3558_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v_a_3581_; size_t v_sz_3582_; lean_object* v___x_3583_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
v_a_3581_ = lean_ctor_get(v___x_3579_, 1);
lean_inc(v_a_3581_);
lean_dec_ref_known(v___x_3579_, 2);
v_sz_3582_ = lean_array_size(v_needs_3557_);
v___x_3583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_3538_, v_needs_3557_, v_sz_3582_, v___x_3578_, v_a_3580_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3581_);
lean_dec_ref(v_needs_3557_);
return v___x_3583_;
}
else
{
lean_dec_ref(v_needs_3557_);
lean_dec_ref(v_pkg_3538_);
lean_dec_ref(v_a_3531_);
return v___x_3579_;
}
}
}
}
else
{
lean_dec(v_config_3540_);
lean_dec(v_name_3539_);
lean_dec_ref(v_pkg_3538_);
lean_dec_ref(v_a_3531_);
return v___x_3547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object* v_self_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
lean_dec_ref(v_a_3591_);
lean_dec(v_a_3590_);
lean_dec(v_a_3589_);
lean_dec(v_a_3588_);
return v_res_3594_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3596_; uint8_t v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___f_3596_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3597_ = 1;
v___x_3598_ = l_Lake_instDataKindUnit;
v___x_3599_ = ((lean_object*)(l_Lake_LeanLib_extraDepFacetConfig___closed__0));
v___x_3600_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3601_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
lean_ctor_set(v___x_3601_, 1, v___x_3599_);
lean_ctor_set(v___x_3601_, 2, v___x_3598_);
lean_ctor_set(v___x_3601_, 3, v___f_3596_);
lean_ctor_set_uint8(v___x_3601_, sizeof(void*)*4, v___x_3597_);
lean_ctor_set_uint8(v___x_3601_, sizeof(void*)*4 + 1, v___x_3597_);
return v___x_3601_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = lean_obj_once(&l_Lake_LeanLib_extraDepFacetConfig___closed__1, &l_Lake_LeanLib_extraDepFacetConfig___closed__1_once, _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* v_self_3603_, size_t v_sz_3604_, size_t v_i_3605_, lean_object* v_bs_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
uint8_t v___x_3614_; 
v___x_3614_ = lean_usize_dec_lt(v_i_3605_, v_sz_3604_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; 
lean_dec_ref(v___y_3607_);
lean_dec_ref(v_self_3603_);
v___x_3615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3615_, 0, v_bs_3606_);
lean_ctor_set(v___x_3615_, 1, v___y_3612_);
return v___x_3615_;
}
else
{
lean_object* v_pkg_3616_; lean_object* v_name_3617_; lean_object* v_keyName_3618_; lean_object* v_v_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v_pkg_3616_ = lean_ctor_get(v_self_3603_, 0);
v_name_3617_ = lean_ctor_get(v_self_3603_, 1);
v_keyName_3618_ = lean_ctor_get(v_pkg_3616_, 2);
v_v_3619_ = lean_array_uget_borrowed(v_bs_3606_, v_i_3605_);
lean_inc(v_name_3617_);
lean_inc(v_keyName_3618_);
v___x_3620_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3620_, 0, v_keyName_3618_);
lean_ctor_set(v___x_3620_, 1, v_name_3617_);
v___x_3621_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc(v_v_3619_);
lean_inc_ref(v_self_3603_);
v___x_3622_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3620_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
lean_ctor_set(v___x_3622_, 2, v_self_3603_);
lean_ctor_set(v___x_3622_, 3, v_v_3619_);
lean_inc_ref(v___y_3607_);
lean_inc_ref(v___y_3611_);
lean_inc(v___y_3610_);
lean_inc(v___y_3609_);
lean_inc(v___y_3608_);
v___x_3623_ = lean_apply_7(v___y_3607_, v___x_3622_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, lean_box(0));
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v_a_3625_; lean_object* v___x_3626_; lean_object* v_bs_x27_3627_; lean_object* v___x_3628_; size_t v___x_3629_; size_t v___x_3630_; lean_object* v___x_3631_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
v_a_3625_ = lean_ctor_get(v___x_3623_, 1);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3623_, 2);
v___x_3626_ = lean_unsigned_to_nat(0u);
v_bs_x27_3627_ = lean_array_uset(v_bs_3606_, v_i_3605_, v___x_3626_);
v___x_3628_ = l_Lake_Job_toOpaque___redArg(v_a_3624_);
v___x_3629_ = ((size_t)1ULL);
v___x_3630_ = lean_usize_add(v_i_3605_, v___x_3629_);
v___x_3631_ = lean_array_uset(v_bs_x27_3627_, v_i_3605_, v___x_3628_);
v_i_3605_ = v___x_3630_;
v_bs_3606_ = v___x_3631_;
v___y_3612_ = v_a_3625_;
goto _start;
}
else
{
lean_object* v_a_3633_; lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_dec_ref(v___y_3607_);
lean_dec_ref(v_bs_3606_);
lean_dec_ref(v_self_3603_);
v_a_3633_ = lean_ctor_get(v___x_3623_, 0);
v_a_3634_ = lean_ctor_get(v___x_3623_, 1);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3623_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_inc(v_a_3633_);
lean_dec(v___x_3623_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3633_);
lean_ctor_set(v_reuseFailAlloc_3640_, 1, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* v_self_3642_, lean_object* v_sz_3643_, lean_object* v_i_3644_, lean_object* v_bs_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
size_t v_sz_boxed_3653_; size_t v_i_boxed_3654_; lean_object* v_res_3655_; 
v_sz_boxed_3653_ = lean_unbox_usize(v_sz_3643_);
lean_dec(v_sz_3643_);
v_i_boxed_3654_ = lean_unbox_usize(v_i_3644_);
lean_dec(v_i_3644_);
v_res_3655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3642_, v_sz_boxed_3653_, v_i_boxed_3654_, v_bs_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec(v___y_3648_);
lean_dec(v___y_3647_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object* v_self_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v_config_3665_; lean_object* v_defaultFacets_3666_; size_t v_sz_3667_; size_t v___x_3668_; lean_object* v___x_3669_; 
v_config_3665_ = lean_ctor_get(v_self_3657_, 2);
v_defaultFacets_3666_ = lean_ctor_get(v_config_3665_, 7);
lean_inc_ref(v_defaultFacets_3666_);
v_sz_3667_ = lean_array_size(v_defaultFacets_3666_);
v___x_3668_ = ((size_t)0ULL);
v___x_3669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3657_, v_sz_3667_, v___x_3668_, v_defaultFacets_3666_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3680_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
v_a_3671_ = lean_ctor_get(v___x_3669_, 1);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3673_ = v___x_3669_;
v_isShared_3674_ = v_isSharedCheck_3680_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_inc(v_a_3670_);
lean_dec(v___x_3669_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3680_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3678_; 
v___x_3675_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0));
v___x_3676_ = l_Lake_Job_mixArray___redArg(v_a_3670_, v___x_3675_);
lean_dec(v_a_3670_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v___x_3676_);
v___x_3678_ = v___x_3673_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_a_3671_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
v_a_3681_ = lean_ctor_get(v___x_3669_, 0);
v_a_3682_ = lean_ctor_get(v___x_3669_, 1);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3669_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_inc(v_a_3681_);
lean_dec(v___x_3669_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3681_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object* v_self_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
lean_dec_ref(v_a_3695_);
lean_dec(v_a_3694_);
lean_dec(v_a_3693_);
lean_dec(v_a_3692_);
return v_res_3698_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3700_; uint8_t v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___f_3700_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3701_ = 1;
v___x_3702_ = l_Lake_instDataKindUnit;
v___x_3703_ = ((lean_object*)(l_Lake_LeanLib_defaultFacetConfig___closed__0));
v___x_3704_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3705_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
lean_ctor_set(v___x_3705_, 1, v___x_3703_);
lean_ctor_set(v___x_3705_, 2, v___x_3702_);
lean_ctor_set(v___x_3705_, 3, v___f_3700_);
lean_ctor_set_uint8(v___x_3705_, sizeof(void*)*4, v___x_3701_);
lean_ctor_set_uint8(v___x_3705_, sizeof(void*)*4 + 1, v___x_3701_);
return v___x_3705_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_obj_once(&l_Lake_LeanLib_defaultFacetConfig___closed__1, &l_Lake_LeanLib_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanLib_defaultFacetConfig___closed__1);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_3707_, lean_object* v_v_3708_, lean_object* v_t_3709_){
_start:
{
if (lean_obj_tag(v_t_3709_) == 0)
{
lean_object* v_size_3710_; lean_object* v_k_3711_; lean_object* v_v_3712_; lean_object* v_l_3713_; lean_object* v_r_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3994_; 
v_size_3710_ = lean_ctor_get(v_t_3709_, 0);
v_k_3711_ = lean_ctor_get(v_t_3709_, 1);
v_v_3712_ = lean_ctor_get(v_t_3709_, 2);
v_l_3713_ = lean_ctor_get(v_t_3709_, 3);
v_r_3714_ = lean_ctor_get(v_t_3709_, 4);
v_isSharedCheck_3994_ = !lean_is_exclusive(v_t_3709_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3716_ = v_t_3709_;
v_isShared_3717_ = v_isSharedCheck_3994_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_r_3714_);
lean_inc(v_l_3713_);
lean_inc(v_v_3712_);
lean_inc(v_k_3711_);
lean_inc(v_size_3710_);
lean_dec(v_t_3709_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3994_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
uint8_t v___x_3718_; 
v___x_3718_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3707_, v_k_3711_);
switch(v___x_3718_)
{
case 0:
{
lean_object* v_impl_3719_; lean_object* v___x_3720_; 
lean_dec(v_size_3710_);
v_impl_3719_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3707_, v_v_3708_, v_l_3713_);
v___x_3720_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3714_) == 0)
{
lean_object* v_size_3721_; lean_object* v_size_3722_; lean_object* v_k_3723_; lean_object* v_v_3724_; lean_object* v_l_3725_; lean_object* v_r_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; uint8_t v___x_3729_; 
v_size_3721_ = lean_ctor_get(v_r_3714_, 0);
v_size_3722_ = lean_ctor_get(v_impl_3719_, 0);
lean_inc(v_size_3722_);
v_k_3723_ = lean_ctor_get(v_impl_3719_, 1);
lean_inc(v_k_3723_);
v_v_3724_ = lean_ctor_get(v_impl_3719_, 2);
lean_inc(v_v_3724_);
v_l_3725_ = lean_ctor_get(v_impl_3719_, 3);
lean_inc(v_l_3725_);
v_r_3726_ = lean_ctor_get(v_impl_3719_, 4);
lean_inc(v_r_3726_);
v___x_3727_ = lean_unsigned_to_nat(3u);
v___x_3728_ = lean_nat_mul(v___x_3727_, v_size_3721_);
v___x_3729_ = lean_nat_dec_lt(v___x_3728_, v_size_3722_);
lean_dec(v___x_3728_);
if (v___x_3729_ == 0)
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3733_; 
lean_dec(v_r_3726_);
lean_dec(v_l_3725_);
lean_dec(v_v_3724_);
lean_dec(v_k_3723_);
v___x_3730_ = lean_nat_add(v___x_3720_, v_size_3722_);
lean_dec(v_size_3722_);
v___x_3731_ = lean_nat_add(v___x_3730_, v_size_3721_);
lean_dec(v___x_3730_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 3, v_impl_3719_);
lean_ctor_set(v___x_3716_, 0, v___x_3731_);
v___x_3733_ = v___x_3716_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3734_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3734_, 3, v_impl_3719_);
lean_ctor_set(v_reuseFailAlloc_3734_, 4, v_r_3714_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
else
{
lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3800_; 
v_isSharedCheck_3800_ = !lean_is_exclusive(v_impl_3719_);
if (v_isSharedCheck_3800_ == 0)
{
lean_object* v_unused_3801_; lean_object* v_unused_3802_; lean_object* v_unused_3803_; lean_object* v_unused_3804_; lean_object* v_unused_3805_; 
v_unused_3801_ = lean_ctor_get(v_impl_3719_, 4);
lean_dec(v_unused_3801_);
v_unused_3802_ = lean_ctor_get(v_impl_3719_, 3);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_impl_3719_, 2);
lean_dec(v_unused_3803_);
v_unused_3804_ = lean_ctor_get(v_impl_3719_, 1);
lean_dec(v_unused_3804_);
v_unused_3805_ = lean_ctor_get(v_impl_3719_, 0);
lean_dec(v_unused_3805_);
v___x_3736_ = v_impl_3719_;
v_isShared_3737_ = v_isSharedCheck_3800_;
goto v_resetjp_3735_;
}
else
{
lean_dec(v_impl_3719_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3800_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v_size_3738_; lean_object* v_size_3739_; lean_object* v_k_3740_; lean_object* v_v_3741_; lean_object* v_l_3742_; lean_object* v_r_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; uint8_t v___x_3746_; 
v_size_3738_ = lean_ctor_get(v_l_3725_, 0);
v_size_3739_ = lean_ctor_get(v_r_3726_, 0);
v_k_3740_ = lean_ctor_get(v_r_3726_, 1);
v_v_3741_ = lean_ctor_get(v_r_3726_, 2);
v_l_3742_ = lean_ctor_get(v_r_3726_, 3);
v_r_3743_ = lean_ctor_get(v_r_3726_, 4);
v___x_3744_ = lean_unsigned_to_nat(2u);
v___x_3745_ = lean_nat_mul(v___x_3744_, v_size_3738_);
v___x_3746_ = lean_nat_dec_lt(v_size_3739_, v___x_3745_);
lean_dec(v___x_3745_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3775_; 
lean_inc(v_r_3743_);
lean_inc(v_l_3742_);
lean_inc(v_v_3741_);
lean_inc(v_k_3740_);
v_isSharedCheck_3775_ = !lean_is_exclusive(v_r_3726_);
if (v_isSharedCheck_3775_ == 0)
{
lean_object* v_unused_3776_; lean_object* v_unused_3777_; lean_object* v_unused_3778_; lean_object* v_unused_3779_; lean_object* v_unused_3780_; 
v_unused_3776_ = lean_ctor_get(v_r_3726_, 4);
lean_dec(v_unused_3776_);
v_unused_3777_ = lean_ctor_get(v_r_3726_, 3);
lean_dec(v_unused_3777_);
v_unused_3778_ = lean_ctor_get(v_r_3726_, 2);
lean_dec(v_unused_3778_);
v_unused_3779_ = lean_ctor_get(v_r_3726_, 1);
lean_dec(v_unused_3779_);
v_unused_3780_ = lean_ctor_get(v_r_3726_, 0);
lean_dec(v_unused_3780_);
v___x_3748_ = v_r_3726_;
v_isShared_3749_ = v_isSharedCheck_3775_;
goto v_resetjp_3747_;
}
else
{
lean_dec(v_r_3726_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3775_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___x_3763_; lean_object* v___y_3765_; 
v___x_3750_ = lean_nat_add(v___x_3720_, v_size_3722_);
lean_dec(v_size_3722_);
v___x_3751_ = lean_nat_add(v___x_3750_, v_size_3721_);
lean_dec(v___x_3750_);
v___x_3763_ = lean_nat_add(v___x_3720_, v_size_3738_);
if (lean_obj_tag(v_l_3742_) == 0)
{
lean_object* v_size_3773_; 
v_size_3773_ = lean_ctor_get(v_l_3742_, 0);
lean_inc(v_size_3773_);
v___y_3765_ = v_size_3773_;
goto v___jp_3764_;
}
else
{
lean_object* v___x_3774_; 
v___x_3774_ = lean_unsigned_to_nat(0u);
v___y_3765_ = v___x_3774_;
goto v___jp_3764_;
}
v___jp_3752_:
{
lean_object* v___x_3756_; lean_object* v___x_3758_; 
v___x_3756_ = lean_nat_add(v___y_3754_, v___y_3755_);
lean_dec(v___y_3755_);
lean_dec(v___y_3754_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 4, v_r_3714_);
lean_ctor_set(v___x_3748_, 3, v_r_3743_);
lean_ctor_set(v___x_3748_, 2, v_v_3712_);
lean_ctor_set(v___x_3748_, 1, v_k_3711_);
lean_ctor_set(v___x_3748_, 0, v___x_3756_);
v___x_3758_ = v___x_3748_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3756_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_r_3743_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v_r_3714_);
v___x_3758_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3760_; 
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 4, v___x_3758_);
lean_ctor_set(v___x_3736_, 3, v___y_3753_);
lean_ctor_set(v___x_3736_, 2, v_v_3741_);
lean_ctor_set(v___x_3736_, 1, v_k_3740_);
lean_ctor_set(v___x_3736_, 0, v___x_3751_);
v___x_3760_ = v___x_3736_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3751_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_k_3740_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v_v_3741_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v___y_3753_);
lean_ctor_set(v_reuseFailAlloc_3761_, 4, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
v___jp_3764_:
{
lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3766_ = lean_nat_add(v___x_3763_, v___y_3765_);
lean_dec(v___y_3765_);
lean_dec(v___x_3763_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 4, v_l_3742_);
lean_ctor_set(v___x_3716_, 3, v_l_3725_);
lean_ctor_set(v___x_3716_, 2, v_v_3724_);
lean_ctor_set(v___x_3716_, 1, v_k_3723_);
lean_ctor_set(v___x_3716_, 0, v___x_3766_);
v___x_3768_ = v___x_3716_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3766_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_k_3723_);
lean_ctor_set(v_reuseFailAlloc_3772_, 2, v_v_3724_);
lean_ctor_set(v_reuseFailAlloc_3772_, 3, v_l_3725_);
lean_ctor_set(v_reuseFailAlloc_3772_, 4, v_l_3742_);
v___x_3768_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3769_; 
v___x_3769_ = lean_nat_add(v___x_3720_, v_size_3721_);
if (lean_obj_tag(v_r_3743_) == 0)
{
lean_object* v_size_3770_; 
v_size_3770_ = lean_ctor_get(v_r_3743_, 0);
lean_inc(v_size_3770_);
v___y_3753_ = v___x_3768_;
v___y_3754_ = v___x_3769_;
v___y_3755_ = v_size_3770_;
goto v___jp_3752_;
}
else
{
lean_object* v___x_3771_; 
v___x_3771_ = lean_unsigned_to_nat(0u);
v___y_3753_ = v___x_3768_;
v___y_3754_ = v___x_3769_;
v___y_3755_ = v___x_3771_;
goto v___jp_3752_;
}
}
}
}
}
else
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3786_; 
lean_del_object(v___x_3716_);
v___x_3781_ = lean_nat_add(v___x_3720_, v_size_3722_);
lean_dec(v_size_3722_);
v___x_3782_ = lean_nat_add(v___x_3781_, v_size_3721_);
lean_dec(v___x_3781_);
v___x_3783_ = lean_nat_add(v___x_3720_, v_size_3721_);
v___x_3784_ = lean_nat_add(v___x_3783_, v_size_3739_);
lean_dec(v___x_3783_);
lean_inc_ref(v_r_3714_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 4, v_r_3714_);
lean_ctor_set(v___x_3736_, 3, v_r_3726_);
lean_ctor_set(v___x_3736_, 2, v_v_3712_);
lean_ctor_set(v___x_3736_, 1, v_k_3711_);
lean_ctor_set(v___x_3736_, 0, v___x_3784_);
v___x_3786_ = v___x_3736_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3784_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3799_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3799_, 3, v_r_3726_);
lean_ctor_set(v_reuseFailAlloc_3799_, 4, v_r_3714_);
v___x_3786_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
v_isSharedCheck_3793_ = !lean_is_exclusive(v_r_3714_);
if (v_isSharedCheck_3793_ == 0)
{
lean_object* v_unused_3794_; lean_object* v_unused_3795_; lean_object* v_unused_3796_; lean_object* v_unused_3797_; lean_object* v_unused_3798_; 
v_unused_3794_ = lean_ctor_get(v_r_3714_, 4);
lean_dec(v_unused_3794_);
v_unused_3795_ = lean_ctor_get(v_r_3714_, 3);
lean_dec(v_unused_3795_);
v_unused_3796_ = lean_ctor_get(v_r_3714_, 2);
lean_dec(v_unused_3796_);
v_unused_3797_ = lean_ctor_get(v_r_3714_, 1);
lean_dec(v_unused_3797_);
v_unused_3798_ = lean_ctor_get(v_r_3714_, 0);
lean_dec(v_unused_3798_);
v___x_3788_ = v_r_3714_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_dec(v_r_3714_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 4, v___x_3786_);
lean_ctor_set(v___x_3788_, 3, v_l_3725_);
lean_ctor_set(v___x_3788_, 2, v_v_3724_);
lean_ctor_set(v___x_3788_, 1, v_k_3723_);
lean_ctor_set(v___x_3788_, 0, v___x_3782_);
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3792_, 1, v_k_3723_);
lean_ctor_set(v_reuseFailAlloc_3792_, 2, v_v_3724_);
lean_ctor_set(v_reuseFailAlloc_3792_, 3, v_l_3725_);
lean_ctor_set(v_reuseFailAlloc_3792_, 4, v___x_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3806_; 
v_l_3806_ = lean_ctor_get(v_impl_3719_, 3);
lean_inc(v_l_3806_);
if (lean_obj_tag(v_l_3806_) == 0)
{
lean_object* v_r_3807_; lean_object* v_k_3808_; lean_object* v_v_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3820_; 
v_r_3807_ = lean_ctor_get(v_impl_3719_, 4);
v_k_3808_ = lean_ctor_get(v_impl_3719_, 1);
v_v_3809_ = lean_ctor_get(v_impl_3719_, 2);
v_isSharedCheck_3820_ = !lean_is_exclusive(v_impl_3719_);
if (v_isSharedCheck_3820_ == 0)
{
lean_object* v_unused_3821_; lean_object* v_unused_3822_; 
v_unused_3821_ = lean_ctor_get(v_impl_3719_, 3);
lean_dec(v_unused_3821_);
v_unused_3822_ = lean_ctor_get(v_impl_3719_, 0);
lean_dec(v_unused_3822_);
v___x_3811_ = v_impl_3719_;
v_isShared_3812_ = v_isSharedCheck_3820_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_r_3807_);
lean_inc(v_v_3809_);
lean_inc(v_k_3808_);
lean_dec(v_impl_3719_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3820_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3813_; lean_object* v___x_3815_; 
v___x_3813_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3807_);
if (v_isShared_3812_ == 0)
{
lean_ctor_set(v___x_3811_, 3, v_r_3807_);
lean_ctor_set(v___x_3811_, 2, v_v_3712_);
lean_ctor_set(v___x_3811_, 1, v_k_3711_);
lean_ctor_set(v___x_3811_, 0, v___x_3720_);
v___x_3815_ = v___x_3811_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3819_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3819_, 3, v_r_3807_);
lean_ctor_set(v_reuseFailAlloc_3819_, 4, v_r_3807_);
v___x_3815_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
lean_object* v___x_3817_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 4, v___x_3815_);
lean_ctor_set(v___x_3716_, 3, v_l_3806_);
lean_ctor_set(v___x_3716_, 2, v_v_3809_);
lean_ctor_set(v___x_3716_, 1, v_k_3808_);
lean_ctor_set(v___x_3716_, 0, v___x_3813_);
v___x_3817_ = v___x_3716_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_k_3808_);
lean_ctor_set(v_reuseFailAlloc_3818_, 2, v_v_3809_);
lean_ctor_set(v_reuseFailAlloc_3818_, 3, v_l_3806_);
lean_ctor_set(v_reuseFailAlloc_3818_, 4, v___x_3815_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
else
{
lean_object* v_r_3823_; 
v_r_3823_ = lean_ctor_get(v_impl_3719_, 4);
lean_inc(v_r_3823_);
if (lean_obj_tag(v_r_3823_) == 0)
{
lean_object* v_k_3824_; lean_object* v_v_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3848_; 
v_k_3824_ = lean_ctor_get(v_impl_3719_, 1);
v_v_3825_ = lean_ctor_get(v_impl_3719_, 2);
v_isSharedCheck_3848_ = !lean_is_exclusive(v_impl_3719_);
if (v_isSharedCheck_3848_ == 0)
{
lean_object* v_unused_3849_; lean_object* v_unused_3850_; lean_object* v_unused_3851_; 
v_unused_3849_ = lean_ctor_get(v_impl_3719_, 4);
lean_dec(v_unused_3849_);
v_unused_3850_ = lean_ctor_get(v_impl_3719_, 3);
lean_dec(v_unused_3850_);
v_unused_3851_ = lean_ctor_get(v_impl_3719_, 0);
lean_dec(v_unused_3851_);
v___x_3827_ = v_impl_3719_;
v_isShared_3828_ = v_isSharedCheck_3848_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_v_3825_);
lean_inc(v_k_3824_);
lean_dec(v_impl_3719_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3848_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v_k_3829_; lean_object* v_v_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3844_; 
v_k_3829_ = lean_ctor_get(v_r_3823_, 1);
v_v_3830_ = lean_ctor_get(v_r_3823_, 2);
v_isSharedCheck_3844_ = !lean_is_exclusive(v_r_3823_);
if (v_isSharedCheck_3844_ == 0)
{
lean_object* v_unused_3845_; lean_object* v_unused_3846_; lean_object* v_unused_3847_; 
v_unused_3845_ = lean_ctor_get(v_r_3823_, 4);
lean_dec(v_unused_3845_);
v_unused_3846_ = lean_ctor_get(v_r_3823_, 3);
lean_dec(v_unused_3846_);
v_unused_3847_ = lean_ctor_get(v_r_3823_, 0);
lean_dec(v_unused_3847_);
v___x_3832_ = v_r_3823_;
v_isShared_3833_ = v_isSharedCheck_3844_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_v_3830_);
lean_inc(v_k_3829_);
lean_dec(v_r_3823_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3844_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3834_; lean_object* v___x_3836_; 
v___x_3834_ = lean_unsigned_to_nat(3u);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 4, v_l_3806_);
lean_ctor_set(v___x_3832_, 3, v_l_3806_);
lean_ctor_set(v___x_3832_, 2, v_v_3825_);
lean_ctor_set(v___x_3832_, 1, v_k_3824_);
lean_ctor_set(v___x_3832_, 0, v___x_3720_);
v___x_3836_ = v___x_3832_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_k_3824_);
lean_ctor_set(v_reuseFailAlloc_3843_, 2, v_v_3825_);
lean_ctor_set(v_reuseFailAlloc_3843_, 3, v_l_3806_);
lean_ctor_set(v_reuseFailAlloc_3843_, 4, v_l_3806_);
v___x_3836_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v___x_3838_; 
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 4, v_l_3806_);
lean_ctor_set(v___x_3827_, 2, v_v_3712_);
lean_ctor_set(v___x_3827_, 1, v_k_3711_);
lean_ctor_set(v___x_3827_, 0, v___x_3720_);
v___x_3838_ = v___x_3827_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3842_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3842_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3842_, 3, v_l_3806_);
lean_ctor_set(v_reuseFailAlloc_3842_, 4, v_l_3806_);
v___x_3838_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3840_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 4, v___x_3838_);
lean_ctor_set(v___x_3716_, 3, v___x_3836_);
lean_ctor_set(v___x_3716_, 2, v_v_3830_);
lean_ctor_set(v___x_3716_, 1, v_k_3829_);
lean_ctor_set(v___x_3716_, 0, v___x_3834_);
v___x_3840_ = v___x_3716_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3834_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v_k_3829_);
lean_ctor_set(v_reuseFailAlloc_3841_, 2, v_v_3830_);
lean_ctor_set(v_reuseFailAlloc_3841_, 3, v___x_3836_);
lean_ctor_set(v_reuseFailAlloc_3841_, 4, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
}
else
{
lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3852_ = lean_unsigned_to_nat(2u);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 4, v_r_3823_);
lean_ctor_set(v___x_3716_, 3, v_impl_3719_);
lean_ctor_set(v___x_3716_, 0, v___x_3852_);
v___x_3854_ = v___x_3716_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3855_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3855_, 3, v_impl_3719_);
lean_ctor_set(v_reuseFailAlloc_3855_, 4, v_r_3823_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3857_; 
lean_dec(v_v_3712_);
lean_dec(v_k_3711_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 2, v_v_3708_);
lean_ctor_set(v___x_3716_, 1, v_k_3707_);
v___x_3857_ = v___x_3716_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_size_3710_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v_k_3707_);
lean_ctor_set(v_reuseFailAlloc_3858_, 2, v_v_3708_);
lean_ctor_set(v_reuseFailAlloc_3858_, 3, v_l_3713_);
lean_ctor_set(v_reuseFailAlloc_3858_, 4, v_r_3714_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
default: 
{
lean_object* v_impl_3859_; lean_object* v___x_3860_; 
lean_dec(v_size_3710_);
v_impl_3859_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3707_, v_v_3708_, v_r_3714_);
v___x_3860_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3713_) == 0)
{
lean_object* v_size_3861_; lean_object* v_size_3862_; lean_object* v_k_3863_; lean_object* v_v_3864_; lean_object* v_l_3865_; lean_object* v_r_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; 
v_size_3861_ = lean_ctor_get(v_l_3713_, 0);
v_size_3862_ = lean_ctor_get(v_impl_3859_, 0);
lean_inc(v_size_3862_);
v_k_3863_ = lean_ctor_get(v_impl_3859_, 1);
lean_inc(v_k_3863_);
v_v_3864_ = lean_ctor_get(v_impl_3859_, 2);
lean_inc(v_v_3864_);
v_l_3865_ = lean_ctor_get(v_impl_3859_, 3);
lean_inc(v_l_3865_);
v_r_3866_ = lean_ctor_get(v_impl_3859_, 4);
lean_inc(v_r_3866_);
v___x_3867_ = lean_unsigned_to_nat(3u);
v___x_3868_ = lean_nat_mul(v___x_3867_, v_size_3861_);
v___x_3869_ = lean_nat_dec_lt(v___x_3868_, v_size_3862_);
lean_dec(v___x_3868_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3873_; 
lean_dec(v_r_3866_);
lean_dec(v_l_3865_);
lean_dec(v_v_3864_);
lean_dec(v_k_3863_);
v___x_3870_ = lean_nat_add(v___x_3860_, v_size_3861_);
v___x_3871_ = lean_nat_add(v___x_3870_, v_size_3862_);
lean_dec(v_size_3862_);
lean_dec(v___x_3870_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 4, v_impl_3859_);
lean_ctor_set(v___x_3716_, 0, v___x_3871_);
v___x_3873_ = v___x_3716_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3871_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3874_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3874_, 3, v_l_3713_);
lean_ctor_set(v_reuseFailAlloc_3874_, 4, v_impl_3859_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
else
{
lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3938_; 
v_isSharedCheck_3938_ = !lean_is_exclusive(v_impl_3859_);
if (v_isSharedCheck_3938_ == 0)
{
lean_object* v_unused_3939_; lean_object* v_unused_3940_; lean_object* v_unused_3941_; lean_object* v_unused_3942_; lean_object* v_unused_3943_; 
v_unused_3939_ = lean_ctor_get(v_impl_3859_, 4);
lean_dec(v_unused_3939_);
v_unused_3940_ = lean_ctor_get(v_impl_3859_, 3);
lean_dec(v_unused_3940_);
v_unused_3941_ = lean_ctor_get(v_impl_3859_, 2);
lean_dec(v_unused_3941_);
v_unused_3942_ = lean_ctor_get(v_impl_3859_, 1);
lean_dec(v_unused_3942_);
v_unused_3943_ = lean_ctor_get(v_impl_3859_, 0);
lean_dec(v_unused_3943_);
v___x_3876_ = v_impl_3859_;
v_isShared_3877_ = v_isSharedCheck_3938_;
goto v_resetjp_3875_;
}
else
{
lean_dec(v_impl_3859_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3938_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v_size_3878_; lean_object* v_k_3879_; lean_object* v_v_3880_; lean_object* v_l_3881_; lean_object* v_r_3882_; lean_object* v_size_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; uint8_t v___x_3886_; 
v_size_3878_ = lean_ctor_get(v_l_3865_, 0);
v_k_3879_ = lean_ctor_get(v_l_3865_, 1);
v_v_3880_ = lean_ctor_get(v_l_3865_, 2);
v_l_3881_ = lean_ctor_get(v_l_3865_, 3);
v_r_3882_ = lean_ctor_get(v_l_3865_, 4);
v_size_3883_ = lean_ctor_get(v_r_3866_, 0);
v___x_3884_ = lean_unsigned_to_nat(2u);
v___x_3885_ = lean_nat_mul(v___x_3884_, v_size_3883_);
v___x_3886_ = lean_nat_dec_lt(v_size_3878_, v___x_3885_);
lean_dec(v___x_3885_);
if (v___x_3886_ == 0)
{
lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3914_; 
lean_inc(v_r_3882_);
lean_inc(v_l_3881_);
lean_inc(v_v_3880_);
lean_inc(v_k_3879_);
v_isSharedCheck_3914_ = !lean_is_exclusive(v_l_3865_);
if (v_isSharedCheck_3914_ == 0)
{
lean_object* v_unused_3915_; lean_object* v_unused_3916_; lean_object* v_unused_3917_; lean_object* v_unused_3918_; lean_object* v_unused_3919_; 
v_unused_3915_ = lean_ctor_get(v_l_3865_, 4);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_l_3865_, 3);
lean_dec(v_unused_3916_);
v_unused_3917_ = lean_ctor_get(v_l_3865_, 2);
lean_dec(v_unused_3917_);
v_unused_3918_ = lean_ctor_get(v_l_3865_, 1);
lean_dec(v_unused_3918_);
v_unused_3919_ = lean_ctor_get(v_l_3865_, 0);
lean_dec(v_unused_3919_);
v___x_3888_ = v_l_3865_;
v_isShared_3889_ = v_isSharedCheck_3914_;
goto v_resetjp_3887_;
}
else
{
lean_dec(v_l_3865_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3914_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3904_; 
v___x_3890_ = lean_nat_add(v___x_3860_, v_size_3861_);
v___x_3891_ = lean_nat_add(v___x_3890_, v_size_3862_);
lean_dec(v_size_3862_);
if (lean_obj_tag(v_l_3881_) == 0)
{
lean_object* v_size_3912_; 
v_size_3912_ = lean_ctor_get(v_l_3881_, 0);
lean_inc(v_size_3912_);
v___y_3904_ = v_size_3912_;
goto v___jp_3903_;
}
else
{
lean_object* v___x_3913_; 
v___x_3913_ = lean_unsigned_to_nat(0u);
v___y_3904_ = v___x_3913_;
goto v___jp_3903_;
}
v___jp_3892_:
{
lean_object* v___x_3896_; lean_object* v___x_3898_; 
v___x_3896_ = lean_nat_add(v___y_3893_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec(v___y_3893_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 4, v_r_3866_);
lean_ctor_set(v___x_3888_, 3, v_r_3882_);
lean_ctor_set(v___x_3888_, 2, v_v_3864_);
lean_ctor_set(v___x_3888_, 1, v_k_3863_);
lean_ctor_set(v___x_3888_, 0, v___x_3896_);
v___x_3898_ = v___x_3888_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v_k_3863_);
lean_ctor_set(v_reuseFailAlloc_3902_, 2, v_v_3864_);
lean_ctor_set(v_reuseFailAlloc_3902_, 3, v_r_3882_);
lean_ctor_set(v_reuseFailAlloc_3902_, 4, v_r_3866_);
v___x_3898_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
lean_object* v___x_3900_; 
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 4, v___x_3898_);
lean_ctor_set(v___x_3876_, 3, v___y_3894_);
lean_ctor_set(v___x_3876_, 2, v_v_3880_);
lean_ctor_set(v___x_3876_, 1, v_k_3879_);
lean_ctor_set(v___x_3876_, 0, v___x_3891_);
v___x_3900_ = v___x_3876_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v_k_3879_);
lean_ctor_set(v_reuseFailAlloc_3901_, 2, v_v_3880_);
lean_ctor_set(v_reuseFailAlloc_3901_, 3, v___y_3894_);
lean_ctor_set(v_reuseFailAlloc_3901_, 4, v___x_3898_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
v___jp_3903_:
{
lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3905_ = lean_nat_add(v___x_3890_, v___y_3904_);
lean_dec(v___y_3904_);
lean_dec(v___x_3890_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 4, v_l_3881_);
lean_ctor_set(v___x_3716_, 0, v___x_3905_);
v___x_3907_ = v___x_3716_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_l_3713_);
lean_ctor_set(v_reuseFailAlloc_3911_, 4, v_l_3881_);
v___x_3907_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3908_; 
v___x_3908_ = lean_nat_add(v___x_3860_, v_size_3883_);
if (lean_obj_tag(v_r_3882_) == 0)
{
lean_object* v_size_3909_; 
v_size_3909_ = lean_ctor_get(v_r_3882_, 0);
lean_inc(v_size_3909_);
v___y_3893_ = v___x_3908_;
v___y_3894_ = v___x_3907_;
v___y_3895_ = v_size_3909_;
goto v___jp_3892_;
}
else
{
lean_object* v___x_3910_; 
v___x_3910_ = lean_unsigned_to_nat(0u);
v___y_3893_ = v___x_3908_;
v___y_3894_ = v___x_3907_;
v___y_3895_ = v___x_3910_;
goto v___jp_3892_;
}
}
}
}
}
else
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3924_; 
lean_del_object(v___x_3716_);
v___x_3920_ = lean_nat_add(v___x_3860_, v_size_3861_);
v___x_3921_ = lean_nat_add(v___x_3920_, v_size_3862_);
lean_dec(v_size_3862_);
v___x_3922_ = lean_nat_add(v___x_3920_, v_size_3878_);
lean_dec(v___x_3920_);
lean_inc_ref(v_l_3713_);
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 4, v_l_3865_);
lean_ctor_set(v___x_3876_, 3, v_l_3713_);
lean_ctor_set(v___x_3876_, 2, v_v_3712_);
lean_ctor_set(v___x_3876_, 1, v_k_3711_);
lean_ctor_set(v___x_3876_, 0, v___x_3922_);
v___x_3924_ = v___x_3876_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3922_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3937_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3937_, 3, v_l_3713_);
lean_ctor_set(v_reuseFailAlloc_3937_, 4, v_l_3865_);
v___x_3924_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
v_isSharedCheck_3931_ = !lean_is_exclusive(v_l_3713_);
if (v_isSharedCheck_3931_ == 0)
{
lean_object* v_unused_3932_; lean_object* v_unused_3933_; lean_object* v_unused_3934_; lean_object* v_unused_3935_; lean_object* v_unused_3936_; 
v_unused_3932_ = lean_ctor_get(v_l_3713_, 4);
lean_dec(v_unused_3932_);
v_unused_3933_ = lean_ctor_get(v_l_3713_, 3);
lean_dec(v_unused_3933_);
v_unused_3934_ = lean_ctor_get(v_l_3713_, 2);
lean_dec(v_unused_3934_);
v_unused_3935_ = lean_ctor_get(v_l_3713_, 1);
lean_dec(v_unused_3935_);
v_unused_3936_ = lean_ctor_get(v_l_3713_, 0);
lean_dec(v_unused_3936_);
v___x_3926_ = v_l_3713_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_dec(v_l_3713_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 4, v_r_3866_);
lean_ctor_set(v___x_3926_, 3, v___x_3924_);
lean_ctor_set(v___x_3926_, 2, v_v_3864_);
lean_ctor_set(v___x_3926_, 1, v_k_3863_);
lean_ctor_set(v___x_3926_, 0, v___x_3921_);
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3921_);
lean_ctor_set(v_reuseFailAlloc_3930_, 1, v_k_3863_);
lean_ctor_set(v_reuseFailAlloc_3930_, 2, v_v_3864_);
lean_ctor_set(v_reuseFailAlloc_3930_, 3, v___x_3924_);
lean_ctor_set(v_reuseFailAlloc_3930_, 4, v_r_3866_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3944_; 
v_l_3944_ = lean_ctor_get(v_impl_3859_, 3);
lean_inc(v_l_3944_);
if (lean_obj_tag(v_l_3944_) == 0)
{
lean_object* v_r_3945_; lean_object* v_k_3946_; lean_object* v_v_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3970_; 
v_r_3945_ = lean_ctor_get(v_impl_3859_, 4);
v_k_3946_ = lean_ctor_get(v_impl_3859_, 1);
v_v_3947_ = lean_ctor_get(v_impl_3859_, 2);
v_isSharedCheck_3970_ = !lean_is_exclusive(v_impl_3859_);
if (v_isSharedCheck_3970_ == 0)
{
lean_object* v_unused_3971_; lean_object* v_unused_3972_; 
v_unused_3971_ = lean_ctor_get(v_impl_3859_, 3);
lean_dec(v_unused_3971_);
v_unused_3972_ = lean_ctor_get(v_impl_3859_, 0);
lean_dec(v_unused_3972_);
v___x_3949_ = v_impl_3859_;
v_isShared_3950_ = v_isSharedCheck_3970_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_r_3945_);
lean_inc(v_v_3947_);
lean_inc(v_k_3946_);
lean_dec(v_impl_3859_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3970_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v_k_3951_; lean_object* v_v_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3966_; 
v_k_3951_ = lean_ctor_get(v_l_3944_, 1);
v_v_3952_ = lean_ctor_get(v_l_3944_, 2);
v_isSharedCheck_3966_ = !lean_is_exclusive(v_l_3944_);
if (v_isSharedCheck_3966_ == 0)
{
lean_object* v_unused_3967_; lean_object* v_unused_3968_; lean_object* v_unused_3969_; 
v_unused_3967_ = lean_ctor_get(v_l_3944_, 4);
lean_dec(v_unused_3967_);
v_unused_3968_ = lean_ctor_get(v_l_3944_, 3);
lean_dec(v_unused_3968_);
v_unused_3969_ = lean_ctor_get(v_l_3944_, 0);
lean_dec(v_unused_3969_);
v___x_3954_ = v_l_3944_;
v_isShared_3955_ = v_isSharedCheck_3966_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_v_3952_);
lean_inc(v_k_3951_);
lean_dec(v_l_3944_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3966_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v___x_3958_; 
v___x_3956_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3945_, 2);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 4, v_r_3945_);
lean_ctor_set(v___x_3954_, 3, v_r_3945_);
lean_ctor_set(v___x_3954_, 2, v_v_3712_);
lean_ctor_set(v___x_3954_, 1, v_k_3711_);
lean_ctor_set(v___x_3954_, 0, v___x_3860_);
v___x_3958_ = v___x_3954_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3860_);
lean_ctor_set(v_reuseFailAlloc_3965_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3965_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3965_, 3, v_r_3945_);
lean_ctor_set(v_reuseFailAlloc_3965_, 4, v_r_3945_);
v___x_3958_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
lean_object* v___x_3960_; 
lean_inc(v_r_3945_);
if (v_isShared_3950_ == 0)
{
lean_ctor_set(v___x_3949_, 3, v_r_3945_);
lean_ctor_set(v___x_3949_, 0, v___x_3860_);
v___x_3960_ = v___x_3949_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3860_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_k_3946_);
lean_ctor_set(v_reuseFailAlloc_3964_, 2, v_v_3947_);
lean_ctor_set(v_reuseFailAlloc_3964_, 3, v_r_3945_);
lean_ctor_set(v_reuseFailAlloc_3964_, 4, v_r_3945_);
v___x_3960_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
lean_object* v___x_3962_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 4, v___x_3960_);
lean_ctor_set(v___x_3716_, 3, v___x_3958_);
lean_ctor_set(v___x_3716_, 2, v_v_3952_);
lean_ctor_set(v___x_3716_, 1, v_k_3951_);
lean_ctor_set(v___x_3716_, 0, v___x_3956_);
v___x_3962_ = v___x_3716_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v___x_3956_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v_k_3951_);
lean_ctor_set(v_reuseFailAlloc_3963_, 2, v_v_3952_);
lean_ctor_set(v_reuseFailAlloc_3963_, 3, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_3963_, 4, v___x_3960_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
}
}
else
{
lean_object* v_r_3973_; 
v_r_3973_ = lean_ctor_get(v_impl_3859_, 4);
lean_inc(v_r_3973_);
if (lean_obj_tag(v_r_3973_) == 0)
{
lean_object* v_k_3974_; lean_object* v_v_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3986_; 
v_k_3974_ = lean_ctor_get(v_impl_3859_, 1);
v_v_3975_ = lean_ctor_get(v_impl_3859_, 2);
v_isSharedCheck_3986_ = !lean_is_exclusive(v_impl_3859_);
if (v_isSharedCheck_3986_ == 0)
{
lean_object* v_unused_3987_; lean_object* v_unused_3988_; lean_object* v_unused_3989_; 
v_unused_3987_ = lean_ctor_get(v_impl_3859_, 4);
lean_dec(v_unused_3987_);
v_unused_3988_ = lean_ctor_get(v_impl_3859_, 3);
lean_dec(v_unused_3988_);
v_unused_3989_ = lean_ctor_get(v_impl_3859_, 0);
lean_dec(v_unused_3989_);
v___x_3977_ = v_impl_3859_;
v_isShared_3978_ = v_isSharedCheck_3986_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_v_3975_);
lean_inc(v_k_3974_);
lean_dec(v_impl_3859_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3986_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3979_; lean_object* v___x_3981_; 
v___x_3979_ = lean_unsigned_to_nat(3u);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 4, v_l_3944_);
lean_ctor_set(v___x_3977_, 2, v_v_3712_);
lean_ctor_set(v___x_3977_, 1, v_k_3711_);
lean_ctor_set(v___x_3977_, 0, v___x_3860_);
v___x_3981_ = v___x_3977_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3860_);
lean_ctor_set(v_reuseFailAlloc_3985_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3985_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3985_, 3, v_l_3944_);
lean_ctor_set(v_reuseFailAlloc_3985_, 4, v_l_3944_);
v___x_3981_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
lean_object* v___x_3983_; 
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 4, v_r_3973_);
lean_ctor_set(v___x_3716_, 3, v___x_3981_);
lean_ctor_set(v___x_3716_, 2, v_v_3975_);
lean_ctor_set(v___x_3716_, 1, v_k_3974_);
lean_ctor_set(v___x_3716_, 0, v___x_3979_);
v___x_3983_ = v___x_3716_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3979_);
lean_ctor_set(v_reuseFailAlloc_3984_, 1, v_k_3974_);
lean_ctor_set(v_reuseFailAlloc_3984_, 2, v_v_3975_);
lean_ctor_set(v_reuseFailAlloc_3984_, 3, v___x_3981_);
lean_ctor_set(v_reuseFailAlloc_3984_, 4, v_r_3973_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3992_; 
v___x_3990_ = lean_unsigned_to_nat(2u);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 4, v_impl_3859_);
lean_ctor_set(v___x_3716_, 3, v_r_3973_);
lean_ctor_set(v___x_3716_, 0, v___x_3990_);
v___x_3992_ = v___x_3716_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3990_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3993_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3993_, 3, v_r_3973_);
lean_ctor_set(v_reuseFailAlloc_3993_, 4, v_impl_3859_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
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
lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = lean_unsigned_to_nat(1u);
v___x_3996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3995_);
lean_ctor_set(v___x_3996_, 1, v_k_3707_);
lean_ctor_set(v___x_3996_, 2, v_v_3708_);
lean_ctor_set(v___x_3996_, 3, v_t_3709_);
lean_ctor_set(v___x_3996_, 4, v_t_3709_);
return v___x_3996_;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3997_ = lean_box(1);
v___x_3998_ = l_Lake_LeanLib_defaultFacetConfig;
v___x_3999_ = l_Lake_LeanLib_defaultFacet;
v___x_4000_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3999_, v___x_3998_, v___x_3997_);
return v___x_4000_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4001_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__0, &l_Lake_LeanLib_initFacetConfigs___closed__0_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__0);
v___x_4002_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig));
v___x_4003_ = l_Lake_LeanLib_modulesFacet;
v___x_4004_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4003_, v___x_4002_, v___x_4001_);
return v___x_4004_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4005_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__1, &l_Lake_LeanLib_initFacetConfigs___closed__1_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__1);
v___x_4006_ = l_Lake_LeanLib_leanArtsFacetConfig;
v___x_4007_ = l_Lake_LeanLib_leanArtsFacet;
v___x_4008_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4007_, v___x_4006_, v___x_4005_);
return v___x_4008_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4009_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__2, &l_Lake_LeanLib_initFacetConfigs___closed__2_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__2);
v___x_4010_ = l_Lake_LeanLib_staticFacetConfig;
v___x_4011_ = l_Lake_LeanLib_staticFacet;
v___x_4012_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4011_, v___x_4010_, v___x_4009_);
return v___x_4012_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4013_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__3, &l_Lake_LeanLib_initFacetConfigs___closed__3_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__3);
v___x_4014_ = l_Lake_LeanLib_staticExportFacetConfig;
v___x_4015_ = l_Lake_LeanLib_staticExportFacet;
v___x_4016_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4015_, v___x_4014_, v___x_4013_);
return v___x_4016_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; 
v___x_4017_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__4, &l_Lake_LeanLib_initFacetConfigs___closed__4_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__4);
v___x_4018_ = l_Lake_LeanLib_sharedFacetConfig;
v___x_4019_ = l_Lake_LeanLib_sharedFacet;
v___x_4020_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4019_, v___x_4018_, v___x_4017_);
return v___x_4020_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4021_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__5, &l_Lake_LeanLib_initFacetConfigs___closed__5_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__5);
v___x_4022_ = l_Lake_LeanLib_extraDepFacetConfig;
v___x_4023_ = l_Lake_LeanLib_extraDepFacet;
v___x_4024_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4023_, v___x_4022_, v___x_4021_);
return v___x_4024_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_4025_; 
v___x_4025_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__6, &l_Lake_LeanLib_initFacetConfigs___closed__6_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__6);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_4026_, lean_object* v_k_4027_, lean_object* v_v_4028_, lean_object* v_t_4029_, lean_object* v_hl_4030_){
_start:
{
lean_object* v___x_4031_; 
v___x_4031_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_4027_, v_v_4028_, v_t_4029_);
return v___x_4031_;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs(void){
_start:
{
lean_object* v___x_4032_; 
v___x_4032_ = l_Lake_LeanLib_initFacetConfigs;
return v___x_4032_;
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
