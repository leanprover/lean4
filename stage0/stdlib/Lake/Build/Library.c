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
lean_object* l_Lake_buildLeanSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_14_, lean_object* v_x_15_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
return v_x_14_;
}
else
{
lean_object* v_key_16_; lean_object* v_value_17_; lean_object* v_tail_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_45_; 
v_key_16_ = lean_ctor_get(v_x_15_, 0);
v_value_17_ = lean_ctor_get(v_x_15_, 1);
v_tail_18_ = lean_ctor_get(v_x_15_, 2);
v_isSharedCheck_45_ = !lean_is_exclusive(v_x_15_);
if (v_isSharedCheck_45_ == 0)
{
v___x_20_ = v_x_15_;
v_isShared_21_ = v_isSharedCheck_45_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_tail_18_);
lean_inc(v_value_17_);
lean_inc(v_key_16_);
lean_dec(v_x_15_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_45_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v_name_22_; lean_object* v___x_23_; uint64_t v___y_25_; 
v_name_22_ = lean_ctor_get(v_key_16_, 1);
v___x_23_ = lean_array_get_size(v_x_14_);
if (lean_obj_tag(v_name_22_) == 0)
{
uint64_t v___x_43_; 
v___x_43_ = 1723ULL;
v___y_25_ = v___x_43_;
goto v___jp_24_;
}
else
{
uint64_t v_hash_44_; 
v_hash_44_ = lean_ctor_get_uint64(v_name_22_, sizeof(void*)*2);
v___y_25_ = v_hash_44_;
goto v___jp_24_;
}
v___jp_24_:
{
uint64_t v___x_26_; uint64_t v___x_27_; uint64_t v_fold_28_; uint64_t v___x_29_; uint64_t v___x_30_; uint64_t v___x_31_; size_t v___x_32_; size_t v___x_33_; size_t v___x_34_; size_t v___x_35_; size_t v___x_36_; lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_26_ = 32ULL;
v___x_27_ = lean_uint64_shift_right(v___y_25_, v___x_26_);
v_fold_28_ = lean_uint64_xor(v___y_25_, v___x_27_);
v___x_29_ = 16ULL;
v___x_30_ = lean_uint64_shift_right(v_fold_28_, v___x_29_);
v___x_31_ = lean_uint64_xor(v_fold_28_, v___x_30_);
v___x_32_ = lean_uint64_to_usize(v___x_31_);
v___x_33_ = lean_usize_of_nat(v___x_23_);
v___x_34_ = ((size_t)1ULL);
v___x_35_ = lean_usize_sub(v___x_33_, v___x_34_);
v___x_36_ = lean_usize_land(v___x_32_, v___x_35_);
v___x_37_ = lean_array_uget_borrowed(v_x_14_, v___x_36_);
lean_inc(v___x_37_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 2, v___x_37_);
v___x_39_ = v___x_20_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_key_16_);
lean_ctor_set(v_reuseFailAlloc_42_, 1, v_value_17_);
lean_ctor_set(v_reuseFailAlloc_42_, 2, v___x_37_);
v___x_39_ = v_reuseFailAlloc_42_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_40_; 
v___x_40_ = lean_array_uset(v_x_14_, v___x_36_, v___x_39_);
v_x_14_ = v___x_40_;
v_x_15_ = v_tail_18_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(lean_object* v_i_46_, lean_object* v_source_47_, lean_object* v_target_48_){
_start:
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_array_get_size(v_source_47_);
v___x_50_ = lean_nat_dec_lt(v_i_46_, v___x_49_);
if (v___x_50_ == 0)
{
lean_dec_ref(v_source_47_);
lean_dec(v_i_46_);
return v_target_48_;
}
else
{
lean_object* v_es_51_; lean_object* v___x_52_; lean_object* v_source_53_; lean_object* v_target_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_es_51_ = lean_array_fget(v_source_47_, v_i_46_);
v___x_52_ = lean_box(0);
v_source_53_ = lean_array_fset(v_source_47_, v_i_46_, v___x_52_);
v_target_54_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(v_target_48_, v_es_51_);
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = lean_nat_add(v_i_46_, v___x_55_);
lean_dec(v_i_46_);
v_i_46_ = v___x_56_;
v_source_47_ = v_source_53_;
v_target_48_ = v_target_54_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(lean_object* v_data_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_nbuckets_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_59_ = lean_array_get_size(v_data_58_);
v___x_60_ = lean_unsigned_to_nat(2u);
v_nbuckets_61_ = lean_nat_mul(v___x_59_, v___x_60_);
v___x_62_ = lean_unsigned_to_nat(0u);
v___x_63_ = lean_box(0);
v___x_64_ = lean_mk_array(v_nbuckets_61_, v___x_63_);
v___x_65_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(v___x_62_, v_data_58_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(lean_object* v_m_66_, lean_object* v_a_67_, lean_object* v_b_68_){
_start:
{
lean_object* v_size_69_; lean_object* v_buckets_70_; lean_object* v_name_71_; lean_object* v___x_72_; uint64_t v___y_74_; 
v_size_69_ = lean_ctor_get(v_m_66_, 0);
v_buckets_70_ = lean_ctor_get(v_m_66_, 1);
v_name_71_ = lean_ctor_get(v_a_67_, 1);
v___x_72_ = lean_array_get_size(v_buckets_70_);
if (lean_obj_tag(v_name_71_) == 0)
{
uint64_t v___x_111_; 
v___x_111_ = 1723ULL;
v___y_74_ = v___x_111_;
goto v___jp_73_;
}
else
{
uint64_t v_hash_112_; 
v_hash_112_ = lean_ctor_get_uint64(v_name_71_, sizeof(void*)*2);
v___y_74_ = v_hash_112_;
goto v___jp_73_;
}
v___jp_73_:
{
uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v_fold_77_; uint64_t v___x_78_; uint64_t v___x_79_; uint64_t v___x_80_; size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; lean_object* v_bkt_86_; uint8_t v___x_87_; 
v___x_75_ = 32ULL;
v___x_76_ = lean_uint64_shift_right(v___y_74_, v___x_75_);
v_fold_77_ = lean_uint64_xor(v___y_74_, v___x_76_);
v___x_78_ = 16ULL;
v___x_79_ = lean_uint64_shift_right(v_fold_77_, v___x_78_);
v___x_80_ = lean_uint64_xor(v_fold_77_, v___x_79_);
v___x_81_ = lean_uint64_to_usize(v___x_80_);
v___x_82_ = lean_usize_of_nat(v___x_72_);
v___x_83_ = ((size_t)1ULL);
v___x_84_ = lean_usize_sub(v___x_82_, v___x_83_);
v___x_85_ = lean_usize_land(v___x_81_, v___x_84_);
v_bkt_86_ = lean_array_uget_borrowed(v_buckets_70_, v___x_85_);
v___x_87_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_67_, v_bkt_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_108_; 
lean_inc_ref(v_buckets_70_);
lean_inc(v_size_69_);
v_isSharedCheck_108_ = !lean_is_exclusive(v_m_66_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; lean_object* v_unused_110_; 
v_unused_109_ = lean_ctor_get(v_m_66_, 1);
lean_dec(v_unused_109_);
v_unused_110_ = lean_ctor_get(v_m_66_, 0);
lean_dec(v_unused_110_);
v___x_89_ = v_m_66_;
v_isShared_90_ = v_isSharedCheck_108_;
goto v_resetjp_88_;
}
else
{
lean_dec(v_m_66_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_108_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v_size_x27_92_; lean_object* v___x_93_; lean_object* v_buckets_x27_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_91_ = lean_unsigned_to_nat(1u);
v_size_x27_92_ = lean_nat_add(v_size_69_, v___x_91_);
lean_dec(v_size_69_);
lean_inc(v_bkt_86_);
v___x_93_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_93_, 0, v_a_67_);
lean_ctor_set(v___x_93_, 1, v_b_68_);
lean_ctor_set(v___x_93_, 2, v_bkt_86_);
v_buckets_x27_94_ = lean_array_uset(v_buckets_70_, v___x_85_, v___x_93_);
v___x_95_ = lean_unsigned_to_nat(4u);
v___x_96_ = lean_nat_mul(v_size_x27_92_, v___x_95_);
v___x_97_ = lean_unsigned_to_nat(3u);
v___x_98_ = lean_nat_div(v___x_96_, v___x_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_array_get_size(v_buckets_x27_94_);
v___x_100_ = lean_nat_dec_le(v___x_98_, v___x_99_);
lean_dec(v___x_98_);
if (v___x_100_ == 0)
{
lean_object* v_val_101_; lean_object* v___x_103_; 
v_val_101_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(v_buckets_x27_94_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_val_101_);
lean_ctor_set(v___x_89_, 0, v_size_x27_92_);
v___x_103_ = v___x_89_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_size_x27_92_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_val_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
else
{
lean_object* v___x_106_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_buckets_x27_94_);
lean_ctor_set(v___x_89_, 0, v_size_x27_92_);
v___x_106_ = v___x_89_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_size_x27_92_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v_buckets_x27_94_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
else
{
lean_dec(v_b_68_);
lean_dec_ref(v_a_67_);
return v_m_66_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(lean_object* v_m_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_buckets_115_; lean_object* v_name_116_; lean_object* v___x_117_; uint64_t v___y_119_; 
v_buckets_115_ = lean_ctor_get(v_m_113_, 1);
v_name_116_ = lean_ctor_get(v_a_114_, 1);
v___x_117_ = lean_array_get_size(v_buckets_115_);
if (lean_obj_tag(v_name_116_) == 0)
{
uint64_t v___x_133_; 
v___x_133_ = 1723ULL;
v___y_119_ = v___x_133_;
goto v___jp_118_;
}
else
{
uint64_t v_hash_134_; 
v_hash_134_ = lean_ctor_get_uint64(v_name_116_, sizeof(void*)*2);
v___y_119_ = v_hash_134_;
goto v___jp_118_;
}
v___jp_118_:
{
uint64_t v___x_120_; uint64_t v___x_121_; uint64_t v_fold_122_; uint64_t v___x_123_; uint64_t v___x_124_; uint64_t v___x_125_; size_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_120_ = 32ULL;
v___x_121_ = lean_uint64_shift_right(v___y_119_, v___x_120_);
v_fold_122_ = lean_uint64_xor(v___y_119_, v___x_121_);
v___x_123_ = 16ULL;
v___x_124_ = lean_uint64_shift_right(v_fold_122_, v___x_123_);
v___x_125_ = lean_uint64_xor(v_fold_122_, v___x_124_);
v___x_126_ = lean_uint64_to_usize(v___x_125_);
v___x_127_ = lean_usize_of_nat(v___x_117_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_sub(v___x_127_, v___x_128_);
v___x_130_ = lean_usize_land(v___x_126_, v___x_129_);
v___x_131_ = lean_array_uget_borrowed(v_buckets_115_, v___x_130_);
v___x_132_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_114_, v___x_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg___boxed(lean_object* v_m_135_, lean_object* v_a_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_135_, v_a_136_);
lean_dec_ref(v_a_136_);
lean_dec_ref(v_m_135_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(lean_object* v_self_139_, lean_object* v_root_140_, lean_object* v_col_141_, uint8_t v_viaImport_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_col_151_; lean_object* v___y_152_; lean_object* v_mods_154_; lean_object* v_modSet_155_; uint8_t v_hasErrors_156_; uint8_t v___x_157_; 
v_mods_154_ = lean_ctor_get(v_col_141_, 0);
v_modSet_155_ = lean_ctor_get(v_col_141_, 1);
v_hasErrors_156_ = lean_ctor_get_uint8(v_col_141_, sizeof(void*)*2);
v___x_157_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_modSet_155_, v_root_140_);
if (v___x_157_ == 0)
{
lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_222_; 
lean_inc_ref(v_modSet_155_);
lean_inc_ref(v_mods_154_);
v_isSharedCheck_222_ = !lean_is_exclusive(v_col_141_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; lean_object* v_unused_224_; 
v_unused_223_ = lean_ctor_get(v_col_141_, 1);
lean_dec(v_unused_223_);
v_unused_224_ = lean_ctor_get(v_col_141_, 0);
lean_dec(v_unused_224_);
v___x_159_ = v_col_141_;
v_isShared_160_ = v_isSharedCheck_222_;
goto v_resetjp_158_;
}
else
{
lean_dec(v_col_141_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_222_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v_lib_161_; lean_object* v_pkg_162_; lean_object* v_name_163_; lean_object* v_keyName_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_lib_161_ = lean_ctor_get(v_root_140_, 0);
v_pkg_162_ = lean_ctor_get(v_lib_161_, 0);
v_name_163_ = lean_ctor_get(v_root_140_, 1);
v_keyName_164_ = lean_ctor_get(v_pkg_162_, 2);
v___x_165_ = lean_box(0);
lean_inc_ref_n(v_root_140_, 2);
v___x_166_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_modSet_155_, v_root_140_, v___x_165_);
v___x_167_ = l_Lake_Module_importsFacet;
lean_inc(v_name_163_);
lean_inc(v_keyName_164_);
v___x_168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_168_, 0, v_keyName_164_);
lean_ctor_set(v___x_168_, 1, v_name_163_);
v___x_169_ = l_Lake_Module_keyword;
v___x_170_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
lean_ctor_set(v___x_170_, 2, v_root_140_);
lean_ctor_set(v___x_170_, 3, v___x_167_);
lean_inc_ref(v_a_143_);
lean_inc_ref(v_a_147_);
lean_inc(v_a_146_);
lean_inc(v_a_145_);
lean_inc(v_a_144_);
v___x_171_ = lean_apply_7(v_a_143_, v___x_170_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, lean_box(0));
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_212_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
v_a_173_ = lean_ctor_get(v___x_171_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_212_ == 0)
{
v___x_175_ = v___x_171_;
v_isShared_176_ = v_isSharedCheck_212_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_inc(v_a_172_);
lean_dec(v___x_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_212_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v_task_177_; lean_object* v___x_178_; lean_object* v___y_180_; 
v_task_177_ = lean_ctor_get(v_a_172_, 0);
lean_inc_ref(v_task_177_);
lean_dec(v_a_172_);
v___x_178_ = lean_io_wait(v_task_177_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_184_; lean_object* v_col_186_; 
lean_del_object(v___x_175_);
v_a_184_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_184_);
lean_dec_ref_known(v___x_178_, 2);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v___x_166_);
v_col_186_ = v___x_159_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_mods_154_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_166_);
lean_ctor_set_uint8(v_reuseFailAlloc_203_, sizeof(void*)*2, v_hasErrors_156_);
v_col_186_ = v_reuseFailAlloc_203_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
size_t v_sz_187_; size_t v___x_188_; lean_object* v___x_189_; 
v_sz_187_ = lean_array_size(v_a_184_);
v___x_188_ = ((size_t)0ULL);
v___x_189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_139_, v_a_184_, v_sz_187_, v___x_188_, v_col_186_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_173_);
lean_dec(v_a_184_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v_a_191_; lean_object* v_mods_192_; lean_object* v_modSet_193_; uint8_t v_hasErrors_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_202_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
v_a_191_ = lean_ctor_get(v___x_189_, 1);
lean_inc(v_a_191_);
lean_dec_ref_known(v___x_189_, 2);
v_mods_192_ = lean_ctor_get(v_a_190_, 0);
v_modSet_193_ = lean_ctor_get(v_a_190_, 1);
v_hasErrors_194_ = lean_ctor_get_uint8(v_a_190_, sizeof(void*)*2);
v_isSharedCheck_202_ = !lean_is_exclusive(v_a_190_);
if (v_isSharedCheck_202_ == 0)
{
v___x_196_ = v_a_190_;
v_isShared_197_ = v_isSharedCheck_202_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_modSet_193_);
lean_inc(v_mods_192_);
lean_dec(v_a_190_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_202_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_198_ = lean_array_push(v_mods_192_, v_root_140_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_198_);
v___x_200_ = v___x_196_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_modSet_193_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, sizeof(void*)*2, v_hasErrors_194_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
v_col_151_ = v___x_200_;
v___y_152_ = v_a_191_;
goto v___jp_150_;
}
}
}
else
{
lean_dec_ref(v_root_140_);
return v___x_189_;
}
}
}
else
{
uint8_t v___x_204_; 
lean_dec_ref_known(v___x_178_, 2);
lean_dec_ref(v_a_143_);
v___x_204_ = 1;
if (v_viaImport_142_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_205_ = lean_array_push(v_mods_154_, v_root_140_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v___x_166_);
lean_ctor_set(v___x_159_, 0, v___x_205_);
v___x_207_ = v___x_159_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v___x_166_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*2, v___x_204_);
v___y_180_ = v___x_207_;
goto v___jp_179_;
}
}
else
{
lean_object* v___x_210_; 
lean_dec_ref(v_root_140_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v___x_166_);
v___x_210_ = v___x_159_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_mods_154_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_166_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*2, v___x_204_);
v___y_180_ = v___x_210_;
goto v___jp_179_;
}
}
}
v___jp_179_:
{
lean_object* v___x_182_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___y_180_);
v___x_182_ = v___x_175_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___y_180_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v_a_173_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
else
{
lean_object* v_a_213_; lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
lean_dec_ref(v___x_166_);
lean_del_object(v___x_159_);
lean_dec_ref(v_mods_154_);
lean_dec_ref(v_a_143_);
lean_dec_ref(v_root_140_);
v_a_213_ = lean_ctor_get(v___x_171_, 0);
v_a_214_ = lean_ctor_get(v___x_171_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_171_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_inc(v_a_213_);
lean_dec(v___x_171_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_213_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_143_);
lean_dec_ref(v_root_140_);
v_col_151_ = v_col_141_;
v___y_152_ = v_a_148_;
goto v___jp_150_;
}
v___jp_150_:
{
lean_object* v___x_153_; 
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v_col_151_);
lean_ctor_set(v___x_153_, 1, v___y_152_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(lean_object* v_self_225_, lean_object* v_as_226_, size_t v_sz_227_, size_t v_i_228_, lean_object* v_b_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_a_238_; lean_object* v_a_239_; uint8_t v___x_243_; 
v___x_243_ = lean_usize_dec_lt(v_i_228_, v_sz_227_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; 
lean_dec_ref(v___y_230_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v_b_229_);
lean_ctor_set(v___x_244_, 1, v___y_235_);
return v___x_244_;
}
else
{
lean_object* v_a_245_; lean_object* v_lib_246_; lean_object* v_name_247_; lean_object* v_name_248_; uint8_t v___x_249_; 
v_a_245_ = lean_array_uget_borrowed(v_as_226_, v_i_228_);
v_lib_246_ = lean_ctor_get(v_a_245_, 0);
v_name_247_ = lean_ctor_get(v_lib_246_, 1);
v_name_248_ = lean_ctor_get(v_self_225_, 1);
v___x_249_ = lean_name_eq(v_name_247_, v_name_248_);
if (v___x_249_ == 0)
{
v_a_238_ = v_b_229_;
v_a_239_ = v___y_235_;
goto v___jp_237_;
}
else
{
lean_object* v___x_250_; 
lean_inc_ref(v___y_230_);
lean_inc(v_a_245_);
v___x_250_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_225_, v_a_245_, v_b_229_, v___x_249_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v_a_252_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
v_a_252_ = lean_ctor_get(v___x_250_, 1);
lean_inc(v_a_252_);
lean_dec_ref_known(v___x_250_, 2);
v_a_238_ = v_a_251_;
v_a_239_ = v_a_252_;
goto v___jp_237_;
}
else
{
lean_dec_ref(v___y_230_);
return v___x_250_;
}
}
}
v___jp_237_:
{
size_t v___x_240_; size_t v___x_241_; 
v___x_240_ = ((size_t)1ULL);
v___x_241_ = lean_usize_add(v_i_228_, v___x_240_);
v_i_228_ = v___x_241_;
v_b_229_ = v_a_238_;
v___y_235_ = v_a_239_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(lean_object* v_self_253_, lean_object* v_as_254_, lean_object* v_sz_255_, lean_object* v_i_256_, lean_object* v_b_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
size_t v_sz_boxed_265_; size_t v_i_boxed_266_; lean_object* v_res_267_; 
v_sz_boxed_265_ = lean_unbox_usize(v_sz_255_);
lean_dec(v_sz_255_);
v_i_boxed_266_ = lean_unbox_usize(v_i_256_);
lean_dec(v_i_256_);
v_res_267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_253_, v_as_254_, v_sz_boxed_265_, v_i_boxed_266_, v_b_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v_as_254_);
lean_dec_ref(v_self_253_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object* v_self_268_, lean_object* v_root_269_, lean_object* v_col_270_, lean_object* v_viaImport_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
uint8_t v_viaImport_boxed_279_; lean_object* v_res_280_; 
v_viaImport_boxed_279_ = lean_unbox(v_viaImport_271_);
v_res_280_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_268_, v_root_269_, v_col_270_, v_viaImport_boxed_279_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_self_268_);
return v_res_280_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_object* v_00_u03b2_281_, lean_object* v_m_282_, lean_object* v_a_283_){
_start:
{
uint8_t v___x_284_; 
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_282_, v_a_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(lean_object* v_00_u03b2_285_, lean_object* v_m_286_, lean_object* v_a_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(v_00_u03b2_285_, v_m_286_, v_a_287_);
lean_dec_ref(v_a_287_);
lean_dec_ref(v_m_286_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1(lean_object* v_00_u03b2_290_, lean_object* v_m_291_, lean_object* v_a_292_, lean_object* v_b_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_m_291_, v_a_292_, v_b_293_);
return v___x_294_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(lean_object* v_00_u03b2_295_, lean_object* v_a_296_, lean_object* v_x_297_){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_296_, v_x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_299_, lean_object* v_a_300_, lean_object* v_x_301_){
_start:
{
uint8_t v_res_302_; lean_object* v_r_303_; 
v_res_302_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(v_00_u03b2_299_, v_a_300_, v_x_301_);
lean_dec(v_x_301_);
lean_dec_ref(v_a_300_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2(lean_object* v_00_u03b2_304_, lean_object* v_data_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(v_data_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_307_, lean_object* v_i_308_, lean_object* v_source_309_, lean_object* v_target_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(v_i_308_, v_source_309_, v_target_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_312_, lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(v_x_313_, v_x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(lean_object* v_self_316_, lean_object* v_as_317_, size_t v_sz_318_, size_t v_i_319_, lean_object* v_b_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_usize_dec_lt(v_i_319_, v_sz_318_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
lean_dec_ref(v___y_321_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v_b_320_);
lean_ctor_set(v___x_329_, 1, v___y_326_);
return v___x_329_;
}
else
{
uint8_t v___x_330_; lean_object* v_a_331_; lean_object* v___x_332_; 
v___x_330_ = 0;
v_a_331_ = lean_array_uget_borrowed(v_as_317_, v_i_319_);
lean_inc_ref(v___y_321_);
lean_inc(v_a_331_);
v___x_332_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_316_, v_a_331_, v_b_320_, v___x_330_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v_a_334_; size_t v___x_335_; size_t v___x_336_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
v_a_334_ = lean_ctor_get(v___x_332_, 1);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_332_, 2);
v___x_335_ = ((size_t)1ULL);
v___x_336_ = lean_usize_add(v_i_319_, v___x_335_);
v_i_319_ = v___x_336_;
v_b_320_ = v_a_333_;
v___y_326_ = v_a_334_;
goto _start;
}
else
{
lean_dec_ref(v___y_321_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0___boxed(lean_object* v_self_338_, lean_object* v_as_339_, lean_object* v_sz_340_, lean_object* v_i_341_, lean_object* v_b_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
size_t v_sz_boxed_350_; size_t v_i_boxed_351_; lean_object* v_res_352_; 
v_sz_boxed_350_ = lean_unbox_usize(v_sz_340_);
lean_dec(v_sz_340_);
v_i_boxed_351_ = lean_unbox_usize(v_i_341_);
lean_dec(v_i_341_);
v_res_352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_338_, v_as_339_, v_sz_boxed_350_, v_i_boxed_351_, v_b_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
lean_dec_ref(v___y_347_);
lean_dec(v___y_346_);
lean_dec(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v_as_339_);
lean_dec_ref(v_self_338_);
return v_res_352_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1));
v___x_356_ = l_Lake_BuildTrace_nil(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(lean_object* v_self_358_, lean_object* v_col_359_, lean_object* v___x_360_, uint8_t v___x_361_, lean_object* v___x_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v___x_370_; 
lean_inc_ref(v_self_358_);
v___x_370_ = l_Lake_LeanLib_getModuleArray(v_self_358_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; size_t v_sz_372_; size_t v___x_373_; lean_object* v___x_374_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_370_, 1);
v_sz_372_ = lean_array_size(v_a_371_);
v___x_373_ = ((size_t)0ULL);
v___x_374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_358_, v_a_371_, v_sz_372_, v___x_373_, v_col_359_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v_a_371_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_402_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_a_376_ = lean_ctor_get(v___x_374_, 1);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_402_ == 0)
{
v___x_378_ = v___x_374_;
v_isShared_379_ = v_isSharedCheck_402_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_402_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v_mods_380_; uint8_t v_hasErrors_381_; lean_object* v___y_383_; 
v_mods_380_ = lean_ctor_get(v_a_375_, 0);
lean_inc_ref(v_mods_380_);
v_hasErrors_381_ = lean_ctor_get_uint8(v_a_375_, sizeof(void*)*2);
lean_dec(v_a_375_);
if (v_hasErrors_381_ == 0)
{
lean_dec_ref(v_self_358_);
v___y_383_ = v_a_376_;
goto v___jp_382_;
}
else
{
lean_object* v_name_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_name_395_ = lean_ctor_get(v_self_358_, 1);
lean_inc(v_name_395_);
lean_dec_ref(v_self_358_);
v___x_396_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_395_, v_hasErrors_381_);
v___x_397_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__3));
v___x_398_ = lean_string_append(v___x_396_, v___x_397_);
v___x_399_ = 3;
v___x_400_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*1, v___x_399_);
v___x_401_ = lean_array_push(v_a_376_, v___x_400_);
v___y_383_ = v___x_401_;
goto v___jp_382_;
}
v___jp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_384_ = lean_mk_empty_array_with_capacity(v___x_360_);
v___x_385_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_386_ = 0;
v___x_387_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_388_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_388_, 0, v___x_384_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
lean_ctor_set(v___x_388_, 2, v___x_360_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*3, v___x_386_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*3 + 1, v___x_361_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 1, v___x_388_);
lean_ctor_set(v___x_378_, 0, v_mods_380_);
v___x_390_ = v___x_378_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_mods_380_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v___x_388_);
v___x_390_ = v_reuseFailAlloc_394_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = lean_task_pure(v___x_390_);
v___x_392_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v___x_362_);
lean_ctor_set(v___x_392_, 2, v___x_385_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*3, v___x_361_);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___y_383_);
return v___x_393_;
}
}
}
}
else
{
lean_object* v_a_403_; lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
lean_dec(v___x_362_);
lean_dec(v___x_360_);
lean_dec_ref(v_self_358_);
v_a_403_ = lean_ctor_get(v___x_374_, 0);
v_a_404_ = lean_ctor_get(v___x_374_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_374_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_inc(v_a_403_);
lean_dec(v___x_374_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_403_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_413_; uint8_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec_ref(v___y_363_);
lean_dec(v___x_362_);
lean_dec(v___x_360_);
lean_dec_ref(v_col_359_);
lean_dec_ref(v_self_358_);
v_a_412_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_370_, 1);
v___x_413_ = lean_io_error_to_string(v_a_412_);
v___x_414_ = 3;
v___x_415_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set_uint8(v___x_415_, sizeof(void*)*1, v___x_414_);
v___x_416_ = lean_array_get_size(v___y_368_);
v___x_417_ = lean_array_push(v___y_368_, v___x_415_);
v___x_418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed(lean_object* v_self_419_, lean_object* v_col_420_, lean_object* v___x_421_, lean_object* v___x_422_, lean_object* v___x_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
uint8_t v___x_7764__boxed_431_; lean_object* v_res_432_; 
v___x_7764__boxed_431_ = lean_unbox(v___x_422_);
v_res_432_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(v_self_419_, v_col_420_, v___x_421_, v___x_7764__boxed_431_, v___x_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec(v___y_426_);
lean_dec(v___y_425_);
return v_res_432_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_box(0);
v___x_436_ = lean_unsigned_to_nat(16u);
v___x_437_ = lean_mk_array(v___x_436_, v___x_435_);
return v___x_437_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
return v___x_440_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3(void){
_start:
{
uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_col_444_; 
v___x_441_ = 0;
v___x_442_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_443_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0));
v_col_444_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_col_444_, 0, v___x_443_);
lean_ctor_set(v_col_444_, 1, v___x_442_);
lean_ctor_set_uint8(v_col_444_, sizeof(void*)*2, v___x_441_);
return v_col_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(lean_object* v_self_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v_col_456_; lean_object* v___x_457_; lean_object* v___f_458_; lean_object* v___x_459_; 
v___x_453_ = lean_box(0);
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = 0;
v_col_456_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3);
v___x_457_ = lean_box(v___x_455_);
v___f_458_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed), 12, 5);
lean_closure_set(v___f_458_, 0, v_self_445_);
lean_closure_set(v___f_458_, 1, v_col_456_);
lean_closure_set(v___f_458_, 2, v___x_454_);
lean_closure_set(v___f_458_, 3, v___x_457_);
lean_closure_set(v___f_458_, 4, v___x_453_);
v___x_459_ = l_Lake_ensureJob___redArg(v___x_453_, v___f_458_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___boxed(lean_object* v_self_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(v_self_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec(v_a_463_);
lean_dec(v_a_462_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(lean_object* v_as_470_, size_t v_i_471_, size_t v_stop_472_, lean_object* v_b_473_){
_start:
{
uint8_t v___x_474_; 
v___x_474_ = lean_usize_dec_eq(v_i_471_, v_stop_472_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v_name_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; size_t v___x_482_; size_t v___x_483_; 
v___x_475_ = lean_array_uget_borrowed(v_as_470_, v_i_471_);
v_name_476_ = lean_ctor_get(v___x_475_, 1);
v___x_477_ = 1;
lean_inc(v_name_476_);
v___x_478_ = l_Lean_Name_toString(v_name_476_, v___x_477_);
v___x_479_ = lean_string_append(v_b_473_, v___x_478_);
lean_dec_ref(v___x_478_);
v___x_480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_481_ = lean_string_append(v___x_479_, v___x_480_);
v___x_482_ = ((size_t)1ULL);
v___x_483_ = lean_usize_add(v_i_471_, v___x_482_);
v_i_471_ = v___x_483_;
v_b_473_ = v___x_481_;
goto _start;
}
else
{
return v_b_473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_485_, lean_object* v_i_486_, lean_object* v_stop_487_, lean_object* v_b_488_){
_start:
{
size_t v_i_boxed_489_; size_t v_stop_boxed_490_; lean_object* v_res_491_; 
v_i_boxed_489_ = lean_unbox_usize(v_i_486_);
lean_dec(v_i_486_);
v_stop_boxed_490_ = lean_unbox_usize(v_stop_487_);
lean_dec(v_stop_487_);
v_res_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_as_485_, v_i_boxed_489_, v_stop_boxed_490_, v_b_488_);
lean_dec_ref(v_as_485_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(size_t v_sz_492_, size_t v_i_493_, lean_object* v_bs_494_){
_start:
{
uint8_t v___x_495_; 
v___x_495_ = lean_usize_dec_lt(v_i_493_, v_sz_492_);
if (v___x_495_ == 0)
{
return v_bs_494_;
}
else
{
lean_object* v_v_496_; lean_object* v_name_497_; lean_object* v___x_498_; lean_object* v_bs_x27_499_; lean_object* v___x_500_; lean_object* v___x_501_; size_t v___x_502_; size_t v___x_503_; lean_object* v___x_504_; 
v_v_496_ = lean_array_uget_borrowed(v_bs_494_, v_i_493_);
v_name_497_ = lean_ctor_get(v_v_496_, 1);
lean_inc(v_name_497_);
v___x_498_ = lean_unsigned_to_nat(0u);
v_bs_x27_499_ = lean_array_uset(v_bs_494_, v_i_493_, v___x_498_);
v___x_500_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_497_, v___x_495_);
v___x_501_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_add(v_i_493_, v___x_502_);
v___x_504_ = lean_array_uset(v_bs_x27_499_, v_i_493_, v___x_501_);
v_i_493_ = v___x_503_;
v_bs_494_ = v___x_504_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_506_, lean_object* v_i_507_, lean_object* v_bs_508_){
_start:
{
size_t v_sz_boxed_509_; size_t v_i_boxed_510_; lean_object* v_res_511_; 
v_sz_boxed_509_ = lean_unbox_usize(v_sz_506_);
lean_dec(v_sz_506_);
v_i_boxed_510_ = lean_unbox_usize(v_i_507_);
lean_dec(v_i_507_);
v_res_511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_509_, v_i_boxed_510_, v_bs_508_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(lean_object* v_a_512_){
_start:
{
size_t v_sz_513_; size_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_sz_513_ = lean_array_size(v_a_512_);
v___x_514_ = ((size_t)0ULL);
v___x_515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_513_, v___x_514_, v_a_512_);
v___x_516_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(uint8_t v_fmt_517_, lean_object* v_a_518_){
_start:
{
lean_object* v___y_520_; 
if (v_fmt_517_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_527_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_array_get_size(v_a_518_);
v___x_530_ = lean_nat_dec_lt(v___x_528_, v___x_529_);
if (v___x_530_ == 0)
{
lean_dec_ref(v_a_518_);
v___y_520_ = v___x_527_;
goto v___jp_519_;
}
else
{
uint8_t v___x_531_; 
v___x_531_ = lean_nat_dec_le(v___x_529_, v___x_529_);
if (v___x_531_ == 0)
{
if (v___x_530_ == 0)
{
lean_dec_ref(v_a_518_);
v___y_520_ = v___x_527_;
goto v___jp_519_;
}
else
{
size_t v___x_532_; size_t v___x_533_; lean_object* v___x_534_; 
v___x_532_ = ((size_t)0ULL);
v___x_533_ = lean_usize_of_nat(v___x_529_);
v___x_534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_518_, v___x_532_, v___x_533_, v___x_527_);
lean_dec_ref(v_a_518_);
v___y_520_ = v___x_534_;
goto v___jp_519_;
}
}
else
{
size_t v___x_535_; size_t v___x_536_; lean_object* v___x_537_; 
v___x_535_ = ((size_t)0ULL);
v___x_536_ = lean_usize_of_nat(v___x_529_);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_518_, v___x_535_, v___x_536_, v___x_527_);
lean_dec_ref(v_a_518_);
v___y_520_ = v___x_537_;
goto v___jp_519_;
}
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(v_a_518_);
v___x_539_ = l_Lean_Json_compress(v___x_538_);
return v___x_539_;
}
v___jp_519_:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_string_utf8_byte_size(v___y_520_);
lean_inc_ref(v___y_520_);
v___x_524_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_524_, 0, v___y_520_);
lean_ctor_set(v___x_524_, 1, v___x_522_);
lean_ctor_set(v___x_524_, 2, v___x_523_);
v___x_525_ = l_String_Slice_Pos_prevn(v___x_524_, v___x_523_, v___x_521_);
lean_dec_ref_known(v___x_524_, 3);
v___x_526_ = lean_string_utf8_extract_fast(v___y_520_, v___x_522_, v___x_525_);
lean_dec(v___x_525_);
lean_dec_ref(v___y_520_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0___boxed(lean_object* v_fmt_540_, lean_object* v_a_541_){
_start:
{
uint8_t v_fmt_boxed_542_; lean_object* v_res_543_; 
v_fmt_boxed_542_ = lean_unbox(v_fmt_540_);
v_res_543_ = l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(v_fmt_boxed_542_, v_a_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(lean_object* v_as_557_, size_t v_i_558_, size_t v_stop_559_, lean_object* v_b_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = lean_usize_dec_eq(v_i_558_, v_stop_559_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v_lib_570_; lean_object* v_pkg_571_; lean_object* v_name_572_; lean_object* v_keyName_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_569_ = lean_array_uget_borrowed(v_as_557_, v_i_558_);
v_lib_570_ = lean_ctor_get(v___x_569_, 0);
v_pkg_571_ = lean_ctor_get(v_lib_570_, 0);
v_name_572_ = lean_ctor_get(v___x_569_, 1);
v_keyName_573_ = lean_ctor_get(v_pkg_571_, 2);
v___x_574_ = l_Lake_Module_leanArtsFacet;
lean_inc(v_name_572_);
lean_inc(v_keyName_573_);
v___x_575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_575_, 0, v_keyName_573_);
lean_ctor_set(v___x_575_, 1, v_name_572_);
v___x_576_ = l_Lake_Module_keyword;
lean_inc(v___x_569_);
v___x_577_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
lean_ctor_set(v___x_577_, 2, v___x_569_);
lean_ctor_set(v___x_577_, 3, v___x_574_);
lean_inc_ref(v___y_561_);
lean_inc_ref(v___y_565_);
lean_inc(v___y_564_);
lean_inc(v___y_563_);
lean_inc(v___y_562_);
v___x_578_ = lean_apply_7(v___y_561_, v___x_577_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, lean_box(0));
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v_a_580_; lean_object* v___x_581_; size_t v___x_582_; size_t v___x_583_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
v_a_580_ = lean_ctor_get(v___x_578_, 1);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_578_, 2);
v___x_581_ = l_Lake_Job_mix___redArg(v_b_560_, v_a_579_);
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_add(v_i_558_, v___x_582_);
v_i_558_ = v___x_583_;
v_b_560_ = v___x_581_;
v___y_566_ = v_a_580_;
goto _start;
}
else
{
lean_object* v_a_585_; lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref(v___y_561_);
lean_dec_ref(v_b_560_);
v_a_585_ = lean_ctor_get(v___x_578_, 0);
v_a_586_ = lean_ctor_get(v___x_578_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_578_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_inc(v_a_585_);
lean_dec(v___x_578_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_585_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_object* v___x_594_; 
lean_dec_ref(v___y_561_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v_b_560_);
lean_ctor_set(v___x_594_, 1, v___y_566_);
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0___boxed(lean_object* v_as_595_, lean_object* v_i_596_, lean_object* v_stop_597_, lean_object* v_b_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
size_t v_i_boxed_606_; size_t v_stop_boxed_607_; lean_object* v_res_608_; 
v_i_boxed_606_ = lean_unbox_usize(v_i_596_);
lean_dec(v_i_596_);
v_stop_boxed_607_ = lean_unbox_usize(v_stop_597_);
lean_dec(v_stop_597_);
v_res_608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_as_595_, v_i_boxed_606_, v_stop_boxed_607_, v_b_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v_as_595_);
return v_res_608_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_613_ = 0;
v___x_614_ = 0;
v___x_615_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v___x_616_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v___x_612_);
lean_ctor_set(v___x_616_, 2, v___x_611_);
lean_ctor_set_uint8(v___x_616_, sizeof(void*)*3, v___x_614_);
lean_ctor_set_uint8(v___x_616_, sizeof(void*)*3 + 1, v___x_613_);
return v___x_616_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1);
v___x_618_ = lean_box(0);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v___x_617_);
return v___x_619_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2);
v___x_621_ = lean_task_pure(v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4(void){
_start:
{
uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_622_ = 0;
v___x_623_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_624_ = lean_box(0);
v___x_625_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3);
v___x_626_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_624_);
lean_ctor_set(v___x_626_, 2, v___x_623_);
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*3, v___x_622_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(lean_object* v_self_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_pkg_635_; lean_object* v_name_636_; lean_object* v_keyName_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_pkg_635_ = lean_ctor_get(v_self_627_, 0);
v_name_636_ = lean_ctor_get(v_self_627_, 1);
v_keyName_637_ = lean_ctor_get(v_pkg_635_, 2);
v___x_638_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_636_);
lean_inc(v_keyName_637_);
v___x_639_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_639_, 0, v_keyName_637_);
lean_ctor_set(v___x_639_, 1, v_name_636_);
v___x_640_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_641_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
lean_ctor_set(v___x_641_, 2, v_self_627_);
lean_ctor_set(v___x_641_, 3, v___x_638_);
lean_inc_ref(v_a_628_);
lean_inc_ref(v_a_632_);
lean_inc(v_a_631_);
lean_inc(v_a_630_);
lean_inc(v_a_629_);
v___x_642_ = lean_apply_7(v_a_628_, v___x_641_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, lean_box(0));
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v_a_644_; lean_object* v___x_645_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
v_a_644_ = lean_ctor_get(v___x_642_, 1);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_642_, 2);
v___x_645_ = l_Lake_Job_await___redArg(v_a_643_, v_a_644_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_668_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
v_a_647_ = lean_ctor_get(v___x_645_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_668_ == 0)
{
v___x_649_ = v___x_645_;
v_isShared_650_ = v_isSharedCheck_668_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_inc(v_a_646_);
lean_dec(v___x_645_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_668_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4);
v___x_653_ = lean_array_get_size(v_a_646_);
v___x_654_ = lean_nat_dec_lt(v___x_651_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_656_; 
lean_dec(v_a_646_);
lean_dec_ref(v_a_628_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_652_);
v___x_656_ = v___x_649_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_a_647_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
else
{
uint8_t v___x_658_; 
v___x_658_ = lean_nat_dec_le(v___x_653_, v___x_653_);
if (v___x_658_ == 0)
{
if (v___x_654_ == 0)
{
lean_object* v___x_660_; 
lean_dec(v_a_646_);
lean_dec_ref(v_a_628_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_652_);
v___x_660_ = v___x_649_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_a_647_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
else
{
size_t v___x_662_; size_t v___x_663_; lean_object* v___x_664_; 
lean_del_object(v___x_649_);
v___x_662_ = ((size_t)0ULL);
v___x_663_ = lean_usize_of_nat(v___x_653_);
v___x_664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_646_, v___x_662_, v___x_663_, v___x_652_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_647_);
lean_dec(v_a_646_);
return v___x_664_;
}
}
else
{
size_t v___x_665_; size_t v___x_666_; lean_object* v___x_667_; 
lean_del_object(v___x_649_);
v___x_665_ = ((size_t)0ULL);
v___x_666_ = lean_usize_of_nat(v___x_653_);
v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_646_, v___x_665_, v___x_666_, v___x_652_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_647_);
lean_dec(v_a_646_);
return v___x_667_;
}
}
}
}
else
{
lean_object* v_a_669_; lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v_a_628_);
v_a_669_ = lean_ctor_get(v___x_645_, 0);
v_a_670_ = lean_ctor_get(v___x_645_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_645_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_inc(v_a_669_);
lean_dec(v___x_645_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_669_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
else
{
lean_object* v_a_678_; lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_a_628_);
v_a_678_ = lean_ctor_get(v___x_642_, 0);
v_a_679_ = lean_ctor_get(v___x_642_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_642_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_inc(v_a_678_);
lean_dec(v___x_642_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_678_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_a_679_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___boxed(lean_object* v_self_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(v_self_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec(v_a_690_);
lean_dec(v_a_689_);
return v_res_695_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_box(0);
v___x_697_ = l_Lean_Json_compress(v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(uint8_t v_fmt_698_){
_start:
{
if (v_fmt_698_ == 0)
{
lean_object* v___x_699_; 
v___x_699_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
return v___x_699_;
}
else
{
lean_object* v___x_700_; 
v___x_700_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_701_){
_start:
{
uint8_t v_fmt_boxed_702_; lean_object* v_res_703_; 
v_fmt_boxed_702_ = lean_unbox(v_fmt_701_);
v_res_703_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_boxed_702_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(uint8_t v_fmt_704_, lean_object* v_a_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___boxed(lean_object* v_fmt_707_, lean_object* v_a_708_){
_start:
{
uint8_t v_fmt_boxed_709_; lean_object* v_res_710_; 
v_fmt_boxed_709_ = lean_unbox(v_fmt_707_);
v_res_710_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(v_fmt_boxed_709_, v_a_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0(uint8_t v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v___y_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
uint8_t v___y_68__boxed_716_; lean_object* v_res_717_; 
v___y_68__boxed_716_ = lean_unbox(v___y_714_);
v_res_717_ = l_Lake_LeanLib_leanArtsFacetConfig___lam__0(v___y_68__boxed_716_, v___y_715_);
return v_res_717_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_720_; uint8_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___f_720_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_721_ = 1;
v___x_722_ = l_Lake_instDataKindUnit;
v___x_723_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__1));
v___x_724_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_725_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v___x_723_);
lean_ctor_set(v___x_725_, 2, v___x_722_);
lean_ctor_set(v___x_725_, 3, v___f_720_);
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*4, v___x_721_);
lean_ctor_set_uint8(v___x_725_, sizeof(void*)*4 + 1, v___x_721_);
return v___x_725_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig(void){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = lean_obj_once(&l_Lake_LeanLib_leanArtsFacetConfig___closed__2, &l_Lake_LeanLib_leanArtsFacetConfig___closed__2_once, _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(lean_object* v_a_727_, lean_object* v_x_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lake_ModuleFacet_fetch___redArg(v_x_728_, v_a_727_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object* v_a_737_, lean_object* v_x_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(v_a_737_, v_x_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec(v___y_741_);
lean_dec(v___y_740_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(uint8_t v_shouldExport_747_, lean_object* v___x_748_, lean_object* v_bs_749_, lean_object* v_a_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_lib_758_; lean_object* v_config_759_; lean_object* v_nativeFacets_760_; lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___x_763_; size_t v_sz_764_; size_t v___x_765_; lean_object* v___x_197263__overap_766_; lean_object* v___x_767_; 
v_lib_758_ = lean_ctor_get(v_a_750_, 0);
v_config_759_ = lean_ctor_get(v_lib_758_, 2);
v_nativeFacets_760_ = lean_ctor_get(v_config_759_, 8);
lean_inc_ref(v_nativeFacets_760_);
v___f_761_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed), 9, 1);
lean_closure_set(v___f_761_, 0, v_a_750_);
v___x_762_ = lean_box(v_shouldExport_747_);
v___x_763_ = lean_apply_1(v_nativeFacets_760_, v___x_762_);
v_sz_764_ = lean_array_size(v___x_763_);
v___x_765_ = ((size_t)0ULL);
v___x_197263__overap_766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_748_, v___f_761_, v_sz_764_, v___x_765_, v___x_763_);
lean_inc_ref(v___y_755_);
lean_inc(v___y_754_);
lean_inc(v___y_753_);
lean_inc(v___y_752_);
v___x_767_ = lean_apply_7(v___x_197263__overap_766_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, lean_box(0));
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_777_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_a_769_ = lean_ctor_get(v___x_767_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_777_ == 0)
{
v___x_771_ = v___x_767_;
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_777_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = l_Array_append___redArg(v_bs_749_, v_a_768_);
lean_dec(v_a_768_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_773_);
v___x_775_ = v___x_771_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_a_769_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
else
{
lean_dec_ref(v_bs_749_);
return v___x_767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed(lean_object* v_shouldExport_778_, lean_object* v___x_779_, lean_object* v_bs_780_, lean_object* v_a_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
uint8_t v_shouldExport_boxed_789_; lean_object* v_res_790_; 
v_shouldExport_boxed_789_ = lean_unbox(v_shouldExport_778_);
v_res_790_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(v_shouldExport_boxed_789_, v___x_779_, v_bs_780_, v_a_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec(v___y_784_);
lean_dec(v___y_783_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(lean_object* v___x_791_, lean_object* v_pkg_792_, lean_object* v_x_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lake_Target_fetchIn___redArg(v___x_791_, v_pkg_792_, v_x_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object* v___x_802_, lean_object* v_pkg_803_, lean_object* v_x_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(v___x_802_, v_pkg_803_, v_x_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec(v___y_807_);
lean_dec(v___y_806_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object* v_a_813_, lean_object* v_x_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_log_823_; uint8_t v_action_824_; uint8_t v_wantsRebuild_825_; lean_object* v_trace_826_; lean_object* v_buildTime_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_log_823_ = lean_ctor_get(v___y_821_, 0);
v_action_824_ = lean_ctor_get_uint8(v___y_821_, sizeof(void*)*3);
v_wantsRebuild_825_ = lean_ctor_get_uint8(v___y_821_, sizeof(void*)*3 + 1);
v_trace_826_ = lean_ctor_get(v___y_821_, 1);
v_buildTime_827_ = lean_ctor_get(v___y_821_, 2);
v___x_828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_829_ = lean_string_append(v___y_815_, v___x_828_);
v___x_830_ = lean_io_prim_handle_put_str(v_a_813_, v___x_829_);
lean_dec_ref(v___x_829_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_832_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref_known(v___x_830_, 1);
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v_a_831_);
lean_ctor_set(v___x_832_, 1, v___y_821_);
return v___x_832_;
}
else
{
lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_846_; 
lean_inc(v_buildTime_827_);
lean_inc_ref(v_trace_826_);
lean_inc_ref(v_log_823_);
v_isSharedCheck_846_ = !lean_is_exclusive(v___y_821_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; lean_object* v_unused_848_; lean_object* v_unused_849_; 
v_unused_847_ = lean_ctor_get(v___y_821_, 2);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v___y_821_, 1);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v___y_821_, 0);
lean_dec(v_unused_849_);
v___x_834_ = v___y_821_;
v_isShared_835_ = v_isSharedCheck_846_;
goto v_resetjp_833_;
}
else
{
lean_dec(v___y_821_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_846_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v_a_836_; lean_object* v___x_837_; uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v_a_836_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_836_);
lean_dec_ref_known(v___x_830_, 1);
v___x_837_ = lean_io_error_to_string(v_a_836_);
v___x_838_ = 3;
v___x_839_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*1, v___x_838_);
v___x_840_ = lean_array_get_size(v_log_823_);
v___x_841_ = lean_array_push(v_log_823_, v___x_839_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_841_);
v___x_843_ = v___x_834_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_trace_826_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v_buildTime_827_);
lean_ctor_set_uint8(v_reuseFailAlloc_845_, sizeof(void*)*3, v_action_824_);
lean_ctor_set_uint8(v_reuseFailAlloc_845_, sizeof(void*)*3 + 1, v_wantsRebuild_825_);
v___x_843_ = v_reuseFailAlloc_845_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_844_; 
v___x_844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_840_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
return v___x_844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object* v_a_850_, lean_object* v_x_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(v_a_850_, v_x_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v_a_850_);
return v_res_860_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_868_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3));
v___x_869_ = lean_unsigned_to_nat(5u);
v___x_870_ = lean_mk_empty_array_with_capacity(v___x_869_);
v___x_871_ = lean_array_push(v___x_870_, v___x_868_);
return v___x_871_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4));
v___x_873_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6);
v___x_874_ = lean_array_push(v___x_873_, v___x_872_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(uint8_t v_bootstrap_877_, lean_object* v___y_878_, lean_object* v_oFiles_879_, uint8_t v_shouldExport_880_, uint8_t v___x_881_, lean_object* v___x_882_, size_t v___x_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
if (v_bootstrap_877_ == 0)
{
lean_object* v_toContext_891_; lean_object* v_lakeEnv_892_; lean_object* v_lean_893_; lean_object* v_log_894_; uint8_t v_action_895_; uint8_t v_wantsRebuild_896_; lean_object* v_trace_897_; lean_object* v_buildTime_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v___y_884_);
lean_dec_ref(v___x_882_);
v_toContext_891_ = lean_ctor_get(v___y_888_, 1);
v_lakeEnv_892_ = lean_ctor_get(v_toContext_891_, 0);
v_lean_893_ = lean_ctor_get(v_lakeEnv_892_, 1);
v_log_894_ = lean_ctor_get(v___y_889_, 0);
v_action_895_ = lean_ctor_get_uint8(v___y_889_, sizeof(void*)*3);
v_wantsRebuild_896_ = lean_ctor_get_uint8(v___y_889_, sizeof(void*)*3 + 1);
v_trace_897_ = lean_ctor_get(v___y_889_, 1);
v_buildTime_898_ = lean_ctor_get(v___y_889_, 2);
v_isSharedCheck_928_ = !lean_is_exclusive(v___y_889_);
if (v_isSharedCheck_928_ == 0)
{
v___x_900_ = v___y_889_;
v_isShared_901_ = v_isSharedCheck_928_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_buildTime_898_);
lean_inc(v_trace_897_);
lean_inc(v_log_894_);
lean_dec(v___y_889_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_928_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v_ar_902_; lean_object* v___x_903_; 
v_ar_902_ = lean_ctor_get(v_lean_893_, 13);
lean_inc_ref(v_ar_902_);
v___x_903_ = l_Lake_compileStaticLib(v___y_878_, v_oFiles_879_, v_ar_902_, v_bootstrap_877_, v_log_894_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_915_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_a_905_ = lean_ctor_get(v___x_903_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_915_ == 0)
{
v___x_907_ = v___x_903_;
v_isShared_908_ = v_isSharedCheck_915_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_915_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v_a_905_);
v___x_910_ = v___x_900_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_905_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_trace_897_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_buildTime_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_914_, sizeof(void*)*3, v_action_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_914_, sizeof(void*)*3 + 1, v_wantsRebuild_896_);
v___x_910_ = v_reuseFailAlloc_914_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_912_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 1, v___x_910_);
v___x_912_ = v___x_907_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_904_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_927_; 
v_a_916_ = lean_ctor_get(v___x_903_, 0);
v_a_917_ = lean_ctor_get(v___x_903_, 1);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_927_ == 0)
{
v___x_919_ = v___x_903_;
v_isShared_920_ = v_isSharedCheck_927_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_inc(v_a_916_);
lean_dec(v___x_903_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_927_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v_a_917_);
v___x_922_ = v___x_900_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_917_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_trace_897_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_buildTime_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_926_, sizeof(void*)*3, v_action_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_926_, sizeof(void*)*3 + 1, v_wantsRebuild_896_);
v___x_922_ = v_reuseFailAlloc_926_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_924_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 1, v___x_922_);
v___x_924_ = v___x_919_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_916_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
}
else
{
uint8_t v___x_929_; 
v___x_929_ = l_System_Platform_isOSX;
if (v___x_929_ == 0)
{
uint8_t v___x_930_; 
lean_dec_ref(v___y_884_);
lean_dec_ref(v___x_882_);
v___x_930_ = l_System_Platform_isWindows;
if (v___x_930_ == 0)
{
lean_object* v_toContext_931_; lean_object* v_lakeEnv_932_; lean_object* v_lean_933_; lean_object* v_log_934_; uint8_t v_action_935_; uint8_t v_wantsRebuild_936_; lean_object* v_trace_937_; lean_object* v_buildTime_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_968_; 
v_toContext_931_ = lean_ctor_get(v___y_888_, 1);
v_lakeEnv_932_ = lean_ctor_get(v_toContext_931_, 0);
v_lean_933_ = lean_ctor_get(v_lakeEnv_932_, 1);
v_log_934_ = lean_ctor_get(v___y_889_, 0);
v_action_935_ = lean_ctor_get_uint8(v___y_889_, sizeof(void*)*3);
v_wantsRebuild_936_ = lean_ctor_get_uint8(v___y_889_, sizeof(void*)*3 + 1);
v_trace_937_ = lean_ctor_get(v___y_889_, 1);
v_buildTime_938_ = lean_ctor_get(v___y_889_, 2);
v_isSharedCheck_968_ = !lean_is_exclusive(v___y_889_);
if (v_isSharedCheck_968_ == 0)
{
v___x_940_ = v___y_889_;
v_isShared_941_ = v_isSharedCheck_968_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_buildTime_938_);
lean_inc(v_trace_937_);
lean_inc(v_log_934_);
lean_dec(v___y_889_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_968_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v_ar_942_; lean_object* v___x_943_; 
v_ar_942_ = lean_ctor_get(v_lean_933_, 13);
lean_inc_ref(v_ar_942_);
v___x_943_ = l_Lake_compileStaticLib(v___y_878_, v_oFiles_879_, v_ar_942_, v___x_930_, v_log_934_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_955_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_a_945_ = lean_ctor_get(v___x_943_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_955_ == 0)
{
v___x_947_ = v___x_943_;
v_isShared_948_ = v_isSharedCheck_955_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_955_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v_a_945_);
v___x_950_ = v___x_940_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_945_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_trace_937_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_buildTime_938_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*3, v_action_935_);
lean_ctor_set_uint8(v_reuseFailAlloc_954_, sizeof(void*)*3 + 1, v_wantsRebuild_936_);
v___x_950_ = v_reuseFailAlloc_954_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_952_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v___x_950_);
v___x_952_ = v___x_947_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_944_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
else
{
lean_object* v_a_956_; lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_967_; 
v_a_956_ = lean_ctor_get(v___x_943_, 0);
v_a_957_ = lean_ctor_get(v___x_943_, 1);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_967_ == 0)
{
v___x_959_ = v___x_943_;
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_inc(v_a_956_);
lean_dec(v___x_943_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v_a_957_);
v___x_962_ = v___x_940_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_957_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_trace_937_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_buildTime_938_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3, v_action_935_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3 + 1, v_wantsRebuild_936_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 1, v___x_962_);
v___x_964_ = v___x_959_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_956_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_969_; lean_object* v_lakeEnv_970_; lean_object* v_lean_971_; lean_object* v_log_972_; uint8_t v_action_973_; uint8_t v_wantsRebuild_974_; lean_object* v_trace_975_; lean_object* v_buildTime_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1006_; 
v_toContext_969_ = lean_ctor_get(v___y_888_, 1);
v_lakeEnv_970_ = lean_ctor_get(v_toContext_969_, 0);
v_lean_971_ = lean_ctor_get(v_lakeEnv_970_, 1);
v_log_972_ = lean_ctor_get(v___y_889_, 0);
v_action_973_ = lean_ctor_get_uint8(v___y_889_, sizeof(void*)*3);
v_wantsRebuild_974_ = lean_ctor_get_uint8(v___y_889_, sizeof(void*)*3 + 1);
v_trace_975_ = lean_ctor_get(v___y_889_, 1);
v_buildTime_976_ = lean_ctor_get(v___y_889_, 2);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___y_889_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_978_ = v___y_889_;
v_isShared_979_ = v_isSharedCheck_1006_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_buildTime_976_);
lean_inc(v_trace_975_);
lean_inc(v_log_972_);
lean_dec(v___y_889_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1006_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_ar_980_; lean_object* v___x_981_; 
v_ar_980_ = lean_ctor_get(v_lean_971_, 13);
lean_inc_ref(v_ar_980_);
v___x_981_ = l_Lake_compileStaticLib(v___y_878_, v_oFiles_879_, v_ar_980_, v_shouldExport_880_, v_log_972_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_993_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
v_a_983_ = lean_ctor_get(v___x_981_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_993_ == 0)
{
v___x_985_ = v___x_981_;
v_isShared_986_ = v_isSharedCheck_993_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_inc(v_a_982_);
lean_dec(v___x_981_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_993_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v_a_983_);
v___x_988_ = v___x_978_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_983_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_trace_975_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v_buildTime_976_);
lean_ctor_set_uint8(v_reuseFailAlloc_992_, sizeof(void*)*3, v_action_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_992_, sizeof(void*)*3 + 1, v_wantsRebuild_974_);
v___x_988_ = v_reuseFailAlloc_992_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v___x_988_);
v___x_990_ = v___x_985_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_982_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v_a_994_; lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1005_; 
v_a_994_ = lean_ctor_get(v___x_981_, 0);
v_a_995_ = lean_ctor_get(v___x_981_, 1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_997_ = v___x_981_;
v_isShared_998_ = v_isSharedCheck_1005_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_inc(v_a_994_);
lean_dec(v___x_981_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1005_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v_a_995_);
v___x_1000_ = v___x_978_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_995_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_trace_975_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_buildTime_976_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*3, v_action_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*3 + 1, v_wantsRebuild_974_);
v___x_1000_ = v_reuseFailAlloc_1004_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1002_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v___x_1000_);
v___x_1002_ = v___x_997_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_994_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1007_; uint8_t v_action_1008_; uint8_t v_wantsRebuild_1009_; lean_object* v_trace_1010_; lean_object* v_buildTime_1011_; lean_object* v___x_1012_; 
v_log_1007_ = lean_ctor_get(v___y_889_, 0);
v_action_1008_ = lean_ctor_get_uint8(v___y_889_, sizeof(void*)*3);
v_wantsRebuild_1009_ = lean_ctor_get_uint8(v___y_889_, sizeof(void*)*3 + 1);
v_trace_1010_ = lean_ctor_get(v___y_889_, 1);
v_buildTime_1011_ = lean_ctor_get(v___y_889_, 2);
lean_inc_ref(v___y_878_);
v___x_1012_ = l_Lake_createParentDirs(v___y_878_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v_a_1016_; lean_object* v___y_1063_; uint8_t v___x_1065_; lean_object* v___x_1066_; 
lean_dec_ref_known(v___x_1012_, 1);
v___x_1013_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_878_);
v___x_1014_ = l_System_FilePath_addExtension(v___y_878_, v___x_1013_);
v___x_1065_ = 1;
v___x_1066_ = lean_io_prim_handle_mk(v___x_1014_, v___x_1065_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1068_ = l_Lake_EquipT_instMonad___redArg(v___x_882_);
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = lean_array_get_size(v_oFiles_879_);
v___x_1071_ = lean_nat_dec_lt(v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_dec_ref(v___x_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v_oFiles_879_);
v_a_1016_ = v___y_889_;
goto v___jp_1015_;
}
else
{
lean_object* v___f_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___f_1072_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1072_, 0, v_a_1067_);
v___x_1073_ = lean_box(0);
v___x_1074_ = lean_nat_dec_le(v___x_1070_, v___x_1070_);
if (v___x_1074_ == 0)
{
if (v___x_1071_ == 0)
{
lean_dec_ref(v___f_1072_);
lean_dec_ref(v___x_1068_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v_oFiles_879_);
v_a_1016_ = v___y_889_;
goto v___jp_1015_;
}
else
{
size_t v___x_1075_; lean_object* v___x_197422__overap_1076_; lean_object* v___x_1077_; 
v___x_1075_ = lean_usize_of_nat(v___x_1070_);
v___x_197422__overap_1076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1068_, v___f_1072_, v_oFiles_879_, v___x_883_, v___x_1075_, v___x_1073_);
lean_inc_ref(v___y_888_);
lean_inc(v___y_887_);
lean_inc(v___y_886_);
lean_inc(v___y_885_);
v___x_1077_ = lean_apply_7(v___x_197422__overap_1076_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, lean_box(0));
v___y_1063_ = v___x_1077_;
goto v___jp_1062_;
}
}
else
{
size_t v___x_1078_; lean_object* v___x_197424__overap_1079_; lean_object* v___x_1080_; 
v___x_1078_ = lean_usize_of_nat(v___x_1070_);
v___x_197424__overap_1079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1068_, v___f_1072_, v_oFiles_879_, v___x_883_, v___x_1078_, v___x_1073_);
lean_inc_ref(v___y_888_);
lean_inc(v___y_887_);
lean_inc(v___y_886_);
lean_inc(v___y_885_);
v___x_1080_ = lean_apply_7(v___x_197424__overap_1079_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, lean_box(0));
v___y_1063_ = v___x_1080_;
goto v___jp_1062_;
}
}
}
else
{
lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1094_; 
lean_inc(v_buildTime_1011_);
lean_inc_ref(v_trace_1010_);
lean_inc_ref(v_log_1007_);
lean_dec_ref(v___x_1014_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v___x_882_);
lean_dec_ref(v_oFiles_879_);
lean_dec_ref(v___y_878_);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___y_889_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; lean_object* v_unused_1096_; lean_object* v_unused_1097_; 
v_unused_1095_ = lean_ctor_get(v___y_889_, 2);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v___y_889_, 1);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v___y_889_, 0);
lean_dec(v_unused_1097_);
v___x_1082_ = v___y_889_;
v_isShared_1083_ = v_isSharedCheck_1094_;
goto v_resetjp_1081_;
}
else
{
lean_dec(v___y_889_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1094_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_a_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1091_; 
v_a_1084_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1085_ = lean_io_error_to_string(v_a_1084_);
v___x_1086_ = 3;
v___x_1087_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*1, v___x_1086_);
v___x_1088_ = lean_array_get_size(v_log_1007_);
v___x_1089_ = lean_array_push(v_log_1007_, v___x_1087_);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1089_);
v___x_1091_ = v___x_1082_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_trace_1010_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_buildTime_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1093_, sizeof(void*)*3, v_action_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1093_, sizeof(void*)*3 + 1, v_wantsRebuild_1009_);
v___x_1091_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1088_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
return v___x_1092_;
}
}
}
v___jp_1015_:
{
lean_object* v___x_1017_; lean_object* v_log_1018_; uint8_t v_action_1019_; uint8_t v_wantsRebuild_1020_; lean_object* v_trace_1021_; lean_object* v_buildTime_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1061_; 
v___x_1017_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1018_ = lean_ctor_get(v_a_1016_, 0);
v_action_1019_ = lean_ctor_get_uint8(v_a_1016_, sizeof(void*)*3);
v_wantsRebuild_1020_ = lean_ctor_get_uint8(v_a_1016_, sizeof(void*)*3 + 1);
v_trace_1021_ = lean_ctor_get(v_a_1016_, 1);
v_buildTime_1022_ = lean_ctor_get(v_a_1016_, 2);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_a_1016_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1024_ = v_a_1016_;
v_isShared_1025_ = v_isSharedCheck_1061_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_buildTime_1022_);
lean_inc(v_trace_1021_);
lean_inc(v_log_1018_);
lean_dec(v_a_1016_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1061_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1026_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1027_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1028_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1029_ = lean_array_push(v___x_1028_, v___y_878_);
v___x_1030_ = lean_array_push(v___x_1029_, v___x_1027_);
v___x_1031_ = lean_array_push(v___x_1030_, v___x_1014_);
v___x_1032_ = lean_box(0);
v___x_1033_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1034_ = 0;
v___x_1035_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1035_, 0, v___x_1017_);
lean_ctor_set(v___x_1035_, 1, v___x_1026_);
lean_ctor_set(v___x_1035_, 2, v___x_1031_);
lean_ctor_set(v___x_1035_, 3, v___x_1032_);
lean_ctor_set(v___x_1035_, 4, v___x_1033_);
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*5, v___x_881_);
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*5 + 1, v___x_1034_);
v___x_1036_ = l_Lake_proc(v___x_1035_, v___x_1034_, v___x_1032_, v_log_1018_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1048_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
v_a_1038_ = lean_ctor_get(v___x_1036_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1040_ = v___x_1036_;
v_isShared_1041_ = v_isSharedCheck_1048_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_inc(v_a_1037_);
lean_dec(v___x_1036_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1048_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v_a_1038_);
v___x_1043_ = v___x_1024_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1038_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v_trace_1021_);
lean_ctor_set(v_reuseFailAlloc_1047_, 2, v_buildTime_1022_);
lean_ctor_set_uint8(v_reuseFailAlloc_1047_, sizeof(void*)*3, v_action_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1047_, sizeof(void*)*3 + 1, v_wantsRebuild_1020_);
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
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_1049_; lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1060_; 
v_a_1049_ = lean_ctor_get(v___x_1036_, 0);
v_a_1050_ = lean_ctor_get(v___x_1036_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1052_ = v___x_1036_;
v_isShared_1053_ = v_isSharedCheck_1060_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_inc(v_a_1049_);
lean_dec(v___x_1036_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1060_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v_a_1050_);
v___x_1055_ = v___x_1024_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1050_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_trace_1021_);
lean_ctor_set(v_reuseFailAlloc_1059_, 2, v_buildTime_1022_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, sizeof(void*)*3, v_action_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, sizeof(void*)*3 + 1, v_wantsRebuild_1020_);
v___x_1055_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1057_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 1, v___x_1055_);
v___x_1057_ = v___x_1052_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1049_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
v___jp_1062_:
{
if (lean_obj_tag(v___y_1063_) == 0)
{
lean_object* v_a_1064_; 
v_a_1064_ = lean_ctor_get(v___y_1063_, 1);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___y_1063_, 2);
v_a_1016_ = v_a_1064_;
goto v___jp_1015_;
}
else
{
lean_dec_ref(v___x_1014_);
lean_dec_ref(v___y_878_);
return v___y_1063_;
}
}
}
else
{
lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1111_; 
lean_inc(v_buildTime_1011_);
lean_inc_ref(v_trace_1010_);
lean_inc_ref(v_log_1007_);
lean_dec_ref(v___y_884_);
lean_dec_ref(v___x_882_);
lean_dec_ref(v_oFiles_879_);
lean_dec_ref(v___y_878_);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___y_889_);
if (v_isSharedCheck_1111_ == 0)
{
lean_object* v_unused_1112_; lean_object* v_unused_1113_; lean_object* v_unused_1114_; 
v_unused_1112_ = lean_ctor_get(v___y_889_, 2);
lean_dec(v_unused_1112_);
v_unused_1113_ = lean_ctor_get(v___y_889_, 1);
lean_dec(v_unused_1113_);
v_unused_1114_ = lean_ctor_get(v___y_889_, 0);
lean_dec(v_unused_1114_);
v___x_1099_ = v___y_889_;
v_isShared_1100_ = v_isSharedCheck_1111_;
goto v_resetjp_1098_;
}
else
{
lean_dec(v___y_889_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1111_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_a_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v_a_1101_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1102_ = lean_io_error_to_string(v_a_1101_);
v___x_1103_ = 3;
v___x_1104_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set_uint8(v___x_1104_, sizeof(void*)*1, v___x_1103_);
v___x_1105_ = lean_array_get_size(v_log_1007_);
v___x_1106_ = lean_array_push(v_log_1007_, v___x_1104_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1106_);
v___x_1108_ = v___x_1099_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_trace_1010_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_buildTime_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1110_, sizeof(void*)*3, v_action_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1110_, sizeof(void*)*3 + 1, v_wantsRebuild_1009_);
v___x_1108_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1105_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
return v___x_1109_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object* v_bootstrap_1115_, lean_object* v___y_1116_, lean_object* v_oFiles_1117_, lean_object* v_shouldExport_1118_, lean_object* v___x_1119_, lean_object* v___x_1120_, lean_object* v___x_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
uint8_t v_bootstrap_boxed_1129_; uint8_t v_shouldExport_boxed_1130_; uint8_t v___x_197796__boxed_1131_; size_t v___x_197798__boxed_1132_; lean_object* v_res_1133_; 
v_bootstrap_boxed_1129_ = lean_unbox(v_bootstrap_1115_);
v_shouldExport_boxed_1130_ = lean_unbox(v_shouldExport_1118_);
v___x_197796__boxed_1131_ = lean_unbox(v___x_1119_);
v___x_197798__boxed_1132_ = lean_unbox_usize(v___x_1121_);
lean_dec(v___x_1121_);
v_res_1133_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(v_bootstrap_boxed_1129_, v___y_1116_, v_oFiles_1117_, v_shouldExport_boxed_1130_, v___x_197796__boxed_1131_, v___x_1120_, v___x_197798__boxed_1132_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec(v___y_1123_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(uint8_t v_bootstrap_1135_, lean_object* v___y_1136_, uint8_t v_shouldExport_1137_, uint8_t v___x_1138_, lean_object* v___x_1139_, size_t v___x_1140_, lean_object* v_oFiles_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___y_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1149_ = lean_box(v_bootstrap_1135_);
v___x_1150_ = lean_box(v_shouldExport_1137_);
v___x_1151_ = lean_box(v___x_1138_);
v___x_1152_ = lean_box_usize(v___x_1140_);
lean_inc_ref(v___y_1136_);
v___y_1153_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed), 14, 7);
lean_closure_set(v___y_1153_, 0, v___x_1149_);
lean_closure_set(v___y_1153_, 1, v___y_1136_);
lean_closure_set(v___y_1153_, 2, v_oFiles_1141_);
lean_closure_set(v___y_1153_, 3, v___x_1150_);
lean_closure_set(v___y_1153_, 4, v___x_1151_);
lean_closure_set(v___y_1153_, 5, v___x_1139_);
lean_closure_set(v___y_1153_, 6, v___x_1152_);
v___x_1154_ = 0;
v___x_1155_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1156_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1136_, v___y_1153_, v___x_1154_, v___x_1155_, v___x_1138_, v___x_1154_, v___x_1154_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1166_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_a_1158_ = lean_ctor_get(v___x_1156_, 1);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1160_ = v___x_1156_;
v_isShared_1161_ = v_isSharedCheck_1166_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1166_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v_path_1162_; lean_object* v___x_1164_; 
v_path_1162_ = lean_ctor_get(v_a_1157_, 1);
lean_inc_ref(v_path_1162_);
lean_dec(v_a_1157_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v_path_1162_);
v___x_1164_ = v___x_1160_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_path_1162_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_a_1158_);
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
lean_object* v_a_1167_; lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
v_a_1167_ = lean_ctor_get(v___x_1156_, 0);
v_a_1168_ = lean_ctor_get(v___x_1156_, 1);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1156_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_inc(v_a_1167_);
lean_dec(v___x_1156_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1167_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object* v_bootstrap_1176_, lean_object* v___y_1177_, lean_object* v_shouldExport_1178_, lean_object* v___x_1179_, lean_object* v___x_1180_, lean_object* v___x_1181_, lean_object* v_oFiles_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
uint8_t v_bootstrap_boxed_1190_; uint8_t v_shouldExport_boxed_1191_; uint8_t v___x_198221__boxed_1192_; size_t v___x_198223__boxed_1193_; lean_object* v_res_1194_; 
v_bootstrap_boxed_1190_ = lean_unbox(v_bootstrap_1176_);
v_shouldExport_boxed_1191_ = lean_unbox(v_shouldExport_1178_);
v___x_198221__boxed_1192_ = lean_unbox(v___x_1179_);
v___x_198223__boxed_1193_ = lean_unbox_usize(v___x_1181_);
lean_dec(v___x_1181_);
v_res_1194_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(v_bootstrap_boxed_1190_, v___y_1177_, v_shouldExport_boxed_1191_, v___x_198221__boxed_1192_, v___x_1180_, v___x_198223__boxed_1193_, v_oFiles_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec(v___y_1184_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object* v___x_1199_, lean_object* v___x_1200_, lean_object* v_config_1201_, lean_object* v_config_1202_, lean_object* v___x_1203_, lean_object* v___f_1204_, uint8_t v_shouldExport_1205_, uint8_t v___x_1206_, lean_object* v___x_1207_, lean_object* v___x_1208_, lean_object* v_dir_1209_, lean_object* v_self_1210_, lean_object* v___f_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___y_1220_; uint8_t v___y_1221_; lean_object* v___y_1222_; size_t v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v_a_1240_; lean_object* v_a_1241_; lean_object* v___y_1285_; lean_object* v___x_1297_; 
lean_inc_ref(v___y_1212_);
lean_inc_ref(v___y_1216_);
lean_inc(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc(v___x_1200_);
v___x_1297_ = lean_apply_7(v___y_1212_, v___x_1199_, v___x_1200_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, lean_box(0));
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v_a_1299_; lean_object* v___x_1300_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
v_a_1299_ = lean_ctor_get(v___x_1297_, 1);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1297_, 2);
v___x_1300_ = l_Lake_Job_await___redArg(v_a_1298_, v_a_1299_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v_a_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
v_a_1302_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1300_, 2);
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_1305_ = lean_array_get_size(v_a_1301_);
v___x_1306_ = lean_nat_dec_lt(v___x_1303_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_dec(v_a_1301_);
lean_dec_ref(v___f_1211_);
v_a_1240_ = v___x_1304_;
v_a_1241_ = v_a_1302_;
goto v___jp_1239_;
}
else
{
uint8_t v___x_1307_; 
v___x_1307_ = lean_nat_dec_le(v___x_1305_, v___x_1305_);
if (v___x_1307_ == 0)
{
if (v___x_1306_ == 0)
{
lean_dec(v_a_1301_);
lean_dec_ref(v___f_1211_);
v_a_1240_ = v___x_1304_;
v_a_1241_ = v_a_1302_;
goto v___jp_1239_;
}
else
{
size_t v___x_1308_; size_t v___x_1309_; lean_object* v___x_197561__overap_1310_; lean_object* v___x_1311_; 
v___x_1308_ = ((size_t)0ULL);
v___x_1309_ = lean_usize_of_nat(v___x_1305_);
lean_inc_ref(v___x_1203_);
v___x_197561__overap_1310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1203_, v___f_1211_, v_a_1301_, v___x_1308_, v___x_1309_, v___x_1304_);
lean_inc_ref(v___y_1216_);
lean_inc(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc(v___x_1200_);
lean_inc_ref(v___y_1212_);
v___x_1311_ = lean_apply_7(v___x_197561__overap_1310_, v___y_1212_, v___x_1200_, v___y_1214_, v___y_1215_, v___y_1216_, v_a_1302_, lean_box(0));
v___y_1285_ = v___x_1311_;
goto v___jp_1284_;
}
}
else
{
size_t v___x_1312_; size_t v___x_1313_; lean_object* v___x_197564__overap_1314_; lean_object* v___x_1315_; 
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = lean_usize_of_nat(v___x_1305_);
lean_inc_ref(v___x_1203_);
v___x_197564__overap_1314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1203_, v___f_1211_, v_a_1301_, v___x_1312_, v___x_1313_, v___x_1304_);
lean_inc_ref(v___y_1216_);
lean_inc(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc(v___x_1200_);
lean_inc_ref(v___y_1212_);
v___x_1315_ = lean_apply_7(v___x_197564__overap_1314_, v___y_1212_, v___x_1200_, v___y_1214_, v___y_1215_, v___y_1216_, v_a_1302_, lean_box(0));
v___y_1285_ = v___x_1315_;
goto v___jp_1284_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___f_1211_);
lean_dec_ref(v_self_1210_);
lean_dec_ref(v_dir_1209_);
lean_dec(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___f_1204_);
lean_dec_ref(v___x_1203_);
lean_dec_ref(v_config_1201_);
lean_dec(v___x_1200_);
v_a_1316_ = lean_ctor_get(v___x_1300_, 0);
v_a_1317_ = lean_ctor_get(v___x_1300_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1300_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_inc(v_a_1316_);
lean_dec(v___x_1300_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1316_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v___y_1212_);
lean_dec_ref(v___f_1211_);
lean_dec_ref(v_self_1210_);
lean_dec_ref(v_dir_1209_);
lean_dec(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___f_1204_);
lean_dec_ref(v___x_1203_);
lean_dec_ref(v_config_1201_);
lean_dec(v___x_1200_);
v_a_1325_ = lean_ctor_get(v___x_1297_, 0);
v_a_1326_ = lean_ctor_get(v___x_1297_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1297_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_inc(v_a_1325_);
lean_dec(v___x_1297_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1325_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
v___jp_1219_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___f_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1226_ = lean_box(v___y_1221_);
v___x_1227_ = lean_box(v_shouldExport_1205_);
v___x_1228_ = lean_box(v___x_1206_);
v___x_1229_ = lean_box_usize(v___y_1223_);
v___f_1230_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed), 14, 6);
lean_closure_set(v___f_1230_, 0, v___x_1226_);
lean_closure_set(v___f_1230_, 1, v___y_1225_);
lean_closure_set(v___f_1230_, 2, v___x_1227_);
lean_closure_set(v___f_1230_, 3, v___x_1228_);
lean_closure_set(v___f_1230_, 4, v___x_1207_);
lean_closure_set(v___f_1230_, 5, v___x_1229_);
v___x_1231_ = l_Array_append___redArg(v___y_1224_, v___y_1220_);
lean_dec_ref(v___y_1220_);
v___x_1232_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_1233_ = l_Lake_Job_collectArray___redArg(v___x_1231_, v___x_1232_);
lean_dec_ref(v___x_1231_);
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1235_ = 0;
v___x_1236_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_1237_ = l_Lake_Job_mapM___redArg(v___x_1208_, v___x_1233_, v___f_1230_, v___x_1234_, v___x_1235_, v___y_1212_, v___x_1200_, v___y_1214_, v___y_1215_, v___y_1216_, v___x_1236_);
lean_dec(v___x_1200_);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v___y_1222_);
return v___x_1238_;
}
v___jp_1239_:
{
lean_object* v_toLeanConfig_1242_; lean_object* v_toLeanConfig_1243_; uint8_t v_bootstrap_1244_; lean_object* v_buildDir_1245_; lean_object* v_nativeLibDir_1246_; lean_object* v_moreLinkObjs_1247_; lean_object* v_moreLinkObjs_1248_; lean_object* v___x_1249_; size_t v_sz_1250_; size_t v___x_1251_; lean_object* v___x_197501__overap_1252_; lean_object* v___x_1253_; 
v_toLeanConfig_1242_ = lean_ctor_get(v_config_1201_, 1);
lean_inc_ref(v_toLeanConfig_1242_);
v_toLeanConfig_1243_ = lean_ctor_get(v_config_1202_, 0);
v_bootstrap_1244_ = lean_ctor_get_uint8(v_config_1201_, sizeof(void*)*27);
v_buildDir_1245_ = lean_ctor_get(v_config_1201_, 5);
lean_inc_ref(v_buildDir_1245_);
v_nativeLibDir_1246_ = lean_ctor_get(v_config_1201_, 7);
lean_inc_ref(v_nativeLibDir_1246_);
lean_dec_ref(v_config_1201_);
v_moreLinkObjs_1247_ = lean_ctor_get(v_toLeanConfig_1242_, 6);
lean_inc_ref(v_moreLinkObjs_1247_);
lean_dec_ref(v_toLeanConfig_1242_);
v_moreLinkObjs_1248_ = lean_ctor_get(v_toLeanConfig_1243_, 6);
v___x_1249_ = l_Array_append___redArg(v_moreLinkObjs_1247_, v_moreLinkObjs_1248_);
v_sz_1250_ = lean_array_size(v___x_1249_);
v___x_1251_ = ((size_t)0ULL);
v___x_197501__overap_1252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1203_, v___f_1204_, v_sz_1250_, v___x_1251_, v___x_1249_);
lean_inc_ref(v___y_1216_);
lean_inc(v___y_1215_);
lean_inc(v___y_1214_);
lean_inc(v___x_1200_);
lean_inc_ref(v___y_1212_);
v___x_1253_ = lean_apply_7(v___x_197501__overap_1252_, v___y_1212_, v___x_1200_, v___y_1214_, v___y_1215_, v___y_1216_, v_a_1241_, lean_box(0));
if (lean_obj_tag(v___x_1253_) == 0)
{
if (v_shouldExport_1205_ == 0)
{
lean_object* v_a_1254_; lean_object* v_a_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
v_a_1255_ = lean_ctor_get(v___x_1253_, 1);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1253_, 2);
v___x_1256_ = l_System_FilePath_normalize(v_buildDir_1245_);
v___x_1257_ = l_Lake_joinRelative(v_dir_1209_, v___x_1256_);
v___x_1258_ = l_System_FilePath_normalize(v_nativeLibDir_1246_);
v___x_1259_ = l_Lake_joinRelative(v___x_1257_, v___x_1258_);
v___x_1260_ = l_Lake_LeanLib_libName(v_self_1210_);
v___x_1261_ = l_Lake_nameToStaticLib(v___x_1260_, v_shouldExport_1205_);
v___x_1262_ = l_Lake_joinRelative(v___x_1259_, v___x_1261_);
v___y_1220_ = v_a_1254_;
v___y_1221_ = v_bootstrap_1244_;
v___y_1222_ = v_a_1255_;
v___y_1223_ = v___x_1251_;
v___y_1224_ = v_a_1240_;
v___y_1225_ = v___x_1262_;
goto v___jp_1219_;
}
else
{
lean_object* v_a_1263_; lean_object* v_a_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v_a_1263_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1263_);
v_a_1264_ = lean_ctor_get(v___x_1253_, 1);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1253_, 2);
v___x_1265_ = l_System_FilePath_normalize(v_buildDir_1245_);
v___x_1266_ = l_Lake_joinRelative(v_dir_1209_, v___x_1265_);
v___x_1267_ = l_System_FilePath_normalize(v_nativeLibDir_1246_);
v___x_1268_ = l_Lake_joinRelative(v___x_1266_, v___x_1267_);
v___x_1269_ = l_Lake_LeanLib_libName(v_self_1210_);
v___x_1270_ = 0;
v___x_1271_ = l_Lake_nameToStaticLib(v___x_1269_, v___x_1270_);
v___x_1272_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_1273_ = l_System_FilePath_addExtension(v___x_1271_, v___x_1272_);
v___x_1274_ = l_Lake_joinRelative(v___x_1268_, v___x_1273_);
v___y_1220_ = v_a_1263_;
v___y_1221_ = v_bootstrap_1244_;
v___y_1222_ = v_a_1264_;
v___y_1223_ = v___x_1251_;
v___y_1224_ = v_a_1240_;
v___y_1225_ = v___x_1274_;
goto v___jp_1219_;
}
}
else
{
lean_object* v_a_1275_; lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_nativeLibDir_1246_);
lean_dec_ref(v_buildDir_1245_);
lean_dec_ref(v_a_1240_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_self_1210_);
lean_dec_ref(v_dir_1209_);
lean_dec(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec(v___x_1200_);
v_a_1275_ = lean_ctor_get(v___x_1253_, 0);
v_a_1276_ = lean_ctor_get(v___x_1253_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1253_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_inc(v_a_1275_);
lean_dec(v___x_1253_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1275_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
v___jp_1284_:
{
if (lean_obj_tag(v___y_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v_a_1287_; 
v_a_1286_ = lean_ctor_get(v___y_1285_, 0);
lean_inc(v_a_1286_);
v_a_1287_ = lean_ctor_get(v___y_1285_, 1);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___y_1285_, 2);
v_a_1240_ = v_a_1286_;
v_a_1241_ = v_a_1287_;
goto v___jp_1239_;
}
else
{
lean_object* v_a_1288_; lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_self_1210_);
lean_dec_ref(v_dir_1209_);
lean_dec(v___x_1208_);
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___f_1204_);
lean_dec_ref(v___x_1203_);
lean_dec_ref(v_config_1201_);
lean_dec(v___x_1200_);
v_a_1288_ = lean_ctor_get(v___y_1285_, 0);
v_a_1289_ = lean_ctor_get(v___y_1285_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___y_1285_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___y_1285_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_inc(v_a_1288_);
lean_dec(v___y_1285_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed(lean_object** _args){
lean_object* v___x_1334_ = _args[0];
lean_object* v___x_1335_ = _args[1];
lean_object* v_config_1336_ = _args[2];
lean_object* v_config_1337_ = _args[3];
lean_object* v___x_1338_ = _args[4];
lean_object* v___f_1339_ = _args[5];
lean_object* v_shouldExport_1340_ = _args[6];
lean_object* v___x_1341_ = _args[7];
lean_object* v___x_1342_ = _args[8];
lean_object* v___x_1343_ = _args[9];
lean_object* v_dir_1344_ = _args[10];
lean_object* v_self_1345_ = _args[11];
lean_object* v___f_1346_ = _args[12];
lean_object* v___y_1347_ = _args[13];
lean_object* v___y_1348_ = _args[14];
lean_object* v___y_1349_ = _args[15];
lean_object* v___y_1350_ = _args[16];
lean_object* v___y_1351_ = _args[17];
lean_object* v___y_1352_ = _args[18];
lean_object* v___y_1353_ = _args[19];
_start:
{
uint8_t v_shouldExport_boxed_1354_; uint8_t v___x_198325__boxed_1355_; lean_object* v_res_1356_; 
v_shouldExport_boxed_1354_ = lean_unbox(v_shouldExport_1340_);
v___x_198325__boxed_1355_ = lean_unbox(v___x_1341_);
v_res_1356_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(v___x_1334_, v___x_1335_, v_config_1336_, v_config_1337_, v___x_1338_, v___f_1339_, v_shouldExport_boxed_1354_, v___x_198325__boxed_1355_, v___x_1342_, v___x_1343_, v_dir_1344_, v_self_1345_, v___f_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec(v_config_1337_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object* v_self_1360_, uint8_t v_shouldExport_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v_toApplicative_1370_; lean_object* v_toBind_1371_; lean_object* v_toFunctor_1372_; lean_object* v_toPure_1373_; lean_object* v___f_1374_; lean_object* v___f_1375_; lean_object* v___f_1376_; lean_object* v___f_1377_; lean_object* v___x_1378_; lean_object* v___f_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v_toBuildConfig_1387_; lean_object* v_registeredJobs_1388_; uint8_t v_verbosity_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___f_1392_; uint8_t v___x_1393_; uint8_t v___x_1394_; uint8_t v___x_1395_; lean_object* v___y_1397_; 
v___x_1369_ = l_instMonadBaseIO;
v_toApplicative_1370_ = lean_ctor_get(v___x_1369_, 0);
v_toBind_1371_ = lean_ctor_get(v___x_1369_, 1);
v_toFunctor_1372_ = lean_ctor_get(v_toApplicative_1370_, 0);
v_toPure_1373_ = lean_ctor_get(v_toApplicative_1370_, 1);
lean_inc_n(v_toBind_1371_, 3);
lean_inc_n(v_toPure_1373_, 5);
v___f_1374_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1374_, 0, v_toPure_1373_);
lean_closure_set(v___f_1374_, 1, v_toBind_1371_);
v___f_1375_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1375_, 0, v_toPure_1373_);
lean_closure_set(v___f_1375_, 1, v_toBind_1371_);
lean_inc_ref(v___f_1374_);
v___f_1376_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1376_, 0, v_toPure_1373_);
lean_closure_set(v___f_1376_, 1, v___f_1374_);
lean_inc_ref_n(v_toFunctor_1372_, 2);
v___f_1377_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1377_, 0, v_toFunctor_1372_);
lean_closure_set(v___f_1377_, 1, v_toPure_1373_);
lean_closure_set(v___f_1377_, 2, v_toBind_1371_);
v___x_1378_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1372_);
v___f_1379_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1379_, 0, v_toPure_1373_);
v___x_1380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
lean_ctor_set(v___x_1380_, 1, v___f_1379_);
lean_ctor_set(v___x_1380_, 2, v___f_1377_);
lean_ctor_set(v___x_1380_, 3, v___f_1376_);
lean_ctor_set(v___x_1380_, 4, v___f_1375_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
lean_ctor_set(v___x_1381_, 1, v___f_1374_);
v___x_1382_ = l_ReaderT_instMonad___redArg(v___x_1381_);
v___x_1383_ = l_StateRefT_x27_instMonad___redArg(v___x_1382_);
v___x_1384_ = l_ReaderT_instMonad___redArg(v___x_1383_);
v___x_1385_ = l_ReaderT_instMonad___redArg(v___x_1384_);
lean_inc_ref(v___x_1385_);
v___x_1386_ = l_Lake_EquipT_instMonad___redArg(v___x_1385_);
v_toBuildConfig_1387_ = lean_ctor_get(v_a_1366_, 0);
v_registeredJobs_1388_ = lean_ctor_get(v_a_1366_, 3);
v_verbosity_1389_ = lean_ctor_get_uint8(v_toBuildConfig_1387_, sizeof(void*)*4 + 3);
v___x_1390_ = l_Lake_instDataKindFilePath;
v___x_1391_ = lean_box(v_shouldExport_1361_);
lean_inc_ref(v___x_1386_);
v___f_1392_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1392_, 0, v___x_1391_);
lean_closure_set(v___f_1392_, 1, v___x_1386_);
v___x_1393_ = 2;
v___x_1394_ = l_Lake_instDecidableEqVerbosity(v_verbosity_1389_, v___x_1393_);
v___x_1395_ = 1;
if (v___x_1394_ == 0)
{
lean_object* v___x_1443_; 
v___x_1443_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_1397_ = v___x_1443_;
goto v___jp_1396_;
}
else
{
if (v_shouldExport_1361_ == 0)
{
lean_object* v___x_1444_; 
v___x_1444_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___y_1397_ = v___x_1444_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1445_; 
v___x_1445_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_1397_ = v___x_1445_;
goto v___jp_1396_;
}
}
v___jp_1396_:
{
lean_object* v_pkg_1398_; lean_object* v_name_1399_; lean_object* v_config_1400_; lean_object* v_keyName_1401_; lean_object* v_dir_1402_; lean_object* v_config_1403_; lean_object* v___f_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___f_1412_; lean_object* v___x_1413_; 
v_pkg_1398_ = lean_ctor_get(v_self_1360_, 0);
v_name_1399_ = lean_ctor_get(v_self_1360_, 1);
lean_inc_n(v_name_1399_, 2);
v_config_1400_ = lean_ctor_get(v_self_1360_, 2);
lean_inc(v_config_1400_);
v_keyName_1401_ = lean_ctor_get(v_pkg_1398_, 2);
v_dir_1402_ = lean_ctor_get(v_pkg_1398_, 4);
lean_inc_ref(v_dir_1402_);
v_config_1403_ = lean_ctor_get(v_pkg_1398_, 6);
lean_inc_ref(v_config_1403_);
lean_inc_ref_n(v_pkg_1398_, 2);
v___f_1404_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(v___f_1404_, 0, v___x_1390_);
lean_closure_set(v___f_1404_, 1, v_pkg_1398_);
v___x_1405_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_1401_);
v___x_1406_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1406_, 0, v_keyName_1401_);
lean_ctor_set(v___x_1406_, 1, v_name_1399_);
v___x_1407_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_1360_);
v___x_1408_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1406_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
lean_ctor_set(v___x_1408_, 2, v_self_1360_);
lean_ctor_set(v___x_1408_, 3, v___x_1405_);
v___x_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1409_, 0, v_pkg_1398_);
v___x_1410_ = lean_box(v_shouldExport_1361_);
v___x_1411_ = lean_box(v___x_1395_);
v___f_1412_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed), 20, 13);
lean_closure_set(v___f_1412_, 0, v___x_1408_);
lean_closure_set(v___f_1412_, 1, v___x_1409_);
lean_closure_set(v___f_1412_, 2, v_config_1403_);
lean_closure_set(v___f_1412_, 3, v_config_1400_);
lean_closure_set(v___f_1412_, 4, v___x_1386_);
lean_closure_set(v___f_1412_, 5, v___f_1404_);
lean_closure_set(v___f_1412_, 6, v___x_1410_);
lean_closure_set(v___f_1412_, 7, v___x_1411_);
lean_closure_set(v___f_1412_, 8, v___x_1385_);
lean_closure_set(v___f_1412_, 9, v___x_1390_);
lean_closure_set(v___f_1412_, 10, v_dir_1402_);
lean_closure_set(v___f_1412_, 11, v_self_1360_);
lean_closure_set(v___f_1412_, 12, v___f_1392_);
v___x_1413_ = l_Lake_ensureJob___redArg(v___x_1390_, v___f_1412_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1442_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_a_1415_ = lean_ctor_get(v___x_1413_, 1);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1417_ = v___x_1413_;
v_isShared_1418_ = v_isSharedCheck_1442_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1442_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_task_1419_; lean_object* v_kind_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1440_; 
v_task_1419_ = lean_ctor_get(v_a_1414_, 0);
v_kind_1420_ = lean_ctor_get(v_a_1414_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_a_1414_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v_a_1414_, 2);
lean_dec(v_unused_1441_);
v___x_1422_ = v_a_1414_;
v_isShared_1423_ = v_isSharedCheck_1440_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_kind_1420_);
lean_inc(v_task_1419_);
lean_dec(v_a_1414_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1440_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; lean_object* v_job_1431_; 
v___x_1424_ = lean_st_ref_take(v_registeredJobs_1388_);
v___x_1425_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1399_, v___x_1395_);
v___x_1426_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0));
v___x_1427_ = lean_string_append(v___x_1425_, v___x_1426_);
v___x_1428_ = lean_string_append(v___x_1427_, v___y_1397_);
v___x_1429_ = 0;
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 2, v___x_1428_);
v_job_1431_ = v___x_1422_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_task_1419_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_kind_1420_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v___x_1428_);
v_job_1431_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
lean_ctor_set_uint8(v_job_1431_, sizeof(void*)*3, v___x_1429_);
lean_inc_ref(v_job_1431_);
v___x_1432_ = l_Lake_Job_toOpaque___redArg(v_job_1431_);
v___x_1433_ = lean_array_push(v___x_1424_, v___x_1432_);
v___x_1434_ = lean_st_ref_set(v_registeredJobs_1388_, v___x_1433_);
v___x_1435_ = l_Lake_Job_renew___redArg(v_job_1431_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1435_);
v___x_1437_ = v___x_1417_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_a_1415_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
else
{
lean_dec(v_name_1399_);
return v___x_1413_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object* v_self_1446_, lean_object* v_shouldExport_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_){
_start:
{
uint8_t v_shouldExport_boxed_1455_; lean_object* v_res_1456_; 
v_shouldExport_boxed_1455_ = lean_unbox(v_shouldExport_1447_);
v_res_1456_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1446_, v_shouldExport_boxed_1455_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec(v_a_1451_);
lean_dec(v_a_1450_);
lean_dec(v_a_1449_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t v_fmt_1457_, lean_object* v_a_1458_){
_start:
{
if (v_fmt_1457_ == 0)
{
return v_a_1458_;
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1459_ = l_Lake_mkRelPathString(v_a_1458_);
v___x_1460_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
v___x_1461_ = l_Lean_Json_compress(v___x_1460_);
return v___x_1461_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object* v_fmt_1462_, lean_object* v_a_1463_){
_start:
{
uint8_t v_fmt_boxed_1464_; lean_object* v_res_1465_; 
v_fmt_boxed_1464_ = lean_unbox(v_fmt_1462_);
v_res_1465_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_boxed_1464_, v_a_1463_);
return v_res_1465_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2(void){
_start:
{
uint8_t v___x_1468_; lean_object* v_name_1469_; lean_object* v___x_1470_; 
v___x_1468_ = 1;
v_name_1469_ = l_Lake_instDataKindFilePath;
v___x_1470_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1469_, v___x_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* v_defaultPkg_1474_, lean_object* v_self_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
uint8_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = 1;
lean_inc_ref_n(v_self_1475_, 2);
v___x_1484_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1474_, v_self_1475_, v_self_1475_, v___x_1483_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v_snd_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1527_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
v_snd_1486_ = lean_ctor_get(v_a_1485_, 1);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_a_1485_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; 
v_unused_1528_ = lean_ctor_get(v_a_1485_, 0);
lean_dec(v_unused_1528_);
v___x_1488_ = v_a_1485_;
v_isShared_1489_ = v_isSharedCheck_1527_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_snd_1486_);
lean_dec(v_a_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1527_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1525_; 
v_a_1490_ = lean_ctor_get(v___x_1484_, 1);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; 
v_unused_1526_ = lean_ctor_get(v___x_1484_, 0);
lean_dec(v_unused_1526_);
v___x_1492_ = v___x_1484_;
v_isShared_1493_ = v_isSharedCheck_1525_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1484_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1525_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_kind_1494_; lean_object* v_name_1495_; lean_object* v___y_1497_; uint8_t v___x_1515_; 
v_kind_1494_ = lean_ctor_get(v_snd_1486_, 1);
v_name_1495_ = l_Lake_instDataKindFilePath;
v___x_1515_ = lean_name_eq(v_kind_1494_, v_name_1495_);
if (v___x_1515_ == 0)
{
uint8_t v___x_1516_; 
lean_inc(v_kind_1494_);
lean_del_object(v___x_1488_);
lean_dec(v_snd_1486_);
v___x_1516_ = l_Lean_Name_isAnonymous(v_kind_1494_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1517_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1518_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1494_, v___x_1483_);
v___x_1519_ = lean_string_append(v___x_1517_, v___x_1518_);
lean_dec_ref(v___x_1518_);
v___x_1520_ = lean_string_append(v___x_1519_, v___x_1517_);
v___y_1497_ = v___x_1520_;
goto v___jp_1496_;
}
else
{
lean_object* v___x_1521_; 
lean_dec(v_kind_1494_);
v___x_1521_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1497_ = v___x_1521_;
goto v___jp_1496_;
}
}
else
{
lean_object* v___x_1523_; 
lean_del_object(v___x_1492_);
lean_dec_ref(v_self_1475_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 1, v_a_1490_);
lean_ctor_set(v___x_1488_, 0, v_snd_1486_);
v___x_1523_ = v___x_1488_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_snd_1486_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_a_1490_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
v___jp_1496_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1498_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1499_ = l_Lake_PartialBuildKey_toString(v_self_1475_);
v___x_1500_ = lean_string_append(v___x_1498_, v___x_1499_);
lean_dec_ref(v___x_1499_);
v___x_1501_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1502_ = lean_string_append(v___x_1500_, v___x_1501_);
v___x_1503_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
v___x_1504_ = lean_string_append(v___x_1502_, v___x_1503_);
v___x_1505_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1506_ = lean_string_append(v___x_1504_, v___x_1505_);
v___x_1507_ = lean_string_append(v___x_1506_, v___y_1497_);
lean_dec_ref(v___y_1497_);
v___x_1508_ = 3;
v___x_1509_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
lean_ctor_set_uint8(v___x_1509_, sizeof(void*)*1, v___x_1508_);
v___x_1510_ = lean_array_get_size(v_a_1490_);
v___x_1511_ = lean_array_push(v_a_1490_, v___x_1509_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 1);
lean_ctor_set(v___x_1492_, 1, v___x_1511_);
lean_ctor_set(v___x_1492_, 0, v___x_1510_);
v___x_1513_ = v___x_1492_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v___x_1511_);
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
else
{
lean_object* v_a_1529_; lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec_ref(v_self_1475_);
v_a_1529_ = lean_ctor_get(v___x_1484_, 0);
v_a_1530_ = lean_ctor_get(v___x_1484_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1484_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_inc(v_a_1529_);
lean_dec(v___x_1484_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1529_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* v_defaultPkg_1538_, lean_object* v_self_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1538_, v_self_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_);
lean_dec_ref(v_a_1544_);
lean_dec(v_a_1543_);
lean_dec(v_a_1542_);
lean_dec(v_a_1541_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* v___x_1548_, size_t v_sz_1549_, size_t v_i_1550_, lean_object* v_bs_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
uint8_t v___x_1559_; 
v___x_1559_ = lean_usize_dec_lt(v_i_1550_, v_sz_1549_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; 
lean_dec_ref(v___y_1552_);
lean_dec_ref(v___x_1548_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v_bs_1551_);
lean_ctor_set(v___x_1560_, 1, v___y_1557_);
return v___x_1560_;
}
else
{
lean_object* v_v_1561_; lean_object* v___x_1562_; 
v_v_1561_ = lean_array_uget_borrowed(v_bs_1551_, v_i_1550_);
lean_inc_ref(v___y_1552_);
lean_inc(v_v_1561_);
lean_inc_ref(v___x_1548_);
v___x_1562_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1548_, v_v_1561_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v_a_1564_; lean_object* v___x_1565_; lean_object* v_bs_x27_1566_; size_t v___x_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
v_a_1564_ = lean_ctor_get(v___x_1562_, 1);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1562_, 2);
v___x_1565_ = lean_unsigned_to_nat(0u);
v_bs_x27_1566_ = lean_array_uset(v_bs_1551_, v_i_1550_, v___x_1565_);
v___x_1567_ = ((size_t)1ULL);
v___x_1568_ = lean_usize_add(v_i_1550_, v___x_1567_);
v___x_1569_ = lean_array_uset(v_bs_x27_1566_, v_i_1550_, v_a_1563_);
v_i_1550_ = v___x_1568_;
v_bs_1551_ = v___x_1569_;
v___y_1557_ = v_a_1564_;
goto _start;
}
else
{
lean_object* v_a_1571_; lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec_ref(v___y_1552_);
lean_dec_ref(v_bs_1551_);
lean_dec_ref(v___x_1548_);
v_a_1571_ = lean_ctor_get(v___x_1562_, 0);
v_a_1572_ = lean_ctor_get(v___x_1562_, 1);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1562_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_inc(v_a_1571_);
lean_dec(v___x_1562_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1571_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* v___x_1580_, lean_object* v_sz_1581_, lean_object* v_i_1582_, lean_object* v_bs_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
size_t v_sz_boxed_1591_; size_t v_i_boxed_1592_; lean_object* v_res_1593_; 
v_sz_boxed_1591_ = lean_unbox_usize(v_sz_1581_);
lean_dec(v_sz_1581_);
v_i_boxed_1592_ = lean_unbox_usize(v_i_1582_);
lean_dec(v_i_1582_);
v_res_1593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1580_, v_sz_boxed_1591_, v_i_boxed_1592_, v_bs_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec(v___y_1585_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(lean_object* v_a_1594_, lean_object* v_as_1595_, size_t v_i_1596_, size_t v_stop_1597_, lean_object* v_b_1598_, lean_object* v___y_1599_){
_start:
{
uint8_t v___x_1601_; 
v___x_1601_ = lean_usize_dec_eq(v_i_1596_, v_stop_1597_);
if (v___x_1601_ == 0)
{
lean_object* v_log_1602_; uint8_t v_action_1603_; uint8_t v_wantsRebuild_1604_; lean_object* v_trace_1605_; lean_object* v_buildTime_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_log_1602_ = lean_ctor_get(v___y_1599_, 0);
v_action_1603_ = lean_ctor_get_uint8(v___y_1599_, sizeof(void*)*3);
v_wantsRebuild_1604_ = lean_ctor_get_uint8(v___y_1599_, sizeof(void*)*3 + 1);
v_trace_1605_ = lean_ctor_get(v___y_1599_, 1);
v_buildTime_1606_ = lean_ctor_get(v___y_1599_, 2);
v___x_1607_ = lean_array_uget_borrowed(v_as_1595_, v_i_1596_);
v___x_1608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
lean_inc(v___x_1607_);
v___x_1609_ = lean_string_append(v___x_1607_, v___x_1608_);
v___x_1610_ = lean_io_prim_handle_put_str(v_a_1594_, v___x_1609_);
lean_dec_ref(v___x_1609_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; size_t v___x_1612_; size_t v___x_1613_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1612_ = ((size_t)1ULL);
v___x_1613_ = lean_usize_add(v_i_1596_, v___x_1612_);
v_i_1596_ = v___x_1613_;
v_b_1598_ = v_a_1611_;
goto _start;
}
else
{
lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1628_; 
lean_inc(v_buildTime_1606_);
lean_inc_ref(v_trace_1605_);
lean_inc_ref(v_log_1602_);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___y_1599_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; lean_object* v_unused_1630_; lean_object* v_unused_1631_; 
v_unused_1629_ = lean_ctor_get(v___y_1599_, 2);
lean_dec(v_unused_1629_);
v_unused_1630_ = lean_ctor_get(v___y_1599_, 1);
lean_dec(v_unused_1630_);
v_unused_1631_ = lean_ctor_get(v___y_1599_, 0);
lean_dec(v_unused_1631_);
v___x_1616_ = v___y_1599_;
v_isShared_1617_ = v_isSharedCheck_1628_;
goto v_resetjp_1615_;
}
else
{
lean_dec(v___y_1599_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1628_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v_a_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
v_a_1618_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1610_, 1);
v___x_1619_ = lean_io_error_to_string(v_a_1618_);
v___x_1620_ = 3;
v___x_1621_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set_uint8(v___x_1621_, sizeof(void*)*1, v___x_1620_);
v___x_1622_ = lean_array_get_size(v_log_1602_);
v___x_1623_ = lean_array_push(v_log_1602_, v___x_1621_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1623_);
v___x_1625_ = v___x_1616_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_trace_1605_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_buildTime_1606_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*3, v_action_1603_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*3 + 1, v_wantsRebuild_1604_);
v___x_1625_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1622_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
return v___x_1626_;
}
}
}
}
else
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v_b_1598_);
lean_ctor_set(v___x_1632_, 1, v___y_1599_);
return v___x_1632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(lean_object* v_a_1633_, lean_object* v_as_1634_, lean_object* v_i_1635_, lean_object* v_stop_1636_, lean_object* v_b_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
size_t v_i_boxed_1640_; size_t v_stop_boxed_1641_; lean_object* v_res_1642_; 
v_i_boxed_1640_ = lean_unbox_usize(v_i_1635_);
lean_dec(v_i_1635_);
v_stop_boxed_1641_ = lean_unbox_usize(v_stop_1636_);
lean_dec(v_stop_1636_);
v_res_1642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1633_, v_as_1634_, v_i_boxed_1640_, v_stop_boxed_1641_, v_b_1637_, v___y_1638_);
lean_dec_ref(v_as_1634_);
lean_dec(v_a_1633_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(uint8_t v_bootstrap_1643_, lean_object* v___y_1644_, lean_object* v_oFiles_1645_, uint8_t v_shouldExport_1646_, uint8_t v___x_1647_, size_t v___x_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
if (v_bootstrap_1643_ == 0)
{
lean_object* v_toContext_1656_; lean_object* v_lakeEnv_1657_; lean_object* v_lean_1658_; lean_object* v_log_1659_; uint8_t v_action_1660_; uint8_t v_wantsRebuild_1661_; lean_object* v_trace_1662_; lean_object* v_buildTime_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1693_; 
v_toContext_1656_ = lean_ctor_get(v___y_1653_, 1);
v_lakeEnv_1657_ = lean_ctor_get(v_toContext_1656_, 0);
v_lean_1658_ = lean_ctor_get(v_lakeEnv_1657_, 1);
v_log_1659_ = lean_ctor_get(v___y_1654_, 0);
v_action_1660_ = lean_ctor_get_uint8(v___y_1654_, sizeof(void*)*3);
v_wantsRebuild_1661_ = lean_ctor_get_uint8(v___y_1654_, sizeof(void*)*3 + 1);
v_trace_1662_ = lean_ctor_get(v___y_1654_, 1);
v_buildTime_1663_ = lean_ctor_get(v___y_1654_, 2);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___y_1654_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1665_ = v___y_1654_;
v_isShared_1666_ = v_isSharedCheck_1693_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_buildTime_1663_);
lean_inc(v_trace_1662_);
lean_inc(v_log_1659_);
lean_dec(v___y_1654_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1693_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v_ar_1667_; lean_object* v___x_1668_; 
v_ar_1667_ = lean_ctor_get(v_lean_1658_, 13);
lean_inc_ref(v_ar_1667_);
v___x_1668_ = l_Lake_compileStaticLib(v___y_1644_, v_oFiles_1645_, v_ar_1667_, v_bootstrap_1643_, v_log_1659_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1680_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_a_1670_ = lean_ctor_get(v___x_1668_, 1);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1672_ = v___x_1668_;
v_isShared_1673_ = v_isSharedCheck_1680_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1680_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v_a_1670_);
v___x_1675_ = v___x_1665_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_a_1670_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_trace_1662_);
lean_ctor_set(v_reuseFailAlloc_1679_, 2, v_buildTime_1663_);
lean_ctor_set_uint8(v_reuseFailAlloc_1679_, sizeof(void*)*3, v_action_1660_);
lean_ctor_set_uint8(v_reuseFailAlloc_1679_, sizeof(void*)*3 + 1, v_wantsRebuild_1661_);
v___x_1675_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1677_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 1, v___x_1675_);
v___x_1677_ = v___x_1672_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1669_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1692_; 
v_a_1681_ = lean_ctor_get(v___x_1668_, 0);
v_a_1682_ = lean_ctor_get(v___x_1668_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1684_ = v___x_1668_;
v_isShared_1685_ = v_isSharedCheck_1692_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_inc(v_a_1681_);
lean_dec(v___x_1668_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1692_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v_a_1682_);
v___x_1687_ = v___x_1665_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1682_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_trace_1662_);
lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_buildTime_1663_);
lean_ctor_set_uint8(v_reuseFailAlloc_1691_, sizeof(void*)*3, v_action_1660_);
lean_ctor_set_uint8(v_reuseFailAlloc_1691_, sizeof(void*)*3 + 1, v_wantsRebuild_1661_);
v___x_1687_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1689_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v___x_1687_);
v___x_1689_ = v___x_1684_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1681_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
}
else
{
uint8_t v___x_1694_; 
v___x_1694_ = l_System_Platform_isOSX;
if (v___x_1694_ == 0)
{
uint8_t v___x_1695_; 
v___x_1695_ = l_System_Platform_isWindows;
if (v___x_1695_ == 0)
{
lean_object* v_toContext_1696_; lean_object* v_lakeEnv_1697_; lean_object* v_lean_1698_; lean_object* v_log_1699_; uint8_t v_action_1700_; uint8_t v_wantsRebuild_1701_; lean_object* v_trace_1702_; lean_object* v_buildTime_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1733_; 
v_toContext_1696_ = lean_ctor_get(v___y_1653_, 1);
v_lakeEnv_1697_ = lean_ctor_get(v_toContext_1696_, 0);
v_lean_1698_ = lean_ctor_get(v_lakeEnv_1697_, 1);
v_log_1699_ = lean_ctor_get(v___y_1654_, 0);
v_action_1700_ = lean_ctor_get_uint8(v___y_1654_, sizeof(void*)*3);
v_wantsRebuild_1701_ = lean_ctor_get_uint8(v___y_1654_, sizeof(void*)*3 + 1);
v_trace_1702_ = lean_ctor_get(v___y_1654_, 1);
v_buildTime_1703_ = lean_ctor_get(v___y_1654_, 2);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___y_1654_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1705_ = v___y_1654_;
v_isShared_1706_ = v_isSharedCheck_1733_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_buildTime_1703_);
lean_inc(v_trace_1702_);
lean_inc(v_log_1699_);
lean_dec(v___y_1654_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1733_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v_ar_1707_; lean_object* v___x_1708_; 
v_ar_1707_ = lean_ctor_get(v_lean_1698_, 13);
lean_inc_ref(v_ar_1707_);
v___x_1708_ = l_Lake_compileStaticLib(v___y_1644_, v_oFiles_1645_, v_ar_1707_, v___x_1695_, v_log_1699_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1720_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_a_1710_ = lean_ctor_get(v___x_1708_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1712_ = v___x_1708_;
v_isShared_1713_ = v_isSharedCheck_1720_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1720_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v_a_1710_);
v___x_1715_ = v___x_1705_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1710_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_trace_1702_);
lean_ctor_set(v_reuseFailAlloc_1719_, 2, v_buildTime_1703_);
lean_ctor_set_uint8(v_reuseFailAlloc_1719_, sizeof(void*)*3, v_action_1700_);
lean_ctor_set_uint8(v_reuseFailAlloc_1719_, sizeof(void*)*3 + 1, v_wantsRebuild_1701_);
v___x_1715_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1717_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 1, v___x_1715_);
v___x_1717_ = v___x_1712_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1709_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1732_; 
v_a_1721_ = lean_ctor_get(v___x_1708_, 0);
v_a_1722_ = lean_ctor_get(v___x_1708_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1724_ = v___x_1708_;
v_isShared_1725_ = v_isSharedCheck_1732_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_inc(v_a_1721_);
lean_dec(v___x_1708_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1732_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v_a_1722_);
v___x_1727_ = v___x_1705_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1722_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_trace_1702_);
lean_ctor_set(v_reuseFailAlloc_1731_, 2, v_buildTime_1703_);
lean_ctor_set_uint8(v_reuseFailAlloc_1731_, sizeof(void*)*3, v_action_1700_);
lean_ctor_set_uint8(v_reuseFailAlloc_1731_, sizeof(void*)*3 + 1, v_wantsRebuild_1701_);
v___x_1727_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1729_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v___x_1727_);
v___x_1729_ = v___x_1724_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1721_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1734_; lean_object* v_lakeEnv_1735_; lean_object* v_lean_1736_; lean_object* v_log_1737_; uint8_t v_action_1738_; uint8_t v_wantsRebuild_1739_; lean_object* v_trace_1740_; lean_object* v_buildTime_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1771_; 
v_toContext_1734_ = lean_ctor_get(v___y_1653_, 1);
v_lakeEnv_1735_ = lean_ctor_get(v_toContext_1734_, 0);
v_lean_1736_ = lean_ctor_get(v_lakeEnv_1735_, 1);
v_log_1737_ = lean_ctor_get(v___y_1654_, 0);
v_action_1738_ = lean_ctor_get_uint8(v___y_1654_, sizeof(void*)*3);
v_wantsRebuild_1739_ = lean_ctor_get_uint8(v___y_1654_, sizeof(void*)*3 + 1);
v_trace_1740_ = lean_ctor_get(v___y_1654_, 1);
v_buildTime_1741_ = lean_ctor_get(v___y_1654_, 2);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___y_1654_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1743_ = v___y_1654_;
v_isShared_1744_ = v_isSharedCheck_1771_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_buildTime_1741_);
lean_inc(v_trace_1740_);
lean_inc(v_log_1737_);
lean_dec(v___y_1654_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1771_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v_ar_1745_; lean_object* v___x_1746_; 
v_ar_1745_ = lean_ctor_get(v_lean_1736_, 13);
lean_inc_ref(v_ar_1745_);
v___x_1746_ = l_Lake_compileStaticLib(v___y_1644_, v_oFiles_1645_, v_ar_1745_, v_shouldExport_1646_, v_log_1737_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1758_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_a_1748_ = lean_ctor_get(v___x_1746_, 1);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1750_ = v___x_1746_;
v_isShared_1751_ = v_isSharedCheck_1758_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1758_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v_a_1748_);
v___x_1753_ = v___x_1743_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1748_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_trace_1740_);
lean_ctor_set(v_reuseFailAlloc_1757_, 2, v_buildTime_1741_);
lean_ctor_set_uint8(v_reuseFailAlloc_1757_, sizeof(void*)*3, v_action_1738_);
lean_ctor_set_uint8(v_reuseFailAlloc_1757_, sizeof(void*)*3 + 1, v_wantsRebuild_1739_);
v___x_1753_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1755_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 1, v___x_1753_);
v___x_1755_ = v___x_1750_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1747_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v___x_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1770_; 
v_a_1759_ = lean_ctor_get(v___x_1746_, 0);
v_a_1760_ = lean_ctor_get(v___x_1746_, 1);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1762_ = v___x_1746_;
v_isShared_1763_ = v_isSharedCheck_1770_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_inc(v_a_1759_);
lean_dec(v___x_1746_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1770_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v_a_1760_);
v___x_1765_ = v___x_1743_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1760_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_trace_1740_);
lean_ctor_set(v_reuseFailAlloc_1769_, 2, v_buildTime_1741_);
lean_ctor_set_uint8(v_reuseFailAlloc_1769_, sizeof(void*)*3, v_action_1738_);
lean_ctor_set_uint8(v_reuseFailAlloc_1769_, sizeof(void*)*3 + 1, v_wantsRebuild_1739_);
v___x_1765_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1767_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 1, v___x_1765_);
v___x_1767_ = v___x_1762_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1759_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1772_; uint8_t v_action_1773_; uint8_t v_wantsRebuild_1774_; lean_object* v_trace_1775_; lean_object* v_buildTime_1776_; lean_object* v___x_1777_; 
v_log_1772_ = lean_ctor_get(v___y_1654_, 0);
v_action_1773_ = lean_ctor_get_uint8(v___y_1654_, sizeof(void*)*3);
v_wantsRebuild_1774_ = lean_ctor_get_uint8(v___y_1654_, sizeof(void*)*3 + 1);
v_trace_1775_ = lean_ctor_get(v___y_1654_, 1);
v_buildTime_1776_ = lean_ctor_get(v___y_1654_, 2);
lean_inc_ref(v___y_1644_);
v___x_1777_ = l_Lake_createParentDirs(v___y_1644_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v_a_1781_; lean_object* v___y_1830_; uint8_t v___x_1832_; lean_object* v___x_1833_; 
lean_dec_ref_known(v___x_1777_, 1);
v___x_1778_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1644_);
v___x_1779_ = l_System_FilePath_addExtension(v___y_1644_, v___x_1778_);
v___x_1832_ = 1;
v___x_1833_ = lean_io_prim_handle_mk(v___x_1779_, v___x_1832_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1835_ = lean_unsigned_to_nat(0u);
v___x_1836_ = lean_array_get_size(v_oFiles_1645_);
v___x_1837_ = lean_nat_dec_lt(v___x_1835_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_dec(v_a_1834_);
lean_dec_ref(v_oFiles_1645_);
v_a_1781_ = v___y_1654_;
goto v___jp_1780_;
}
else
{
lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = lean_nat_dec_le(v___x_1836_, v___x_1836_);
if (v___x_1839_ == 0)
{
if (v___x_1837_ == 0)
{
lean_dec(v_a_1834_);
lean_dec_ref(v_oFiles_1645_);
v_a_1781_ = v___y_1654_;
goto v___jp_1780_;
}
else
{
size_t v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_usize_of_nat(v___x_1836_);
v___x_1841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1834_, v_oFiles_1645_, v___x_1648_, v___x_1840_, v___x_1838_, v___y_1654_);
lean_dec_ref(v_oFiles_1645_);
lean_dec(v_a_1834_);
v___y_1830_ = v___x_1841_;
goto v___jp_1829_;
}
}
else
{
size_t v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = lean_usize_of_nat(v___x_1836_);
v___x_1843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1834_, v_oFiles_1645_, v___x_1648_, v___x_1842_, v___x_1838_, v___y_1654_);
lean_dec_ref(v_oFiles_1645_);
lean_dec(v_a_1834_);
v___y_1830_ = v___x_1843_;
goto v___jp_1829_;
}
}
}
else
{
lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1857_; 
lean_inc(v_buildTime_1776_);
lean_inc_ref(v_trace_1775_);
lean_inc_ref(v_log_1772_);
lean_dec_ref(v___x_1779_);
lean_dec_ref(v_oFiles_1645_);
lean_dec_ref(v___y_1644_);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___y_1654_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; lean_object* v_unused_1859_; lean_object* v_unused_1860_; 
v_unused_1858_ = lean_ctor_get(v___y_1654_, 2);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v___y_1654_, 1);
lean_dec(v_unused_1859_);
v_unused_1860_ = lean_ctor_get(v___y_1654_, 0);
lean_dec(v_unused_1860_);
v___x_1845_ = v___y_1654_;
v_isShared_1846_ = v_isSharedCheck_1857_;
goto v_resetjp_1844_;
}
else
{
lean_dec(v___y_1654_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1857_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v_a_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
v_a_1847_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1848_ = lean_io_error_to_string(v_a_1847_);
v___x_1849_ = 3;
v___x_1850_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set_uint8(v___x_1850_, sizeof(void*)*1, v___x_1849_);
v___x_1851_ = lean_array_get_size(v_log_1772_);
v___x_1852_ = lean_array_push(v_log_1772_, v___x_1850_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1852_);
v___x_1854_ = v___x_1845_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_trace_1775_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v_buildTime_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1856_, sizeof(void*)*3, v_action_1773_);
lean_ctor_set_uint8(v_reuseFailAlloc_1856_, sizeof(void*)*3 + 1, v_wantsRebuild_1774_);
v___x_1854_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1851_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
return v___x_1855_;
}
}
}
v___jp_1780_:
{
lean_object* v___x_1782_; lean_object* v_log_1783_; uint8_t v_action_1784_; uint8_t v_wantsRebuild_1785_; lean_object* v_trace_1786_; lean_object* v_buildTime_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1828_; 
v___x_1782_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1783_ = lean_ctor_get(v_a_1781_, 0);
v_action_1784_ = lean_ctor_get_uint8(v_a_1781_, sizeof(void*)*3);
v_wantsRebuild_1785_ = lean_ctor_get_uint8(v_a_1781_, sizeof(void*)*3 + 1);
v_trace_1786_ = lean_ctor_get(v_a_1781_, 1);
v_buildTime_1787_ = lean_ctor_get(v_a_1781_, 2);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_a_1781_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1789_ = v_a_1781_;
v_isShared_1790_ = v_isSharedCheck_1828_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_buildTime_1787_);
lean_inc(v_trace_1786_);
lean_inc(v_log_1783_);
lean_dec(v_a_1781_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1828_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1791_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1792_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1793_ = lean_unsigned_to_nat(5u);
v___x_1794_ = lean_mk_empty_array_with_capacity(v___x_1793_);
lean_dec_ref(v___x_1794_);
v___x_1795_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1796_ = lean_array_push(v___x_1795_, v___y_1644_);
v___x_1797_ = lean_array_push(v___x_1796_, v___x_1792_);
v___x_1798_ = lean_array_push(v___x_1797_, v___x_1779_);
v___x_1799_ = lean_box(0);
v___x_1800_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1801_ = 0;
v___x_1802_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1802_, 0, v___x_1782_);
lean_ctor_set(v___x_1802_, 1, v___x_1791_);
lean_ctor_set(v___x_1802_, 2, v___x_1798_);
lean_ctor_set(v___x_1802_, 3, v___x_1799_);
lean_ctor_set(v___x_1802_, 4, v___x_1800_);
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*5, v___x_1647_);
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*5 + 1, v___x_1801_);
v___x_1803_ = l_Lake_proc(v___x_1802_, v___x_1801_, v___x_1799_, v_log_1783_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1815_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
v_a_1805_ = lean_ctor_get(v___x_1803_, 1);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1807_ = v___x_1803_;
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_inc(v_a_1804_);
lean_dec(v___x_1803_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1815_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v_a_1805_);
v___x_1810_ = v___x_1789_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1805_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_trace_1786_);
lean_ctor_set(v_reuseFailAlloc_1814_, 2, v_buildTime_1787_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*3, v_action_1784_);
lean_ctor_set_uint8(v_reuseFailAlloc_1814_, sizeof(void*)*3 + 1, v_wantsRebuild_1785_);
v___x_1810_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1812_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 1, v___x_1810_);
v___x_1812_ = v___x_1807_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1804_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1827_; 
v_a_1816_ = lean_ctor_get(v___x_1803_, 0);
v_a_1817_ = lean_ctor_get(v___x_1803_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1819_ = v___x_1803_;
v_isShared_1820_ = v_isSharedCheck_1827_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_inc(v_a_1816_);
lean_dec(v___x_1803_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1827_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v_a_1817_);
v___x_1822_ = v___x_1789_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1817_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_trace_1786_);
lean_ctor_set(v_reuseFailAlloc_1826_, 2, v_buildTime_1787_);
lean_ctor_set_uint8(v_reuseFailAlloc_1826_, sizeof(void*)*3, v_action_1784_);
lean_ctor_set_uint8(v_reuseFailAlloc_1826_, sizeof(void*)*3 + 1, v_wantsRebuild_1785_);
v___x_1822_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1824_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 1, v___x_1822_);
v___x_1824_ = v___x_1819_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1816_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
}
v___jp_1829_:
{
if (lean_obj_tag(v___y_1830_) == 0)
{
lean_object* v_a_1831_; 
v_a_1831_ = lean_ctor_get(v___y_1830_, 1);
lean_inc(v_a_1831_);
lean_dec_ref_known(v___y_1830_, 2);
v_a_1781_ = v_a_1831_;
goto v___jp_1780_;
}
else
{
lean_dec_ref(v___x_1779_);
lean_dec_ref(v___y_1644_);
return v___y_1830_;
}
}
}
else
{
lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1874_; 
lean_inc(v_buildTime_1776_);
lean_inc_ref(v_trace_1775_);
lean_inc_ref(v_log_1772_);
lean_dec_ref(v_oFiles_1645_);
lean_dec_ref(v___y_1644_);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___y_1654_);
if (v_isSharedCheck_1874_ == 0)
{
lean_object* v_unused_1875_; lean_object* v_unused_1876_; lean_object* v_unused_1877_; 
v_unused_1875_ = lean_ctor_get(v___y_1654_, 2);
lean_dec(v_unused_1875_);
v_unused_1876_ = lean_ctor_get(v___y_1654_, 1);
lean_dec(v_unused_1876_);
v_unused_1877_ = lean_ctor_get(v___y_1654_, 0);
lean_dec(v_unused_1877_);
v___x_1862_ = v___y_1654_;
v_isShared_1863_ = v_isSharedCheck_1874_;
goto v_resetjp_1861_;
}
else
{
lean_dec(v___y_1654_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1874_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_a_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; 
v_a_1864_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1777_, 1);
v___x_1865_ = lean_io_error_to_string(v_a_1864_);
v___x_1866_ = 3;
v___x_1867_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*1, v___x_1866_);
v___x_1868_ = lean_array_get_size(v_log_1772_);
v___x_1869_ = lean_array_push(v_log_1772_, v___x_1867_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1869_);
v___x_1871_ = v___x_1862_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_trace_1775_);
lean_ctor_set(v_reuseFailAlloc_1873_, 2, v_buildTime_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1873_, sizeof(void*)*3, v_action_1773_);
lean_ctor_set_uint8(v_reuseFailAlloc_1873_, sizeof(void*)*3 + 1, v_wantsRebuild_1774_);
v___x_1871_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1868_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
return v___x_1872_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object* v_bootstrap_1878_, lean_object* v___y_1879_, lean_object* v_oFiles_1880_, lean_object* v_shouldExport_1881_, lean_object* v___x_1882_, lean_object* v___x_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
uint8_t v_bootstrap_boxed_1891_; uint8_t v_shouldExport_boxed_1892_; uint8_t v___x_6746__boxed_1893_; size_t v___x_6747__boxed_1894_; lean_object* v_res_1895_; 
v_bootstrap_boxed_1891_ = lean_unbox(v_bootstrap_1878_);
v_shouldExport_boxed_1892_ = lean_unbox(v_shouldExport_1881_);
v___x_6746__boxed_1893_ = lean_unbox(v___x_1882_);
v___x_6747__boxed_1894_ = lean_unbox_usize(v___x_1883_);
lean_dec(v___x_1883_);
v_res_1895_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_boxed_1891_, v___y_1879_, v_oFiles_1880_, v_shouldExport_boxed_1892_, v___x_6746__boxed_1893_, v___x_6747__boxed_1894_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec(v___y_1885_);
lean_dec_ref(v___y_1884_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t v_bootstrap_1896_, lean_object* v___y_1897_, uint8_t v_shouldExport_1898_, uint8_t v___x_1899_, size_t v___x_1900_, lean_object* v_oFiles_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___y_1913_; uint8_t v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1909_ = lean_box(v_bootstrap_1896_);
v___x_1910_ = lean_box(v_shouldExport_1898_);
v___x_1911_ = lean_box(v___x_1899_);
v___x_1912_ = lean_box_usize(v___x_1900_);
lean_inc_ref(v___y_1897_);
v___y_1913_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed), 13, 6);
lean_closure_set(v___y_1913_, 0, v___x_1909_);
lean_closure_set(v___y_1913_, 1, v___y_1897_);
lean_closure_set(v___y_1913_, 2, v_oFiles_1901_);
lean_closure_set(v___y_1913_, 3, v___x_1910_);
lean_closure_set(v___y_1913_, 4, v___x_1911_);
lean_closure_set(v___y_1913_, 5, v___x_1912_);
v___x_1914_ = 0;
v___x_1915_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1916_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1897_, v___y_1913_, v___x_1914_, v___x_1915_, v___x_1899_, v___x_1914_, v___x_1914_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1926_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_a_1918_ = lean_ctor_get(v___x_1916_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1920_ = v___x_1916_;
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1926_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_path_1922_; lean_object* v___x_1924_; 
v_path_1922_ = lean_ctor_get(v_a_1917_, 1);
lean_inc_ref(v_path_1922_);
lean_dec(v_a_1917_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v_path_1922_);
v___x_1924_ = v___x_1920_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_path_1922_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_a_1918_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
v_a_1927_ = lean_ctor_get(v___x_1916_, 0);
v_a_1928_ = lean_ctor_get(v___x_1916_, 1);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1916_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_inc(v_a_1927_);
lean_dec(v___x_1916_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1927_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_a_1928_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* v_bootstrap_1936_, lean_object* v___y_1937_, lean_object* v_shouldExport_1938_, lean_object* v___x_1939_, lean_object* v___x_1940_, lean_object* v_oFiles_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
uint8_t v_bootstrap_boxed_1949_; uint8_t v_shouldExport_boxed_1950_; uint8_t v___x_7156__boxed_1951_; size_t v___x_7157__boxed_1952_; lean_object* v_res_1953_; 
v_bootstrap_boxed_1949_ = lean_unbox(v_bootstrap_1936_);
v_shouldExport_boxed_1950_ = lean_unbox(v_shouldExport_1938_);
v___x_7156__boxed_1951_ = lean_unbox(v___x_1939_);
v___x_7157__boxed_1952_ = lean_unbox_usize(v___x_1940_);
lean_dec(v___x_1940_);
v_res_1953_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_boxed_1949_, v___y_1937_, v_shouldExport_boxed_1950_, v___x_7156__boxed_1951_, v___x_7157__boxed_1952_, v_oFiles_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec(v___y_1943_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* v_a_1954_, size_t v_sz_1955_, size_t v_i_1956_, lean_object* v_bs_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
uint8_t v___x_1965_; 
v___x_1965_ = lean_usize_dec_lt(v_i_1956_, v_sz_1955_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
lean_dec_ref(v___y_1958_);
lean_dec_ref(v_a_1954_);
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_bs_1957_);
lean_ctor_set(v___x_1966_, 1, v___y_1963_);
return v___x_1966_;
}
else
{
lean_object* v_v_1967_; lean_object* v___x_1968_; 
v_v_1967_ = lean_array_uget_borrowed(v_bs_1957_, v_i_1956_);
lean_inc_ref(v___y_1958_);
lean_inc_ref(v_a_1954_);
lean_inc(v_v_1967_);
v___x_1968_ = l_Lake_ModuleFacet_fetch___redArg(v_v_1967_, v_a_1954_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v_a_1970_; lean_object* v___x_1971_; lean_object* v_bs_x27_1972_; size_t v___x_1973_; size_t v___x_1974_; lean_object* v___x_1975_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
v_a_1970_ = lean_ctor_get(v___x_1968_, 1);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1968_, 2);
v___x_1971_ = lean_unsigned_to_nat(0u);
v_bs_x27_1972_ = lean_array_uset(v_bs_1957_, v_i_1956_, v___x_1971_);
v___x_1973_ = ((size_t)1ULL);
v___x_1974_ = lean_usize_add(v_i_1956_, v___x_1973_);
v___x_1975_ = lean_array_uset(v_bs_x27_1972_, v_i_1956_, v_a_1969_);
v_i_1956_ = v___x_1974_;
v_bs_1957_ = v___x_1975_;
v___y_1963_ = v_a_1970_;
goto _start;
}
else
{
lean_object* v_a_1977_; lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec_ref(v___y_1958_);
lean_dec_ref(v_bs_1957_);
lean_dec_ref(v_a_1954_);
v_a_1977_ = lean_ctor_get(v___x_1968_, 0);
v_a_1978_ = lean_ctor_get(v___x_1968_, 1);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1968_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_inc(v_a_1977_);
lean_dec(v___x_1968_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1977_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object* v_a_1986_, lean_object* v_sz_1987_, lean_object* v_i_1988_, lean_object* v_bs_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
size_t v_sz_boxed_1997_; size_t v_i_boxed_1998_; lean_object* v_res_1999_; 
v_sz_boxed_1997_ = lean_unbox_usize(v_sz_1987_);
lean_dec(v_sz_1987_);
v_i_boxed_1998_ = lean_unbox_usize(v_i_1988_);
lean_dec(v_i_1988_);
v_res_1999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_1986_, v_sz_boxed_1997_, v_i_boxed_1998_, v_bs_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec(v___y_1991_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(uint8_t v_shouldExport_2000_, lean_object* v_as_2001_, size_t v_i_2002_, size_t v_stop_2003_, lean_object* v_b_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
uint8_t v___x_2012_; 
v___x_2012_ = lean_usize_dec_eq(v_i_2002_, v_stop_2003_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; lean_object* v_lib_2014_; lean_object* v_config_2015_; lean_object* v_nativeFacets_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; size_t v_sz_2019_; size_t v___x_2020_; lean_object* v___x_2021_; 
v___x_2013_ = lean_array_uget_borrowed(v_as_2001_, v_i_2002_);
v_lib_2014_ = lean_ctor_get(v___x_2013_, 0);
v_config_2015_ = lean_ctor_get(v_lib_2014_, 2);
v_nativeFacets_2016_ = lean_ctor_get(v_config_2015_, 8);
v___x_2017_ = lean_box(v_shouldExport_2000_);
lean_inc_ref(v_nativeFacets_2016_);
v___x_2018_ = lean_apply_1(v_nativeFacets_2016_, v___x_2017_);
v_sz_2019_ = lean_array_size(v___x_2018_);
v___x_2020_ = ((size_t)0ULL);
lean_inc_ref(v___y_2005_);
lean_inc(v___x_2013_);
v___x_2021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2013_, v_sz_2019_, v___x_2020_, v___x_2018_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v_a_2023_; lean_object* v___x_2024_; size_t v___x_2025_; size_t v___x_2026_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
v_a_2023_ = lean_ctor_get(v___x_2021_, 1);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2021_, 2);
v___x_2024_ = l_Array_append___redArg(v_b_2004_, v_a_2022_);
lean_dec(v_a_2022_);
v___x_2025_ = ((size_t)1ULL);
v___x_2026_ = lean_usize_add(v_i_2002_, v___x_2025_);
v_i_2002_ = v___x_2026_;
v_b_2004_ = v___x_2024_;
v___y_2010_ = v_a_2023_;
goto _start;
}
else
{
lean_dec_ref(v___y_2005_);
lean_dec_ref(v_b_2004_);
return v___x_2021_;
}
}
else
{
lean_object* v___x_2028_; 
lean_dec_ref(v___y_2005_);
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v_b_2004_);
lean_ctor_set(v___x_2028_, 1, v___y_2010_);
return v___x_2028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(lean_object* v_shouldExport_2029_, lean_object* v_as_2030_, lean_object* v_i_2031_, lean_object* v_stop_2032_, lean_object* v_b_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
uint8_t v_shouldExport_boxed_2041_; size_t v_i_boxed_2042_; size_t v_stop_boxed_2043_; lean_object* v_res_2044_; 
v_shouldExport_boxed_2041_ = lean_unbox(v_shouldExport_2029_);
v_i_boxed_2042_ = lean_unbox_usize(v_i_2031_);
lean_dec(v_i_2031_);
v_stop_boxed_2043_ = lean_unbox_usize(v_stop_2032_);
lean_dec(v_stop_2032_);
v_res_2044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_boxed_2041_, v_as_2030_, v_i_boxed_2042_, v_stop_boxed_2043_, v_b_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v_as_2030_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object* v___x_2045_, lean_object* v___x_2046_, lean_object* v_config_2047_, lean_object* v_config_2048_, lean_object* v_pkg_2049_, uint8_t v_shouldExport_2050_, uint8_t v___x_2051_, lean_object* v___x_2052_, lean_object* v_dir_2053_, lean_object* v_self_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
uint8_t v___y_2063_; size_t v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v_a_2083_; lean_object* v_a_2084_; lean_object* v___y_2127_; lean_object* v___x_2139_; 
lean_inc_ref(v___y_2055_);
lean_inc_ref(v___y_2059_);
lean_inc(v___y_2058_);
lean_inc(v___y_2057_);
lean_inc(v___x_2046_);
v___x_2139_ = lean_apply_7(v___y_2055_, v___x_2045_, v___x_2046_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, lean_box(0));
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v_a_2141_; lean_object* v___x_2142_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
v_a_2141_ = lean_ctor_get(v___x_2139_, 1);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2139_, 2);
v___x_2142_ = l_Lake_Job_await___redArg(v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v_a_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
v_a_2144_ = lean_ctor_get(v___x_2142_, 1);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2142_, 2);
v___x_2145_ = lean_unsigned_to_nat(0u);
v___x_2146_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_2147_ = lean_array_get_size(v_a_2143_);
v___x_2148_ = lean_nat_dec_lt(v___x_2145_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_dec(v_a_2143_);
v_a_2083_ = v___x_2146_;
v_a_2084_ = v_a_2144_;
goto v___jp_2082_;
}
else
{
uint8_t v___x_2149_; 
v___x_2149_ = lean_nat_dec_le(v___x_2147_, v___x_2147_);
if (v___x_2149_ == 0)
{
if (v___x_2148_ == 0)
{
lean_dec(v_a_2143_);
v_a_2083_ = v___x_2146_;
v_a_2084_ = v_a_2144_;
goto v___jp_2082_;
}
else
{
size_t v___x_2150_; size_t v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = ((size_t)0ULL);
v___x_2151_ = lean_usize_of_nat(v___x_2147_);
lean_inc_ref(v___y_2055_);
v___x_2152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2050_, v_a_2143_, v___x_2150_, v___x_2151_, v___x_2146_, v___y_2055_, v___x_2046_, v___y_2057_, v___y_2058_, v___y_2059_, v_a_2144_);
lean_dec(v_a_2143_);
v___y_2127_ = v___x_2152_;
goto v___jp_2126_;
}
}
else
{
size_t v___x_2153_; size_t v___x_2154_; lean_object* v___x_2155_; 
v___x_2153_ = ((size_t)0ULL);
v___x_2154_ = lean_usize_of_nat(v___x_2147_);
lean_inc_ref(v___y_2055_);
v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2050_, v_a_2143_, v___x_2153_, v___x_2154_, v___x_2146_, v___y_2055_, v___x_2046_, v___y_2057_, v___y_2058_, v___y_2059_, v_a_2144_);
lean_dec(v_a_2143_);
v___y_2127_ = v___x_2155_;
goto v___jp_2126_;
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec_ref(v___y_2055_);
lean_dec_ref(v_self_2054_);
lean_dec_ref(v_dir_2053_);
lean_dec(v___x_2052_);
lean_dec_ref(v_pkg_2049_);
lean_dec_ref(v_config_2047_);
lean_dec(v___x_2046_);
v_a_2156_ = lean_ctor_get(v___x_2142_, 0);
v_a_2157_ = lean_ctor_get(v___x_2142_, 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2142_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_inc(v_a_2156_);
lean_dec(v___x_2142_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2156_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec_ref(v___y_2055_);
lean_dec_ref(v_self_2054_);
lean_dec_ref(v_dir_2053_);
lean_dec(v___x_2052_);
lean_dec_ref(v_pkg_2049_);
lean_dec_ref(v_config_2047_);
lean_dec(v___x_2046_);
v_a_2165_ = lean_ctor_get(v___x_2139_, 0);
v_a_2166_ = lean_ctor_get(v___x_2139_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2139_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_inc(v_a_2165_);
lean_dec(v___x_2139_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2165_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
v___jp_2062_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___f_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; uint8_t v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2069_ = lean_box(v___y_2063_);
v___x_2070_ = lean_box(v_shouldExport_2050_);
v___x_2071_ = lean_box(v___x_2051_);
v___x_2072_ = lean_box_usize(v___y_2064_);
v___f_2073_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2073_, 0, v___x_2069_);
lean_closure_set(v___f_2073_, 1, v___y_2068_);
lean_closure_set(v___f_2073_, 2, v___x_2070_);
lean_closure_set(v___f_2073_, 3, v___x_2071_);
lean_closure_set(v___f_2073_, 4, v___x_2072_);
v___x_2074_ = l_Array_append___redArg(v___y_2067_, v___y_2065_);
lean_dec_ref(v___y_2065_);
v___x_2075_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_2076_ = l_Lake_Job_collectArray___redArg(v___x_2074_, v___x_2075_);
lean_dec_ref(v___x_2074_);
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2078_ = 0;
v___x_2079_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2080_ = l_Lake_Job_mapM___redArg(v___x_2052_, v___x_2076_, v___f_2073_, v___x_2077_, v___x_2078_, v___y_2055_, v___x_2046_, v___y_2057_, v___y_2058_, v___y_2059_, v___x_2079_);
lean_dec(v___x_2046_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
lean_ctor_set(v___x_2081_, 1, v___y_2066_);
return v___x_2081_;
}
v___jp_2082_:
{
lean_object* v_toLeanConfig_2085_; lean_object* v_toLeanConfig_2086_; uint8_t v_bootstrap_2087_; lean_object* v_buildDir_2088_; lean_object* v_nativeLibDir_2089_; lean_object* v_moreLinkObjs_2090_; lean_object* v_moreLinkObjs_2091_; lean_object* v___x_2092_; size_t v_sz_2093_; size_t v___x_2094_; lean_object* v___x_2095_; 
v_toLeanConfig_2085_ = lean_ctor_get(v_config_2047_, 1);
lean_inc_ref(v_toLeanConfig_2085_);
v_toLeanConfig_2086_ = lean_ctor_get(v_config_2048_, 0);
v_bootstrap_2087_ = lean_ctor_get_uint8(v_config_2047_, sizeof(void*)*27);
v_buildDir_2088_ = lean_ctor_get(v_config_2047_, 5);
lean_inc_ref(v_buildDir_2088_);
v_nativeLibDir_2089_ = lean_ctor_get(v_config_2047_, 7);
lean_inc_ref(v_nativeLibDir_2089_);
lean_dec_ref(v_config_2047_);
v_moreLinkObjs_2090_ = lean_ctor_get(v_toLeanConfig_2085_, 6);
lean_inc_ref(v_moreLinkObjs_2090_);
lean_dec_ref(v_toLeanConfig_2085_);
v_moreLinkObjs_2091_ = lean_ctor_get(v_toLeanConfig_2086_, 6);
v___x_2092_ = l_Array_append___redArg(v_moreLinkObjs_2090_, v_moreLinkObjs_2091_);
v_sz_2093_ = lean_array_size(v___x_2092_);
v___x_2094_ = ((size_t)0ULL);
lean_inc_ref(v___y_2055_);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_2049_, v_sz_2093_, v___x_2094_, v___x_2092_, v___y_2055_, v___x_2046_, v___y_2057_, v___y_2058_, v___y_2059_, v_a_2084_);
if (lean_obj_tag(v___x_2095_) == 0)
{
if (v_shouldExport_2050_ == 0)
{
lean_object* v_a_2096_; lean_object* v_a_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
v_a_2097_ = lean_ctor_get(v___x_2095_, 1);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2095_, 2);
v___x_2098_ = l_System_FilePath_normalize(v_buildDir_2088_);
v___x_2099_ = l_Lake_joinRelative(v_dir_2053_, v___x_2098_);
v___x_2100_ = l_System_FilePath_normalize(v_nativeLibDir_2089_);
v___x_2101_ = l_Lake_joinRelative(v___x_2099_, v___x_2100_);
v___x_2102_ = l_Lake_LeanLib_libName(v_self_2054_);
v___x_2103_ = l_Lake_nameToStaticLib(v___x_2102_, v_shouldExport_2050_);
v___x_2104_ = l_Lake_joinRelative(v___x_2101_, v___x_2103_);
v___y_2063_ = v_bootstrap_2087_;
v___y_2064_ = v___x_2094_;
v___y_2065_ = v_a_2096_;
v___y_2066_ = v_a_2097_;
v___y_2067_ = v_a_2083_;
v___y_2068_ = v___x_2104_;
goto v___jp_2062_;
}
else
{
lean_object* v_a_2105_; lean_object* v_a_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v_a_2105_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2105_);
v_a_2106_ = lean_ctor_get(v___x_2095_, 1);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2095_, 2);
v___x_2107_ = l_System_FilePath_normalize(v_buildDir_2088_);
v___x_2108_ = l_Lake_joinRelative(v_dir_2053_, v___x_2107_);
v___x_2109_ = l_System_FilePath_normalize(v_nativeLibDir_2089_);
v___x_2110_ = l_Lake_joinRelative(v___x_2108_, v___x_2109_);
v___x_2111_ = l_Lake_LeanLib_libName(v_self_2054_);
v___x_2112_ = 0;
v___x_2113_ = l_Lake_nameToStaticLib(v___x_2111_, v___x_2112_);
v___x_2114_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_2115_ = l_System_FilePath_addExtension(v___x_2113_, v___x_2114_);
v___x_2116_ = l_Lake_joinRelative(v___x_2110_, v___x_2115_);
v___y_2063_ = v_bootstrap_2087_;
v___y_2064_ = v___x_2094_;
v___y_2065_ = v_a_2105_;
v___y_2066_ = v_a_2106_;
v___y_2067_ = v_a_2083_;
v___y_2068_ = v___x_2116_;
goto v___jp_2062_;
}
}
else
{
lean_object* v_a_2117_; lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec_ref(v_nativeLibDir_2089_);
lean_dec_ref(v_buildDir_2088_);
lean_dec_ref(v_a_2083_);
lean_dec_ref(v___y_2055_);
lean_dec_ref(v_self_2054_);
lean_dec_ref(v_dir_2053_);
lean_dec(v___x_2052_);
lean_dec(v___x_2046_);
v_a_2117_ = lean_ctor_get(v___x_2095_, 0);
v_a_2118_ = lean_ctor_get(v___x_2095_, 1);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2095_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_inc(v_a_2117_);
lean_dec(v___x_2095_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2117_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
v___jp_2126_:
{
if (lean_obj_tag(v___y_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v_a_2129_; 
v_a_2128_ = lean_ctor_get(v___y_2127_, 0);
lean_inc(v_a_2128_);
v_a_2129_ = lean_ctor_get(v___y_2127_, 1);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___y_2127_, 2);
v_a_2083_ = v_a_2128_;
v_a_2084_ = v_a_2129_;
goto v___jp_2082_;
}
else
{
lean_object* v_a_2130_; lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec_ref(v___y_2055_);
lean_dec_ref(v_self_2054_);
lean_dec_ref(v_dir_2053_);
lean_dec(v___x_2052_);
lean_dec_ref(v_pkg_2049_);
lean_dec_ref(v_config_2047_);
lean_dec(v___x_2046_);
v_a_2130_ = lean_ctor_get(v___y_2127_, 0);
v_a_2131_ = lean_ctor_get(v___y_2127_, 1);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___y_2127_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___y_2127_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_inc(v_a_2130_);
lean_dec(v___y_2127_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2130_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(lean_object** _args){
lean_object* v___x_2174_ = _args[0];
lean_object* v___x_2175_ = _args[1];
lean_object* v_config_2176_ = _args[2];
lean_object* v_config_2177_ = _args[3];
lean_object* v_pkg_2178_ = _args[4];
lean_object* v_shouldExport_2179_ = _args[5];
lean_object* v___x_2180_ = _args[6];
lean_object* v___x_2181_ = _args[7];
lean_object* v_dir_2182_ = _args[8];
lean_object* v_self_2183_ = _args[9];
lean_object* v___y_2184_ = _args[10];
lean_object* v___y_2185_ = _args[11];
lean_object* v___y_2186_ = _args[12];
lean_object* v___y_2187_ = _args[13];
lean_object* v___y_2188_ = _args[14];
lean_object* v___y_2189_ = _args[15];
lean_object* v___y_2190_ = _args[16];
_start:
{
uint8_t v_shouldExport_boxed_2191_; uint8_t v___x_7358__boxed_2192_; lean_object* v_res_2193_; 
v_shouldExport_boxed_2191_ = lean_unbox(v_shouldExport_2179_);
v___x_7358__boxed_2192_ = lean_unbox(v___x_2180_);
v_res_2193_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v___x_2174_, v___x_2175_, v_config_2176_, v_config_2177_, v_pkg_2178_, v_shouldExport_boxed_2191_, v___x_7358__boxed_2192_, v___x_2181_, v_dir_2182_, v_self_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec(v_config_2177_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object* v___y_2194_, lean_object* v_self_2195_, uint8_t v_shouldExport_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v_toBuildConfig_2203_; lean_object* v_registeredJobs_2204_; uint8_t v_verbosity_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; uint8_t v___x_2208_; uint8_t v___x_2209_; lean_object* v___y_2211_; 
v_toBuildConfig_2203_ = lean_ctor_get(v_a_2200_, 0);
v_registeredJobs_2204_ = lean_ctor_get(v_a_2200_, 3);
v_verbosity_2205_ = lean_ctor_get_uint8(v_toBuildConfig_2203_, sizeof(void*)*4 + 3);
v___x_2206_ = l_Lake_instDataKindFilePath;
v___x_2207_ = 2;
v___x_2208_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2205_, v___x_2207_);
v___x_2209_ = 1;
if (v___x_2208_ == 0)
{
lean_object* v___x_2256_; 
v___x_2256_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_2211_ = v___x_2256_;
goto v___jp_2210_;
}
else
{
if (v_shouldExport_2196_ == 0)
{
lean_object* v___x_2257_; 
v___x_2257_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___y_2211_ = v___x_2257_;
goto v___jp_2210_;
}
else
{
lean_object* v___x_2258_; 
v___x_2258_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_2211_ = v___x_2258_;
goto v___jp_2210_;
}
}
v___jp_2210_:
{
lean_object* v_pkg_2212_; lean_object* v_name_2213_; lean_object* v_config_2214_; lean_object* v_keyName_2215_; lean_object* v_dir_2216_; lean_object* v_config_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___f_2225_; lean_object* v___x_2226_; 
v_pkg_2212_ = lean_ctor_get(v_self_2195_, 0);
lean_inc_ref_n(v_pkg_2212_, 2);
v_name_2213_ = lean_ctor_get(v_self_2195_, 1);
lean_inc_n(v_name_2213_, 2);
v_config_2214_ = lean_ctor_get(v_self_2195_, 2);
lean_inc(v_config_2214_);
v_keyName_2215_ = lean_ctor_get(v_pkg_2212_, 2);
v_dir_2216_ = lean_ctor_get(v_pkg_2212_, 4);
lean_inc_ref(v_dir_2216_);
v_config_2217_ = lean_ctor_get(v_pkg_2212_, 6);
lean_inc_ref(v_config_2217_);
v___x_2218_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_2215_);
v___x_2219_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2219_, 0, v_keyName_2215_);
lean_ctor_set(v___x_2219_, 1, v_name_2213_);
v___x_2220_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_2195_);
v___x_2221_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2219_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
lean_ctor_set(v___x_2221_, 2, v_self_2195_);
lean_ctor_set(v___x_2221_, 3, v___x_2218_);
v___x_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_pkg_2212_);
v___x_2223_ = lean_box(v_shouldExport_2196_);
v___x_2224_ = lean_box(v___x_2209_);
v___f_2225_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed), 17, 10);
lean_closure_set(v___f_2225_, 0, v___x_2221_);
lean_closure_set(v___f_2225_, 1, v___x_2222_);
lean_closure_set(v___f_2225_, 2, v_config_2217_);
lean_closure_set(v___f_2225_, 3, v_config_2214_);
lean_closure_set(v___f_2225_, 4, v_pkg_2212_);
lean_closure_set(v___f_2225_, 5, v___x_2223_);
lean_closure_set(v___f_2225_, 6, v___x_2224_);
lean_closure_set(v___f_2225_, 7, v___x_2206_);
lean_closure_set(v___f_2225_, 8, v_dir_2216_);
lean_closure_set(v___f_2225_, 9, v_self_2195_);
v___x_2226_ = l_Lake_ensureJob___redArg(v___x_2206_, v___f_2225_, v___y_2194_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2255_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_a_2228_ = lean_ctor_get(v___x_2226_, 1);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2230_ = v___x_2226_;
v_isShared_2231_ = v_isSharedCheck_2255_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2255_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v_task_2232_; lean_object* v_kind_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2253_; 
v_task_2232_ = lean_ctor_get(v_a_2227_, 0);
v_kind_2233_ = lean_ctor_get(v_a_2227_, 1);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_a_2227_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; 
v_unused_2254_ = lean_ctor_get(v_a_2227_, 2);
lean_dec(v_unused_2254_);
v___x_2235_ = v_a_2227_;
v_isShared_2236_ = v_isSharedCheck_2253_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_kind_2233_);
lean_inc(v_task_2232_);
lean_dec(v_a_2227_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2253_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; lean_object* v_job_2244_; 
v___x_2237_ = lean_st_ref_take(v_registeredJobs_2204_);
v___x_2238_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2213_, v___x_2209_);
v___x_2239_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0));
v___x_2240_ = lean_string_append(v___x_2238_, v___x_2239_);
v___x_2241_ = lean_string_append(v___x_2240_, v___y_2211_);
v___x_2242_ = 0;
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 2, v___x_2241_);
v_job_2244_ = v___x_2235_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_task_2232_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_kind_2233_);
lean_ctor_set(v_reuseFailAlloc_2252_, 2, v___x_2241_);
v_job_2244_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
lean_ctor_set_uint8(v_job_2244_, sizeof(void*)*3, v___x_2242_);
lean_inc_ref(v_job_2244_);
v___x_2245_ = l_Lake_Job_toOpaque___redArg(v_job_2244_);
v___x_2246_ = lean_array_push(v___x_2237_, v___x_2245_);
v___x_2247_ = lean_st_ref_set(v_registeredJobs_2204_, v___x_2246_);
v___x_2248_ = l_Lake_Job_renew___redArg(v_job_2244_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 0, v___x_2248_);
v___x_2250_ = v___x_2230_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_a_2228_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
}
else
{
lean_dec(v_name_2213_);
return v___x_2226_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* v___y_2259_, lean_object* v_self_2260_, lean_object* v_shouldExport_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
uint8_t v_shouldExport_boxed_2268_; lean_object* v_res_2269_; 
v_shouldExport_boxed_2268_ = lean_unbox(v_shouldExport_2261_);
v_res_2269_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2259_, v_self_2260_, v_shouldExport_boxed_2268_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec(v_a_2262_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* v_x_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
uint8_t v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = 0;
v___x_2279_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2271_, v_x_2270_, v___x_2278_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object* v_x_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec(v___y_2282_);
return v_res_2288_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2291_; uint8_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___f_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___f_2291_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2292_ = 1;
v___x_2293_ = l_Lake_instDataKindFilePath;
v___f_2294_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__0));
v___x_2295_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2296_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_ctor_set(v___x_2296_, 1, v___f_2294_);
lean_ctor_set(v___x_2296_, 2, v___x_2293_);
lean_ctor_set(v___x_2296_, 3, v___f_2291_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*4, v___x_2292_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*4 + 1, v___x_2292_);
return v___x_2296_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = lean_obj_once(&l_Lake_LeanLib_staticFacetConfig___closed__2, &l_Lake_LeanLib_staticFacetConfig___closed__2_once, _init_l_Lake_LeanLib_staticFacetConfig___closed__2);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(lean_object* v_a_2298_, lean_object* v_as_2299_, size_t v_i_2300_, size_t v_stop_2301_, lean_object* v_b_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2298_, v_as_2299_, v_i_2300_, v_stop_2301_, v_b_2302_, v___y_2308_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* v_a_2311_, lean_object* v_as_2312_, lean_object* v_i_2313_, lean_object* v_stop_2314_, lean_object* v_b_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
size_t v_i_boxed_2323_; size_t v_stop_boxed_2324_; lean_object* v_res_2325_; 
v_i_boxed_2323_ = lean_unbox_usize(v_i_2313_);
lean_dec(v_i_2313_);
v_stop_boxed_2324_ = lean_unbox_usize(v_stop_2314_);
lean_dec(v_stop_2314_);
v_res_2325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_2311_, v_as_2312_, v_i_boxed_2323_, v_stop_boxed_2324_, v_b_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v_as_2312_);
lean_dec(v_a_2311_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* v_x_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
uint8_t v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = 1;
v___x_2335_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2327_, v_x_2326_, v___x_2334_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object* v_x_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec(v___y_2338_);
return v_res_2344_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; lean_object* v___f_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___f_2346_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2347_ = 1;
v___x_2348_ = l_Lake_instDataKindFilePath;
v___f_2349_ = ((lean_object*)(l_Lake_LeanLib_staticExportFacetConfig___closed__0));
v___x_2350_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2351_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
lean_ctor_set(v___x_2351_, 1, v___f_2349_);
lean_ctor_set(v___x_2351_, 2, v___x_2348_);
lean_ctor_set(v___x_2351_, 3, v___f_2346_);
lean_ctor_set_uint8(v___x_2351_, sizeof(void*)*4, v___x_2347_);
lean_ctor_set_uint8(v___x_2351_, sizeof(void*)*4 + 1, v___x_2347_);
return v___x_2351_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig(void){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_obj_once(&l_Lake_LeanLib_staticExportFacetConfig___closed__1, &l_Lake_LeanLib_staticExportFacetConfig___closed__1_once, _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1);
return v___x_2352_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0(void){
_start:
{
uint8_t v___x_2353_; lean_object* v_name_2354_; lean_object* v___x_2355_; 
v___x_2353_ = 1;
v_name_2354_ = l_Lake_instDataKindDynlib;
v___x_2355_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2354_, v___x_2353_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object* v_defaultPkg_2356_, lean_object* v_self_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
uint8_t v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = 1;
lean_inc_ref_n(v_self_2357_, 2);
v___x_2366_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_2356_, v_self_2357_, v_self_2357_, v___x_2365_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v_snd_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2409_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
v_snd_2368_ = lean_ctor_get(v_a_2367_, 1);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_a_2367_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; 
v_unused_2410_ = lean_ctor_get(v_a_2367_, 0);
lean_dec(v_unused_2410_);
v___x_2370_ = v_a_2367_;
v_isShared_2371_ = v_isSharedCheck_2409_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_snd_2368_);
lean_dec(v_a_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2409_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2407_; 
v_a_2372_ = lean_ctor_get(v___x_2366_, 1);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2407_ == 0)
{
lean_object* v_unused_2408_; 
v_unused_2408_ = lean_ctor_get(v___x_2366_, 0);
lean_dec(v_unused_2408_);
v___x_2374_ = v___x_2366_;
v_isShared_2375_ = v_isSharedCheck_2407_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2366_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2407_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v_kind_2376_; lean_object* v_name_2377_; lean_object* v___y_2379_; uint8_t v___x_2397_; 
v_kind_2376_ = lean_ctor_get(v_snd_2368_, 1);
v_name_2377_ = l_Lake_instDataKindDynlib;
v___x_2397_ = lean_name_eq(v_kind_2376_, v_name_2377_);
if (v___x_2397_ == 0)
{
uint8_t v___x_2398_; 
lean_inc(v_kind_2376_);
lean_del_object(v___x_2370_);
lean_dec(v_snd_2368_);
v___x_2398_ = l_Lean_Name_isAnonymous(v_kind_2376_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2399_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_2400_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2376_, v___x_2365_);
v___x_2401_ = lean_string_append(v___x_2399_, v___x_2400_);
lean_dec_ref(v___x_2400_);
v___x_2402_ = lean_string_append(v___x_2401_, v___x_2399_);
v___y_2379_ = v___x_2402_;
goto v___jp_2378_;
}
else
{
lean_object* v___x_2403_; 
lean_dec(v_kind_2376_);
v___x_2403_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_2379_ = v___x_2403_;
goto v___jp_2378_;
}
}
else
{
lean_object* v___x_2405_; 
lean_del_object(v___x_2374_);
lean_dec_ref(v_self_2357_);
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 1, v_a_2372_);
lean_ctor_set(v___x_2370_, 0, v_snd_2368_);
v___x_2405_ = v___x_2370_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_snd_2368_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v_a_2372_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
v___jp_2378_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2380_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_2381_ = l_Lake_PartialBuildKey_toString(v_self_2357_);
v___x_2382_ = lean_string_append(v___x_2380_, v___x_2381_);
lean_dec_ref(v___x_2381_);
v___x_2383_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_2384_ = lean_string_append(v___x_2382_, v___x_2383_);
v___x_2385_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0);
v___x_2386_ = lean_string_append(v___x_2384_, v___x_2385_);
v___x_2387_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_2388_ = lean_string_append(v___x_2386_, v___x_2387_);
v___x_2389_ = lean_string_append(v___x_2388_, v___y_2379_);
lean_dec_ref(v___y_2379_);
v___x_2390_ = 3;
v___x_2391_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set_uint8(v___x_2391_, sizeof(void*)*1, v___x_2390_);
v___x_2392_ = lean_array_get_size(v_a_2372_);
v___x_2393_ = lean_array_push(v_a_2372_, v___x_2391_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set_tag(v___x_2374_, 1);
lean_ctor_set(v___x_2374_, 1, v___x_2393_);
lean_ctor_set(v___x_2374_, 0, v___x_2392_);
v___x_2395_ = v___x_2374_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v___x_2393_);
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
else
{
lean_object* v_a_2411_; lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec_ref(v_self_2357_);
v_a_2411_ = lean_ctor_get(v___x_2366_, 0);
v_a_2412_ = lean_ctor_get(v___x_2366_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2366_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_inc(v_a_2411_);
lean_dec(v___x_2366_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2411_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* v_defaultPkg_2420_, lean_object* v_self_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_2420_, v_self_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
lean_dec_ref(v_a_2426_);
lean_dec(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec(v_a_2423_);
return v_res_2429_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0));
v___x_2433_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
lean_ctor_set(v___x_2434_, 1, v___x_2432_);
return v___x_2434_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5(void){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object* v___x_2436_, lean_object* v_as_2437_, size_t v_i_2438_, size_t v_stop_2439_, lean_object* v_b_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
uint8_t v___x_2448_; 
v___x_2448_ = lean_usize_dec_eq(v_i_2438_, v_stop_2439_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_array_uget_borrowed(v_as_2437_, v_i_2438_);
lean_inc_ref(v___y_2441_);
lean_inc(v___x_2449_);
lean_inc_ref(v___x_2436_);
v___x_2450_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_2436_, v___x_2449_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v_a_2452_; lean_object* v___x_2453_; size_t v___x_2454_; size_t v___x_2455_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
v_a_2452_ = lean_ctor_get(v___x_2450_, 1);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2450_, 2);
v___x_2453_ = lean_array_push(v_b_2440_, v_a_2451_);
v___x_2454_ = ((size_t)1ULL);
v___x_2455_ = lean_usize_add(v_i_2438_, v___x_2454_);
v_i_2438_ = v___x_2455_;
v_b_2440_ = v___x_2453_;
v___y_2446_ = v_a_2452_;
goto _start;
}
else
{
lean_object* v_a_2457_; lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec_ref(v___y_2441_);
lean_dec_ref(v_b_2440_);
lean_dec_ref(v___x_2436_);
v_a_2457_ = lean_ctor_get(v___x_2450_, 0);
v_a_2458_ = lean_ctor_get(v___x_2450_, 1);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2450_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_inc(v_a_2457_);
lean_dec(v___x_2450_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2457_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
else
{
lean_object* v___x_2466_; 
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___x_2436_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v_b_2440_);
lean_ctor_set(v___x_2466_, 1, v___y_2446_);
return v___x_2466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* v___x_2467_, lean_object* v_as_2468_, lean_object* v_i_2469_, lean_object* v_stop_2470_, lean_object* v_b_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
size_t v_i_boxed_2479_; size_t v_stop_boxed_2480_; lean_object* v_res_2481_; 
v_i_boxed_2479_ = lean_unbox_usize(v_i_2469_);
lean_dec(v_i_2469_);
v_stop_boxed_2480_ = lean_unbox_usize(v_stop_2470_);
lean_dec(v_stop_2470_);
v_res_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_2467_, v_as_2468_, v_i_boxed_2479_, v_stop_boxed_2480_, v_b_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v_as_2468_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object* v_self_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v_toHashSet_2484_; lean_object* v_toArray_2485_; uint8_t v___x_2486_; 
v_toHashSet_2484_ = lean_ctor_get(v_self_2482_, 0);
v_toArray_2485_ = lean_ctor_get(v_self_2482_, 1);
v___x_2486_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_2484_, v_a_2483_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2496_; 
lean_inc_ref(v_toArray_2485_);
lean_inc_ref(v_toHashSet_2484_);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_self_2482_);
if (v_isSharedCheck_2496_ == 0)
{
lean_object* v_unused_2497_; lean_object* v_unused_2498_; 
v_unused_2497_ = lean_ctor_get(v_self_2482_, 1);
lean_dec(v_unused_2497_);
v_unused_2498_ = lean_ctor_get(v_self_2482_, 0);
lean_dec(v_unused_2498_);
v___x_2488_ = v_self_2482_;
v_isShared_2489_ = v_isSharedCheck_2496_;
goto v_resetjp_2487_;
}
else
{
lean_dec(v_self_2482_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2496_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2494_; 
v___x_2490_ = lean_box(0);
lean_inc_ref(v_a_2483_);
v___x_2491_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_toHashSet_2484_, v_a_2483_, v___x_2490_);
v___x_2492_ = lean_array_push(v_toArray_2485_, v_a_2483_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 1, v___x_2492_);
lean_ctor_set(v___x_2488_, 0, v___x_2491_);
v___x_2494_ = v___x_2488_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
else
{
lean_dec_ref(v_a_2483_);
return v_self_2482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object* v_as_2499_, size_t v_i_2500_, size_t v_stop_2501_, lean_object* v_b_2502_){
_start:
{
uint8_t v___x_2503_; 
v___x_2503_ = lean_usize_dec_eq(v_i_2500_, v_stop_2501_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; size_t v___x_2506_; size_t v___x_2507_; 
v___x_2504_ = lean_array_uget_borrowed(v_as_2499_, v_i_2500_);
lean_inc(v___x_2504_);
v___x_2505_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_2502_, v___x_2504_);
v___x_2506_ = ((size_t)1ULL);
v___x_2507_ = lean_usize_add(v_i_2500_, v___x_2506_);
v_i_2500_ = v___x_2507_;
v_b_2502_ = v___x_2505_;
goto _start;
}
else
{
return v_b_2502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object* v_as_2509_, lean_object* v_i_2510_, lean_object* v_stop_2511_, lean_object* v_b_2512_){
_start:
{
size_t v_i_boxed_2513_; size_t v_stop_boxed_2514_; lean_object* v_res_2515_; 
v_i_boxed_2513_ = lean_unbox_usize(v_i_2510_);
lean_dec(v_i_2510_);
v_stop_boxed_2514_ = lean_unbox_usize(v_stop_2511_);
lean_dec(v_stop_2511_);
v_res_2515_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_2509_, v_i_boxed_2513_, v_stop_boxed_2514_, v_b_2512_);
lean_dec_ref(v_as_2509_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object* v_self_2516_, lean_object* v_arr_2517_){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; uint8_t v___x_2520_; 
v___x_2518_ = lean_unsigned_to_nat(0u);
v___x_2519_ = lean_array_get_size(v_arr_2517_);
v___x_2520_ = lean_nat_dec_lt(v___x_2518_, v___x_2519_);
if (v___x_2520_ == 0)
{
return v_self_2516_;
}
else
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_nat_dec_le(v___x_2519_, v___x_2519_);
if (v___x_2521_ == 0)
{
if (v___x_2520_ == 0)
{
return v_self_2516_;
}
else
{
size_t v___x_2522_; size_t v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = ((size_t)0ULL);
v___x_2523_ = lean_usize_of_nat(v___x_2519_);
v___x_2524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2517_, v___x_2522_, v___x_2523_, v_self_2516_);
return v___x_2524_;
}
}
else
{
size_t v___x_2525_; size_t v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = ((size_t)0ULL);
v___x_2526_ = lean_usize_of_nat(v___x_2519_);
v___x_2527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2517_, v___x_2525_, v___x_2526_, v_self_2516_);
return v___x_2527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(lean_object* v_self_2528_, lean_object* v_arr_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_self_2528_, v_arr_2529_);
lean_dec_ref(v_arr_2529_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(lean_object* v_as_2531_, size_t v_i_2532_, size_t v_stop_2533_, lean_object* v_b_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
uint8_t v___x_2542_; 
v___x_2542_ = lean_usize_dec_eq(v_i_2532_, v_stop_2533_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v_lib_2544_; lean_object* v_pkg_2545_; lean_object* v_name_2546_; lean_object* v_keyName_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2543_ = lean_array_uget_borrowed(v_as_2531_, v_i_2532_);
v_lib_2544_ = lean_ctor_get(v___x_2543_, 0);
v_pkg_2545_ = lean_ctor_get(v_lib_2544_, 0);
v_name_2546_ = lean_ctor_get(v___x_2543_, 1);
v_keyName_2547_ = lean_ctor_get(v_pkg_2545_, 2);
v___x_2548_ = l_Lake_Module_transImportsFacet;
lean_inc(v_name_2546_);
lean_inc(v_keyName_2547_);
v___x_2549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2549_, 0, v_keyName_2547_);
lean_ctor_set(v___x_2549_, 1, v_name_2546_);
v___x_2550_ = l_Lake_Module_keyword;
lean_inc(v___x_2543_);
v___x_2551_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2549_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
lean_ctor_set(v___x_2551_, 2, v___x_2543_);
lean_ctor_set(v___x_2551_, 3, v___x_2548_);
lean_inc_ref(v___y_2535_);
lean_inc_ref(v___y_2539_);
lean_inc(v___y_2538_);
lean_inc(v___y_2537_);
lean_inc(v___y_2536_);
v___x_2552_ = lean_apply_7(v___y_2535_, v___x_2551_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, lean_box(0));
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v_a_2554_; lean_object* v___x_2555_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
v_a_2554_ = lean_ctor_get(v___x_2552_, 1);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2552_, 2);
v___x_2555_ = l_Lake_Job_await___redArg(v_a_2553_, v_a_2554_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v_a_2557_; lean_object* v___x_2558_; size_t v___x_2559_; size_t v___x_2560_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
v_a_2557_ = lean_ctor_get(v___x_2555_, 1);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2555_, 2);
v___x_2558_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_b_2534_, v_a_2556_);
lean_dec(v_a_2556_);
v___x_2559_ = ((size_t)1ULL);
v___x_2560_ = lean_usize_add(v_i_2532_, v___x_2559_);
v_i_2532_ = v___x_2560_;
v_b_2534_ = v___x_2558_;
v___y_2540_ = v_a_2557_;
goto _start;
}
else
{
lean_object* v_a_2562_; lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref(v___y_2535_);
lean_dec_ref(v_b_2534_);
v_a_2562_ = lean_ctor_get(v___x_2555_, 0);
v_a_2563_ = lean_ctor_get(v___x_2555_, 1);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2555_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_inc(v_a_2562_);
lean_dec(v___x_2555_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2562_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec_ref(v___y_2535_);
lean_dec_ref(v_b_2534_);
v_a_2571_ = lean_ctor_get(v___x_2552_, 0);
v_a_2572_ = lean_ctor_get(v___x_2552_, 1);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2552_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_inc(v_a_2571_);
lean_dec(v___x_2552_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2571_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
else
{
lean_object* v___x_2580_; 
lean_dec_ref(v___y_2535_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v_b_2534_);
lean_ctor_set(v___x_2580_, 1, v___y_2540_);
return v___x_2580_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object* v_as_2581_, lean_object* v_i_2582_, lean_object* v_stop_2583_, lean_object* v_b_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
size_t v_i_boxed_2592_; size_t v_stop_boxed_2593_; lean_object* v_res_2594_; 
v_i_boxed_2592_ = lean_unbox_usize(v_i_2582_);
lean_dec(v_i_2582_);
v_stop_boxed_2593_ = lean_unbox_usize(v_stop_2583_);
lean_dec(v_stop_2583_);
v_res_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_as_2581_, v_i_boxed_2592_, v_stop_boxed_2593_, v_b_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v_as_2581_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(lean_object* v_as_2595_, size_t v_i_2596_, size_t v_stop_2597_, lean_object* v_b_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
uint8_t v___x_2606_; 
v___x_2606_ = lean_usize_dec_eq(v_i_2596_, v_stop_2597_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; lean_object* v_pkg_2608_; lean_object* v_name_2609_; lean_object* v_keyName_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2607_ = lean_array_uget_borrowed(v_as_2595_, v_i_2596_);
v_pkg_2608_ = lean_ctor_get(v___x_2607_, 0);
v_name_2609_ = lean_ctor_get(v___x_2607_, 1);
v_keyName_2610_ = lean_ctor_get(v_pkg_2608_, 2);
v___x_2611_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_2609_);
lean_inc(v_keyName_2610_);
v___x_2612_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2612_, 0, v_keyName_2610_);
lean_ctor_set(v___x_2612_, 1, v_name_2609_);
v___x_2613_ = l_Lake_ExternLib_keyword;
lean_inc(v___x_2607_);
v___x_2614_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2612_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
lean_ctor_set(v___x_2614_, 2, v___x_2607_);
lean_ctor_set(v___x_2614_, 3, v___x_2611_);
lean_inc_ref(v___y_2599_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc(v___y_2600_);
v___x_2615_ = lean_apply_7(v___y_2599_, v___x_2614_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, lean_box(0));
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v_a_2617_; lean_object* v___x_2618_; size_t v___x_2619_; size_t v___x_2620_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
lean_inc(v_a_2616_);
v_a_2617_ = lean_ctor_get(v___x_2615_, 1);
lean_inc(v_a_2617_);
lean_dec_ref_known(v___x_2615_, 2);
v___x_2618_ = lean_array_push(v_b_2598_, v_a_2616_);
v___x_2619_ = ((size_t)1ULL);
v___x_2620_ = lean_usize_add(v_i_2596_, v___x_2619_);
v_i_2596_ = v___x_2620_;
v_b_2598_ = v___x_2618_;
v___y_2604_ = v_a_2617_;
goto _start;
}
else
{
lean_object* v_a_2622_; lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec_ref(v___y_2599_);
lean_dec_ref(v_b_2598_);
v_a_2622_ = lean_ctor_get(v___x_2615_, 0);
v_a_2623_ = lean_ctor_get(v___x_2615_, 1);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2615_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_inc(v_a_2622_);
lean_dec(v___x_2615_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2622_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_object* v___x_2631_; 
lean_dec_ref(v___y_2599_);
v___x_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2631_, 0, v_b_2598_);
lean_ctor_set(v___x_2631_, 1, v___y_2604_);
return v___x_2631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(lean_object* v_as_2632_, lean_object* v_i_2633_, lean_object* v_stop_2634_, lean_object* v_b_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
size_t v_i_boxed_2643_; size_t v_stop_boxed_2644_; lean_object* v_res_2645_; 
v_i_boxed_2643_ = lean_unbox_usize(v_i_2633_);
lean_dec(v_i_2633_);
v_stop_boxed_2644_ = lean_unbox_usize(v_stop_2634_);
lean_dec(v_stop_2634_);
v_res_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v_as_2632_, v_i_boxed_2643_, v_stop_boxed_2644_, v_b_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v_as_2632_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(lean_object* v_as_2646_, size_t v_i_2647_, size_t v_stop_2648_, lean_object* v_b_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_a_2658_; lean_object* v_a_2659_; uint8_t v___x_2663_; 
v___x_2663_ = lean_usize_dec_eq(v_i_2647_, v_stop_2648_);
if (v___x_2663_ == 0)
{
lean_object* v_fst_2664_; lean_object* v_snd_2665_; lean_object* v___x_2666_; lean_object* v_lib_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2704_; 
v_fst_2664_ = lean_ctor_get(v_b_2649_, 0);
v_snd_2665_ = lean_ctor_get(v_b_2649_, 1);
v___x_2666_ = lean_array_uget(v_as_2646_, v_i_2647_);
v_lib_2667_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2704_ == 0)
{
lean_object* v_unused_2705_; 
v_unused_2705_ = lean_ctor_get(v___x_2666_, 1);
lean_dec(v_unused_2705_);
v___x_2669_ = v___x_2666_;
v_isShared_2670_ = v_isSharedCheck_2704_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_lib_2667_);
lean_dec(v___x_2666_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2704_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v_pkg_2671_; lean_object* v_name_2672_; uint8_t v___x_2673_; 
v_pkg_2671_ = lean_ctor_get(v_lib_2667_, 0);
v_name_2672_ = lean_ctor_get(v_lib_2667_, 1);
lean_inc(v_name_2672_);
v___x_2673_ = l_Lean_NameSet_contains(v_fst_2664_, v_name_2672_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2701_; 
lean_inc(v_snd_2665_);
lean_inc(v_fst_2664_);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_b_2649_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; lean_object* v_unused_2703_; 
v_unused_2702_ = lean_ctor_get(v_b_2649_, 1);
lean_dec(v_unused_2702_);
v_unused_2703_ = lean_ctor_get(v_b_2649_, 0);
lean_dec(v_unused_2703_);
v___x_2675_ = v_b_2649_;
v_isShared_2676_ = v_isSharedCheck_2701_;
goto v_resetjp_2674_;
}
else
{
lean_dec(v_b_2649_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2701_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v_keyName_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; 
v_keyName_2677_ = lean_ctor_get(v_pkg_2671_, 2);
v___x_2678_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_2672_);
lean_inc(v_keyName_2677_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set_tag(v___x_2669_, 3);
lean_ctor_set(v___x_2669_, 1, v_name_2672_);
lean_ctor_set(v___x_2669_, 0, v_keyName_2677_);
v___x_2680_ = v___x_2669_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_keyName_2677_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_name_2672_);
v___x_2680_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2682_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2680_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
lean_ctor_set(v___x_2682_, 2, v_lib_2667_);
lean_ctor_set(v___x_2682_, 3, v___x_2678_);
lean_inc_ref(v___y_2650_);
lean_inc_ref(v___y_2654_);
lean_inc(v___y_2653_);
lean_inc(v___y_2652_);
lean_inc(v___y_2651_);
v___x_2683_ = lean_apply_7(v___y_2650_, v___x_2682_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, lean_box(0));
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; lean_object* v_a_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
v_a_2685_ = lean_ctor_get(v___x_2683_, 1);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2683_, 2);
v___x_2686_ = lean_array_push(v_snd_2665_, v_a_2684_);
v___x_2687_ = l_Lean_NameSet_insert(v_fst_2664_, v_name_2672_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 1, v___x_2686_);
lean_ctor_set(v___x_2675_, 0, v___x_2687_);
v___x_2689_ = v___x_2675_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v___x_2686_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
v_a_2658_ = v___x_2689_;
v_a_2659_ = v_a_2685_;
goto v___jp_2657_;
}
}
else
{
lean_object* v_a_2691_; lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_del_object(v___x_2675_);
lean_dec(v_name_2672_);
lean_dec(v_snd_2665_);
lean_dec(v_fst_2664_);
lean_dec_ref(v___y_2650_);
v_a_2691_ = lean_ctor_get(v___x_2683_, 0);
v_a_2692_ = lean_ctor_get(v___x_2683_, 1);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2683_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2683_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_inc(v_a_2691_);
lean_dec(v___x_2683_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2691_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
}
}
else
{
lean_dec(v_name_2672_);
lean_del_object(v___x_2669_);
lean_dec_ref(v_lib_2667_);
v_a_2658_ = v_b_2649_;
v_a_2659_ = v___y_2655_;
goto v___jp_2657_;
}
}
}
else
{
lean_object* v___x_2706_; 
lean_dec_ref(v___y_2650_);
v___x_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2706_, 0, v_b_2649_);
lean_ctor_set(v___x_2706_, 1, v___y_2655_);
return v___x_2706_;
}
v___jp_2657_:
{
size_t v___x_2660_; size_t v___x_2661_; 
v___x_2660_ = ((size_t)1ULL);
v___x_2661_ = lean_usize_add(v_i_2647_, v___x_2660_);
v_i_2647_ = v___x_2661_;
v_b_2649_ = v_a_2658_;
v___y_2655_ = v_a_2659_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object* v_as_2707_, lean_object* v_i_2708_, lean_object* v_stop_2709_, lean_object* v_b_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
size_t v_i_boxed_2718_; size_t v_stop_boxed_2719_; lean_object* v_res_2720_; 
v_i_boxed_2718_ = lean_unbox_usize(v_i_2708_);
lean_dec(v_i_2708_);
v_stop_boxed_2719_ = lean_unbox_usize(v_stop_2709_);
lean_dec(v_stop_2709_);
v_res_2720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_as_2707_, v_i_boxed_2718_, v_stop_boxed_2719_, v_b_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v_as_2707_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(lean_object* v___x_2721_, lean_object* v_as_2722_, size_t v_i_2723_, size_t v_stop_2724_, lean_object* v_b_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
uint8_t v___x_2733_; 
v___x_2733_ = lean_usize_dec_eq(v_i_2723_, v_stop_2724_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = lean_array_uget_borrowed(v_as_2722_, v_i_2723_);
lean_inc_ref(v___y_2726_);
lean_inc(v___x_2734_);
lean_inc_ref(v___x_2721_);
v___x_2735_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v___x_2721_, v___x_2734_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v_a_2737_; lean_object* v___x_2738_; size_t v___x_2739_; size_t v___x_2740_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
v_a_2737_ = lean_ctor_get(v___x_2735_, 1);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2735_, 2);
v___x_2738_ = lean_array_push(v_b_2725_, v_a_2736_);
v___x_2739_ = ((size_t)1ULL);
v___x_2740_ = lean_usize_add(v_i_2723_, v___x_2739_);
v_i_2723_ = v___x_2740_;
v_b_2725_ = v___x_2738_;
v___y_2731_ = v_a_2737_;
goto _start;
}
else
{
lean_object* v_a_2742_; lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec_ref(v___y_2726_);
lean_dec_ref(v_b_2725_);
lean_dec_ref(v___x_2721_);
v_a_2742_ = lean_ctor_get(v___x_2735_, 0);
v_a_2743_ = lean_ctor_get(v___x_2735_, 1);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2735_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_inc(v_a_2742_);
lean_dec(v___x_2735_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2742_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v___x_2751_; 
lean_dec_ref(v___y_2726_);
lean_dec_ref(v___x_2721_);
v___x_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2751_, 0, v_b_2725_);
lean_ctor_set(v___x_2751_, 1, v___y_2731_);
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object* v___x_2752_, lean_object* v_as_2753_, lean_object* v_i_2754_, lean_object* v_stop_2755_, lean_object* v_b_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
size_t v_i_boxed_2764_; size_t v_stop_boxed_2765_; lean_object* v_res_2766_; 
v_i_boxed_2764_ = lean_unbox_usize(v_i_2754_);
lean_dec(v_i_2754_);
v_stop_boxed_2765_ = lean_unbox_usize(v_stop_2755_);
lean_dec(v_stop_2755_);
v_res_2766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v___x_2752_, v_as_2753_, v_i_boxed_2764_, v_stop_boxed_2765_, v_b_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v_as_2753_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(lean_object* v___x_2767_, lean_object* v_as_2768_, size_t v_i_2769_, size_t v_stop_2770_, lean_object* v_b_2771_){
_start:
{
lean_object* v___y_2773_; uint8_t v___x_2777_; 
v___x_2777_ = lean_usize_dec_eq(v_i_2769_, v_stop_2770_);
if (v___x_2777_ == 0)
{
lean_object* v_toConfigDecl_2778_; lean_object* v_name_2779_; lean_object* v_kind_2780_; lean_object* v_config_2781_; lean_object* v___x_2782_; uint8_t v___x_2783_; 
v_toConfigDecl_2778_ = lean_array_uget_borrowed(v_as_2768_, v_i_2769_);
v_name_2779_ = lean_ctor_get(v_toConfigDecl_2778_, 1);
v_kind_2780_ = lean_ctor_get(v_toConfigDecl_2778_, 2);
v_config_2781_ = lean_ctor_get(v_toConfigDecl_2778_, 3);
v___x_2782_ = l_Lake_ExternLib_keyword;
v___x_2783_ = lean_name_eq(v_kind_2780_, v___x_2782_);
if (v___x_2783_ == 0)
{
v___y_2773_ = v_b_2771_;
goto v___jp_2772_;
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
lean_inc(v_config_2781_);
lean_inc(v_name_2779_);
lean_inc_ref(v___x_2767_);
v___x_2784_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2767_);
lean_ctor_set(v___x_2784_, 1, v_name_2779_);
lean_ctor_set(v___x_2784_, 2, v_config_2781_);
v___x_2785_ = lean_array_push(v_b_2771_, v___x_2784_);
v___y_2773_ = v___x_2785_;
goto v___jp_2772_;
}
}
else
{
lean_dec_ref(v___x_2767_);
return v_b_2771_;
}
v___jp_2772_:
{
size_t v___x_2774_; size_t v___x_2775_; 
v___x_2774_ = ((size_t)1ULL);
v___x_2775_ = lean_usize_add(v_i_2769_, v___x_2774_);
v_i_2769_ = v___x_2775_;
v_b_2771_ = v___y_2773_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(lean_object* v___x_2786_, lean_object* v_as_2787_, lean_object* v_i_2788_, lean_object* v_stop_2789_, lean_object* v_b_2790_){
_start:
{
size_t v_i_boxed_2791_; size_t v_stop_boxed_2792_; lean_object* v_res_2793_; 
v_i_boxed_2791_ = lean_unbox_usize(v_i_2788_);
lean_dec(v_i_2788_);
v_stop_boxed_2792_ = lean_unbox_usize(v_stop_2789_);
lean_dec(v_stop_2789_);
v_res_2793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v___x_2786_, v_as_2787_, v_i_boxed_2791_, v_stop_boxed_2792_, v_b_2790_);
lean_dec_ref(v_as_2787_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(lean_object* v_as_2794_, size_t v_i_2795_, size_t v_stop_2796_, lean_object* v_b_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
uint8_t v___x_2805_; 
v___x_2805_ = lean_usize_dec_eq(v_i_2795_, v_stop_2796_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; lean_object* v_lib_2807_; lean_object* v_config_2808_; lean_object* v_nativeFacets_2809_; uint8_t v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; size_t v_sz_2813_; size_t v___x_2814_; lean_object* v___x_2815_; 
v___x_2806_ = lean_array_uget_borrowed(v_as_2794_, v_i_2795_);
v_lib_2807_ = lean_ctor_get(v___x_2806_, 0);
v_config_2808_ = lean_ctor_get(v_lib_2807_, 2);
v_nativeFacets_2809_ = lean_ctor_get(v_config_2808_, 8);
v___x_2810_ = 1;
v___x_2811_ = lean_box(v___x_2810_);
lean_inc_ref(v_nativeFacets_2809_);
v___x_2812_ = lean_apply_1(v_nativeFacets_2809_, v___x_2811_);
v_sz_2813_ = lean_array_size(v___x_2812_);
v___x_2814_ = ((size_t)0ULL);
lean_inc_ref(v___y_2798_);
lean_inc(v___x_2806_);
v___x_2815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2806_, v_sz_2813_, v___x_2814_, v___x_2812_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v_a_2817_; lean_object* v___x_2818_; size_t v___x_2819_; size_t v___x_2820_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
v_a_2817_ = lean_ctor_get(v___x_2815_, 1);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2815_, 2);
v___x_2818_ = l_Array_append___redArg(v_b_2797_, v_a_2816_);
lean_dec(v_a_2816_);
v___x_2819_ = ((size_t)1ULL);
v___x_2820_ = lean_usize_add(v_i_2795_, v___x_2819_);
v_i_2795_ = v___x_2820_;
v_b_2797_ = v___x_2818_;
v___y_2803_ = v_a_2817_;
goto _start;
}
else
{
lean_dec_ref(v___y_2798_);
lean_dec_ref(v_b_2797_);
return v___x_2815_;
}
}
else
{
lean_object* v___x_2822_; 
lean_dec_ref(v___y_2798_);
v___x_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2822_, 0, v_b_2797_);
lean_ctor_set(v___x_2822_, 1, v___y_2803_);
return v___x_2822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object* v_as_2823_, lean_object* v_i_2824_, lean_object* v_stop_2825_, lean_object* v_b_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
size_t v_i_boxed_2834_; size_t v_stop_boxed_2835_; lean_object* v_res_2836_; 
v_i_boxed_2834_ = lean_unbox_usize(v_i_2824_);
lean_dec(v_i_2824_);
v_stop_boxed_2835_ = lean_unbox_usize(v_stop_2825_);
lean_dec(v_stop_2825_);
v_res_2836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_as_2823_, v_i_boxed_2834_, v_stop_boxed_2835_, v_b_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v_as_2823_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(lean_object* v___x_2837_, lean_object* v___x_2838_, lean_object* v_self_2839_, lean_object* v_dir_2840_, lean_object* v_targetDecls_2841_, lean_object* v_pkg_2842_, lean_object* v_name_2843_, lean_object* v_config_2844_, lean_object* v_config_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v_a_2861_; lean_object* v_a_2862_; lean_object* v_a_2880_; lean_object* v_a_2881_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v_a_2926_; lean_object* v_a_2927_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v_snd_2963_; lean_object* v_a_2964_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v_a_3003_; lean_object* v_a_3004_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___x_3042_; 
lean_inc_ref(v___y_2846_);
lean_inc_ref(v___y_2850_);
lean_inc(v___y_2849_);
lean_inc(v___y_2848_);
lean_inc(v___x_2838_);
v___x_3042_ = lean_apply_7(v___y_2846_, v___x_2837_, v___x_2838_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, lean_box(0));
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v_a_3044_; lean_object* v___x_3045_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
v_a_3044_ = lean_ctor_get(v___x_3042_, 1);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3042_, 2);
v___x_3045_ = l_Lake_Job_await___redArg(v_a_3043_, v_a_3044_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v_a_3047_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v_a_3058_; lean_object* v_a_3059_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v_a_3093_; lean_object* v_a_3094_; lean_object* v___y_3119_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
v_a_3047_ = lean_ctor_get(v___x_3045_, 1);
lean_inc(v_a_3047_);
lean_dec_ref_known(v___x_3045_, 2);
v___x_3131_ = lean_unsigned_to_nat(0u);
v___x_3132_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_3133_ = lean_array_get_size(v_a_3046_);
v___x_3134_ = lean_nat_dec_lt(v___x_3131_, v___x_3133_);
if (v___x_3134_ == 0)
{
v_a_3093_ = v___x_3132_;
v_a_3094_ = v_a_3047_;
goto v___jp_3092_;
}
else
{
uint8_t v___x_3135_; 
v___x_3135_ = lean_nat_dec_le(v___x_3133_, v___x_3133_);
if (v___x_3135_ == 0)
{
if (v___x_3134_ == 0)
{
v_a_3093_ = v___x_3132_;
v_a_3094_ = v_a_3047_;
goto v___jp_3092_;
}
else
{
size_t v___x_3136_; size_t v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = ((size_t)0ULL);
v___x_3137_ = lean_usize_of_nat(v___x_3133_);
lean_inc_ref(v___y_2846_);
v___x_3138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3046_, v___x_3136_, v___x_3137_, v___x_3132_, v___y_2846_, v___x_2838_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_3047_);
v___y_3119_ = v___x_3138_;
goto v___jp_3118_;
}
}
else
{
size_t v___x_3139_; size_t v___x_3140_; lean_object* v___x_3141_; 
v___x_3139_ = ((size_t)0ULL);
v___x_3140_ = lean_usize_of_nat(v___x_3133_);
lean_inc_ref(v___y_2846_);
v___x_3141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3046_, v___x_3139_, v___x_3140_, v___x_3132_, v___y_2846_, v___x_2838_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_3047_);
v___y_3119_ = v___x_3141_;
goto v___jp_3118_;
}
}
v___jp_3048_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v___x_3060_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
v___x_3061_ = lean_array_get_size(v_a_3046_);
v___x_3062_ = lean_nat_dec_lt(v___y_3057_, v___x_3061_);
if (v___x_3062_ == 0)
{
lean_dec(v_a_3046_);
v___y_2993_ = v___y_3049_;
v___y_2994_ = v___y_3050_;
v___y_2995_ = v___y_3051_;
v___y_2996_ = v___y_3052_;
v___y_2997_ = v___y_3053_;
v___y_2998_ = v___y_3054_;
v___y_2999_ = v___y_3055_;
v___y_3000_ = v___y_3056_;
v___y_3001_ = v___y_3057_;
v___y_3002_ = v_a_3058_;
v_a_3003_ = v___x_3060_;
v_a_3004_ = v_a_3059_;
goto v___jp_2992_;
}
else
{
uint8_t v___x_3063_; 
v___x_3063_ = lean_nat_dec_le(v___x_3061_, v___x_3061_);
if (v___x_3063_ == 0)
{
if (v___x_3062_ == 0)
{
lean_dec(v_a_3046_);
v___y_2993_ = v___y_3049_;
v___y_2994_ = v___y_3050_;
v___y_2995_ = v___y_3051_;
v___y_2996_ = v___y_3052_;
v___y_2997_ = v___y_3053_;
v___y_2998_ = v___y_3054_;
v___y_2999_ = v___y_3055_;
v___y_3000_ = v___y_3056_;
v___y_3001_ = v___y_3057_;
v___y_3002_ = v_a_3058_;
v_a_3003_ = v___x_3060_;
v_a_3004_ = v_a_3059_;
goto v___jp_2992_;
}
else
{
size_t v___x_3064_; size_t v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = ((size_t)0ULL);
v___x_3065_ = lean_usize_of_nat(v___x_3061_);
lean_inc_ref(v___y_2846_);
v___x_3066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3046_, v___x_3064_, v___x_3065_, v___x_3060_, v___y_2846_, v___x_2838_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_3059_);
lean_dec(v_a_3046_);
v___y_3027_ = v___y_3050_;
v___y_3028_ = v___y_3049_;
v___y_3029_ = v___y_3051_;
v___y_3030_ = v___y_3052_;
v___y_3031_ = v___y_3053_;
v___y_3032_ = v___y_3055_;
v___y_3033_ = v___y_3054_;
v___y_3034_ = v___y_3056_;
v___y_3035_ = v___y_3057_;
v___y_3036_ = v_a_3058_;
v___y_3037_ = v___x_3066_;
goto v___jp_3026_;
}
}
else
{
size_t v___x_3067_; size_t v___x_3068_; lean_object* v___x_3069_; 
v___x_3067_ = ((size_t)0ULL);
v___x_3068_ = lean_usize_of_nat(v___x_3061_);
lean_inc_ref(v___y_2846_);
v___x_3069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3046_, v___x_3067_, v___x_3068_, v___x_3060_, v___y_2846_, v___x_2838_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_3059_);
lean_dec(v_a_3046_);
v___y_3027_ = v___y_3050_;
v___y_3028_ = v___y_3049_;
v___y_3029_ = v___y_3051_;
v___y_3030_ = v___y_3052_;
v___y_3031_ = v___y_3053_;
v___y_3032_ = v___y_3055_;
v___y_3033_ = v___y_3054_;
v___y_3034_ = v___y_3056_;
v___y_3035_ = v___y_3057_;
v___y_3036_ = v_a_3058_;
v___y_3037_ = v___x_3069_;
goto v___jp_3026_;
}
}
}
v___jp_3070_:
{
if (lean_obj_tag(v___y_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v_a_3082_; 
v_a_3081_ = lean_ctor_get(v___y_3080_, 0);
lean_inc(v_a_3081_);
v_a_3082_ = lean_ctor_get(v___y_3080_, 1);
lean_inc(v_a_3082_);
lean_dec_ref_known(v___y_3080_, 2);
v___y_3049_ = v___y_3072_;
v___y_3050_ = v___y_3071_;
v___y_3051_ = v___y_3073_;
v___y_3052_ = v___y_3074_;
v___y_3053_ = v___y_3075_;
v___y_3054_ = v___y_3077_;
v___y_3055_ = v___y_3076_;
v___y_3056_ = v___y_3078_;
v___y_3057_ = v___y_3079_;
v_a_3058_ = v_a_3081_;
v_a_3059_ = v_a_3082_;
goto v___jp_3048_;
}
else
{
lean_object* v_a_3083_; lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec_ref(v___y_3075_);
lean_dec_ref(v___y_3073_);
lean_dec_ref(v___y_3071_);
lean_dec(v_a_3046_);
lean_dec_ref(v___y_2846_);
lean_dec(v_name_2843_);
lean_dec_ref(v_pkg_2842_);
lean_dec_ref(v_dir_2840_);
lean_dec_ref(v_self_2839_);
lean_dec(v___x_2838_);
v_a_3083_ = lean_ctor_get(v___y_3080_, 0);
v_a_3084_ = lean_ctor_get(v___y_3080_, 1);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___y_3080_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___y_3080_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_inc(v_a_3083_);
lean_dec(v___y_3080_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3083_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
v___jp_3092_:
{
lean_object* v_toLeanConfig_3095_; lean_object* v_toLeanConfig_3096_; lean_object* v_buildDir_3097_; lean_object* v_nativeLibDir_3098_; lean_object* v_moreLinkObjs_3099_; lean_object* v_moreLinkLibs_3100_; lean_object* v_moreLinkArgs_3101_; lean_object* v_weakLinkArgs_3102_; lean_object* v_moreLinkObjs_3103_; lean_object* v_moreLinkLibs_3104_; lean_object* v_moreLinkArgs_3105_; lean_object* v_weakLinkArgs_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; uint8_t v___x_3110_; 
v_toLeanConfig_3095_ = lean_ctor_get(v_config_2844_, 1);
lean_inc_ref(v_toLeanConfig_3095_);
v_toLeanConfig_3096_ = lean_ctor_get(v_config_2845_, 0);
v_buildDir_3097_ = lean_ctor_get(v_config_2844_, 5);
lean_inc_ref(v_buildDir_3097_);
v_nativeLibDir_3098_ = lean_ctor_get(v_config_2844_, 7);
lean_inc_ref(v_nativeLibDir_3098_);
lean_dec_ref(v_config_2844_);
v_moreLinkObjs_3099_ = lean_ctor_get(v_toLeanConfig_3095_, 6);
lean_inc_ref(v_moreLinkObjs_3099_);
v_moreLinkLibs_3100_ = lean_ctor_get(v_toLeanConfig_3095_, 7);
lean_inc_ref(v_moreLinkLibs_3100_);
v_moreLinkArgs_3101_ = lean_ctor_get(v_toLeanConfig_3095_, 8);
lean_inc_ref(v_moreLinkArgs_3101_);
v_weakLinkArgs_3102_ = lean_ctor_get(v_toLeanConfig_3095_, 9);
lean_inc_ref(v_weakLinkArgs_3102_);
lean_dec_ref(v_toLeanConfig_3095_);
v_moreLinkObjs_3103_ = lean_ctor_get(v_toLeanConfig_3096_, 6);
v_moreLinkLibs_3104_ = lean_ctor_get(v_toLeanConfig_3096_, 7);
v_moreLinkArgs_3105_ = lean_ctor_get(v_toLeanConfig_3096_, 8);
v_weakLinkArgs_3106_ = lean_ctor_get(v_toLeanConfig_3096_, 9);
v___x_3107_ = l_Array_append___redArg(v_moreLinkObjs_3099_, v_moreLinkObjs_3103_);
v___x_3108_ = lean_unsigned_to_nat(0u);
v___x_3109_ = lean_array_get_size(v___x_3107_);
v___x_3110_ = lean_nat_dec_lt(v___x_3108_, v___x_3109_);
if (v___x_3110_ == 0)
{
lean_dec_ref(v___x_3107_);
v___y_3049_ = v_moreLinkArgs_3105_;
v___y_3050_ = v_nativeLibDir_3098_;
v___y_3051_ = v_moreLinkArgs_3101_;
v___y_3052_ = v_weakLinkArgs_3106_;
v___y_3053_ = v_weakLinkArgs_3102_;
v___y_3054_ = v_moreLinkLibs_3100_;
v___y_3055_ = v_moreLinkLibs_3104_;
v___y_3056_ = v_buildDir_3097_;
v___y_3057_ = v___x_3108_;
v_a_3058_ = v_a_3093_;
v_a_3059_ = v_a_3094_;
goto v___jp_3048_;
}
else
{
uint8_t v___x_3111_; 
v___x_3111_ = lean_nat_dec_le(v___x_3109_, v___x_3109_);
if (v___x_3111_ == 0)
{
if (v___x_3110_ == 0)
{
lean_dec_ref(v___x_3107_);
v___y_3049_ = v_moreLinkArgs_3105_;
v___y_3050_ = v_nativeLibDir_3098_;
v___y_3051_ = v_moreLinkArgs_3101_;
v___y_3052_ = v_weakLinkArgs_3106_;
v___y_3053_ = v_weakLinkArgs_3102_;
v___y_3054_ = v_moreLinkLibs_3100_;
v___y_3055_ = v_moreLinkLibs_3104_;
v___y_3056_ = v_buildDir_3097_;
v___y_3057_ = v___x_3108_;
v_a_3058_ = v_a_3093_;
v_a_3059_ = v_a_3094_;
goto v___jp_3048_;
}
else
{
size_t v___x_3112_; size_t v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = ((size_t)0ULL);
v___x_3113_ = lean_usize_of_nat(v___x_3109_);
lean_inc_ref(v___y_2846_);
lean_inc_ref(v_pkg_2842_);
v___x_3114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2842_, v___x_3107_, v___x_3112_, v___x_3113_, v_a_3093_, v___y_2846_, v___x_2838_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_3094_);
lean_dec_ref(v___x_3107_);
v___y_3071_ = v_nativeLibDir_3098_;
v___y_3072_ = v_moreLinkArgs_3105_;
v___y_3073_ = v_moreLinkArgs_3101_;
v___y_3074_ = v_weakLinkArgs_3106_;
v___y_3075_ = v_weakLinkArgs_3102_;
v___y_3076_ = v_moreLinkLibs_3104_;
v___y_3077_ = v_moreLinkLibs_3100_;
v___y_3078_ = v_buildDir_3097_;
v___y_3079_ = v___x_3108_;
v___y_3080_ = v___x_3114_;
goto v___jp_3070_;
}
}
else
{
size_t v___x_3115_; size_t v___x_3116_; lean_object* v___x_3117_; 
v___x_3115_ = ((size_t)0ULL);
v___x_3116_ = lean_usize_of_nat(v___x_3109_);
lean_inc_ref(v___y_2846_);
lean_inc_ref(v_pkg_2842_);
v___x_3117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2842_, v___x_3107_, v___x_3115_, v___x_3116_, v_a_3093_, v___y_2846_, v___x_2838_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_3094_);
lean_dec_ref(v___x_3107_);
v___y_3071_ = v_nativeLibDir_3098_;
v___y_3072_ = v_moreLinkArgs_3105_;
v___y_3073_ = v_moreLinkArgs_3101_;
v___y_3074_ = v_weakLinkArgs_3106_;
v___y_3075_ = v_weakLinkArgs_3102_;
v___y_3076_ = v_moreLinkLibs_3104_;
v___y_3077_ = v_moreLinkLibs_3100_;
v___y_3078_ = v_buildDir_3097_;
v___y_3079_ = v___x_3108_;
v___y_3080_ = v___x_3117_;
goto v___jp_3070_;
}
}
}
v___jp_3118_:
{
if (lean_obj_tag(v___y_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v_a_3121_; 
v_a_3120_ = lean_ctor_get(v___y_3119_, 0);
lean_inc(v_a_3120_);
v_a_3121_ = lean_ctor_get(v___y_3119_, 1);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___y_3119_, 2);
v_a_3093_ = v_a_3120_;
v_a_3094_ = v_a_3121_;
goto v___jp_3092_;
}
else
{
lean_object* v_a_3122_; lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec(v_a_3046_);
lean_dec_ref(v___y_2846_);
lean_dec_ref(v_config_2844_);
lean_dec(v_name_2843_);
lean_dec_ref(v_pkg_2842_);
lean_dec_ref(v_dir_2840_);
lean_dec_ref(v_self_2839_);
lean_dec(v___x_2838_);
v_a_3122_ = lean_ctor_get(v___y_3119_, 0);
v_a_3123_ = lean_ctor_get(v___y_3119_, 1);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___y_3119_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___y_3119_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_inc(v_a_3122_);
lean_dec(v___y_3119_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3122_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
}
else
{
lean_object* v_a_3142_; lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec_ref(v___y_2846_);
lean_dec_ref(v_config_2844_);
lean_dec(v_name_2843_);
lean_dec_ref(v_pkg_2842_);
lean_dec_ref(v_dir_2840_);
lean_dec_ref(v_self_2839_);
lean_dec(v___x_2838_);
v_a_3142_ = lean_ctor_get(v___x_3045_, 0);
v_a_3143_ = lean_ctor_get(v___x_3045_, 1);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3045_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_inc(v_a_3142_);
lean_dec(v___x_3045_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3142_);
lean_ctor_set(v_reuseFailAlloc_3149_, 1, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
else
{
lean_object* v_a_3151_; lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec_ref(v___y_2846_);
lean_dec_ref(v_config_2844_);
lean_dec(v_name_2843_);
lean_dec_ref(v_pkg_2842_);
lean_dec_ref(v_dir_2840_);
lean_dec_ref(v_self_2839_);
lean_dec(v___x_2838_);
v_a_3151_ = lean_ctor_get(v___x_3042_, 0);
v_a_3152_ = lean_ctor_get(v___x_3042_, 1);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3042_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_inc(v_a_3151_);
lean_dec(v___x_3042_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3151_);
lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
v___jp_2853_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; uint8_t v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
lean_inc_ref(v_self_2839_);
v___x_2863_ = l_Lake_LeanLib_libName(v_self_2839_);
v___x_2864_ = l_System_FilePath_normalize(v___y_2859_);
v___x_2865_ = l_Lake_joinRelative(v_dir_2840_, v___x_2864_);
v___x_2866_ = l_System_FilePath_normalize(v___y_2855_);
v___x_2867_ = l_Lake_joinRelative(v___x_2865_, v___x_2866_);
v___x_2868_ = 0;
v___x_2869_ = l_Lake_nameToSharedLib(v___x_2863_, v___x_2868_);
v___x_2870_ = l_Lake_joinRelative(v___x_2867_, v___x_2869_);
v___x_2871_ = l_Array_append___redArg(v___y_2858_, v___y_2857_);
v___x_2872_ = l_Array_append___redArg(v___y_2856_, v___y_2854_);
v___x_2873_ = l_Lake_LeanLib_isPlugin(v_self_2839_);
v___x_2874_ = l_System_Platform_isWindows;
v___x_2875_ = lean_box(0);
v___x_2876_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2877_ = l_Lake_buildLeanSharedLib(v___x_2863_, v___x_2870_, v___y_2860_, v_a_2861_, v___x_2871_, v___x_2872_, v___x_2873_, v___x_2874_, v___x_2875_, v___y_2846_, v___x_2838_, v___y_2848_, v___y_2849_, v___y_2850_, v___x_2876_);
lean_dec(v___x_2838_);
lean_dec_ref(v___y_2860_);
v___x_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
lean_ctor_set(v___x_2878_, 1, v_a_2862_);
return v___x_2878_;
}
v___jp_2879_:
{
lean_object* v___x_2882_; 
v___x_2882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2882_, 0, v_a_2880_);
lean_ctor_set(v___x_2882_, 1, v_a_2881_);
return v___x_2882_;
}
v___jp_2883_:
{
if (lean_obj_tag(v___y_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v_a_2893_; 
v_a_2892_ = lean_ctor_get(v___y_2891_, 0);
lean_inc(v_a_2892_);
v_a_2893_ = lean_ctor_get(v___y_2891_, 1);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___y_2891_, 2);
v___y_2854_ = v___y_2885_;
v___y_2855_ = v___y_2884_;
v___y_2856_ = v___y_2886_;
v___y_2857_ = v___y_2887_;
v___y_2858_ = v___y_2888_;
v___y_2859_ = v___y_2889_;
v___y_2860_ = v___y_2890_;
v_a_2861_ = v_a_2892_;
v_a_2862_ = v_a_2893_;
goto v___jp_2853_;
}
else
{
lean_object* v_a_2894_; lean_object* v_a_2895_; 
lean_dec_ref(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2884_);
lean_dec_ref(v___y_2846_);
lean_dec_ref(v_dir_2840_);
lean_dec_ref(v_self_2839_);
lean_dec(v___x_2838_);
v_a_2894_ = lean_ctor_get(v___y_2891_, 0);
lean_inc(v_a_2894_);
v_a_2895_ = lean_ctor_get(v___y_2891_, 1);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___y_2891_, 2);
v_a_2880_ = v_a_2894_;
v_a_2881_ = v_a_2895_;
goto v___jp_2879_;
}
}
v___jp_2896_:
{
lean_object* v___x_2908_; uint8_t v___x_2909_; 
v___x_2908_ = lean_array_get_size(v___y_2907_);
v___x_2909_ = lean_nat_dec_lt(v___y_2904_, v___x_2908_);
if (v___x_2909_ == 0)
{
lean_dec_ref(v___y_2907_);
v___y_2854_ = v___y_2898_;
v___y_2855_ = v___y_2897_;
v___y_2856_ = v___y_2899_;
v___y_2857_ = v___y_2900_;
v___y_2858_ = v___y_2901_;
v___y_2859_ = v___y_2902_;
v___y_2860_ = v___y_2905_;
v_a_2861_ = v___y_2903_;
v_a_2862_ = v___y_2906_;
goto v___jp_2853_;
}
else
{
uint8_t v___x_2910_; 
v___x_2910_ = lean_nat_dec_le(v___x_2908_, v___x_2908_);
if (v___x_2910_ == 0)
{
if (v___x_2909_ == 0)
{
lean_dec_ref(v___y_2907_);
v___y_2854_ = v___y_2898_;
v___y_2855_ = v___y_2897_;
v___y_2856_ = v___y_2899_;
v___y_2857_ = v___y_2900_;
v___y_2858_ = v___y_2901_;
v___y_2859_ = v___y_2902_;
v___y_2860_ = v___y_2905_;
v_a_2861_ = v___y_2903_;
v_a_2862_ = v___y_2906_;
goto v___jp_2853_;
}
else
{
size_t v___x_2911_; size_t v___x_2912_; lean_object* v___x_2913_; 
v___x_2911_ = ((size_t)0ULL);
v___x_2912_ = lean_usize_of_nat(v___x_2908_);
lean_inc_ref(v___y_2846_);
v___x_2913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2907_, v___x_2911_, v___x_2912_, v___y_2903_, v___y_2846_, v___x_2838_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2906_);
lean_dec_ref(v___y_2907_);
v___y_2884_ = v___y_2897_;
v___y_2885_ = v___y_2898_;
v___y_2886_ = v___y_2899_;
v___y_2887_ = v___y_2900_;
v___y_2888_ = v___y_2901_;
v___y_2889_ = v___y_2902_;
v___y_2890_ = v___y_2905_;
v___y_2891_ = v___x_2913_;
goto v___jp_2883_;
}
}
else
{
size_t v___x_2914_; size_t v___x_2915_; lean_object* v___x_2916_; 
v___x_2914_ = ((size_t)0ULL);
v___x_2915_ = lean_usize_of_nat(v___x_2908_);
lean_inc_ref(v___y_2846_);
v___x_2916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2907_, v___x_2914_, v___x_2915_, v___y_2903_, v___y_2846_, v___x_2838_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2906_);
lean_dec_ref(v___y_2907_);
v___y_2884_ = v___y_2897_;
v___y_2885_ = v___y_2898_;
v___y_2886_ = v___y_2899_;
v___y_2887_ = v___y_2900_;
v___y_2888_ = v___y_2901_;
v___y_2889_ = v___y_2902_;
v___y_2890_ = v___y_2905_;
v___y_2891_ = v___x_2916_;
goto v___jp_2883_;
}
}
}
v___jp_2917_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; uint8_t v___x_2930_; 
v___x_2928_ = lean_mk_empty_array_with_capacity(v___y_2924_);
v___x_2929_ = lean_array_get_size(v_targetDecls_2841_);
v___x_2930_ = lean_nat_dec_lt(v___y_2924_, v___x_2929_);
if (v___x_2930_ == 0)
{
lean_dec_ref(v_pkg_2842_);
v___y_2897_ = v___y_2919_;
v___y_2898_ = v___y_2918_;
v___y_2899_ = v___y_2920_;
v___y_2900_ = v___y_2921_;
v___y_2901_ = v___y_2922_;
v___y_2902_ = v___y_2923_;
v___y_2903_ = v_a_2926_;
v___y_2904_ = v___y_2924_;
v___y_2905_ = v___y_2925_;
v___y_2906_ = v_a_2927_;
v___y_2907_ = v___x_2928_;
goto v___jp_2896_;
}
else
{
uint8_t v___x_2931_; 
v___x_2931_ = lean_nat_dec_le(v___x_2929_, v___x_2929_);
if (v___x_2931_ == 0)
{
if (v___x_2930_ == 0)
{
lean_dec_ref(v_pkg_2842_);
v___y_2897_ = v___y_2919_;
v___y_2898_ = v___y_2918_;
v___y_2899_ = v___y_2920_;
v___y_2900_ = v___y_2921_;
v___y_2901_ = v___y_2922_;
v___y_2902_ = v___y_2923_;
v___y_2903_ = v_a_2926_;
v___y_2904_ = v___y_2924_;
v___y_2905_ = v___y_2925_;
v___y_2906_ = v_a_2927_;
v___y_2907_ = v___x_2928_;
goto v___jp_2896_;
}
else
{
size_t v___x_2932_; size_t v___x_2933_; lean_object* v___x_2934_; 
v___x_2932_ = ((size_t)0ULL);
v___x_2933_ = lean_usize_of_nat(v___x_2929_);
v___x_2934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2842_, v_targetDecls_2841_, v___x_2932_, v___x_2933_, v___x_2928_);
v___y_2897_ = v___y_2919_;
v___y_2898_ = v___y_2918_;
v___y_2899_ = v___y_2920_;
v___y_2900_ = v___y_2921_;
v___y_2901_ = v___y_2922_;
v___y_2902_ = v___y_2923_;
v___y_2903_ = v_a_2926_;
v___y_2904_ = v___y_2924_;
v___y_2905_ = v___y_2925_;
v___y_2906_ = v_a_2927_;
v___y_2907_ = v___x_2934_;
goto v___jp_2896_;
}
}
else
{
size_t v___x_2935_; size_t v___x_2936_; lean_object* v___x_2937_; 
v___x_2935_ = ((size_t)0ULL);
v___x_2936_ = lean_usize_of_nat(v___x_2929_);
v___x_2937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2842_, v_targetDecls_2841_, v___x_2935_, v___x_2936_, v___x_2928_);
v___y_2897_ = v___y_2919_;
v___y_2898_ = v___y_2918_;
v___y_2899_ = v___y_2920_;
v___y_2900_ = v___y_2921_;
v___y_2901_ = v___y_2922_;
v___y_2902_ = v___y_2923_;
v___y_2903_ = v_a_2926_;
v___y_2904_ = v___y_2924_;
v___y_2905_ = v___y_2925_;
v___y_2906_ = v_a_2927_;
v___y_2907_ = v___x_2937_;
goto v___jp_2896_;
}
}
}
v___jp_2938_:
{
if (lean_obj_tag(v___y_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v_a_2949_; 
v_a_2948_ = lean_ctor_get(v___y_2947_, 0);
lean_inc(v_a_2948_);
v_a_2949_ = lean_ctor_get(v___y_2947_, 1);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___y_2947_, 2);
v___y_2918_ = v___y_2940_;
v___y_2919_ = v___y_2939_;
v___y_2920_ = v___y_2941_;
v___y_2921_ = v___y_2942_;
v___y_2922_ = v___y_2943_;
v___y_2923_ = v___y_2944_;
v___y_2924_ = v___y_2945_;
v___y_2925_ = v___y_2946_;
v_a_2926_ = v_a_2948_;
v_a_2927_ = v_a_2949_;
goto v___jp_2917_;
}
else
{
lean_object* v_a_2950_; lean_object* v_a_2951_; 
lean_dec_ref(v___y_2946_);
lean_dec_ref(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec_ref(v___y_2941_);
lean_dec_ref(v___y_2939_);
lean_dec_ref(v___y_2846_);
lean_dec_ref(v_pkg_2842_);
lean_dec_ref(v_dir_2840_);
lean_dec_ref(v_self_2839_);
lean_dec(v___x_2838_);
v_a_2950_ = lean_ctor_get(v___y_2947_, 0);
lean_inc(v_a_2950_);
v_a_2951_ = lean_ctor_get(v___y_2947_, 1);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___y_2947_, 2);
v_a_2880_ = v_a_2950_;
v_a_2881_ = v_a_2951_;
goto v___jp_2879_;
}
}
v___jp_2952_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2965_ = l_Array_append___redArg(v___y_2959_, v___y_2958_);
v___x_2966_ = lean_array_get_size(v___x_2965_);
v___x_2967_ = lean_nat_dec_lt(v___y_2961_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_dec_ref(v___x_2965_);
v___y_2918_ = v___y_2954_;
v___y_2919_ = v___y_2953_;
v___y_2920_ = v___y_2955_;
v___y_2921_ = v___y_2956_;
v___y_2922_ = v___y_2957_;
v___y_2923_ = v___y_2960_;
v___y_2924_ = v___y_2961_;
v___y_2925_ = v___y_2962_;
v_a_2926_ = v_snd_2963_;
v_a_2927_ = v_a_2964_;
goto v___jp_2917_;
}
else
{
uint8_t v___x_2968_; 
v___x_2968_ = lean_nat_dec_le(v___x_2966_, v___x_2966_);
if (v___x_2968_ == 0)
{
if (v___x_2967_ == 0)
{
lean_dec_ref(v___x_2965_);
v___y_2918_ = v___y_2954_;
v___y_2919_ = v___y_2953_;
v___y_2920_ = v___y_2955_;
v___y_2921_ = v___y_2956_;
v___y_2922_ = v___y_2957_;
v___y_2923_ = v___y_2960_;
v___y_2924_ = v___y_2961_;
v___y_2925_ = v___y_2962_;
v_a_2926_ = v_snd_2963_;
v_a_2927_ = v_a_2964_;
goto v___jp_2917_;
}
else
{
size_t v___x_2969_; size_t v___x_2970_; lean_object* v___x_2971_; 
v___x_2969_ = ((size_t)0ULL);
v___x_2970_ = lean_usize_of_nat(v___x_2966_);
lean_inc_ref(v___y_2846_);
lean_inc_ref(v_pkg_2842_);
v___x_2971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2842_, v___x_2965_, v___x_2969_, v___x_2970_, v_snd_2963_, v___y_2846_, v___x_2838_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_2964_);
lean_dec_ref(v___x_2965_);
v___y_2939_ = v___y_2953_;
v___y_2940_ = v___y_2954_;
v___y_2941_ = v___y_2955_;
v___y_2942_ = v___y_2956_;
v___y_2943_ = v___y_2957_;
v___y_2944_ = v___y_2960_;
v___y_2945_ = v___y_2961_;
v___y_2946_ = v___y_2962_;
v___y_2947_ = v___x_2971_;
goto v___jp_2938_;
}
}
else
{
size_t v___x_2972_; size_t v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = ((size_t)0ULL);
v___x_2973_ = lean_usize_of_nat(v___x_2966_);
lean_inc_ref(v___y_2846_);
lean_inc_ref(v_pkg_2842_);
v___x_2974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2842_, v___x_2965_, v___x_2972_, v___x_2973_, v_snd_2963_, v___y_2846_, v___x_2838_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_2964_);
lean_dec_ref(v___x_2965_);
v___y_2939_ = v___y_2953_;
v___y_2940_ = v___y_2954_;
v___y_2941_ = v___y_2955_;
v___y_2942_ = v___y_2956_;
v___y_2943_ = v___y_2957_;
v___y_2944_ = v___y_2960_;
v___y_2945_ = v___y_2961_;
v___y_2946_ = v___y_2962_;
v___y_2947_ = v___x_2974_;
goto v___jp_2938_;
}
}
}
v___jp_2975_:
{
if (lean_obj_tag(v___y_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v_a_2988_; lean_object* v_snd_2989_; 
v_a_2987_ = lean_ctor_get(v___y_2986_, 0);
lean_inc(v_a_2987_);
v_a_2988_ = lean_ctor_get(v___y_2986_, 1);
lean_inc(v_a_2988_);
lean_dec_ref_known(v___y_2986_, 2);
v_snd_2989_ = lean_ctor_get(v_a_2987_, 1);
lean_inc(v_snd_2989_);
lean_dec(v_a_2987_);
v___y_2953_ = v___y_2977_;
v___y_2954_ = v___y_2976_;
v___y_2955_ = v___y_2978_;
v___y_2956_ = v___y_2979_;
v___y_2957_ = v___y_2980_;
v___y_2958_ = v___y_2982_;
v___y_2959_ = v___y_2981_;
v___y_2960_ = v___y_2983_;
v___y_2961_ = v___y_2984_;
v___y_2962_ = v___y_2985_;
v_snd_2963_ = v_snd_2989_;
v_a_2964_ = v_a_2988_;
goto v___jp_2952_;
}
else
{
lean_object* v_a_2990_; lean_object* v_a_2991_; 
lean_dec_ref(v___y_2985_);
lean_dec_ref(v___y_2983_);
lean_dec_ref(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec_ref(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec_ref(v___y_2846_);
lean_dec_ref(v_pkg_2842_);
lean_dec_ref(v_dir_2840_);
lean_dec_ref(v_self_2839_);
lean_dec(v___x_2838_);
v_a_2990_ = lean_ctor_get(v___y_2986_, 0);
lean_inc(v_a_2990_);
v_a_2991_ = lean_ctor_get(v___y_2986_, 1);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___y_2986_, 2);
v_a_2880_ = v_a_2990_;
v_a_2881_ = v_a_2991_;
goto v___jp_2879_;
}
}
v___jp_2992_:
{
lean_object* v_toArray_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3024_; 
v_toArray_3005_ = lean_ctor_get(v_a_3003_, 1);
v_isSharedCheck_3024_ = !lean_is_exclusive(v_a_3003_);
if (v_isSharedCheck_3024_ == 0)
{
lean_object* v_unused_3025_; 
v_unused_3025_ = lean_ctor_get(v_a_3003_, 0);
lean_dec(v_unused_3025_);
v___x_3007_ = v_a_3003_;
v_isShared_3008_ = v_isSharedCheck_3024_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_toArray_3005_);
lean_dec(v_a_3003_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3024_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; 
v___x_3009_ = lean_mk_empty_array_with_capacity(v___y_3001_);
v___x_3010_ = lean_array_get_size(v_toArray_3005_);
v___x_3011_ = lean_nat_dec_lt(v___y_3001_, v___x_3010_);
if (v___x_3011_ == 0)
{
lean_del_object(v___x_3007_);
lean_dec_ref(v_toArray_3005_);
lean_dec(v_name_2843_);
v___y_2953_ = v___y_2994_;
v___y_2954_ = v___y_2993_;
v___y_2955_ = v___y_2995_;
v___y_2956_ = v___y_2996_;
v___y_2957_ = v___y_2997_;
v___y_2958_ = v___y_2999_;
v___y_2959_ = v___y_2998_;
v___y_2960_ = v___y_3000_;
v___y_2961_ = v___y_3001_;
v___y_2962_ = v___y_3002_;
v_snd_2963_ = v___x_3009_;
v_a_2964_ = v_a_3004_;
goto v___jp_2952_;
}
else
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3015_; 
v___x_3012_ = l_Lean_NameSet_empty;
v___x_3013_ = l_Lean_NameSet_insert(v___x_3012_, v_name_2843_);
lean_inc_ref(v___x_3009_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 1, v___x_3009_);
lean_ctor_set(v___x_3007_, 0, v___x_3013_);
v___x_3015_ = v___x_3007_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v___x_3009_);
v___x_3015_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
uint8_t v___x_3016_; 
v___x_3016_ = lean_nat_dec_le(v___x_3010_, v___x_3010_);
if (v___x_3016_ == 0)
{
if (v___x_3011_ == 0)
{
lean_dec_ref(v___x_3015_);
lean_dec_ref(v_toArray_3005_);
v___y_2953_ = v___y_2994_;
v___y_2954_ = v___y_2993_;
v___y_2955_ = v___y_2995_;
v___y_2956_ = v___y_2996_;
v___y_2957_ = v___y_2997_;
v___y_2958_ = v___y_2999_;
v___y_2959_ = v___y_2998_;
v___y_2960_ = v___y_3000_;
v___y_2961_ = v___y_3001_;
v___y_2962_ = v___y_3002_;
v_snd_2963_ = v___x_3009_;
v_a_2964_ = v_a_3004_;
goto v___jp_2952_;
}
else
{
size_t v___x_3017_; size_t v___x_3018_; lean_object* v___x_3019_; 
lean_dec_ref(v___x_3009_);
v___x_3017_ = ((size_t)0ULL);
v___x_3018_ = lean_usize_of_nat(v___x_3010_);
lean_inc_ref(v___y_2846_);
v___x_3019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_3005_, v___x_3017_, v___x_3018_, v___x_3015_, v___y_2846_, v___x_2838_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_3004_);
lean_dec_ref(v_toArray_3005_);
v___y_2976_ = v___y_2993_;
v___y_2977_ = v___y_2994_;
v___y_2978_ = v___y_2995_;
v___y_2979_ = v___y_2996_;
v___y_2980_ = v___y_2997_;
v___y_2981_ = v___y_2998_;
v___y_2982_ = v___y_2999_;
v___y_2983_ = v___y_3000_;
v___y_2984_ = v___y_3001_;
v___y_2985_ = v___y_3002_;
v___y_2986_ = v___x_3019_;
goto v___jp_2975_;
}
}
else
{
size_t v___x_3020_; size_t v___x_3021_; lean_object* v___x_3022_; 
lean_dec_ref(v___x_3009_);
v___x_3020_ = ((size_t)0ULL);
v___x_3021_ = lean_usize_of_nat(v___x_3010_);
lean_inc_ref(v___y_2846_);
v___x_3022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_3005_, v___x_3020_, v___x_3021_, v___x_3015_, v___y_2846_, v___x_2838_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_3004_);
lean_dec_ref(v_toArray_3005_);
v___y_2976_ = v___y_2993_;
v___y_2977_ = v___y_2994_;
v___y_2978_ = v___y_2995_;
v___y_2979_ = v___y_2996_;
v___y_2980_ = v___y_2997_;
v___y_2981_ = v___y_2998_;
v___y_2982_ = v___y_2999_;
v___y_2983_ = v___y_3000_;
v___y_2984_ = v___y_3001_;
v___y_2985_ = v___y_3002_;
v___y_2986_ = v___x_3022_;
goto v___jp_2975_;
}
}
}
}
}
v___jp_3026_:
{
if (lean_obj_tag(v___y_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v_a_3039_; 
v_a_3038_ = lean_ctor_get(v___y_3037_, 0);
lean_inc(v_a_3038_);
v_a_3039_ = lean_ctor_get(v___y_3037_, 1);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___y_3037_, 2);
v___y_2993_ = v___y_3028_;
v___y_2994_ = v___y_3027_;
v___y_2995_ = v___y_3029_;
v___y_2996_ = v___y_3030_;
v___y_2997_ = v___y_3031_;
v___y_2998_ = v___y_3033_;
v___y_2999_ = v___y_3032_;
v___y_3000_ = v___y_3034_;
v___y_3001_ = v___y_3035_;
v___y_3002_ = v___y_3036_;
v_a_3003_ = v_a_3038_;
v_a_3004_ = v_a_3039_;
goto v___jp_2992_;
}
else
{
lean_object* v_a_3040_; lean_object* v_a_3041_; 
lean_dec_ref(v___y_3036_);
lean_dec_ref(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec_ref(v___y_3031_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v___y_3027_);
lean_dec_ref(v___y_2846_);
lean_dec(v_name_2843_);
lean_dec_ref(v_pkg_2842_);
lean_dec_ref(v_dir_2840_);
lean_dec_ref(v_self_2839_);
lean_dec(v___x_2838_);
v_a_3040_ = lean_ctor_get(v___y_3037_, 0);
lean_inc(v_a_3040_);
v_a_3041_ = lean_ctor_get(v___y_3037_, 1);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___y_3037_, 2);
v_a_2880_ = v_a_3040_;
v_a_2881_ = v_a_3041_;
goto v___jp_2879_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* v___x_3160_, lean_object* v___x_3161_, lean_object* v_self_3162_, lean_object* v_dir_3163_, lean_object* v_targetDecls_3164_, lean_object* v_pkg_3165_, lean_object* v_name_3166_, lean_object* v_config_3167_, lean_object* v_config_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v___x_3160_, v___x_3161_, v_self_3162_, v_dir_3163_, v_targetDecls_3164_, v_pkg_3165_, v_name_3166_, v_config_3167_, v_config_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec(v_config_3168_);
lean_dec_ref(v_targetDecls_3164_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object* v_self_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_){
_start:
{
lean_object* v_pkg_3186_; lean_object* v_name_3187_; lean_object* v_config_3188_; lean_object* v_keyName_3189_; lean_object* v_dir_3190_; lean_object* v_config_3191_; lean_object* v_targetDecls_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___f_3199_; lean_object* v___x_3200_; 
v_pkg_3186_ = lean_ctor_get(v_self_3178_, 0);
lean_inc_ref_n(v_pkg_3186_, 2);
v_name_3187_ = lean_ctor_get(v_self_3178_, 1);
lean_inc_n(v_name_3187_, 3);
v_config_3188_ = lean_ctor_get(v_self_3178_, 2);
lean_inc(v_config_3188_);
v_keyName_3189_ = lean_ctor_get(v_pkg_3186_, 2);
v_dir_3190_ = lean_ctor_get(v_pkg_3186_, 4);
lean_inc_ref(v_dir_3190_);
v_config_3191_ = lean_ctor_get(v_pkg_3186_, 6);
lean_inc_ref(v_config_3191_);
v_targetDecls_3192_ = lean_ctor_get(v_pkg_3186_, 15);
lean_inc_ref(v_targetDecls_3192_);
v___x_3193_ = l_Lake_instDataKindDynlib;
v___x_3194_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_3189_);
v___x_3195_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3195_, 0, v_keyName_3189_);
lean_ctor_set(v___x_3195_, 1, v_name_3187_);
v___x_3196_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3178_);
v___x_3197_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3195_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
lean_ctor_set(v___x_3197_, 2, v_self_3178_);
lean_ctor_set(v___x_3197_, 3, v___x_3194_);
v___x_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3198_, 0, v_pkg_3186_);
v___f_3199_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3199_, 0, v___x_3197_);
lean_closure_set(v___f_3199_, 1, v___x_3198_);
lean_closure_set(v___f_3199_, 2, v_self_3178_);
lean_closure_set(v___f_3199_, 3, v_dir_3190_);
lean_closure_set(v___f_3199_, 4, v_targetDecls_3192_);
lean_closure_set(v___f_3199_, 5, v_pkg_3186_);
lean_closure_set(v___f_3199_, 6, v_name_3187_);
lean_closure_set(v___f_3199_, 7, v_config_3191_);
lean_closure_set(v___f_3199_, 8, v_config_3188_);
v___x_3200_ = l_Lake_ensureJob___redArg(v___x_3193_, v___f_3199_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3230_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
v_a_3202_ = lean_ctor_get(v___x_3200_, 1);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3204_ = v___x_3200_;
v_isShared_3205_ = v_isSharedCheck_3230_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_inc(v_a_3201_);
lean_dec(v___x_3200_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3230_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v_task_3206_; lean_object* v_kind_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3228_; 
v_task_3206_ = lean_ctor_get(v_a_3201_, 0);
v_kind_3207_ = lean_ctor_get(v_a_3201_, 1);
v_isSharedCheck_3228_ = !lean_is_exclusive(v_a_3201_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; 
v_unused_3229_ = lean_ctor_get(v_a_3201_, 2);
lean_dec(v_unused_3229_);
v___x_3209_ = v_a_3201_;
v_isShared_3210_ = v_isSharedCheck_3228_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_kind_3207_);
lean_inc(v_task_3206_);
lean_dec(v_a_3201_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3228_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v_registeredJobs_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; lean_object* v_job_3219_; 
v_registeredJobs_3211_ = lean_ctor_get(v_a_3183_, 3);
v___x_3212_ = lean_st_ref_take(v_registeredJobs_3211_);
v___x_3213_ = 1;
v___x_3214_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3187_, v___x_3213_);
v___x_3215_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0));
v___x_3216_ = lean_string_append(v___x_3214_, v___x_3215_);
v___x_3217_ = 0;
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 2, v___x_3216_);
v_job_3219_ = v___x_3209_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_task_3206_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_kind_3207_);
lean_ctor_set(v_reuseFailAlloc_3227_, 2, v___x_3216_);
v_job_3219_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
lean_ctor_set_uint8(v_job_3219_, sizeof(void*)*3, v___x_3217_);
lean_inc_ref(v_job_3219_);
v___x_3220_ = l_Lake_Job_toOpaque___redArg(v_job_3219_);
v___x_3221_ = lean_array_push(v___x_3212_, v___x_3220_);
v___x_3222_ = lean_st_ref_set(v_registeredJobs_3211_, v___x_3221_);
v___x_3223_ = l_Lake_Job_renew___redArg(v_job_3219_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 0, v___x_3223_);
v___x_3225_ = v___x_3204_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_a_3202_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
}
else
{
lean_dec(v_name_3187_);
return v___x_3200_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object* v_self_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec(v_a_3234_);
lean_dec(v_a_3233_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t v_fmt_3240_, lean_object* v_a_3241_){
_start:
{
if (v_fmt_3240_ == 0)
{
lean_object* v_path_3242_; 
v_path_3242_ = lean_ctor_get(v_a_3241_, 0);
lean_inc_ref(v_path_3242_);
return v_path_3242_;
}
else
{
lean_object* v_path_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v_path_3243_ = lean_ctor_get(v_a_3241_, 0);
lean_inc_ref(v_path_3243_);
v___x_3244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3244_, 0, v_path_3243_);
v___x_3245_ = l_Lean_Json_compress(v___x_3244_);
return v___x_3245_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* v_fmt_3246_, lean_object* v_a_3247_){
_start:
{
uint8_t v_fmt_boxed_3248_; lean_object* v_res_3249_; 
v_fmt_boxed_3248_ = lean_unbox(v_fmt_3246_);
v_res_3249_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_boxed_3248_, v_a_3247_);
lean_dec_ref(v_a_3247_);
return v_res_3249_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3252_; uint8_t v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___f_3252_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__0));
v___x_3253_ = 1;
v___x_3254_ = l_Lake_instDataKindDynlib;
v___x_3255_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__1));
v___x_3256_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3257_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
lean_ctor_set(v___x_3257_, 1, v___x_3255_);
lean_ctor_set(v___x_3257_, 2, v___x_3254_);
lean_ctor_set(v___x_3257_, 3, v___f_3252_);
lean_ctor_set_uint8(v___x_3257_, sizeof(void*)*4, v___x_3253_);
lean_ctor_set_uint8(v___x_3257_, sizeof(void*)*4 + 1, v___x_3253_);
return v___x_3257_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = lean_obj_once(&l_Lake_LeanLib_sharedFacetConfig___closed__2, &l_Lake_LeanLib_sharedFacetConfig___closed__2_once, _init_l_Lake_LeanLib_sharedFacetConfig___closed__2);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* v___x_3259_, lean_object* v_as_3260_, size_t v_sz_3261_, size_t v_i_3262_, lean_object* v_b_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
uint8_t v___x_3271_; 
v___x_3271_ = lean_usize_dec_lt(v_i_3262_, v_sz_3261_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; 
lean_dec_ref(v___y_3264_);
lean_dec_ref(v___x_3259_);
v___x_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3272_, 0, v_b_3263_);
lean_ctor_set(v___x_3272_, 1, v___y_3269_);
return v___x_3272_;
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3274_; 
v_a_3273_ = lean_array_uget_borrowed(v_as_3260_, v_i_3262_);
lean_inc_ref(v___y_3264_);
lean_inc_n(v_a_3273_, 2);
lean_inc_ref(v___x_3259_);
v___x_3274_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v___x_3259_, v_a_3273_, v_a_3273_, v___x_3271_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v_a_3276_; lean_object* v_snd_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; size_t v___x_3280_; size_t v___x_3281_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
v_a_3276_ = lean_ctor_get(v___x_3274_, 1);
lean_inc(v_a_3276_);
lean_dec_ref_known(v___x_3274_, 2);
v_snd_3277_ = lean_ctor_get(v_a_3275_, 1);
lean_inc(v_snd_3277_);
lean_dec(v_a_3275_);
v___x_3278_ = l_Lake_Job_toOpaque___redArg(v_snd_3277_);
v___x_3279_ = l_Lake_Job_mix___redArg(v_b_3263_, v___x_3278_);
v___x_3280_ = ((size_t)1ULL);
v___x_3281_ = lean_usize_add(v_i_3262_, v___x_3280_);
v_i_3262_ = v___x_3281_;
v_b_3263_ = v___x_3279_;
v___y_3269_ = v_a_3276_;
goto _start;
}
else
{
lean_object* v_a_3283_; lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec_ref(v___y_3264_);
lean_dec_ref(v_b_3263_);
lean_dec_ref(v___x_3259_);
v_a_3283_ = lean_ctor_get(v___x_3274_, 0);
v_a_3284_ = lean_ctor_get(v___x_3274_, 1);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3274_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_inc(v_a_3283_);
lean_dec(v___x_3274_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3283_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* v___x_3292_, lean_object* v_as_3293_, lean_object* v_sz_3294_, lean_object* v_i_3295_, lean_object* v_b_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
size_t v_sz_boxed_3304_; size_t v_i_boxed_3305_; lean_object* v_res_3306_; 
v_sz_boxed_3304_ = lean_unbox_usize(v_sz_3294_);
lean_dec(v_sz_3294_);
v_i_boxed_3305_ = lean_unbox_usize(v_i_3295_);
lean_dec(v_i_3295_);
v_res_3306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_3292_, v_as_3293_, v_sz_boxed_3304_, v_i_boxed_3305_, v_b_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v_as_3293_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* v___x_3307_, lean_object* v_as_3308_, size_t v_sz_3309_, size_t v_i_3310_, lean_object* v_b_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
uint8_t v___x_3319_; 
v___x_3319_ = lean_usize_dec_lt(v_i_3310_, v_sz_3309_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; 
lean_dec_ref(v___y_3312_);
lean_dec_ref(v___x_3307_);
v___x_3320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3320_, 0, v_b_3311_);
lean_ctor_set(v___x_3320_, 1, v___y_3317_);
return v___x_3320_;
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3322_; 
v_a_3321_ = lean_array_uget_borrowed(v_as_3308_, v_i_3310_);
lean_inc_ref(v___y_3312_);
lean_inc(v_a_3321_);
lean_inc_ref(v___x_3307_);
v___x_3322_ = l_Lake_Package_fetchTargetJob(v___x_3307_, v_a_3321_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v_a_3324_; lean_object* v___x_3325_; size_t v___x_3326_; size_t v___x_3327_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
v_a_3324_ = lean_ctor_get(v___x_3322_, 1);
lean_inc(v_a_3324_);
lean_dec_ref_known(v___x_3322_, 2);
v___x_3325_ = l_Lake_Job_mix___redArg(v_b_3311_, v_a_3323_);
v___x_3326_ = ((size_t)1ULL);
v___x_3327_ = lean_usize_add(v_i_3310_, v___x_3326_);
v_i_3310_ = v___x_3327_;
v_b_3311_ = v___x_3325_;
v___y_3317_ = v_a_3324_;
goto _start;
}
else
{
lean_object* v_a_3329_; lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec_ref(v___y_3312_);
lean_dec_ref(v_b_3311_);
lean_dec_ref(v___x_3307_);
v_a_3329_ = lean_ctor_get(v___x_3322_, 0);
v_a_3330_ = lean_ctor_get(v___x_3322_, 1);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3322_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_inc(v_a_3329_);
lean_dec(v___x_3322_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3329_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* v___x_3338_, lean_object* v_as_3339_, lean_object* v_sz_3340_, lean_object* v_i_3341_, lean_object* v_b_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
size_t v_sz_boxed_3350_; size_t v_i_boxed_3351_; lean_object* v_res_3352_; 
v_sz_boxed_3350_ = lean_unbox_usize(v_sz_3340_);
lean_dec(v_sz_3340_);
v_i_boxed_3351_ = lean_unbox_usize(v_i_3341_);
lean_dec(v_i_3341_);
v_res_3352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_3338_, v_as_3339_, v_sz_boxed_3350_, v_i_boxed_3351_, v_b_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v_as_3339_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object* v_self_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_){
_start:
{
lean_object* v_pkg_3363_; lean_object* v_name_3364_; lean_object* v_config_3365_; lean_object* v_baseName_3366_; lean_object* v_keyName_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v_pkg_3363_ = lean_ctor_get(v_self_3355_, 0);
lean_inc_ref_n(v_pkg_3363_, 2);
v_name_3364_ = lean_ctor_get(v_self_3355_, 1);
lean_inc(v_name_3364_);
v_config_3365_ = lean_ctor_get(v_self_3355_, 2);
lean_inc(v_config_3365_);
lean_dec_ref(v_self_3355_);
v_baseName_3366_ = lean_ctor_get(v_pkg_3363_, 1);
v_keyName_3367_ = lean_ctor_get(v_pkg_3363_, 2);
v___x_3368_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_3367_);
v___x_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3369_, 0, v_keyName_3367_);
v___x_3370_ = l_Lake_Package_keyword;
v___x_3371_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3369_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
lean_ctor_set(v___x_3371_, 2, v_pkg_3363_);
lean_ctor_set(v___x_3371_, 3, v___x_3368_);
lean_inc_ref(v_a_3356_);
lean_inc_ref(v_a_3360_);
lean_inc(v_a_3359_);
lean_inc(v_a_3358_);
lean_inc(v_a_3357_);
v___x_3372_ = lean_apply_7(v_a_3356_, v___x_3371_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, lean_box(0));
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3410_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
v_a_3374_ = lean_ctor_get(v___x_3372_, 1);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3376_ = v___x_3372_;
v_isShared_3377_ = v_isSharedCheck_3410_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_inc(v_a_3373_);
lean_dec(v___x_3372_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3410_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
uint8_t v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v_needs_3382_; lean_object* v_extraDepTargets_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; uint8_t v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3397_; 
v___x_3378_ = 1;
lean_inc(v_baseName_3366_);
v___x_3379_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3366_, v___x_3378_);
v___x_3380_ = lean_unsigned_to_nat(0u);
v___x_3381_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v_needs_3382_ = lean_ctor_get(v_config_3365_, 5);
lean_inc_ref(v_needs_3382_);
v_extraDepTargets_3383_ = lean_ctor_get(v_config_3365_, 6);
lean_inc_ref(v_extraDepTargets_3383_);
lean_dec(v_config_3365_);
v___x_3384_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0));
v___x_3385_ = lean_string_append(v___x_3379_, v___x_3384_);
v___x_3386_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3364_, v___x_3378_);
v___x_3387_ = lean_string_append(v___x_3385_, v___x_3386_);
lean_dec_ref(v___x_3386_);
v___x_3388_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1));
v___x_3389_ = lean_string_append(v___x_3387_, v___x_3388_);
v___x_3390_ = 0;
v___x_3391_ = 0;
v___x_3392_ = l_Lake_BuildTrace_nil(v___x_3389_);
v___x_3393_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3393_, 0, v___x_3381_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
lean_ctor_set(v___x_3393_, 2, v___x_3380_);
lean_ctor_set_uint8(v___x_3393_, sizeof(void*)*3, v___x_3390_);
lean_ctor_set_uint8(v___x_3393_, sizeof(void*)*3 + 1, v___x_3391_);
v___x_3394_ = lean_box(0);
v___x_3395_ = lean_box(0);
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 1, v___x_3393_);
lean_ctor_set(v___x_3376_, 0, v___x_3395_);
v___x_3397_ = v___x_3376_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3395_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v___x_3393_);
v___x_3397_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v_job_3400_; lean_object* v___x_3401_; size_t v_sz_3402_; size_t v___x_3403_; lean_object* v___x_3404_; 
v___x_3398_ = lean_task_pure(v___x_3397_);
v___x_3399_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v_job_3400_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_3400_, 0, v___x_3398_);
lean_ctor_set(v_job_3400_, 1, v___x_3394_);
lean_ctor_set(v_job_3400_, 2, v___x_3399_);
lean_ctor_set_uint8(v_job_3400_, sizeof(void*)*3, v___x_3391_);
v___x_3401_ = l_Lake_Job_mix___redArg(v_job_3400_, v_a_3373_);
v_sz_3402_ = lean_array_size(v_extraDepTargets_3383_);
v___x_3403_ = ((size_t)0ULL);
lean_inc_ref(v_a_3356_);
lean_inc_ref(v_pkg_3363_);
v___x_3404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_3363_, v_extraDepTargets_3383_, v_sz_3402_, v___x_3403_, v___x_3401_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3374_);
lean_dec_ref(v_extraDepTargets_3383_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v_a_3406_; size_t v_sz_3407_; lean_object* v___x_3408_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
v_a_3406_ = lean_ctor_get(v___x_3404_, 1);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3404_, 2);
v_sz_3407_ = lean_array_size(v_needs_3382_);
v___x_3408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_3363_, v_needs_3382_, v_sz_3407_, v___x_3403_, v_a_3405_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3406_);
lean_dec_ref(v_needs_3382_);
return v___x_3408_;
}
else
{
lean_dec_ref(v_needs_3382_);
lean_dec_ref(v_pkg_3363_);
lean_dec_ref(v_a_3356_);
return v___x_3404_;
}
}
}
}
else
{
lean_dec(v_config_3365_);
lean_dec(v_name_3364_);
lean_dec_ref(v_pkg_3363_);
lean_dec_ref(v_a_3356_);
return v___x_3372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object* v_self_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_);
lean_dec_ref(v_a_3416_);
lean_dec(v_a_3415_);
lean_dec(v_a_3414_);
lean_dec(v_a_3413_);
return v_res_3419_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3421_; uint8_t v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___f_3421_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3422_ = 1;
v___x_3423_ = l_Lake_instDataKindUnit;
v___x_3424_ = ((lean_object*)(l_Lake_LeanLib_extraDepFacetConfig___closed__0));
v___x_3425_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3426_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
lean_ctor_set(v___x_3426_, 1, v___x_3424_);
lean_ctor_set(v___x_3426_, 2, v___x_3423_);
lean_ctor_set(v___x_3426_, 3, v___f_3421_);
lean_ctor_set_uint8(v___x_3426_, sizeof(void*)*4, v___x_3422_);
lean_ctor_set_uint8(v___x_3426_, sizeof(void*)*4 + 1, v___x_3422_);
return v___x_3426_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_obj_once(&l_Lake_LeanLib_extraDepFacetConfig___closed__1, &l_Lake_LeanLib_extraDepFacetConfig___closed__1_once, _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* v_self_3428_, size_t v_sz_3429_, size_t v_i_3430_, lean_object* v_bs_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
uint8_t v___x_3439_; 
v___x_3439_ = lean_usize_dec_lt(v_i_3430_, v_sz_3429_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; 
lean_dec_ref(v___y_3432_);
lean_dec_ref(v_self_3428_);
v___x_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3440_, 0, v_bs_3431_);
lean_ctor_set(v___x_3440_, 1, v___y_3437_);
return v___x_3440_;
}
else
{
lean_object* v_pkg_3441_; lean_object* v_name_3442_; lean_object* v_keyName_3443_; lean_object* v_v_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v_pkg_3441_ = lean_ctor_get(v_self_3428_, 0);
v_name_3442_ = lean_ctor_get(v_self_3428_, 1);
v_keyName_3443_ = lean_ctor_get(v_pkg_3441_, 2);
v_v_3444_ = lean_array_uget_borrowed(v_bs_3431_, v_i_3430_);
lean_inc(v_name_3442_);
lean_inc(v_keyName_3443_);
v___x_3445_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3445_, 0, v_keyName_3443_);
lean_ctor_set(v___x_3445_, 1, v_name_3442_);
v___x_3446_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc(v_v_3444_);
lean_inc_ref(v_self_3428_);
v___x_3447_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3445_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
lean_ctor_set(v___x_3447_, 2, v_self_3428_);
lean_ctor_set(v___x_3447_, 3, v_v_3444_);
lean_inc_ref(v___y_3432_);
lean_inc_ref(v___y_3436_);
lean_inc(v___y_3435_);
lean_inc(v___y_3434_);
lean_inc(v___y_3433_);
v___x_3448_ = lean_apply_7(v___y_3432_, v___x_3447_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, lean_box(0));
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v_a_3450_; lean_object* v___x_3451_; lean_object* v_bs_x27_3452_; lean_object* v___x_3453_; size_t v___x_3454_; size_t v___x_3455_; lean_object* v___x_3456_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
v_a_3450_ = lean_ctor_get(v___x_3448_, 1);
lean_inc(v_a_3450_);
lean_dec_ref_known(v___x_3448_, 2);
v___x_3451_ = lean_unsigned_to_nat(0u);
v_bs_x27_3452_ = lean_array_uset(v_bs_3431_, v_i_3430_, v___x_3451_);
v___x_3453_ = l_Lake_Job_toOpaque___redArg(v_a_3449_);
v___x_3454_ = ((size_t)1ULL);
v___x_3455_ = lean_usize_add(v_i_3430_, v___x_3454_);
v___x_3456_ = lean_array_uset(v_bs_x27_3452_, v_i_3430_, v___x_3453_);
v_i_3430_ = v___x_3455_;
v_bs_3431_ = v___x_3456_;
v___y_3437_ = v_a_3450_;
goto _start;
}
else
{
lean_object* v_a_3458_; lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v___y_3432_);
lean_dec_ref(v_bs_3431_);
lean_dec_ref(v_self_3428_);
v_a_3458_ = lean_ctor_get(v___x_3448_, 0);
v_a_3459_ = lean_ctor_get(v___x_3448_, 1);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3448_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_inc(v_a_3458_);
lean_dec(v___x_3448_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* v_self_3467_, lean_object* v_sz_3468_, lean_object* v_i_3469_, lean_object* v_bs_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
size_t v_sz_boxed_3478_; size_t v_i_boxed_3479_; lean_object* v_res_3480_; 
v_sz_boxed_3478_ = lean_unbox_usize(v_sz_3468_);
lean_dec(v_sz_3468_);
v_i_boxed_3479_ = lean_unbox_usize(v_i_3469_);
lean_dec(v_i_3469_);
v_res_3480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3467_, v_sz_boxed_3478_, v_i_boxed_3479_, v_bs_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec(v___y_3472_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object* v_self_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v_config_3490_; lean_object* v_defaultFacets_3491_; size_t v_sz_3492_; size_t v___x_3493_; lean_object* v___x_3494_; 
v_config_3490_ = lean_ctor_get(v_self_3482_, 2);
v_defaultFacets_3491_ = lean_ctor_get(v_config_3490_, 7);
lean_inc_ref(v_defaultFacets_3491_);
v_sz_3492_ = lean_array_size(v_defaultFacets_3491_);
v___x_3493_ = ((size_t)0ULL);
v___x_3494_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3482_, v_sz_3492_, v___x_3493_, v_defaultFacets_3491_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3505_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
v_a_3496_ = lean_ctor_get(v___x_3494_, 1);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3498_ = v___x_3494_;
v_isShared_3499_ = v_isSharedCheck_3505_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_inc(v_a_3495_);
lean_dec(v___x_3494_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3505_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3503_; 
v___x_3500_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0));
v___x_3501_ = l_Lake_Job_mixArray___redArg(v_a_3495_, v___x_3500_);
lean_dec(v_a_3495_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3501_);
v___x_3503_ = v___x_3498_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3501_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v_a_3496_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
else
{
lean_object* v_a_3506_; lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
v_a_3506_ = lean_ctor_get(v___x_3494_, 0);
v_a_3507_ = lean_ctor_get(v___x_3494_, 1);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3494_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_inc(v_a_3506_);
lean_dec(v___x_3494_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3506_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object* v_self_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
lean_dec_ref(v_a_3520_);
lean_dec(v_a_3519_);
lean_dec(v_a_3518_);
lean_dec(v_a_3517_);
return v_res_3523_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3525_; uint8_t v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___f_3525_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3526_ = 1;
v___x_3527_ = l_Lake_instDataKindUnit;
v___x_3528_ = ((lean_object*)(l_Lake_LeanLib_defaultFacetConfig___closed__0));
v___x_3529_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3530_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
lean_ctor_set(v___x_3530_, 1, v___x_3528_);
lean_ctor_set(v___x_3530_, 2, v___x_3527_);
lean_ctor_set(v___x_3530_, 3, v___f_3525_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*4, v___x_3526_);
lean_ctor_set_uint8(v___x_3530_, sizeof(void*)*4 + 1, v___x_3526_);
return v___x_3530_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = lean_obj_once(&l_Lake_LeanLib_defaultFacetConfig___closed__1, &l_Lake_LeanLib_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanLib_defaultFacetConfig___closed__1);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_3532_, lean_object* v_v_3533_, lean_object* v_t_3534_){
_start:
{
if (lean_obj_tag(v_t_3534_) == 0)
{
lean_object* v_size_3535_; lean_object* v_k_3536_; lean_object* v_v_3537_; lean_object* v_l_3538_; lean_object* v_r_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3819_; 
v_size_3535_ = lean_ctor_get(v_t_3534_, 0);
v_k_3536_ = lean_ctor_get(v_t_3534_, 1);
v_v_3537_ = lean_ctor_get(v_t_3534_, 2);
v_l_3538_ = lean_ctor_get(v_t_3534_, 3);
v_r_3539_ = lean_ctor_get(v_t_3534_, 4);
v_isSharedCheck_3819_ = !lean_is_exclusive(v_t_3534_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3541_ = v_t_3534_;
v_isShared_3542_ = v_isSharedCheck_3819_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_r_3539_);
lean_inc(v_l_3538_);
lean_inc(v_v_3537_);
lean_inc(v_k_3536_);
lean_inc(v_size_3535_);
lean_dec(v_t_3534_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3819_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
uint8_t v___x_3543_; 
v___x_3543_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3532_, v_k_3536_);
switch(v___x_3543_)
{
case 0:
{
lean_object* v_impl_3544_; lean_object* v___x_3545_; 
lean_dec(v_size_3535_);
v_impl_3544_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3532_, v_v_3533_, v_l_3538_);
v___x_3545_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3539_) == 0)
{
lean_object* v_size_3546_; lean_object* v_size_3547_; lean_object* v_k_3548_; lean_object* v_v_3549_; lean_object* v_l_3550_; lean_object* v_r_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v_size_3546_ = lean_ctor_get(v_r_3539_, 0);
v_size_3547_ = lean_ctor_get(v_impl_3544_, 0);
lean_inc(v_size_3547_);
v_k_3548_ = lean_ctor_get(v_impl_3544_, 1);
lean_inc(v_k_3548_);
v_v_3549_ = lean_ctor_get(v_impl_3544_, 2);
lean_inc(v_v_3549_);
v_l_3550_ = lean_ctor_get(v_impl_3544_, 3);
lean_inc(v_l_3550_);
v_r_3551_ = lean_ctor_get(v_impl_3544_, 4);
lean_inc(v_r_3551_);
v___x_3552_ = lean_unsigned_to_nat(3u);
v___x_3553_ = lean_nat_mul(v___x_3552_, v_size_3546_);
v___x_3554_ = lean_nat_dec_lt(v___x_3553_, v_size_3547_);
lean_dec(v___x_3553_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3558_; 
lean_dec(v_r_3551_);
lean_dec(v_l_3550_);
lean_dec(v_v_3549_);
lean_dec(v_k_3548_);
v___x_3555_ = lean_nat_add(v___x_3545_, v_size_3547_);
lean_dec(v_size_3547_);
v___x_3556_ = lean_nat_add(v___x_3555_, v_size_3546_);
lean_dec(v___x_3555_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 3, v_impl_3544_);
lean_ctor_set(v___x_3541_, 0, v___x_3556_);
v___x_3558_ = v___x_3541_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3556_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_k_3536_);
lean_ctor_set(v_reuseFailAlloc_3559_, 2, v_v_3537_);
lean_ctor_set(v_reuseFailAlloc_3559_, 3, v_impl_3544_);
lean_ctor_set(v_reuseFailAlloc_3559_, 4, v_r_3539_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
else
{
lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3625_; 
v_isSharedCheck_3625_ = !lean_is_exclusive(v_impl_3544_);
if (v_isSharedCheck_3625_ == 0)
{
lean_object* v_unused_3626_; lean_object* v_unused_3627_; lean_object* v_unused_3628_; lean_object* v_unused_3629_; lean_object* v_unused_3630_; 
v_unused_3626_ = lean_ctor_get(v_impl_3544_, 4);
lean_dec(v_unused_3626_);
v_unused_3627_ = lean_ctor_get(v_impl_3544_, 3);
lean_dec(v_unused_3627_);
v_unused_3628_ = lean_ctor_get(v_impl_3544_, 2);
lean_dec(v_unused_3628_);
v_unused_3629_ = lean_ctor_get(v_impl_3544_, 1);
lean_dec(v_unused_3629_);
v_unused_3630_ = lean_ctor_get(v_impl_3544_, 0);
lean_dec(v_unused_3630_);
v___x_3561_ = v_impl_3544_;
v_isShared_3562_ = v_isSharedCheck_3625_;
goto v_resetjp_3560_;
}
else
{
lean_dec(v_impl_3544_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3625_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v_size_3563_; lean_object* v_size_3564_; lean_object* v_k_3565_; lean_object* v_v_3566_; lean_object* v_l_3567_; lean_object* v_r_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v_size_3563_ = lean_ctor_get(v_l_3550_, 0);
v_size_3564_ = lean_ctor_get(v_r_3551_, 0);
v_k_3565_ = lean_ctor_get(v_r_3551_, 1);
v_v_3566_ = lean_ctor_get(v_r_3551_, 2);
v_l_3567_ = lean_ctor_get(v_r_3551_, 3);
v_r_3568_ = lean_ctor_get(v_r_3551_, 4);
v___x_3569_ = lean_unsigned_to_nat(2u);
v___x_3570_ = lean_nat_mul(v___x_3569_, v_size_3563_);
v___x_3571_ = lean_nat_dec_lt(v_size_3564_, v___x_3570_);
lean_dec(v___x_3570_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3600_; 
lean_inc(v_r_3568_);
lean_inc(v_l_3567_);
lean_inc(v_v_3566_);
lean_inc(v_k_3565_);
v_isSharedCheck_3600_ = !lean_is_exclusive(v_r_3551_);
if (v_isSharedCheck_3600_ == 0)
{
lean_object* v_unused_3601_; lean_object* v_unused_3602_; lean_object* v_unused_3603_; lean_object* v_unused_3604_; lean_object* v_unused_3605_; 
v_unused_3601_ = lean_ctor_get(v_r_3551_, 4);
lean_dec(v_unused_3601_);
v_unused_3602_ = lean_ctor_get(v_r_3551_, 3);
lean_dec(v_unused_3602_);
v_unused_3603_ = lean_ctor_get(v_r_3551_, 2);
lean_dec(v_unused_3603_);
v_unused_3604_ = lean_ctor_get(v_r_3551_, 1);
lean_dec(v_unused_3604_);
v_unused_3605_ = lean_ctor_get(v_r_3551_, 0);
lean_dec(v_unused_3605_);
v___x_3573_ = v_r_3551_;
v_isShared_3574_ = v_isSharedCheck_3600_;
goto v_resetjp_3572_;
}
else
{
lean_dec(v_r_3551_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3600_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___x_3588_; lean_object* v___y_3590_; 
v___x_3575_ = lean_nat_add(v___x_3545_, v_size_3547_);
lean_dec(v_size_3547_);
v___x_3576_ = lean_nat_add(v___x_3575_, v_size_3546_);
lean_dec(v___x_3575_);
v___x_3588_ = lean_nat_add(v___x_3545_, v_size_3563_);
if (lean_obj_tag(v_l_3567_) == 0)
{
lean_object* v_size_3598_; 
v_size_3598_ = lean_ctor_get(v_l_3567_, 0);
lean_inc(v_size_3598_);
v___y_3590_ = v_size_3598_;
goto v___jp_3589_;
}
else
{
lean_object* v___x_3599_; 
v___x_3599_ = lean_unsigned_to_nat(0u);
v___y_3590_ = v___x_3599_;
goto v___jp_3589_;
}
v___jp_3577_:
{
lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3581_ = lean_nat_add(v___y_3578_, v___y_3580_);
lean_dec(v___y_3580_);
lean_dec(v___y_3578_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 4, v_r_3539_);
lean_ctor_set(v___x_3573_, 3, v_r_3568_);
lean_ctor_set(v___x_3573_, 2, v_v_3537_);
lean_ctor_set(v___x_3573_, 1, v_k_3536_);
lean_ctor_set(v___x_3573_, 0, v___x_3581_);
v___x_3583_ = v___x_3573_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3587_, 1, v_k_3536_);
lean_ctor_set(v_reuseFailAlloc_3587_, 2, v_v_3537_);
lean_ctor_set(v_reuseFailAlloc_3587_, 3, v_r_3568_);
lean_ctor_set(v_reuseFailAlloc_3587_, 4, v_r_3539_);
v___x_3583_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
lean_object* v___x_3585_; 
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 4, v___x_3583_);
lean_ctor_set(v___x_3561_, 3, v___y_3579_);
lean_ctor_set(v___x_3561_, 2, v_v_3566_);
lean_ctor_set(v___x_3561_, 1, v_k_3565_);
lean_ctor_set(v___x_3561_, 0, v___x_3576_);
v___x_3585_ = v___x_3561_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3576_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_k_3565_);
lean_ctor_set(v_reuseFailAlloc_3586_, 2, v_v_3566_);
lean_ctor_set(v_reuseFailAlloc_3586_, 3, v___y_3579_);
lean_ctor_set(v_reuseFailAlloc_3586_, 4, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
v___jp_3589_:
{
lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3591_ = lean_nat_add(v___x_3588_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec(v___x_3588_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 4, v_l_3567_);
lean_ctor_set(v___x_3541_, 3, v_l_3550_);
lean_ctor_set(v___x_3541_, 2, v_v_3549_);
lean_ctor_set(v___x_3541_, 1, v_k_3548_);
lean_ctor_set(v___x_3541_, 0, v___x_3591_);
v___x_3593_ = v___x_3541_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3591_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v_k_3548_);
lean_ctor_set(v_reuseFailAlloc_3597_, 2, v_v_3549_);
lean_ctor_set(v_reuseFailAlloc_3597_, 3, v_l_3550_);
lean_ctor_set(v_reuseFailAlloc_3597_, 4, v_l_3567_);
v___x_3593_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3594_; 
v___x_3594_ = lean_nat_add(v___x_3545_, v_size_3546_);
if (lean_obj_tag(v_r_3568_) == 0)
{
lean_object* v_size_3595_; 
v_size_3595_ = lean_ctor_get(v_r_3568_, 0);
lean_inc(v_size_3595_);
v___y_3578_ = v___x_3594_;
v___y_3579_ = v___x_3593_;
v___y_3580_ = v_size_3595_;
goto v___jp_3577_;
}
else
{
lean_object* v___x_3596_; 
v___x_3596_ = lean_unsigned_to_nat(0u);
v___y_3578_ = v___x_3594_;
v___y_3579_ = v___x_3593_;
v___y_3580_ = v___x_3596_;
goto v___jp_3577_;
}
}
}
}
}
else
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3611_; 
lean_del_object(v___x_3541_);
v___x_3606_ = lean_nat_add(v___x_3545_, v_size_3547_);
lean_dec(v_size_3547_);
v___x_3607_ = lean_nat_add(v___x_3606_, v_size_3546_);
lean_dec(v___x_3606_);
v___x_3608_ = lean_nat_add(v___x_3545_, v_size_3546_);
v___x_3609_ = lean_nat_add(v___x_3608_, v_size_3564_);
lean_dec(v___x_3608_);
lean_inc_ref(v_r_3539_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 4, v_r_3539_);
lean_ctor_set(v___x_3561_, 3, v_r_3551_);
lean_ctor_set(v___x_3561_, 2, v_v_3537_);
lean_ctor_set(v___x_3561_, 1, v_k_3536_);
lean_ctor_set(v___x_3561_, 0, v___x_3609_);
v___x_3611_ = v___x_3561_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_k_3536_);
lean_ctor_set(v_reuseFailAlloc_3624_, 2, v_v_3537_);
lean_ctor_set(v_reuseFailAlloc_3624_, 3, v_r_3551_);
lean_ctor_set(v_reuseFailAlloc_3624_, 4, v_r_3539_);
v___x_3611_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
v_isSharedCheck_3618_ = !lean_is_exclusive(v_r_3539_);
if (v_isSharedCheck_3618_ == 0)
{
lean_object* v_unused_3619_; lean_object* v_unused_3620_; lean_object* v_unused_3621_; lean_object* v_unused_3622_; lean_object* v_unused_3623_; 
v_unused_3619_ = lean_ctor_get(v_r_3539_, 4);
lean_dec(v_unused_3619_);
v_unused_3620_ = lean_ctor_get(v_r_3539_, 3);
lean_dec(v_unused_3620_);
v_unused_3621_ = lean_ctor_get(v_r_3539_, 2);
lean_dec(v_unused_3621_);
v_unused_3622_ = lean_ctor_get(v_r_3539_, 1);
lean_dec(v_unused_3622_);
v_unused_3623_ = lean_ctor_get(v_r_3539_, 0);
lean_dec(v_unused_3623_);
v___x_3613_ = v_r_3539_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_dec(v_r_3539_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 4, v___x_3611_);
lean_ctor_set(v___x_3613_, 3, v_l_3550_);
lean_ctor_set(v___x_3613_, 2, v_v_3549_);
lean_ctor_set(v___x_3613_, 1, v_k_3548_);
lean_ctor_set(v___x_3613_, 0, v___x_3607_);
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3607_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_k_3548_);
lean_ctor_set(v_reuseFailAlloc_3617_, 2, v_v_3549_);
lean_ctor_set(v_reuseFailAlloc_3617_, 3, v_l_3550_);
lean_ctor_set(v_reuseFailAlloc_3617_, 4, v___x_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3631_; 
v_l_3631_ = lean_ctor_get(v_impl_3544_, 3);
lean_inc(v_l_3631_);
if (lean_obj_tag(v_l_3631_) == 0)
{
lean_object* v_r_3632_; lean_object* v_k_3633_; lean_object* v_v_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3645_; 
v_r_3632_ = lean_ctor_get(v_impl_3544_, 4);
v_k_3633_ = lean_ctor_get(v_impl_3544_, 1);
v_v_3634_ = lean_ctor_get(v_impl_3544_, 2);
v_isSharedCheck_3645_ = !lean_is_exclusive(v_impl_3544_);
if (v_isSharedCheck_3645_ == 0)
{
lean_object* v_unused_3646_; lean_object* v_unused_3647_; 
v_unused_3646_ = lean_ctor_get(v_impl_3544_, 3);
lean_dec(v_unused_3646_);
v_unused_3647_ = lean_ctor_get(v_impl_3544_, 0);
lean_dec(v_unused_3647_);
v___x_3636_ = v_impl_3544_;
v_isShared_3637_ = v_isSharedCheck_3645_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_r_3632_);
lean_inc(v_v_3634_);
lean_inc(v_k_3633_);
lean_dec(v_impl_3544_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3645_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3638_; lean_object* v___x_3640_; 
v___x_3638_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3632_);
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 3, v_r_3632_);
lean_ctor_set(v___x_3636_, 2, v_v_3537_);
lean_ctor_set(v___x_3636_, 1, v_k_3536_);
lean_ctor_set(v___x_3636_, 0, v___x_3545_);
v___x_3640_ = v___x_3636_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_k_3536_);
lean_ctor_set(v_reuseFailAlloc_3644_, 2, v_v_3537_);
lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_r_3632_);
lean_ctor_set(v_reuseFailAlloc_3644_, 4, v_r_3632_);
v___x_3640_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3642_; 
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 4, v___x_3640_);
lean_ctor_set(v___x_3541_, 3, v_l_3631_);
lean_ctor_set(v___x_3541_, 2, v_v_3634_);
lean_ctor_set(v___x_3541_, 1, v_k_3633_);
lean_ctor_set(v___x_3541_, 0, v___x_3638_);
v___x_3642_ = v___x_3541_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v___x_3638_);
lean_ctor_set(v_reuseFailAlloc_3643_, 1, v_k_3633_);
lean_ctor_set(v_reuseFailAlloc_3643_, 2, v_v_3634_);
lean_ctor_set(v_reuseFailAlloc_3643_, 3, v_l_3631_);
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
else
{
lean_object* v_r_3648_; 
v_r_3648_ = lean_ctor_get(v_impl_3544_, 4);
lean_inc(v_r_3648_);
if (lean_obj_tag(v_r_3648_) == 0)
{
lean_object* v_k_3649_; lean_object* v_v_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3673_; 
v_k_3649_ = lean_ctor_get(v_impl_3544_, 1);
v_v_3650_ = lean_ctor_get(v_impl_3544_, 2);
v_isSharedCheck_3673_ = !lean_is_exclusive(v_impl_3544_);
if (v_isSharedCheck_3673_ == 0)
{
lean_object* v_unused_3674_; lean_object* v_unused_3675_; lean_object* v_unused_3676_; 
v_unused_3674_ = lean_ctor_get(v_impl_3544_, 4);
lean_dec(v_unused_3674_);
v_unused_3675_ = lean_ctor_get(v_impl_3544_, 3);
lean_dec(v_unused_3675_);
v_unused_3676_ = lean_ctor_get(v_impl_3544_, 0);
lean_dec(v_unused_3676_);
v___x_3652_ = v_impl_3544_;
v_isShared_3653_ = v_isSharedCheck_3673_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_v_3650_);
lean_inc(v_k_3649_);
lean_dec(v_impl_3544_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3673_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v_k_3654_; lean_object* v_v_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3669_; 
v_k_3654_ = lean_ctor_get(v_r_3648_, 1);
v_v_3655_ = lean_ctor_get(v_r_3648_, 2);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_r_3648_);
if (v_isSharedCheck_3669_ == 0)
{
lean_object* v_unused_3670_; lean_object* v_unused_3671_; lean_object* v_unused_3672_; 
v_unused_3670_ = lean_ctor_get(v_r_3648_, 4);
lean_dec(v_unused_3670_);
v_unused_3671_ = lean_ctor_get(v_r_3648_, 3);
lean_dec(v_unused_3671_);
v_unused_3672_ = lean_ctor_get(v_r_3648_, 0);
lean_dec(v_unused_3672_);
v___x_3657_ = v_r_3648_;
v_isShared_3658_ = v_isSharedCheck_3669_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_v_3655_);
lean_inc(v_k_3654_);
lean_dec(v_r_3648_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3669_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3659_ = lean_unsigned_to_nat(3u);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 4, v_l_3631_);
lean_ctor_set(v___x_3657_, 3, v_l_3631_);
lean_ctor_set(v___x_3657_, 2, v_v_3650_);
lean_ctor_set(v___x_3657_, 1, v_k_3649_);
lean_ctor_set(v___x_3657_, 0, v___x_3545_);
v___x_3661_ = v___x_3657_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_k_3649_);
lean_ctor_set(v_reuseFailAlloc_3668_, 2, v_v_3650_);
lean_ctor_set(v_reuseFailAlloc_3668_, 3, v_l_3631_);
lean_ctor_set(v_reuseFailAlloc_3668_, 4, v_l_3631_);
v___x_3661_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3663_; 
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 4, v_l_3631_);
lean_ctor_set(v___x_3652_, 2, v_v_3537_);
lean_ctor_set(v___x_3652_, 1, v_k_3536_);
lean_ctor_set(v___x_3652_, 0, v___x_3545_);
v___x_3663_ = v___x_3652_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3545_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_k_3536_);
lean_ctor_set(v_reuseFailAlloc_3667_, 2, v_v_3537_);
lean_ctor_set(v_reuseFailAlloc_3667_, 3, v_l_3631_);
lean_ctor_set(v_reuseFailAlloc_3667_, 4, v_l_3631_);
v___x_3663_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3665_; 
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 4, v___x_3663_);
lean_ctor_set(v___x_3541_, 3, v___x_3661_);
lean_ctor_set(v___x_3541_, 2, v_v_3655_);
lean_ctor_set(v___x_3541_, 1, v_k_3654_);
lean_ctor_set(v___x_3541_, 0, v___x_3659_);
v___x_3665_ = v___x_3541_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_k_3654_);
lean_ctor_set(v_reuseFailAlloc_3666_, 2, v_v_3655_);
lean_ctor_set(v_reuseFailAlloc_3666_, 3, v___x_3661_);
lean_ctor_set(v_reuseFailAlloc_3666_, 4, v___x_3663_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
}
}
else
{
lean_object* v___x_3677_; lean_object* v___x_3679_; 
v___x_3677_ = lean_unsigned_to_nat(2u);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 4, v_r_3648_);
lean_ctor_set(v___x_3541_, 3, v_impl_3544_);
lean_ctor_set(v___x_3541_, 0, v___x_3677_);
v___x_3679_ = v___x_3541_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3677_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_k_3536_);
lean_ctor_set(v_reuseFailAlloc_3680_, 2, v_v_3537_);
lean_ctor_set(v_reuseFailAlloc_3680_, 3, v_impl_3544_);
lean_ctor_set(v_reuseFailAlloc_3680_, 4, v_r_3648_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3682_; 
lean_dec(v_v_3537_);
lean_dec(v_k_3536_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 2, v_v_3533_);
lean_ctor_set(v___x_3541_, 1, v_k_3532_);
v___x_3682_ = v___x_3541_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_size_3535_);
lean_ctor_set(v_reuseFailAlloc_3683_, 1, v_k_3532_);
lean_ctor_set(v_reuseFailAlloc_3683_, 2, v_v_3533_);
lean_ctor_set(v_reuseFailAlloc_3683_, 3, v_l_3538_);
lean_ctor_set(v_reuseFailAlloc_3683_, 4, v_r_3539_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
default: 
{
lean_object* v_impl_3684_; lean_object* v___x_3685_; 
lean_dec(v_size_3535_);
v_impl_3684_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3532_, v_v_3533_, v_r_3539_);
v___x_3685_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3538_) == 0)
{
lean_object* v_size_3686_; lean_object* v_size_3687_; lean_object* v_k_3688_; lean_object* v_v_3689_; lean_object* v_l_3690_; lean_object* v_r_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; uint8_t v___x_3694_; 
v_size_3686_ = lean_ctor_get(v_l_3538_, 0);
v_size_3687_ = lean_ctor_get(v_impl_3684_, 0);
lean_inc(v_size_3687_);
v_k_3688_ = lean_ctor_get(v_impl_3684_, 1);
lean_inc(v_k_3688_);
v_v_3689_ = lean_ctor_get(v_impl_3684_, 2);
lean_inc(v_v_3689_);
v_l_3690_ = lean_ctor_get(v_impl_3684_, 3);
lean_inc(v_l_3690_);
v_r_3691_ = lean_ctor_get(v_impl_3684_, 4);
lean_inc(v_r_3691_);
v___x_3692_ = lean_unsigned_to_nat(3u);
v___x_3693_ = lean_nat_mul(v___x_3692_, v_size_3686_);
v___x_3694_ = lean_nat_dec_lt(v___x_3693_, v_size_3687_);
lean_dec(v___x_3693_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3698_; 
lean_dec(v_r_3691_);
lean_dec(v_l_3690_);
lean_dec(v_v_3689_);
lean_dec(v_k_3688_);
v___x_3695_ = lean_nat_add(v___x_3685_, v_size_3686_);
v___x_3696_ = lean_nat_add(v___x_3695_, v_size_3687_);
lean_dec(v_size_3687_);
lean_dec(v___x_3695_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 4, v_impl_3684_);
lean_ctor_set(v___x_3541_, 0, v___x_3696_);
v___x_3698_ = v___x_3541_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3696_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v_k_3536_);
lean_ctor_set(v_reuseFailAlloc_3699_, 2, v_v_3537_);
lean_ctor_set(v_reuseFailAlloc_3699_, 3, v_l_3538_);
lean_ctor_set(v_reuseFailAlloc_3699_, 4, v_impl_3684_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
else
{
lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3763_; 
v_isSharedCheck_3763_ = !lean_is_exclusive(v_impl_3684_);
if (v_isSharedCheck_3763_ == 0)
{
lean_object* v_unused_3764_; lean_object* v_unused_3765_; lean_object* v_unused_3766_; lean_object* v_unused_3767_; lean_object* v_unused_3768_; 
v_unused_3764_ = lean_ctor_get(v_impl_3684_, 4);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_impl_3684_, 3);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_impl_3684_, 2);
lean_dec(v_unused_3766_);
v_unused_3767_ = lean_ctor_get(v_impl_3684_, 1);
lean_dec(v_unused_3767_);
v_unused_3768_ = lean_ctor_get(v_impl_3684_, 0);
lean_dec(v_unused_3768_);
v___x_3701_ = v_impl_3684_;
v_isShared_3702_ = v_isSharedCheck_3763_;
goto v_resetjp_3700_;
}
else
{
lean_dec(v_impl_3684_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3763_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v_size_3703_; lean_object* v_k_3704_; lean_object* v_v_3705_; lean_object* v_l_3706_; lean_object* v_r_3707_; lean_object* v_size_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; uint8_t v___x_3711_; 
v_size_3703_ = lean_ctor_get(v_l_3690_, 0);
v_k_3704_ = lean_ctor_get(v_l_3690_, 1);
v_v_3705_ = lean_ctor_get(v_l_3690_, 2);
v_l_3706_ = lean_ctor_get(v_l_3690_, 3);
v_r_3707_ = lean_ctor_get(v_l_3690_, 4);
v_size_3708_ = lean_ctor_get(v_r_3691_, 0);
v___x_3709_ = lean_unsigned_to_nat(2u);
v___x_3710_ = lean_nat_mul(v___x_3709_, v_size_3708_);
v___x_3711_ = lean_nat_dec_lt(v_size_3703_, v___x_3710_);
lean_dec(v___x_3710_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3739_; 
lean_inc(v_r_3707_);
lean_inc(v_l_3706_);
lean_inc(v_v_3705_);
lean_inc(v_k_3704_);
v_isSharedCheck_3739_ = !lean_is_exclusive(v_l_3690_);
if (v_isSharedCheck_3739_ == 0)
{
lean_object* v_unused_3740_; lean_object* v_unused_3741_; lean_object* v_unused_3742_; lean_object* v_unused_3743_; lean_object* v_unused_3744_; 
v_unused_3740_ = lean_ctor_get(v_l_3690_, 4);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_l_3690_, 3);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_l_3690_, 2);
lean_dec(v_unused_3742_);
v_unused_3743_ = lean_ctor_get(v_l_3690_, 1);
lean_dec(v_unused_3743_);
v_unused_3744_ = lean_ctor_get(v_l_3690_, 0);
lean_dec(v_unused_3744_);
v___x_3713_ = v_l_3690_;
v_isShared_3714_ = v_isSharedCheck_3739_;
goto v_resetjp_3712_;
}
else
{
lean_dec(v_l_3690_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3739_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3729_; 
v___x_3715_ = lean_nat_add(v___x_3685_, v_size_3686_);
v___x_3716_ = lean_nat_add(v___x_3715_, v_size_3687_);
lean_dec(v_size_3687_);
if (lean_obj_tag(v_l_3706_) == 0)
{
lean_object* v_size_3737_; 
v_size_3737_ = lean_ctor_get(v_l_3706_, 0);
lean_inc(v_size_3737_);
v___y_3729_ = v_size_3737_;
goto v___jp_3728_;
}
else
{
lean_object* v___x_3738_; 
v___x_3738_ = lean_unsigned_to_nat(0u);
v___y_3729_ = v___x_3738_;
goto v___jp_3728_;
}
v___jp_3717_:
{
lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3721_ = lean_nat_add(v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec(v___y_3719_);
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 4, v_r_3691_);
lean_ctor_set(v___x_3713_, 3, v_r_3707_);
lean_ctor_set(v___x_3713_, 2, v_v_3689_);
lean_ctor_set(v___x_3713_, 1, v_k_3688_);
lean_ctor_set(v___x_3713_, 0, v___x_3721_);
v___x_3723_ = v___x_3713_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_k_3688_);
lean_ctor_set(v_reuseFailAlloc_3727_, 2, v_v_3689_);
lean_ctor_set(v_reuseFailAlloc_3727_, 3, v_r_3707_);
lean_ctor_set(v_reuseFailAlloc_3727_, 4, v_r_3691_);
v___x_3723_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3725_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 4, v___x_3723_);
lean_ctor_set(v___x_3701_, 3, v___y_3718_);
lean_ctor_set(v___x_3701_, 2, v_v_3705_);
lean_ctor_set(v___x_3701_, 1, v_k_3704_);
lean_ctor_set(v___x_3701_, 0, v___x_3716_);
v___x_3725_ = v___x_3701_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3716_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_k_3704_);
lean_ctor_set(v_reuseFailAlloc_3726_, 2, v_v_3705_);
lean_ctor_set(v_reuseFailAlloc_3726_, 3, v___y_3718_);
lean_ctor_set(v_reuseFailAlloc_3726_, 4, v___x_3723_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
v___jp_3728_:
{
lean_object* v___x_3730_; lean_object* v___x_3732_; 
v___x_3730_ = lean_nat_add(v___x_3715_, v___y_3729_);
lean_dec(v___y_3729_);
lean_dec(v___x_3715_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 4, v_l_3706_);
lean_ctor_set(v___x_3541_, 0, v___x_3730_);
v___x_3732_ = v___x_3541_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3730_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v_k_3536_);
lean_ctor_set(v_reuseFailAlloc_3736_, 2, v_v_3537_);
lean_ctor_set(v_reuseFailAlloc_3736_, 3, v_l_3538_);
lean_ctor_set(v_reuseFailAlloc_3736_, 4, v_l_3706_);
v___x_3732_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
lean_object* v___x_3733_; 
v___x_3733_ = lean_nat_add(v___x_3685_, v_size_3708_);
if (lean_obj_tag(v_r_3707_) == 0)
{
lean_object* v_size_3734_; 
v_size_3734_ = lean_ctor_get(v_r_3707_, 0);
lean_inc(v_size_3734_);
v___y_3718_ = v___x_3732_;
v___y_3719_ = v___x_3733_;
v___y_3720_ = v_size_3734_;
goto v___jp_3717_;
}
else
{
lean_object* v___x_3735_; 
v___x_3735_ = lean_unsigned_to_nat(0u);
v___y_3718_ = v___x_3732_;
v___y_3719_ = v___x_3733_;
v___y_3720_ = v___x_3735_;
goto v___jp_3717_;
}
}
}
}
}
else
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3749_; 
lean_del_object(v___x_3541_);
v___x_3745_ = lean_nat_add(v___x_3685_, v_size_3686_);
v___x_3746_ = lean_nat_add(v___x_3745_, v_size_3687_);
lean_dec(v_size_3687_);
v___x_3747_ = lean_nat_add(v___x_3745_, v_size_3703_);
lean_dec(v___x_3745_);
lean_inc_ref(v_l_3538_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 4, v_l_3690_);
lean_ctor_set(v___x_3701_, 3, v_l_3538_);
lean_ctor_set(v___x_3701_, 2, v_v_3537_);
lean_ctor_set(v___x_3701_, 1, v_k_3536_);
lean_ctor_set(v___x_3701_, 0, v___x_3747_);
v___x_3749_ = v___x_3701_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3747_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_k_3536_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_v_3537_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_l_3538_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v_l_3690_);
v___x_3749_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
v_isSharedCheck_3756_ = !lean_is_exclusive(v_l_3538_);
if (v_isSharedCheck_3756_ == 0)
{
lean_object* v_unused_3757_; lean_object* v_unused_3758_; lean_object* v_unused_3759_; lean_object* v_unused_3760_; lean_object* v_unused_3761_; 
v_unused_3757_ = lean_ctor_get(v_l_3538_, 4);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_l_3538_, 3);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_l_3538_, 2);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_l_3538_, 1);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_l_3538_, 0);
lean_dec(v_unused_3761_);
v___x_3751_ = v_l_3538_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_dec(v_l_3538_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 4, v_r_3691_);
lean_ctor_set(v___x_3751_, 3, v___x_3749_);
lean_ctor_set(v___x_3751_, 2, v_v_3689_);
lean_ctor_set(v___x_3751_, 1, v_k_3688_);
lean_ctor_set(v___x_3751_, 0, v___x_3746_);
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3746_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_k_3688_);
lean_ctor_set(v_reuseFailAlloc_3755_, 2, v_v_3689_);
lean_ctor_set(v_reuseFailAlloc_3755_, 3, v___x_3749_);
lean_ctor_set(v_reuseFailAlloc_3755_, 4, v_r_3691_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3769_; 
v_l_3769_ = lean_ctor_get(v_impl_3684_, 3);
lean_inc(v_l_3769_);
if (lean_obj_tag(v_l_3769_) == 0)
{
lean_object* v_r_3770_; lean_object* v_k_3771_; lean_object* v_v_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3795_; 
v_r_3770_ = lean_ctor_get(v_impl_3684_, 4);
v_k_3771_ = lean_ctor_get(v_impl_3684_, 1);
v_v_3772_ = lean_ctor_get(v_impl_3684_, 2);
v_isSharedCheck_3795_ = !lean_is_exclusive(v_impl_3684_);
if (v_isSharedCheck_3795_ == 0)
{
lean_object* v_unused_3796_; lean_object* v_unused_3797_; 
v_unused_3796_ = lean_ctor_get(v_impl_3684_, 3);
lean_dec(v_unused_3796_);
v_unused_3797_ = lean_ctor_get(v_impl_3684_, 0);
lean_dec(v_unused_3797_);
v___x_3774_ = v_impl_3684_;
v_isShared_3775_ = v_isSharedCheck_3795_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_r_3770_);
lean_inc(v_v_3772_);
lean_inc(v_k_3771_);
lean_dec(v_impl_3684_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3795_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v_k_3776_; lean_object* v_v_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3791_; 
v_k_3776_ = lean_ctor_get(v_l_3769_, 1);
v_v_3777_ = lean_ctor_get(v_l_3769_, 2);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_l_3769_);
if (v_isSharedCheck_3791_ == 0)
{
lean_object* v_unused_3792_; lean_object* v_unused_3793_; lean_object* v_unused_3794_; 
v_unused_3792_ = lean_ctor_get(v_l_3769_, 4);
lean_dec(v_unused_3792_);
v_unused_3793_ = lean_ctor_get(v_l_3769_, 3);
lean_dec(v_unused_3793_);
v_unused_3794_ = lean_ctor_get(v_l_3769_, 0);
lean_dec(v_unused_3794_);
v___x_3779_ = v_l_3769_;
v_isShared_3780_ = v_isSharedCheck_3791_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_v_3777_);
lean_inc(v_k_3776_);
lean_dec(v_l_3769_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3791_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3781_; lean_object* v___x_3783_; 
v___x_3781_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3770_, 2);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 4, v_r_3770_);
lean_ctor_set(v___x_3779_, 3, v_r_3770_);
lean_ctor_set(v___x_3779_, 2, v_v_3537_);
lean_ctor_set(v___x_3779_, 1, v_k_3536_);
lean_ctor_set(v___x_3779_, 0, v___x_3685_);
v___x_3783_ = v___x_3779_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3685_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_k_3536_);
lean_ctor_set(v_reuseFailAlloc_3790_, 2, v_v_3537_);
lean_ctor_set(v_reuseFailAlloc_3790_, 3, v_r_3770_);
lean_ctor_set(v_reuseFailAlloc_3790_, 4, v_r_3770_);
v___x_3783_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
lean_object* v___x_3785_; 
lean_inc(v_r_3770_);
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 3, v_r_3770_);
lean_ctor_set(v___x_3774_, 0, v___x_3685_);
v___x_3785_ = v___x_3774_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3685_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_k_3771_);
lean_ctor_set(v_reuseFailAlloc_3789_, 2, v_v_3772_);
lean_ctor_set(v_reuseFailAlloc_3789_, 3, v_r_3770_);
lean_ctor_set(v_reuseFailAlloc_3789_, 4, v_r_3770_);
v___x_3785_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
lean_object* v___x_3787_; 
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 4, v___x_3785_);
lean_ctor_set(v___x_3541_, 3, v___x_3783_);
lean_ctor_set(v___x_3541_, 2, v_v_3777_);
lean_ctor_set(v___x_3541_, 1, v_k_3776_);
lean_ctor_set(v___x_3541_, 0, v___x_3781_);
v___x_3787_ = v___x_3541_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3781_);
lean_ctor_set(v_reuseFailAlloc_3788_, 1, v_k_3776_);
lean_ctor_set(v_reuseFailAlloc_3788_, 2, v_v_3777_);
lean_ctor_set(v_reuseFailAlloc_3788_, 3, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3788_, 4, v___x_3785_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
}
}
else
{
lean_object* v_r_3798_; 
v_r_3798_ = lean_ctor_get(v_impl_3684_, 4);
lean_inc(v_r_3798_);
if (lean_obj_tag(v_r_3798_) == 0)
{
lean_object* v_k_3799_; lean_object* v_v_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3811_; 
v_k_3799_ = lean_ctor_get(v_impl_3684_, 1);
v_v_3800_ = lean_ctor_get(v_impl_3684_, 2);
v_isSharedCheck_3811_ = !lean_is_exclusive(v_impl_3684_);
if (v_isSharedCheck_3811_ == 0)
{
lean_object* v_unused_3812_; lean_object* v_unused_3813_; lean_object* v_unused_3814_; 
v_unused_3812_ = lean_ctor_get(v_impl_3684_, 4);
lean_dec(v_unused_3812_);
v_unused_3813_ = lean_ctor_get(v_impl_3684_, 3);
lean_dec(v_unused_3813_);
v_unused_3814_ = lean_ctor_get(v_impl_3684_, 0);
lean_dec(v_unused_3814_);
v___x_3802_ = v_impl_3684_;
v_isShared_3803_ = v_isSharedCheck_3811_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_v_3800_);
lean_inc(v_k_3799_);
lean_dec(v_impl_3684_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3811_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3804_; lean_object* v___x_3806_; 
v___x_3804_ = lean_unsigned_to_nat(3u);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 4, v_l_3769_);
lean_ctor_set(v___x_3802_, 2, v_v_3537_);
lean_ctor_set(v___x_3802_, 1, v_k_3536_);
lean_ctor_set(v___x_3802_, 0, v___x_3685_);
v___x_3806_ = v___x_3802_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3685_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v_k_3536_);
lean_ctor_set(v_reuseFailAlloc_3810_, 2, v_v_3537_);
lean_ctor_set(v_reuseFailAlloc_3810_, 3, v_l_3769_);
lean_ctor_set(v_reuseFailAlloc_3810_, 4, v_l_3769_);
v___x_3806_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
lean_object* v___x_3808_; 
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 4, v_r_3798_);
lean_ctor_set(v___x_3541_, 3, v___x_3806_);
lean_ctor_set(v___x_3541_, 2, v_v_3800_);
lean_ctor_set(v___x_3541_, 1, v_k_3799_);
lean_ctor_set(v___x_3541_, 0, v___x_3804_);
v___x_3808_ = v___x_3541_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3804_);
lean_ctor_set(v_reuseFailAlloc_3809_, 1, v_k_3799_);
lean_ctor_set(v_reuseFailAlloc_3809_, 2, v_v_3800_);
lean_ctor_set(v_reuseFailAlloc_3809_, 3, v___x_3806_);
lean_ctor_set(v_reuseFailAlloc_3809_, 4, v_r_3798_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
else
{
lean_object* v___x_3815_; lean_object* v___x_3817_; 
v___x_3815_ = lean_unsigned_to_nat(2u);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 4, v_impl_3684_);
lean_ctor_set(v___x_3541_, 3, v_r_3798_);
lean_ctor_set(v___x_3541_, 0, v___x_3815_);
v___x_3817_ = v___x_3541_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3815_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_k_3536_);
lean_ctor_set(v_reuseFailAlloc_3818_, 2, v_v_3537_);
lean_ctor_set(v_reuseFailAlloc_3818_, 3, v_r_3798_);
lean_ctor_set(v_reuseFailAlloc_3818_, 4, v_impl_3684_);
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
}
}
}
}
else
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = lean_unsigned_to_nat(1u);
v___x_3821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
lean_ctor_set(v___x_3821_, 1, v_k_3532_);
lean_ctor_set(v___x_3821_, 2, v_v_3533_);
lean_ctor_set(v___x_3821_, 3, v_t_3534_);
lean_ctor_set(v___x_3821_, 4, v_t_3534_);
return v___x_3821_;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3822_ = lean_box(1);
v___x_3823_ = l_Lake_LeanLib_defaultFacetConfig;
v___x_3824_ = l_Lake_LeanLib_defaultFacet;
v___x_3825_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3824_, v___x_3823_, v___x_3822_);
return v___x_3825_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3826_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__0, &l_Lake_LeanLib_initFacetConfigs___closed__0_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__0);
v___x_3827_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig));
v___x_3828_ = l_Lake_LeanLib_modulesFacet;
v___x_3829_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3828_, v___x_3827_, v___x_3826_);
return v___x_3829_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3830_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__1, &l_Lake_LeanLib_initFacetConfigs___closed__1_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__1);
v___x_3831_ = l_Lake_LeanLib_leanArtsFacetConfig;
v___x_3832_ = l_Lake_LeanLib_leanArtsFacet;
v___x_3833_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3832_, v___x_3831_, v___x_3830_);
return v___x_3833_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3834_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__2, &l_Lake_LeanLib_initFacetConfigs___closed__2_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__2);
v___x_3835_ = l_Lake_LeanLib_staticFacetConfig;
v___x_3836_ = l_Lake_LeanLib_staticFacet;
v___x_3837_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3836_, v___x_3835_, v___x_3834_);
return v___x_3837_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3838_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__3, &l_Lake_LeanLib_initFacetConfigs___closed__3_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__3);
v___x_3839_ = l_Lake_LeanLib_staticExportFacetConfig;
v___x_3840_ = l_Lake_LeanLib_staticExportFacet;
v___x_3841_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3840_, v___x_3839_, v___x_3838_);
return v___x_3841_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3842_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__4, &l_Lake_LeanLib_initFacetConfigs___closed__4_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__4);
v___x_3843_ = l_Lake_LeanLib_sharedFacetConfig;
v___x_3844_ = l_Lake_LeanLib_sharedFacet;
v___x_3845_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3844_, v___x_3843_, v___x_3842_);
return v___x_3845_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3846_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__5, &l_Lake_LeanLib_initFacetConfigs___closed__5_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__5);
v___x_3847_ = l_Lake_LeanLib_extraDepFacetConfig;
v___x_3848_ = l_Lake_LeanLib_extraDepFacet;
v___x_3849_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3848_, v___x_3847_, v___x_3846_);
return v___x_3849_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__6, &l_Lake_LeanLib_initFacetConfigs___closed__6_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__6);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3851_, lean_object* v_k_3852_, lean_object* v_v_3853_, lean_object* v_t_3854_, lean_object* v_hl_3855_){
_start:
{
lean_object* v___x_3856_; 
v___x_3856_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3852_, v_v_3853_, v_t_3854_);
return v___x_3856_;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs(void){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l_Lake_LeanLib_initFacetConfigs;
return v___x_3857_;
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
