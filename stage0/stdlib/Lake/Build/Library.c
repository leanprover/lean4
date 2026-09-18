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
lean_object* l_Lake_Verbosity_ctorIdx(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_dynlibFacet;
extern lean_object* l_Lake_ExternLib_keyword;
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_Lake_Job_waitUnlessCanceled_x3f___redArg(lean_object*, lean_object*);
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
lean_object* l_Lake_EquipT_instMonad___redArg(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__0_value;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1;
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
static const lean_string_object l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = ": some modules have bad imports or could not be read"};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_nbuckets_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_59_ = lean_array_get_size(v_data_58_);
v___x_60_ = lean_unsigned_to_nat(2u);
v_nbuckets_61_ = lean_nat_mul(v___x_59_, v___x_60_);
v___x_62_ = lean_unsigned_to_nat(0u);
v___x_63_ = lean_box(0);
v___x_64_ = lean_mk_array(v_nbuckets_61_, v___x_63_);
v___x_65_ = lean_array_propagate_mark(v_data_58_, v___x_64_);
v___x_66_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(v___x_62_, v_data_58_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(lean_object* v_m_67_, lean_object* v_a_68_, lean_object* v_b_69_){
_start:
{
lean_object* v_size_70_; lean_object* v_buckets_71_; lean_object* v_name_72_; lean_object* v___x_73_; uint64_t v___y_75_; 
v_size_70_ = lean_ctor_get(v_m_67_, 0);
v_buckets_71_ = lean_ctor_get(v_m_67_, 1);
v_name_72_ = lean_ctor_get(v_a_68_, 1);
v___x_73_ = lean_array_get_size(v_buckets_71_);
if (lean_obj_tag(v_name_72_) == 0)
{
uint64_t v___x_112_; 
v___x_112_ = 1723ULL;
v___y_75_ = v___x_112_;
goto v___jp_74_;
}
else
{
uint64_t v_hash_113_; 
v_hash_113_ = lean_ctor_get_uint64(v_name_72_, sizeof(void*)*2);
v___y_75_ = v_hash_113_;
goto v___jp_74_;
}
v___jp_74_:
{
uint64_t v___x_76_; uint64_t v___x_77_; uint64_t v_fold_78_; uint64_t v___x_79_; uint64_t v___x_80_; uint64_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; size_t v___x_86_; lean_object* v_bkt_87_; uint8_t v___x_88_; 
v___x_76_ = 32ULL;
v___x_77_ = lean_uint64_shift_right(v___y_75_, v___x_76_);
v_fold_78_ = lean_uint64_xor(v___y_75_, v___x_77_);
v___x_79_ = 16ULL;
v___x_80_ = lean_uint64_shift_right(v_fold_78_, v___x_79_);
v___x_81_ = lean_uint64_xor(v_fold_78_, v___x_80_);
v___x_82_ = lean_uint64_to_usize(v___x_81_);
v___x_83_ = lean_usize_of_nat(v___x_73_);
v___x_84_ = ((size_t)1ULL);
v___x_85_ = lean_usize_sub(v___x_83_, v___x_84_);
v___x_86_ = lean_usize_land(v___x_82_, v___x_85_);
v_bkt_87_ = lean_array_uget_borrowed(v_buckets_71_, v___x_86_);
v___x_88_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_68_, v_bkt_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_109_; 
lean_inc_ref(v_buckets_71_);
lean_inc(v_size_70_);
v_isSharedCheck_109_ = !lean_is_exclusive(v_m_67_);
if (v_isSharedCheck_109_ == 0)
{
lean_object* v_unused_110_; lean_object* v_unused_111_; 
v_unused_110_ = lean_ctor_get(v_m_67_, 1);
lean_dec(v_unused_110_);
v_unused_111_ = lean_ctor_get(v_m_67_, 0);
lean_dec(v_unused_111_);
v___x_90_ = v_m_67_;
v_isShared_91_ = v_isSharedCheck_109_;
goto v_resetjp_89_;
}
else
{
lean_dec(v_m_67_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_109_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v_size_x27_93_; lean_object* v___x_94_; lean_object* v_buckets_x27_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_92_ = lean_unsigned_to_nat(1u);
v_size_x27_93_ = lean_nat_add(v_size_70_, v___x_92_);
lean_dec(v_size_70_);
lean_inc(v_bkt_87_);
v___x_94_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_94_, 0, v_a_68_);
lean_ctor_set(v___x_94_, 1, v_b_69_);
lean_ctor_set(v___x_94_, 2, v_bkt_87_);
v_buckets_x27_95_ = lean_array_uset(v_buckets_71_, v___x_86_, v___x_94_);
v___x_96_ = lean_unsigned_to_nat(4u);
v___x_97_ = lean_nat_mul(v_size_x27_93_, v___x_96_);
v___x_98_ = lean_unsigned_to_nat(3u);
v___x_99_ = lean_nat_div(v___x_97_, v___x_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_array_get_size(v_buckets_x27_95_);
v___x_101_ = lean_nat_dec_le(v___x_99_, v___x_100_);
lean_dec(v___x_99_);
if (v___x_101_ == 0)
{
lean_object* v_val_102_; lean_object* v___x_104_; 
v_val_102_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(v_buckets_x27_95_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v_val_102_);
lean_ctor_set(v___x_90_, 0, v_size_x27_93_);
v___x_104_ = v___x_90_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_size_x27_93_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_val_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
else
{
lean_object* v___x_107_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v_buckets_x27_95_);
lean_ctor_set(v___x_90_, 0, v_size_x27_93_);
v___x_107_ = v___x_90_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_size_x27_93_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_buckets_x27_95_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
else
{
lean_dec(v_b_69_);
lean_dec_ref(v_a_68_);
return v_m_67_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(lean_object* v_m_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_buckets_116_; lean_object* v_name_117_; lean_object* v___x_118_; uint64_t v___y_120_; 
v_buckets_116_ = lean_ctor_get(v_m_114_, 1);
v_name_117_ = lean_ctor_get(v_a_115_, 1);
v___x_118_ = lean_array_get_size(v_buckets_116_);
if (lean_obj_tag(v_name_117_) == 0)
{
uint64_t v___x_134_; 
v___x_134_ = 1723ULL;
v___y_120_ = v___x_134_;
goto v___jp_119_;
}
else
{
uint64_t v_hash_135_; 
v_hash_135_ = lean_ctor_get_uint64(v_name_117_, sizeof(void*)*2);
v___y_120_ = v_hash_135_;
goto v___jp_119_;
}
v___jp_119_:
{
uint64_t v___x_121_; uint64_t v___x_122_; uint64_t v_fold_123_; uint64_t v___x_124_; uint64_t v___x_125_; uint64_t v___x_126_; size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_121_ = 32ULL;
v___x_122_ = lean_uint64_shift_right(v___y_120_, v___x_121_);
v_fold_123_ = lean_uint64_xor(v___y_120_, v___x_122_);
v___x_124_ = 16ULL;
v___x_125_ = lean_uint64_shift_right(v_fold_123_, v___x_124_);
v___x_126_ = lean_uint64_xor(v_fold_123_, v___x_125_);
v___x_127_ = lean_uint64_to_usize(v___x_126_);
v___x_128_ = lean_usize_of_nat(v___x_118_);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_sub(v___x_128_, v___x_129_);
v___x_131_ = lean_usize_land(v___x_127_, v___x_130_);
v___x_132_ = lean_array_uget_borrowed(v_buckets_116_, v___x_131_);
v___x_133_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_115_, v___x_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg___boxed(lean_object* v_m_136_, lean_object* v_a_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_136_, v_a_137_);
lean_dec_ref(v_a_137_);
lean_dec_ref(v_m_136_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__0));
v___x_142_ = l_Lake_BuildTrace_nil(v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(lean_object* v_self_143_, lean_object* v_root_144_, lean_object* v_col_145_, uint8_t v_viaImport_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_col_155_; lean_object* v___y_156_; lean_object* v_mods_158_; lean_object* v_modSet_159_; uint8_t v_hasErrors_160_; uint8_t v___x_161_; 
v_mods_158_ = lean_ctor_get(v_col_145_, 0);
v_modSet_159_ = lean_ctor_get(v_col_145_, 1);
v_hasErrors_160_ = lean_ctor_get_uint8(v_col_145_, sizeof(void*)*2);
v___x_161_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_modSet_159_, v_root_144_);
if (v___x_161_ == 0)
{
lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_238_; 
lean_inc_ref(v_modSet_159_);
lean_inc_ref(v_mods_158_);
v_isSharedCheck_238_ = !lean_is_exclusive(v_col_145_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; lean_object* v_unused_240_; 
v_unused_239_ = lean_ctor_get(v_col_145_, 1);
lean_dec(v_unused_239_);
v_unused_240_ = lean_ctor_get(v_col_145_, 0);
lean_dec(v_unused_240_);
v___x_163_ = v_col_145_;
v_isShared_164_ = v_isSharedCheck_238_;
goto v_resetjp_162_;
}
else
{
lean_dec(v_col_145_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_238_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v_lib_165_; lean_object* v_pkg_166_; lean_object* v_name_167_; lean_object* v_keyName_168_; uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_col_173_; 
v_lib_165_ = lean_ctor_get(v_root_144_, 0);
v_pkg_166_ = lean_ctor_get(v_lib_165_, 0);
v_name_167_ = lean_ctor_get(v_root_144_, 1);
v_keyName_168_ = lean_ctor_get(v_pkg_166_, 2);
v___x_169_ = 1;
v___x_170_ = lean_box(0);
lean_inc_ref(v_root_144_);
v___x_171_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_modSet_159_, v_root_144_, v___x_170_);
lean_inc_ref(v___x_171_);
lean_inc_ref(v_mods_158_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 1, v___x_171_);
v_col_173_ = v___x_163_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_mods_158_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v___x_171_);
lean_ctor_set_uint8(v_reuseFailAlloc_237_, sizeof(void*)*2, v_hasErrors_160_);
v_col_173_ = v_reuseFailAlloc_237_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_174_ = l_Lake_Module_importsFacet;
lean_inc(v_name_167_);
lean_inc(v_keyName_168_);
v___x_175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_175_, 0, v_keyName_168_);
lean_ctor_set(v___x_175_, 1, v_name_167_);
v___x_176_ = l_Lake_Module_keyword;
lean_inc_ref(v_root_144_);
v___x_177_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_177_, 0, v___x_175_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
lean_ctor_set(v___x_177_, 2, v_root_144_);
lean_ctor_set(v___x_177_, 3, v___x_174_);
lean_inc_ref(v_a_147_);
lean_inc_ref(v_a_151_);
lean_inc(v_a_150_);
lean_inc(v_a_149_);
lean_inc(v_a_148_);
v___x_178_ = lean_apply_7(v_a_147_, v___x_177_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, lean_box(0));
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v_a_180_; uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
v_a_180_ = lean_ctor_get(v___x_178_, 1);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_178_, 2);
v___x_181_ = 0;
v___x_182_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_184_, 0, v_a_180_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___x_183_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*3, v___x_181_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*3 + 1, v___x_161_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*3 + 2, v___x_161_);
v___x_185_ = l_Lake_Job_waitUnlessCanceled_x3f___redArg(v_a_179_, v___x_184_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_217_; 
v_a_186_ = lean_ctor_get(v___x_185_, 1);
v_a_187_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_217_ == 0)
{
v___x_189_ = v___x_185_;
v_isShared_190_ = v_isSharedCheck_217_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_186_);
lean_inc(v_a_187_);
lean_dec(v___x_185_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_217_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_log_191_; lean_object* v___y_193_; 
v_log_191_ = lean_ctor_get(v_a_186_, 0);
lean_inc_ref(v_log_191_);
lean_dec(v_a_186_);
if (lean_obj_tag(v_a_187_) == 1)
{
lean_object* v_val_197_; size_t v_sz_198_; size_t v___x_199_; lean_object* v___x_200_; 
lean_del_object(v___x_189_);
lean_dec_ref(v___x_171_);
lean_dec_ref(v_mods_158_);
v_val_197_ = lean_ctor_get(v_a_187_, 0);
lean_inc(v_val_197_);
lean_dec_ref_known(v_a_187_, 1);
v_sz_198_ = lean_array_size(v_val_197_);
v___x_199_ = ((size_t)0ULL);
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_143_, v_val_197_, v_sz_198_, v___x_199_, v_col_173_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_log_191_);
lean_dec(v_val_197_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v_a_202_; lean_object* v_mods_203_; lean_object* v_modSet_204_; uint8_t v_hasErrors_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_213_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
v_a_202_ = lean_ctor_get(v___x_200_, 1);
lean_inc(v_a_202_);
lean_dec_ref_known(v___x_200_, 2);
v_mods_203_ = lean_ctor_get(v_a_201_, 0);
v_modSet_204_ = lean_ctor_get(v_a_201_, 1);
v_hasErrors_205_ = lean_ctor_get_uint8(v_a_201_, sizeof(void*)*2);
v_isSharedCheck_213_ = !lean_is_exclusive(v_a_201_);
if (v_isSharedCheck_213_ == 0)
{
v___x_207_ = v_a_201_;
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_modSet_204_);
lean_inc(v_mods_203_);
lean_dec(v_a_201_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = lean_array_push(v_mods_203_, v_root_144_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_209_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_modSet_204_);
lean_ctor_set_uint8(v_reuseFailAlloc_212_, sizeof(void*)*2, v_hasErrors_205_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
v_col_155_ = v___x_211_;
v___y_156_ = v_a_202_;
goto v___jp_154_;
}
}
}
else
{
lean_dec_ref(v_root_144_);
return v___x_200_;
}
}
else
{
lean_dec(v_a_187_);
lean_dec_ref(v_col_173_);
lean_dec_ref(v_a_147_);
if (v_viaImport_146_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_array_push(v_mods_158_, v_root_144_);
v___x_215_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_171_);
lean_ctor_set_uint8(v___x_215_, sizeof(void*)*2, v___x_169_);
v___y_193_ = v___x_215_;
goto v___jp_192_;
}
else
{
lean_object* v___x_216_; 
lean_dec_ref(v_root_144_);
v___x_216_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_216_, 0, v_mods_158_);
lean_ctor_set(v___x_216_, 1, v___x_171_);
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*2, v___x_169_);
v___y_193_ = v___x_216_;
goto v___jp_192_;
}
}
v___jp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 1, v_log_191_);
lean_ctor_set(v___x_189_, 0, v___y_193_);
v___x_195_ = v___x_189_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___y_193_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_log_191_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
else
{
lean_object* v_a_218_; lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_227_; 
lean_dec_ref(v_col_173_);
lean_dec_ref(v___x_171_);
lean_dec_ref(v_mods_158_);
lean_dec_ref(v_a_147_);
lean_dec_ref(v_root_144_);
v_a_218_ = lean_ctor_get(v___x_185_, 1);
v_a_219_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_227_ == 0)
{
v___x_221_ = v___x_185_;
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_218_);
lean_inc(v_a_219_);
lean_dec(v___x_185_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_227_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v_log_223_; lean_object* v___x_225_; 
v_log_223_ = lean_ctor_get(v_a_218_, 0);
lean_inc_ref(v_log_223_);
lean_dec(v_a_218_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 1, v_log_223_);
v___x_225_ = v___x_221_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_219_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v_log_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_object* v_a_228_; lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_236_; 
lean_dec_ref(v_col_173_);
lean_dec_ref(v___x_171_);
lean_dec_ref(v_mods_158_);
lean_dec_ref(v_a_147_);
lean_dec_ref(v_root_144_);
v_a_228_ = lean_ctor_get(v___x_178_, 0);
v_a_229_ = lean_ctor_get(v___x_178_, 1);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_236_ == 0)
{
v___x_231_ = v___x_178_;
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_inc(v_a_228_);
lean_dec(v___x_178_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_236_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
if (v_isShared_232_ == 0)
{
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_a_228_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_a_229_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_a_147_);
lean_dec_ref(v_root_144_);
v_col_155_ = v_col_145_;
v___y_156_ = v_a_152_;
goto v___jp_154_;
}
v___jp_154_:
{
lean_object* v___x_157_; 
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v_col_155_);
lean_ctor_set(v___x_157_, 1, v___y_156_);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(lean_object* v_self_241_, lean_object* v_as_242_, size_t v_sz_243_, size_t v_i_244_, lean_object* v_b_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_a_254_; lean_object* v_a_255_; uint8_t v___x_259_; 
v___x_259_ = lean_usize_dec_lt(v_i_244_, v_sz_243_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; 
lean_dec_ref(v___y_246_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v_b_245_);
lean_ctor_set(v___x_260_, 1, v___y_251_);
return v___x_260_;
}
else
{
lean_object* v_a_261_; lean_object* v_lib_262_; lean_object* v_name_263_; lean_object* v_name_264_; uint8_t v___x_265_; 
v_a_261_ = lean_array_uget_borrowed(v_as_242_, v_i_244_);
v_lib_262_ = lean_ctor_get(v_a_261_, 0);
v_name_263_ = lean_ctor_get(v_lib_262_, 1);
v_name_264_ = lean_ctor_get(v_self_241_, 1);
v___x_265_ = lean_name_eq(v_name_263_, v_name_264_);
if (v___x_265_ == 0)
{
v_a_254_ = v_b_245_;
v_a_255_ = v___y_251_;
goto v___jp_253_;
}
else
{
lean_object* v___x_266_; 
lean_inc_ref(v___y_246_);
lean_inc(v_a_261_);
v___x_266_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_241_, v_a_261_, v_b_245_, v___x_265_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v_a_268_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
v_a_268_ = lean_ctor_get(v___x_266_, 1);
lean_inc(v_a_268_);
lean_dec_ref_known(v___x_266_, 2);
v_a_254_ = v_a_267_;
v_a_255_ = v_a_268_;
goto v___jp_253_;
}
else
{
lean_dec_ref(v___y_246_);
return v___x_266_;
}
}
}
v___jp_253_:
{
size_t v___x_256_; size_t v___x_257_; 
v___x_256_ = ((size_t)1ULL);
v___x_257_ = lean_usize_add(v_i_244_, v___x_256_);
v_i_244_ = v___x_257_;
v_b_245_ = v_a_254_;
v___y_251_ = v_a_255_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(lean_object* v_self_269_, lean_object* v_as_270_, lean_object* v_sz_271_, lean_object* v_i_272_, lean_object* v_b_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
size_t v_sz_boxed_281_; size_t v_i_boxed_282_; lean_object* v_res_283_; 
v_sz_boxed_281_ = lean_unbox_usize(v_sz_271_);
lean_dec(v_sz_271_);
v_i_boxed_282_ = lean_unbox_usize(v_i_272_);
lean_dec(v_i_272_);
v_res_283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_269_, v_as_270_, v_sz_boxed_281_, v_i_boxed_282_, v_b_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v_as_270_);
lean_dec_ref(v_self_269_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object* v_self_284_, lean_object* v_root_285_, lean_object* v_col_286_, lean_object* v_viaImport_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
uint8_t v_viaImport_boxed_295_; lean_object* v_res_296_; 
v_viaImport_boxed_295_ = lean_unbox(v_viaImport_287_);
v_res_296_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_284_, v_root_285_, v_col_286_, v_viaImport_boxed_295_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_self_284_);
return v_res_296_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_object* v_00_u03b2_297_, lean_object* v_m_298_, lean_object* v_a_299_){
_start:
{
uint8_t v___x_300_; 
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_298_, v_a_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(lean_object* v_00_u03b2_301_, lean_object* v_m_302_, lean_object* v_a_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(v_00_u03b2_301_, v_m_302_, v_a_303_);
lean_dec_ref(v_a_303_);
lean_dec_ref(v_m_302_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1(lean_object* v_00_u03b2_306_, lean_object* v_m_307_, lean_object* v_a_308_, lean_object* v_b_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_m_307_, v_a_308_, v_b_309_);
return v___x_310_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(lean_object* v_00_u03b2_311_, lean_object* v_a_312_, lean_object* v_x_313_){
_start:
{
uint8_t v___x_314_; 
v___x_314_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_312_, v_x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_315_, lean_object* v_a_316_, lean_object* v_x_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(v_00_u03b2_315_, v_a_316_, v_x_317_);
lean_dec(v_x_317_);
lean_dec_ref(v_a_316_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2(lean_object* v_00_u03b2_320_, lean_object* v_data_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(v_data_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_323_, lean_object* v_i_324_, lean_object* v_source_325_, lean_object* v_target_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(v_i_324_, v_source_325_, v_target_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_328_, lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(v_x_329_, v_x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(lean_object* v_self_332_, lean_object* v_as_333_, size_t v_sz_334_, size_t v_i_335_, lean_object* v_b_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
uint8_t v___x_344_; 
v___x_344_ = lean_usize_dec_lt(v_i_335_, v_sz_334_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
lean_dec_ref(v___y_337_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v_b_336_);
lean_ctor_set(v___x_345_, 1, v___y_342_);
return v___x_345_;
}
else
{
uint8_t v___x_346_; lean_object* v_a_347_; lean_object* v___x_348_; 
v___x_346_ = 0;
v_a_347_ = lean_array_uget_borrowed(v_as_333_, v_i_335_);
lean_inc_ref(v___y_337_);
lean_inc(v_a_347_);
v___x_348_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_332_, v_a_347_, v_b_336_, v___x_346_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v_a_350_; size_t v___x_351_; size_t v___x_352_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
v_a_350_ = lean_ctor_get(v___x_348_, 1);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_348_, 2);
v___x_351_ = ((size_t)1ULL);
v___x_352_ = lean_usize_add(v_i_335_, v___x_351_);
v_i_335_ = v___x_352_;
v_b_336_ = v_a_349_;
v___y_342_ = v_a_350_;
goto _start;
}
else
{
lean_dec_ref(v___y_337_);
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0___boxed(lean_object* v_self_354_, lean_object* v_as_355_, lean_object* v_sz_356_, lean_object* v_i_357_, lean_object* v_b_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
size_t v_sz_boxed_366_; size_t v_i_boxed_367_; lean_object* v_res_368_; 
v_sz_boxed_366_ = lean_unbox_usize(v_sz_356_);
lean_dec(v_sz_356_);
v_i_boxed_367_ = lean_unbox_usize(v_i_357_);
lean_dec(v_i_357_);
v_res_368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_354_, v_as_355_, v_sz_boxed_366_, v_i_boxed_367_, v_b_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v_as_355_);
lean_dec_ref(v_self_354_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(lean_object* v_self_371_, lean_object* v_col_372_, lean_object* v___x_373_, uint8_t v___x_374_, lean_object* v___x_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___x_383_; 
lean_inc_ref(v_self_371_);
v___x_383_ = l_Lake_LeanLib_getModuleArray(v_self_371_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; size_t v_sz_385_; size_t v___x_386_; lean_object* v___x_387_; 
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v___x_383_, 1);
v_sz_385_ = lean_array_size(v_a_384_);
v___x_386_ = ((size_t)0ULL);
v___x_387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_371_, v_a_384_, v_sz_385_, v___x_386_, v_col_372_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v_a_384_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_415_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
v_a_389_ = lean_ctor_get(v___x_387_, 1);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_415_ == 0)
{
v___x_391_ = v___x_387_;
v_isShared_392_ = v_isSharedCheck_415_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_inc(v_a_388_);
lean_dec(v___x_387_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_415_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v_mods_393_; uint8_t v_hasErrors_394_; lean_object* v___y_396_; 
v_mods_393_ = lean_ctor_get(v_a_388_, 0);
lean_inc_ref(v_mods_393_);
v_hasErrors_394_ = lean_ctor_get_uint8(v_a_388_, sizeof(void*)*2);
lean_dec(v_a_388_);
if (v_hasErrors_394_ == 0)
{
lean_dec_ref(v_self_371_);
v___y_396_ = v_a_389_;
goto v___jp_395_;
}
else
{
lean_object* v_name_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_name_408_ = lean_ctor_get(v_self_371_, 1);
lean_inc(v_name_408_);
lean_dec_ref(v_self_371_);
v___x_409_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_408_, v_hasErrors_394_);
v___x_410_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1));
v___x_411_ = lean_string_append(v___x_409_, v___x_410_);
v___x_412_ = 3;
v___x_413_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_413_, 0, v___x_411_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*1, v___x_412_);
v___x_414_ = lean_array_push(v_a_389_, v___x_413_);
v___y_396_ = v___x_414_;
goto v___jp_395_;
}
v___jp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_397_ = lean_mk_empty_array_with_capacity(v___x_373_);
v___x_398_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_399_ = 0;
v___x_400_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_401_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_401_, 0, v___x_397_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
lean_ctor_set(v___x_401_, 2, v___x_373_);
lean_ctor_set_uint8(v___x_401_, sizeof(void*)*3, v___x_399_);
lean_ctor_set_uint8(v___x_401_, sizeof(void*)*3 + 1, v___x_374_);
lean_ctor_set_uint8(v___x_401_, sizeof(void*)*3 + 2, v___x_374_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v___x_401_);
lean_ctor_set(v___x_391_, 0, v_mods_393_);
v___x_403_ = v___x_391_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_mods_393_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_401_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_404_ = lean_task_pure(v___x_403_);
v___x_405_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_375_);
lean_ctor_set(v___x_405_, 2, v___x_398_);
lean_ctor_set_uint8(v___x_405_, sizeof(void*)*3, v___x_374_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___y_396_);
return v___x_406_;
}
}
}
}
else
{
lean_object* v_a_416_; lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec(v___x_375_);
lean_dec(v___x_373_);
lean_dec_ref(v_self_371_);
v_a_416_ = lean_ctor_get(v___x_387_, 0);
v_a_417_ = lean_ctor_get(v___x_387_, 1);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_387_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_inc(v_a_416_);
lean_dec(v___x_387_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_416_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_426_; uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec_ref(v___y_376_);
lean_dec(v___x_375_);
lean_dec(v___x_373_);
lean_dec_ref(v_col_372_);
lean_dec_ref(v_self_371_);
v_a_425_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_383_, 1);
v___x_426_ = lean_io_error_to_string(v_a_425_);
v___x_427_ = 3;
v___x_428_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*1, v___x_427_);
v___x_429_ = lean_array_get_size(v___y_381_);
v___x_430_ = lean_array_push(v___y_381_, v___x_428_);
v___x_431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed(lean_object* v_self_432_, lean_object* v_col_433_, lean_object* v___x_434_, lean_object* v___x_435_, lean_object* v___x_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
uint8_t v___x_7367__boxed_444_; lean_object* v_res_445_; 
v___x_7367__boxed_444_ = lean_unbox(v___x_435_);
v_res_445_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(v_self_432_, v_col_433_, v___x_434_, v___x_7367__boxed_444_, v___x_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec(v___y_439_);
lean_dec(v___y_438_);
return v_res_445_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_448_ = lean_box(0);
v___x_449_ = lean_unsigned_to_nat(16u);
v___x_450_ = lean_mk_array(v___x_449_, v___x_448_);
return v___x_450_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1);
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3(void){
_start:
{
uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_col_457_; 
v___x_454_ = 0;
v___x_455_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_456_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0));
v_col_457_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_col_457_, 0, v___x_456_);
lean_ctor_set(v_col_457_, 1, v___x_455_);
lean_ctor_set_uint8(v_col_457_, sizeof(void*)*2, v___x_454_);
return v_col_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(lean_object* v_self_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; lean_object* v_col_469_; lean_object* v___x_470_; lean_object* v___f_471_; lean_object* v___x_472_; 
v___x_466_ = lean_box(0);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = 0;
v_col_469_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3);
v___x_470_ = lean_box(v___x_468_);
v___f_471_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed), 12, 5);
lean_closure_set(v___f_471_, 0, v_self_458_);
lean_closure_set(v___f_471_, 1, v_col_469_);
lean_closure_set(v___f_471_, 2, v___x_467_);
lean_closure_set(v___f_471_, 3, v___x_470_);
lean_closure_set(v___f_471_, 4, v___x_466_);
v___x_472_ = l_Lake_ensureJob___redArg(v___x_466_, v___f_471_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___boxed(lean_object* v_self_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(v_self_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec(v_a_476_);
lean_dec(v_a_475_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(lean_object* v_as_483_, size_t v_i_484_, size_t v_stop_485_, lean_object* v_b_486_){
_start:
{
uint8_t v___x_487_; 
v___x_487_ = lean_usize_dec_eq(v_i_484_, v_stop_485_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; lean_object* v_name_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; size_t v___x_495_; size_t v___x_496_; 
v___x_488_ = lean_array_uget_borrowed(v_as_483_, v_i_484_);
v_name_489_ = lean_ctor_get(v___x_488_, 1);
v___x_490_ = 1;
lean_inc(v_name_489_);
v___x_491_ = l_Lean_Name_toString(v_name_489_, v___x_490_);
v___x_492_ = lean_string_append(v_b_486_, v___x_491_);
lean_dec_ref(v___x_491_);
v___x_493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_494_ = lean_string_append(v___x_492_, v___x_493_);
v___x_495_ = ((size_t)1ULL);
v___x_496_ = lean_usize_add(v_i_484_, v___x_495_);
v_i_484_ = v___x_496_;
v_b_486_ = v___x_494_;
goto _start;
}
else
{
return v_b_486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_498_, lean_object* v_i_499_, lean_object* v_stop_500_, lean_object* v_b_501_){
_start:
{
size_t v_i_boxed_502_; size_t v_stop_boxed_503_; lean_object* v_res_504_; 
v_i_boxed_502_ = lean_unbox_usize(v_i_499_);
lean_dec(v_i_499_);
v_stop_boxed_503_ = lean_unbox_usize(v_stop_500_);
lean_dec(v_stop_500_);
v_res_504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_as_498_, v_i_boxed_502_, v_stop_boxed_503_, v_b_501_);
lean_dec_ref(v_as_498_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(size_t v_sz_505_, size_t v_i_506_, lean_object* v_bs_507_){
_start:
{
uint8_t v___x_508_; 
v___x_508_ = lean_usize_dec_lt(v_i_506_, v_sz_505_);
if (v___x_508_ == 0)
{
return v_bs_507_;
}
else
{
lean_object* v_v_509_; lean_object* v_name_510_; lean_object* v___x_511_; lean_object* v_bs_x27_512_; lean_object* v___x_513_; lean_object* v___x_514_; size_t v___x_515_; size_t v___x_516_; lean_object* v___x_517_; 
v_v_509_ = lean_array_uget_borrowed(v_bs_507_, v_i_506_);
v_name_510_ = lean_ctor_get(v_v_509_, 1);
lean_inc(v_name_510_);
v___x_511_ = lean_unsigned_to_nat(0u);
v_bs_x27_512_ = lean_array_uset(v_bs_507_, v_i_506_, v___x_511_);
v___x_513_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_510_, v___x_508_);
v___x_514_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
v___x_515_ = ((size_t)1ULL);
v___x_516_ = lean_usize_add(v_i_506_, v___x_515_);
v___x_517_ = lean_array_uset(v_bs_x27_512_, v_i_506_, v___x_514_);
v_i_506_ = v___x_516_;
v_bs_507_ = v___x_517_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_519_, lean_object* v_i_520_, lean_object* v_bs_521_){
_start:
{
size_t v_sz_boxed_522_; size_t v_i_boxed_523_; lean_object* v_res_524_; 
v_sz_boxed_522_ = lean_unbox_usize(v_sz_519_);
lean_dec(v_sz_519_);
v_i_boxed_523_ = lean_unbox_usize(v_i_520_);
lean_dec(v_i_520_);
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_522_, v_i_boxed_523_, v_bs_521_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(lean_object* v_a_525_){
_start:
{
size_t v_sz_526_; size_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_sz_526_ = lean_array_size(v_a_525_);
v___x_527_ = ((size_t)0ULL);
v___x_528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_526_, v___x_527_, v_a_525_);
v___x_529_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(uint8_t v_fmt_530_, lean_object* v_a_531_){
_start:
{
lean_object* v___y_533_; 
if (v_fmt_530_ == 0)
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_540_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_array_get_size(v_a_531_);
v___x_543_ = lean_nat_dec_lt(v___x_541_, v___x_542_);
if (v___x_543_ == 0)
{
lean_dec_ref(v_a_531_);
v___y_533_ = v___x_540_;
goto v___jp_532_;
}
else
{
size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; 
v___x_544_ = ((size_t)0ULL);
v___x_545_ = lean_usize_of_nat(v___x_542_);
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_531_, v___x_544_, v___x_545_, v___x_540_);
lean_dec_ref(v_a_531_);
v___y_533_ = v___x_546_;
goto v___jp_532_;
}
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(v_a_531_);
v___x_548_ = l_Lean_Json_compress(v___x_547_);
return v___x_548_;
}
v___jp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = lean_string_utf8_byte_size(v___y_533_);
lean_inc_ref(v___y_533_);
v___x_537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_537_, 0, v___y_533_);
lean_ctor_set(v___x_537_, 1, v___x_535_);
lean_ctor_set(v___x_537_, 2, v___x_536_);
v___x_538_ = l_String_Slice_Pos_prevn(v___x_537_, v___x_536_, v___x_534_);
lean_dec_ref_known(v___x_537_, 3);
v___x_539_ = lean_string_utf8_extract_fast(v___y_533_, v___x_535_, v___x_538_);
lean_dec(v___x_538_);
lean_dec_ref(v___y_533_);
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0___boxed(lean_object* v_fmt_549_, lean_object* v_a_550_){
_start:
{
uint8_t v_fmt_boxed_551_; lean_object* v_res_552_; 
v_fmt_boxed_551_ = lean_unbox(v_fmt_549_);
v_res_552_ = l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(v_fmt_boxed_551_, v_a_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(lean_object* v_as_566_, size_t v_i_567_, size_t v_stop_568_, lean_object* v_b_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
uint8_t v___x_577_; 
v___x_577_ = lean_usize_dec_eq(v_i_567_, v_stop_568_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v_lib_579_; lean_object* v_pkg_580_; lean_object* v_name_581_; lean_object* v_keyName_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_578_ = lean_array_uget_borrowed(v_as_566_, v_i_567_);
v_lib_579_ = lean_ctor_get(v___x_578_, 0);
v_pkg_580_ = lean_ctor_get(v_lib_579_, 0);
v_name_581_ = lean_ctor_get(v___x_578_, 1);
v_keyName_582_ = lean_ctor_get(v_pkg_580_, 2);
v___x_583_ = l_Lake_Module_leanArtsFacet;
lean_inc(v_name_581_);
lean_inc(v_keyName_582_);
v___x_584_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_584_, 0, v_keyName_582_);
lean_ctor_set(v___x_584_, 1, v_name_581_);
v___x_585_ = l_Lake_Module_keyword;
lean_inc(v___x_578_);
v___x_586_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
lean_ctor_set(v___x_586_, 2, v___x_578_);
lean_ctor_set(v___x_586_, 3, v___x_583_);
lean_inc_ref(v___y_570_);
lean_inc_ref(v___y_574_);
lean_inc(v___y_573_);
lean_inc(v___y_572_);
lean_inc(v___y_571_);
v___x_587_ = lean_apply_7(v___y_570_, v___x_586_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, lean_box(0));
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v_a_589_; lean_object* v___x_590_; size_t v___x_591_; size_t v___x_592_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
v_a_589_ = lean_ctor_get(v___x_587_, 1);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_587_, 2);
v___x_590_ = l_Lake_Job_mix___redArg(v_b_569_, v_a_588_);
v___x_591_ = ((size_t)1ULL);
v___x_592_ = lean_usize_add(v_i_567_, v___x_591_);
v_i_567_ = v___x_592_;
v_b_569_ = v___x_590_;
v___y_575_ = v_a_589_;
goto _start;
}
else
{
lean_object* v_a_594_; lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec_ref(v___y_570_);
lean_dec_ref(v_b_569_);
v_a_594_ = lean_ctor_get(v___x_587_, 0);
v_a_595_ = lean_ctor_get(v___x_587_, 1);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_587_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_inc(v_a_594_);
lean_dec(v___x_587_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_594_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v___x_603_; 
lean_dec_ref(v___y_570_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v_b_569_);
lean_ctor_set(v___x_603_, 1, v___y_575_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0___boxed(lean_object* v_as_604_, lean_object* v_i_605_, lean_object* v_stop_606_, lean_object* v_b_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
size_t v_i_boxed_615_; size_t v_stop_boxed_616_; lean_object* v_res_617_; 
v_i_boxed_615_ = lean_unbox_usize(v_i_605_);
lean_dec(v_i_605_);
v_stop_boxed_616_ = lean_unbox_usize(v_stop_606_);
lean_dec(v_stop_606_);
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_as_604_, v_i_boxed_615_, v_stop_boxed_616_, v_b_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v_as_604_);
return v_res_617_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_622_ = 0;
v___x_623_ = 0;
v___x_624_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v___x_625_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_621_);
lean_ctor_set(v___x_625_, 2, v___x_620_);
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*3, v___x_623_);
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*3 + 1, v___x_622_);
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*3 + 2, v___x_622_);
return v___x_625_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1);
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_626_);
return v___x_628_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2);
v___x_630_ = lean_task_pure(v___x_629_);
return v___x_630_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4(void){
_start:
{
uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_631_ = 0;
v___x_632_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_633_ = lean_box(0);
v___x_634_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3);
v___x_635_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_633_);
lean_ctor_set(v___x_635_, 2, v___x_632_);
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*3, v___x_631_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(lean_object* v_self_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_pkg_644_; lean_object* v_name_645_; lean_object* v_keyName_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_pkg_644_ = lean_ctor_get(v_self_636_, 0);
v_name_645_ = lean_ctor_get(v_self_636_, 1);
v_keyName_646_ = lean_ctor_get(v_pkg_644_, 2);
v___x_647_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_645_);
lean_inc(v_keyName_646_);
v___x_648_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_648_, 0, v_keyName_646_);
lean_ctor_set(v___x_648_, 1, v_name_645_);
v___x_649_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_650_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
lean_ctor_set(v___x_650_, 2, v_self_636_);
lean_ctor_set(v___x_650_, 3, v___x_647_);
lean_inc_ref(v_a_637_);
lean_inc_ref(v_a_641_);
lean_inc(v_a_640_);
lean_inc(v_a_639_);
lean_inc(v_a_638_);
v___x_651_ = lean_apply_7(v_a_637_, v___x_650_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, lean_box(0));
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v_a_653_; lean_object* v___x_654_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
v_a_653_ = lean_ctor_get(v___x_651_, 1);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_651_, 2);
v___x_654_ = l_Lake_Job_await___redArg(v_a_652_, v_a_653_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_677_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_a_656_ = lean_ctor_get(v___x_654_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_677_ == 0)
{
v___x_658_ = v___x_654_;
v_isShared_659_ = v_isSharedCheck_677_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_677_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4);
v___x_662_ = lean_array_get_size(v_a_655_);
v___x_663_ = lean_nat_dec_lt(v___x_660_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_665_; 
lean_dec(v_a_655_);
lean_dec_ref(v_a_637_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_661_);
v___x_665_ = v___x_658_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_a_656_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
else
{
uint8_t v___x_667_; 
v___x_667_ = lean_nat_dec_le(v___x_662_, v___x_662_);
if (v___x_667_ == 0)
{
if (v___x_663_ == 0)
{
lean_object* v___x_669_; 
lean_dec(v_a_655_);
lean_dec_ref(v_a_637_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_661_);
v___x_669_ = v___x_658_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_a_656_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
lean_del_object(v___x_658_);
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_662_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_655_, v___x_671_, v___x_672_, v___x_661_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_656_);
lean_dec(v_a_655_);
return v___x_673_;
}
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
lean_del_object(v___x_658_);
v___x_674_ = ((size_t)0ULL);
v___x_675_ = lean_usize_of_nat(v___x_662_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_655_, v___x_674_, v___x_675_, v___x_661_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_656_);
lean_dec(v_a_655_);
return v___x_676_;
}
}
}
}
else
{
lean_object* v_a_678_; lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_a_637_);
v_a_678_ = lean_ctor_get(v___x_654_, 0);
v_a_679_ = lean_ctor_get(v___x_654_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_654_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_inc(v_a_678_);
lean_dec(v___x_654_);
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
else
{
lean_object* v_a_687_; lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec_ref(v_a_637_);
v_a_687_ = lean_ctor_get(v___x_651_, 0);
v_a_688_ = lean_ctor_get(v___x_651_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_651_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_inc(v_a_687_);
lean_dec(v___x_651_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_687_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___boxed(lean_object* v_self_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(v_self_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec(v_a_699_);
lean_dec(v_a_698_);
return v_res_704_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_box(0);
v___x_706_ = l_Lean_Json_compress(v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(uint8_t v_fmt_707_){
_start:
{
if (v_fmt_707_ == 0)
{
lean_object* v___x_708_; 
v___x_708_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
return v___x_708_;
}
else
{
lean_object* v___x_709_; 
v___x_709_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_710_){
_start:
{
uint8_t v_fmt_boxed_711_; lean_object* v_res_712_; 
v_fmt_boxed_711_ = lean_unbox(v_fmt_710_);
v_res_712_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_boxed_711_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(uint8_t v_fmt_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___boxed(lean_object* v_fmt_716_, lean_object* v_a_717_){
_start:
{
uint8_t v_fmt_boxed_718_; lean_object* v_res_719_; 
v_fmt_boxed_718_ = lean_unbox(v_fmt_716_);
v_res_719_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(v_fmt_boxed_718_, v_a_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0(uint8_t v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v___y_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
uint8_t v___y_68__boxed_725_; lean_object* v_res_726_; 
v___y_68__boxed_725_ = lean_unbox(v___y_723_);
v_res_726_ = l_Lake_LeanLib_leanArtsFacetConfig___lam__0(v___y_68__boxed_725_, v___y_724_);
return v_res_726_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_729_; uint8_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___f_729_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_730_ = 1;
v___x_731_ = l_Lake_instDataKindUnit;
v___x_732_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__1));
v___x_733_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_734_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v___x_732_);
lean_ctor_set(v___x_734_, 2, v___x_731_);
lean_ctor_set(v___x_734_, 3, v___f_729_);
lean_ctor_set_uint8(v___x_734_, sizeof(void*)*4, v___x_730_);
lean_ctor_set_uint8(v___x_734_, sizeof(void*)*4 + 1, v___x_730_);
return v___x_734_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig(void){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_obj_once(&l_Lake_LeanLib_leanArtsFacetConfig___closed__2, &l_Lake_LeanLib_leanArtsFacetConfig___closed__2_once, _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(lean_object* v_a_736_, lean_object* v_x_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lake_ModuleFacet_fetch___redArg(v_x_737_, v_a_736_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object* v_a_746_, lean_object* v_x_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(v_a_746_, v_x_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec(v___y_750_);
lean_dec(v___y_749_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(uint8_t v_shouldExport_756_, lean_object* v___x_757_, lean_object* v_bs_758_, lean_object* v_a_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v_lib_767_; lean_object* v_config_768_; lean_object* v_nativeFacets_769_; lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_772_; size_t v_sz_773_; size_t v___x_774_; lean_object* v___x_189790__overap_775_; lean_object* v___x_776_; 
v_lib_767_ = lean_ctor_get(v_a_759_, 0);
v_config_768_ = lean_ctor_get(v_lib_767_, 2);
v_nativeFacets_769_ = lean_ctor_get(v_config_768_, 8);
lean_inc_ref(v_nativeFacets_769_);
v___f_770_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed), 9, 1);
lean_closure_set(v___f_770_, 0, v_a_759_);
v___x_771_ = lean_box(v_shouldExport_756_);
v___x_772_ = lean_apply_1(v_nativeFacets_769_, v___x_771_);
v_sz_773_ = lean_array_size(v___x_772_);
v___x_774_ = ((size_t)0ULL);
v___x_189790__overap_775_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_757_, v___f_770_, v_sz_773_, v___x_774_, v___x_772_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
lean_inc(v___y_762_);
lean_inc(v___y_761_);
v___x_776_ = lean_apply_7(v___x_189790__overap_775_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, lean_box(0));
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_786_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
v_a_778_ = lean_ctor_get(v___x_776_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_786_ == 0)
{
v___x_780_ = v___x_776_;
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_inc(v_a_777_);
lean_dec(v___x_776_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = l_Array_append___redArg(v_bs_758_, v_a_777_);
lean_dec(v_a_777_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_a_778_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_dec_ref(v_bs_758_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed(lean_object* v_shouldExport_787_, lean_object* v___x_788_, lean_object* v_bs_789_, lean_object* v_a_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
uint8_t v_shouldExport_boxed_798_; lean_object* v_res_799_; 
v_shouldExport_boxed_798_ = lean_unbox(v_shouldExport_787_);
v_res_799_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(v_shouldExport_boxed_798_, v___x_788_, v_bs_789_, v_a_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec(v___y_793_);
lean_dec(v___y_792_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(lean_object* v___x_800_, lean_object* v_pkg_801_, lean_object* v_x_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lake_Target_fetchIn___redArg(v___x_800_, v_pkg_801_, v_x_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object* v___x_811_, lean_object* v_pkg_812_, lean_object* v_x_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(v___x_811_, v_pkg_812_, v_x_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec(v___y_816_);
lean_dec(v___y_815_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object* v_a_822_, lean_object* v_x_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_log_832_; uint8_t v_action_833_; uint8_t v_wantsRebuild_834_; uint8_t v_canceled_835_; lean_object* v_trace_836_; lean_object* v_buildTime_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_log_832_ = lean_ctor_get(v___y_830_, 0);
v_action_833_ = lean_ctor_get_uint8(v___y_830_, sizeof(void*)*3);
v_wantsRebuild_834_ = lean_ctor_get_uint8(v___y_830_, sizeof(void*)*3 + 1);
v_canceled_835_ = lean_ctor_get_uint8(v___y_830_, sizeof(void*)*3 + 2);
v_trace_836_ = lean_ctor_get(v___y_830_, 1);
v_buildTime_837_ = lean_ctor_get(v___y_830_, 2);
v___x_838_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_839_ = lean_string_append(v___y_824_, v___x_838_);
v___x_840_ = lean_io_prim_handle_put_str(v_a_822_, v___x_839_);
lean_dec_ref(v___x_839_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_842_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
lean_dec_ref_known(v___x_840_, 1);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v_a_841_);
lean_ctor_set(v___x_842_, 1, v___y_830_);
return v___x_842_;
}
else
{
lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_856_; 
lean_inc(v_buildTime_837_);
lean_inc_ref(v_trace_836_);
lean_inc_ref(v_log_832_);
v_isSharedCheck_856_ = !lean_is_exclusive(v___y_830_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; lean_object* v_unused_858_; lean_object* v_unused_859_; 
v_unused_857_ = lean_ctor_get(v___y_830_, 2);
lean_dec(v_unused_857_);
v_unused_858_ = lean_ctor_get(v___y_830_, 1);
lean_dec(v_unused_858_);
v_unused_859_ = lean_ctor_get(v___y_830_, 0);
lean_dec(v_unused_859_);
v___x_844_ = v___y_830_;
v_isShared_845_ = v_isSharedCheck_856_;
goto v_resetjp_843_;
}
else
{
lean_dec(v___y_830_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_856_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_a_846_; lean_object* v___x_847_; uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v_a_846_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_840_, 1);
v___x_847_ = lean_io_error_to_string(v_a_846_);
v___x_848_ = 3;
v___x_849_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*1, v___x_848_);
v___x_850_ = lean_array_get_size(v_log_832_);
v___x_851_ = lean_array_push(v_log_832_, v___x_849_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_851_);
v___x_853_ = v___x_844_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_trace_836_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_buildTime_837_);
lean_ctor_set_uint8(v_reuseFailAlloc_855_, sizeof(void*)*3, v_action_833_);
lean_ctor_set_uint8(v_reuseFailAlloc_855_, sizeof(void*)*3 + 1, v_wantsRebuild_834_);
lean_ctor_set_uint8(v_reuseFailAlloc_855_, sizeof(void*)*3 + 2, v_canceled_835_);
v___x_853_ = v_reuseFailAlloc_855_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; 
v___x_854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_850_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
return v___x_854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object* v_a_860_, lean_object* v_x_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(v_a_860_, v_x_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v_a_860_);
return v_res_870_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_878_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3));
v___x_879_ = lean_unsigned_to_nat(5u);
v___x_880_ = lean_mk_empty_array_with_capacity(v___x_879_);
v___x_881_ = lean_array_push(v___x_880_, v___x_878_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4));
v___x_883_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6);
v___x_884_ = lean_array_push(v___x_883_, v___x_882_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(uint8_t v_bootstrap_887_, lean_object* v___y_888_, lean_object* v_oFiles_889_, uint8_t v_shouldExport_890_, uint8_t v___x_891_, lean_object* v___x_892_, size_t v___x_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
if (v_bootstrap_887_ == 0)
{
lean_object* v_toContext_901_; lean_object* v_lakeEnv_902_; lean_object* v_lean_903_; lean_object* v_log_904_; uint8_t v_action_905_; uint8_t v_wantsRebuild_906_; uint8_t v_canceled_907_; lean_object* v_trace_908_; lean_object* v_buildTime_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v___y_894_);
lean_dec_ref(v___x_892_);
v_toContext_901_ = lean_ctor_get(v___y_898_, 1);
v_lakeEnv_902_ = lean_ctor_get(v_toContext_901_, 0);
v_lean_903_ = lean_ctor_get(v_lakeEnv_902_, 1);
v_log_904_ = lean_ctor_get(v___y_899_, 0);
v_action_905_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*3);
v_wantsRebuild_906_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*3 + 1);
v_canceled_907_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*3 + 2);
v_trace_908_ = lean_ctor_get(v___y_899_, 1);
v_buildTime_909_ = lean_ctor_get(v___y_899_, 2);
v_isSharedCheck_939_ = !lean_is_exclusive(v___y_899_);
if (v_isSharedCheck_939_ == 0)
{
v___x_911_ = v___y_899_;
v_isShared_912_ = v_isSharedCheck_939_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_buildTime_909_);
lean_inc(v_trace_908_);
lean_inc(v_log_904_);
lean_dec(v___y_899_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_939_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_ar_913_; lean_object* v___x_914_; 
v_ar_913_ = lean_ctor_get(v_lean_903_, 13);
lean_inc_ref(v_ar_913_);
v___x_914_ = l_Lake_compileStaticLib(v___y_888_, v_oFiles_889_, v_ar_913_, v_bootstrap_887_, v_log_904_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_926_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_a_916_ = lean_ctor_get(v___x_914_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_926_ == 0)
{
v___x_918_ = v___x_914_;
v_isShared_919_ = v_isSharedCheck_926_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_926_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_a_916_);
v___x_921_ = v___x_911_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_916_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_trace_908_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_buildTime_909_);
lean_ctor_set_uint8(v_reuseFailAlloc_925_, sizeof(void*)*3, v_action_905_);
lean_ctor_set_uint8(v_reuseFailAlloc_925_, sizeof(void*)*3 + 1, v_wantsRebuild_906_);
lean_ctor_set_uint8(v_reuseFailAlloc_925_, sizeof(void*)*3 + 2, v_canceled_907_);
v___x_921_ = v_reuseFailAlloc_925_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_923_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v___x_921_);
v___x_923_ = v___x_918_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_915_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_938_; 
v_a_927_ = lean_ctor_get(v___x_914_, 0);
v_a_928_ = lean_ctor_get(v___x_914_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_938_ == 0)
{
v___x_930_ = v___x_914_;
v_isShared_931_ = v_isSharedCheck_938_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_inc(v_a_927_);
lean_dec(v___x_914_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_938_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v_a_928_);
v___x_933_ = v___x_911_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_928_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_trace_908_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_buildTime_909_);
lean_ctor_set_uint8(v_reuseFailAlloc_937_, sizeof(void*)*3, v_action_905_);
lean_ctor_set_uint8(v_reuseFailAlloc_937_, sizeof(void*)*3 + 1, v_wantsRebuild_906_);
lean_ctor_set_uint8(v_reuseFailAlloc_937_, sizeof(void*)*3 + 2, v_canceled_907_);
v___x_933_ = v_reuseFailAlloc_937_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_935_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_933_);
v___x_935_ = v___x_930_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_927_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
}
else
{
uint8_t v___x_940_; 
v___x_940_ = l_System_Platform_isOSX;
if (v___x_940_ == 0)
{
uint8_t v___x_941_; 
lean_dec_ref(v___y_894_);
lean_dec_ref(v___x_892_);
v___x_941_ = l_System_Platform_isWindows;
if (v___x_941_ == 0)
{
lean_object* v_toContext_942_; lean_object* v_lakeEnv_943_; lean_object* v_lean_944_; lean_object* v_log_945_; uint8_t v_action_946_; uint8_t v_wantsRebuild_947_; uint8_t v_canceled_948_; lean_object* v_trace_949_; lean_object* v_buildTime_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_980_; 
v_toContext_942_ = lean_ctor_get(v___y_898_, 1);
v_lakeEnv_943_ = lean_ctor_get(v_toContext_942_, 0);
v_lean_944_ = lean_ctor_get(v_lakeEnv_943_, 1);
v_log_945_ = lean_ctor_get(v___y_899_, 0);
v_action_946_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*3);
v_wantsRebuild_947_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*3 + 1);
v_canceled_948_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*3 + 2);
v_trace_949_ = lean_ctor_get(v___y_899_, 1);
v_buildTime_950_ = lean_ctor_get(v___y_899_, 2);
v_isSharedCheck_980_ = !lean_is_exclusive(v___y_899_);
if (v_isSharedCheck_980_ == 0)
{
v___x_952_ = v___y_899_;
v_isShared_953_ = v_isSharedCheck_980_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_buildTime_950_);
lean_inc(v_trace_949_);
lean_inc(v_log_945_);
lean_dec(v___y_899_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_980_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_ar_954_; lean_object* v___x_955_; 
v_ar_954_ = lean_ctor_get(v_lean_944_, 13);
lean_inc_ref(v_ar_954_);
v___x_955_ = l_Lake_compileStaticLib(v___y_888_, v_oFiles_889_, v_ar_954_, v___x_941_, v_log_945_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_967_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_a_957_ = lean_ctor_get(v___x_955_, 1);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_967_ == 0)
{
v___x_959_ = v___x_955_;
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_967_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v_a_957_);
v___x_962_ = v___x_952_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_957_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_trace_949_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_buildTime_950_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3, v_action_946_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3 + 1, v_wantsRebuild_947_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3 + 2, v_canceled_948_);
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
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_968_; lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_979_; 
v_a_968_ = lean_ctor_get(v___x_955_, 0);
v_a_969_ = lean_ctor_get(v___x_955_, 1);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_979_ == 0)
{
v___x_971_ = v___x_955_;
v_isShared_972_ = v_isSharedCheck_979_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_inc(v_a_968_);
lean_dec(v___x_955_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_979_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v_a_969_);
v___x_974_ = v___x_952_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_969_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_trace_949_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_buildTime_950_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, sizeof(void*)*3, v_action_946_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, sizeof(void*)*3 + 1, v_wantsRebuild_947_);
lean_ctor_set_uint8(v_reuseFailAlloc_978_, sizeof(void*)*3 + 2, v_canceled_948_);
v___x_974_ = v_reuseFailAlloc_978_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_976_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 1, v___x_974_);
v___x_976_ = v___x_971_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_968_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_981_; lean_object* v_lakeEnv_982_; lean_object* v_lean_983_; lean_object* v_log_984_; uint8_t v_action_985_; uint8_t v_wantsRebuild_986_; uint8_t v_canceled_987_; lean_object* v_trace_988_; lean_object* v_buildTime_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1019_; 
v_toContext_981_ = lean_ctor_get(v___y_898_, 1);
v_lakeEnv_982_ = lean_ctor_get(v_toContext_981_, 0);
v_lean_983_ = lean_ctor_get(v_lakeEnv_982_, 1);
v_log_984_ = lean_ctor_get(v___y_899_, 0);
v_action_985_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*3);
v_wantsRebuild_986_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*3 + 1);
v_canceled_987_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*3 + 2);
v_trace_988_ = lean_ctor_get(v___y_899_, 1);
v_buildTime_989_ = lean_ctor_get(v___y_899_, 2);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___y_899_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_991_ = v___y_899_;
v_isShared_992_ = v_isSharedCheck_1019_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_buildTime_989_);
lean_inc(v_trace_988_);
lean_inc(v_log_984_);
lean_dec(v___y_899_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1019_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v_ar_993_; lean_object* v___x_994_; 
v_ar_993_ = lean_ctor_get(v_lean_983_, 13);
lean_inc_ref(v_ar_993_);
v___x_994_ = l_Lake_compileStaticLib(v___y_888_, v_oFiles_889_, v_ar_993_, v_shouldExport_890_, v_log_984_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1006_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_a_996_ = lean_ctor_get(v___x_994_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_998_ = v___x_994_;
v_isShared_999_ = v_isSharedCheck_1006_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1006_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_a_996_);
v___x_1001_ = v___x_991_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_996_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_trace_988_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_buildTime_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_1005_, sizeof(void*)*3, v_action_985_);
lean_ctor_set_uint8(v_reuseFailAlloc_1005_, sizeof(void*)*3 + 1, v_wantsRebuild_986_);
lean_ctor_set_uint8(v_reuseFailAlloc_1005_, sizeof(void*)*3 + 2, v_canceled_987_);
v___x_1001_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1003_; 
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 1, v___x_1001_);
v___x_1003_ = v___x_998_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_995_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1018_; 
v_a_1007_ = lean_ctor_get(v___x_994_, 0);
v_a_1008_ = lean_ctor_get(v___x_994_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1010_ = v___x_994_;
v_isShared_1011_ = v_isSharedCheck_1018_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_inc(v_a_1007_);
lean_dec(v___x_994_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1018_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v_a_1008_);
v___x_1013_ = v___x_991_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1008_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_trace_988_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v_buildTime_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_1017_, sizeof(void*)*3, v_action_985_);
lean_ctor_set_uint8(v_reuseFailAlloc_1017_, sizeof(void*)*3 + 1, v_wantsRebuild_986_);
lean_ctor_set_uint8(v_reuseFailAlloc_1017_, sizeof(void*)*3 + 2, v_canceled_987_);
v___x_1013_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1015_; 
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 1, v___x_1013_);
v___x_1015_ = v___x_1010_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1007_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1020_; uint8_t v_action_1021_; uint8_t v_wantsRebuild_1022_; uint8_t v_canceled_1023_; lean_object* v_trace_1024_; lean_object* v_buildTime_1025_; lean_object* v___x_1026_; 
v_log_1020_ = lean_ctor_get(v___y_899_, 0);
v_action_1021_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*3);
v_wantsRebuild_1022_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*3 + 1);
v_canceled_1023_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*3 + 2);
v_trace_1024_ = lean_ctor_get(v___y_899_, 1);
v_buildTime_1025_ = lean_ctor_get(v___y_899_, 2);
lean_inc_ref(v___y_888_);
v___x_1026_ = l_Lake_createParentDirs(v___y_888_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v_a_1030_; lean_object* v___y_1078_; uint8_t v___x_1080_; lean_object* v___x_1081_; 
lean_dec_ref_known(v___x_1026_, 1);
v___x_1027_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_888_);
v___x_1028_ = l_System_FilePath_addExtension(v___y_888_, v___x_1027_);
v___x_1080_ = 1;
v___x_1081_ = lean_io_prim_handle_mk(v___x_1028_, v___x_1080_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = lean_array_get_size(v_oFiles_889_);
v___x_1085_ = lean_nat_dec_lt(v___x_1083_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec(v_a_1082_);
lean_dec_ref(v___y_894_);
lean_dec_ref(v___x_892_);
lean_dec_ref(v_oFiles_889_);
v_a_1030_ = v___y_899_;
goto v___jp_1029_;
}
else
{
lean_object* v___f_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___f_1086_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1086_, 0, v_a_1082_);
v___x_1087_ = lean_box(0);
v___x_1088_ = lean_nat_dec_le(v___x_1084_, v___x_1084_);
if (v___x_1088_ == 0)
{
if (v___x_1085_ == 0)
{
lean_dec_ref(v___f_1086_);
lean_dec_ref(v___y_894_);
lean_dec_ref(v___x_892_);
lean_dec_ref(v_oFiles_889_);
v_a_1030_ = v___y_899_;
goto v___jp_1029_;
}
else
{
size_t v___x_1089_; lean_object* v___x_189948__overap_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_usize_of_nat(v___x_1084_);
v___x_189948__overap_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_892_, v___f_1086_, v_oFiles_889_, v___x_893_, v___x_1089_, v___x_1087_);
lean_inc_ref(v___y_898_);
lean_inc(v___y_897_);
lean_inc(v___y_896_);
lean_inc(v___y_895_);
v___x_1091_ = lean_apply_7(v___x_189948__overap_1090_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, lean_box(0));
v___y_1078_ = v___x_1091_;
goto v___jp_1077_;
}
}
else
{
size_t v___x_1092_; lean_object* v___x_189950__overap_1093_; lean_object* v___x_1094_; 
v___x_1092_ = lean_usize_of_nat(v___x_1084_);
v___x_189950__overap_1093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_892_, v___f_1086_, v_oFiles_889_, v___x_893_, v___x_1092_, v___x_1087_);
lean_inc_ref(v___y_898_);
lean_inc(v___y_897_);
lean_inc(v___y_896_);
lean_inc(v___y_895_);
v___x_1094_ = lean_apply_7(v___x_189950__overap_1093_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, lean_box(0));
v___y_1078_ = v___x_1094_;
goto v___jp_1077_;
}
}
}
else
{
lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1108_; 
lean_inc(v_buildTime_1025_);
lean_inc_ref(v_trace_1024_);
lean_inc_ref(v_log_1020_);
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___y_894_);
lean_dec_ref(v___x_892_);
lean_dec_ref(v_oFiles_889_);
lean_dec_ref(v___y_888_);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___y_899_);
if (v_isSharedCheck_1108_ == 0)
{
lean_object* v_unused_1109_; lean_object* v_unused_1110_; lean_object* v_unused_1111_; 
v_unused_1109_ = lean_ctor_get(v___y_899_, 2);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v___y_899_, 1);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v___y_899_, 0);
lean_dec(v_unused_1111_);
v___x_1096_ = v___y_899_;
v_isShared_1097_ = v_isSharedCheck_1108_;
goto v_resetjp_1095_;
}
else
{
lean_dec(v___y_899_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1108_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v_a_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v_a_1098_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1099_ = lean_io_error_to_string(v_a_1098_);
v___x_1100_ = 3;
v___x_1101_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set_uint8(v___x_1101_, sizeof(void*)*1, v___x_1100_);
v___x_1102_ = lean_array_get_size(v_log_1020_);
v___x_1103_ = lean_array_push(v_log_1020_, v___x_1101_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v___x_1103_);
v___x_1105_ = v___x_1096_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_trace_1024_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_buildTime_1025_);
lean_ctor_set_uint8(v_reuseFailAlloc_1107_, sizeof(void*)*3, v_action_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1107_, sizeof(void*)*3 + 1, v_wantsRebuild_1022_);
lean_ctor_set_uint8(v_reuseFailAlloc_1107_, sizeof(void*)*3 + 2, v_canceled_1023_);
v___x_1105_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1102_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
return v___x_1106_;
}
}
}
v___jp_1029_:
{
lean_object* v___x_1031_; lean_object* v_log_1032_; uint8_t v_action_1033_; uint8_t v_wantsRebuild_1034_; uint8_t v_canceled_1035_; lean_object* v_trace_1036_; lean_object* v_buildTime_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1076_; 
v___x_1031_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1032_ = lean_ctor_get(v_a_1030_, 0);
v_action_1033_ = lean_ctor_get_uint8(v_a_1030_, sizeof(void*)*3);
v_wantsRebuild_1034_ = lean_ctor_get_uint8(v_a_1030_, sizeof(void*)*3 + 1);
v_canceled_1035_ = lean_ctor_get_uint8(v_a_1030_, sizeof(void*)*3 + 2);
v_trace_1036_ = lean_ctor_get(v_a_1030_, 1);
v_buildTime_1037_ = lean_ctor_get(v_a_1030_, 2);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_a_1030_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1039_ = v_a_1030_;
v_isShared_1040_ = v_isSharedCheck_1076_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_buildTime_1037_);
lean_inc(v_trace_1036_);
lean_inc(v_log_1032_);
lean_dec(v_a_1030_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1076_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1041_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1042_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1043_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1044_ = lean_array_push(v___x_1043_, v___y_888_);
v___x_1045_ = lean_array_push(v___x_1044_, v___x_1042_);
v___x_1046_ = lean_array_push(v___x_1045_, v___x_1028_);
v___x_1047_ = lean_box(0);
v___x_1048_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1049_ = 0;
v___x_1050_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1050_, 0, v___x_1031_);
lean_ctor_set(v___x_1050_, 1, v___x_1041_);
lean_ctor_set(v___x_1050_, 2, v___x_1046_);
lean_ctor_set(v___x_1050_, 3, v___x_1047_);
lean_ctor_set(v___x_1050_, 4, v___x_1048_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*5, v___x_891_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*5 + 1, v___x_1049_);
v___x_1051_ = l_Lake_proc(v___x_1050_, v___x_1049_, v___x_1047_, v_log_1032_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1063_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_a_1053_ = lean_ctor_get(v___x_1051_, 1);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1055_ = v___x_1051_;
v_isShared_1056_ = v_isSharedCheck_1063_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1063_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v_a_1053_);
v___x_1058_ = v___x_1039_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1053_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_trace_1036_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v_buildTime_1037_);
lean_ctor_set_uint8(v_reuseFailAlloc_1062_, sizeof(void*)*3, v_action_1033_);
lean_ctor_set_uint8(v_reuseFailAlloc_1062_, sizeof(void*)*3 + 1, v_wantsRebuild_1034_);
lean_ctor_set_uint8(v_reuseFailAlloc_1062_, sizeof(void*)*3 + 2, v_canceled_1035_);
v___x_1058_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1060_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 1, v___x_1058_);
v___x_1060_ = v___x_1055_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1052_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v___x_1058_);
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
else
{
lean_object* v_a_1064_; lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1075_; 
v_a_1064_ = lean_ctor_get(v___x_1051_, 0);
v_a_1065_ = lean_ctor_get(v___x_1051_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1067_ = v___x_1051_;
v_isShared_1068_ = v_isSharedCheck_1075_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_inc(v_a_1064_);
lean_dec(v___x_1051_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1075_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v_a_1065_);
v___x_1070_ = v___x_1039_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1065_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_trace_1036_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_buildTime_1037_);
lean_ctor_set_uint8(v_reuseFailAlloc_1074_, sizeof(void*)*3, v_action_1033_);
lean_ctor_set_uint8(v_reuseFailAlloc_1074_, sizeof(void*)*3 + 1, v_wantsRebuild_1034_);
lean_ctor_set_uint8(v_reuseFailAlloc_1074_, sizeof(void*)*3 + 2, v_canceled_1035_);
v___x_1070_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1072_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 1, v___x_1070_);
v___x_1072_ = v___x_1067_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1064_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
}
v___jp_1077_:
{
if (lean_obj_tag(v___y_1078_) == 0)
{
lean_object* v_a_1079_; 
v_a_1079_ = lean_ctor_get(v___y_1078_, 1);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___y_1078_, 2);
v_a_1030_ = v_a_1079_;
goto v___jp_1029_;
}
else
{
lean_dec_ref(v___x_1028_);
lean_dec_ref(v___y_888_);
return v___y_1078_;
}
}
}
else
{
lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1125_; 
lean_inc(v_buildTime_1025_);
lean_inc_ref(v_trace_1024_);
lean_inc_ref(v_log_1020_);
lean_dec_ref(v___y_894_);
lean_dec_ref(v___x_892_);
lean_dec_ref(v_oFiles_889_);
lean_dec_ref(v___y_888_);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___y_899_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; lean_object* v_unused_1127_; lean_object* v_unused_1128_; 
v_unused_1126_ = lean_ctor_get(v___y_899_, 2);
lean_dec(v_unused_1126_);
v_unused_1127_ = lean_ctor_get(v___y_899_, 1);
lean_dec(v_unused_1127_);
v_unused_1128_ = lean_ctor_get(v___y_899_, 0);
lean_dec(v_unused_1128_);
v___x_1113_ = v___y_899_;
v_isShared_1114_ = v_isSharedCheck_1125_;
goto v_resetjp_1112_;
}
else
{
lean_dec(v___y_899_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1125_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v_a_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v_a_1115_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1116_ = lean_io_error_to_string(v_a_1115_);
v___x_1117_ = 3;
v___x_1118_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*1, v___x_1117_);
v___x_1119_ = lean_array_get_size(v_log_1020_);
v___x_1120_ = lean_array_push(v_log_1020_, v___x_1118_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1120_);
v___x_1122_ = v___x_1113_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_trace_1024_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_buildTime_1025_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*3, v_action_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*3 + 1, v_wantsRebuild_1022_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*3 + 2, v_canceled_1023_);
v___x_1122_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1119_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
return v___x_1123_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object* v_bootstrap_1129_, lean_object* v___y_1130_, lean_object* v_oFiles_1131_, lean_object* v_shouldExport_1132_, lean_object* v___x_1133_, lean_object* v___x_1134_, lean_object* v___x_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
uint8_t v_bootstrap_boxed_1143_; uint8_t v_shouldExport_boxed_1144_; uint8_t v___x_190318__boxed_1145_; size_t v___x_190320__boxed_1146_; lean_object* v_res_1147_; 
v_bootstrap_boxed_1143_ = lean_unbox(v_bootstrap_1129_);
v_shouldExport_boxed_1144_ = lean_unbox(v_shouldExport_1132_);
v___x_190318__boxed_1145_ = lean_unbox(v___x_1133_);
v___x_190320__boxed_1146_ = lean_unbox_usize(v___x_1135_);
lean_dec(v___x_1135_);
v_res_1147_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(v_bootstrap_boxed_1143_, v___y_1130_, v_oFiles_1131_, v_shouldExport_boxed_1144_, v___x_190318__boxed_1145_, v___x_1134_, v___x_190320__boxed_1146_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec(v___y_1137_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(uint8_t v_bootstrap_1149_, lean_object* v___y_1150_, uint8_t v_shouldExport_1151_, uint8_t v___x_1152_, lean_object* v___x_1153_, size_t v___x_1154_, lean_object* v_oFiles_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___y_1167_; uint8_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1163_ = lean_box(v_bootstrap_1149_);
v___x_1164_ = lean_box(v_shouldExport_1151_);
v___x_1165_ = lean_box(v___x_1152_);
v___x_1166_ = lean_box_usize(v___x_1154_);
lean_inc_ref(v___y_1150_);
v___y_1167_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed), 14, 7);
lean_closure_set(v___y_1167_, 0, v___x_1163_);
lean_closure_set(v___y_1167_, 1, v___y_1150_);
lean_closure_set(v___y_1167_, 2, v_oFiles_1155_);
lean_closure_set(v___y_1167_, 3, v___x_1164_);
lean_closure_set(v___y_1167_, 4, v___x_1165_);
lean_closure_set(v___y_1167_, 5, v___x_1153_);
lean_closure_set(v___y_1167_, 6, v___x_1166_);
v___x_1168_ = 0;
v___x_1169_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1170_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1150_, v___y_1167_, v___x_1168_, v___x_1169_, v___x_1152_, v___x_1168_, v___x_1168_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1180_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_a_1172_ = lean_ctor_get(v___x_1170_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1174_ = v___x_1170_;
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1180_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_path_1176_; lean_object* v___x_1178_; 
v_path_1176_ = lean_ctor_get(v_a_1171_, 1);
lean_inc_ref(v_path_1176_);
lean_dec(v_a_1171_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v_path_1176_);
v___x_1178_ = v___x_1174_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_path_1176_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_a_1172_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
v_a_1181_ = lean_ctor_get(v___x_1170_, 0);
v_a_1182_ = lean_ctor_get(v___x_1170_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1170_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_inc(v_a_1181_);
lean_dec(v___x_1170_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1181_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object* v_bootstrap_1190_, lean_object* v___y_1191_, lean_object* v_shouldExport_1192_, lean_object* v___x_1193_, lean_object* v___x_1194_, lean_object* v___x_1195_, lean_object* v_oFiles_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
uint8_t v_bootstrap_boxed_1204_; uint8_t v_shouldExport_boxed_1205_; uint8_t v___x_190741__boxed_1206_; size_t v___x_190743__boxed_1207_; lean_object* v_res_1208_; 
v_bootstrap_boxed_1204_ = lean_unbox(v_bootstrap_1190_);
v_shouldExport_boxed_1205_ = lean_unbox(v_shouldExport_1192_);
v___x_190741__boxed_1206_ = lean_unbox(v___x_1193_);
v___x_190743__boxed_1207_ = lean_unbox_usize(v___x_1195_);
lean_dec(v___x_1195_);
v_res_1208_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(v_bootstrap_boxed_1204_, v___y_1191_, v_shouldExport_boxed_1205_, v___x_190741__boxed_1206_, v___x_1194_, v___x_190743__boxed_1207_, v_oFiles_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec(v___y_1198_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object* v_config_1213_, lean_object* v_config_1214_, uint8_t v_shouldExport_1215_, uint8_t v___x_1216_, lean_object* v___x_1217_, lean_object* v___x_1218_, lean_object* v___x_1219_, lean_object* v___x_1220_, lean_object* v___f_1221_, lean_object* v_dir_1222_, lean_object* v_self_1223_, lean_object* v___x_1224_, lean_object* v___f_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
size_t v___y_1234_; uint8_t v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v_a_1254_; lean_object* v_a_1255_; lean_object* v___x_1298_; 
lean_inc_ref(v___y_1226_);
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1229_);
lean_inc(v___y_1228_);
lean_inc(v___x_1219_);
v___x_1298_ = lean_apply_7(v___y_1226_, v___x_1224_, v___x_1219_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, lean_box(0));
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v_a_1300_; lean_object* v___x_1301_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
v_a_1300_ = lean_ctor_get(v___x_1298_, 1);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1298_, 2);
v___x_1301_ = l_Lake_Job_await___redArg(v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v_a_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
v_a_1303_ = lean_ctor_get(v___x_1301_, 1);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1301_, 2);
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_1306_ = lean_array_get_size(v_a_1302_);
v___x_1307_ = lean_nat_dec_lt(v___x_1304_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_dec(v_a_1302_);
lean_dec_ref(v___f_1225_);
v_a_1254_ = v___x_1305_;
v_a_1255_ = v_a_1303_;
goto v___jp_1253_;
}
else
{
size_t v___x_1308_; size_t v___x_1309_; lean_object* v___x_190078__overap_1310_; lean_object* v___x_1311_; 
v___x_1308_ = ((size_t)0ULL);
v___x_1309_ = lean_usize_of_nat(v___x_1306_);
lean_inc_ref(v___x_1220_);
v___x_190078__overap_1310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1220_, v___f_1225_, v_a_1302_, v___x_1308_, v___x_1309_, v___x_1305_);
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1229_);
lean_inc(v___y_1228_);
lean_inc(v___x_1219_);
lean_inc_ref(v___y_1226_);
v___x_1311_ = lean_apply_7(v___x_190078__overap_1310_, v___y_1226_, v___x_1219_, v___y_1228_, v___y_1229_, v___y_1230_, v_a_1303_, lean_box(0));
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v_a_1313_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
v_a_1313_ = lean_ctor_get(v___x_1311_, 1);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1311_, 2);
v_a_1254_ = v_a_1312_;
v_a_1255_ = v_a_1313_;
goto v___jp_1253_;
}
else
{
lean_object* v_a_1314_; lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v___y_1226_);
lean_dec_ref(v_self_1223_);
lean_dec_ref(v_dir_1222_);
lean_dec_ref(v___f_1221_);
lean_dec_ref(v___x_1220_);
lean_dec(v___x_1219_);
lean_dec(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v_config_1213_);
v_a_1314_ = lean_ctor_get(v___x_1311_, 0);
v_a_1315_ = lean_ctor_get(v___x_1311_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1311_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_inc(v_a_1314_);
lean_dec(v___x_1311_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1314_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec_ref(v___y_1226_);
lean_dec_ref(v___f_1225_);
lean_dec_ref(v_self_1223_);
lean_dec_ref(v_dir_1222_);
lean_dec_ref(v___f_1221_);
lean_dec_ref(v___x_1220_);
lean_dec(v___x_1219_);
lean_dec(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v_config_1213_);
v_a_1323_ = lean_ctor_get(v___x_1301_, 0);
v_a_1324_ = lean_ctor_get(v___x_1301_, 1);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1301_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_inc(v_a_1323_);
lean_dec(v___x_1301_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1323_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v___y_1226_);
lean_dec_ref(v___f_1225_);
lean_dec_ref(v_self_1223_);
lean_dec_ref(v_dir_1222_);
lean_dec_ref(v___f_1221_);
lean_dec_ref(v___x_1220_);
lean_dec(v___x_1219_);
lean_dec(v___x_1218_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v_config_1213_);
v_a_1332_ = lean_ctor_get(v___x_1298_, 0);
v_a_1333_ = lean_ctor_get(v___x_1298_, 1);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1298_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_inc(v_a_1332_);
lean_dec(v___x_1298_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1332_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
v___jp_1233_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___f_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1240_ = lean_box(v___y_1235_);
v___x_1241_ = lean_box(v_shouldExport_1215_);
v___x_1242_ = lean_box(v___x_1216_);
v___x_1243_ = lean_box_usize(v___y_1234_);
v___f_1244_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed), 14, 6);
lean_closure_set(v___f_1244_, 0, v___x_1240_);
lean_closure_set(v___f_1244_, 1, v___y_1239_);
lean_closure_set(v___f_1244_, 2, v___x_1241_);
lean_closure_set(v___f_1244_, 3, v___x_1242_);
lean_closure_set(v___f_1244_, 4, v___x_1217_);
lean_closure_set(v___f_1244_, 5, v___x_1243_);
v___x_1245_ = l_Array_append___redArg(v___y_1236_, v___y_1237_);
lean_dec_ref(v___y_1237_);
v___x_1246_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_1247_ = l_Lake_Job_collectArray___redArg(v___x_1245_, v___x_1246_);
lean_dec_ref(v___x_1245_);
v___x_1248_ = lean_unsigned_to_nat(0u);
v___x_1249_ = 0;
v___x_1250_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_1251_ = l_Lake_Job_mapM___redArg(v___x_1218_, v___x_1247_, v___f_1244_, v___x_1248_, v___x_1249_, v___y_1226_, v___x_1219_, v___y_1228_, v___y_1229_, v___y_1230_, v___x_1250_);
lean_dec(v___x_1219_);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v___y_1238_);
return v___x_1252_;
}
v___jp_1253_:
{
lean_object* v_toLeanConfig_1256_; lean_object* v_toLeanConfig_1257_; uint8_t v_bootstrap_1258_; lean_object* v_buildDir_1259_; lean_object* v_nativeLibDir_1260_; lean_object* v_moreLinkObjs_1261_; lean_object* v_moreLinkObjs_1262_; lean_object* v___x_1263_; size_t v_sz_1264_; size_t v___x_1265_; lean_object* v___x_190036__overap_1266_; lean_object* v___x_1267_; 
v_toLeanConfig_1256_ = lean_ctor_get(v_config_1213_, 1);
lean_inc_ref(v_toLeanConfig_1256_);
v_toLeanConfig_1257_ = lean_ctor_get(v_config_1214_, 0);
v_bootstrap_1258_ = lean_ctor_get_uint8(v_config_1213_, sizeof(void*)*28);
v_buildDir_1259_ = lean_ctor_get(v_config_1213_, 5);
lean_inc_ref(v_buildDir_1259_);
v_nativeLibDir_1260_ = lean_ctor_get(v_config_1213_, 7);
lean_inc_ref(v_nativeLibDir_1260_);
lean_dec_ref(v_config_1213_);
v_moreLinkObjs_1261_ = lean_ctor_get(v_toLeanConfig_1256_, 6);
lean_inc_ref(v_moreLinkObjs_1261_);
lean_dec_ref(v_toLeanConfig_1256_);
v_moreLinkObjs_1262_ = lean_ctor_get(v_toLeanConfig_1257_, 6);
v___x_1263_ = l_Array_append___redArg(v_moreLinkObjs_1261_, v_moreLinkObjs_1262_);
v_sz_1264_ = lean_array_size(v___x_1263_);
v___x_1265_ = ((size_t)0ULL);
v___x_190036__overap_1266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1220_, v___f_1221_, v_sz_1264_, v___x_1265_, v___x_1263_);
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1229_);
lean_inc(v___y_1228_);
lean_inc(v___x_1219_);
lean_inc_ref(v___y_1226_);
v___x_1267_ = lean_apply_7(v___x_190036__overap_1266_, v___y_1226_, v___x_1219_, v___y_1228_, v___y_1229_, v___y_1230_, v_a_1255_, lean_box(0));
if (lean_obj_tag(v___x_1267_) == 0)
{
if (v_shouldExport_1215_ == 0)
{
lean_object* v_a_1268_; lean_object* v_a_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
v_a_1269_ = lean_ctor_get(v___x_1267_, 1);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1267_, 2);
v___x_1270_ = l_System_FilePath_normalize(v_buildDir_1259_);
v___x_1271_ = l_Lake_joinRelative(v_dir_1222_, v___x_1270_);
v___x_1272_ = l_System_FilePath_normalize(v_nativeLibDir_1260_);
v___x_1273_ = l_Lake_joinRelative(v___x_1271_, v___x_1272_);
v___x_1274_ = l_Lake_LeanLib_libName(v_self_1223_);
v___x_1275_ = l_Lake_nameToStaticLib(v___x_1274_, v_shouldExport_1215_);
v___x_1276_ = l_Lake_joinRelative(v___x_1273_, v___x_1275_);
v___y_1234_ = v___x_1265_;
v___y_1235_ = v_bootstrap_1258_;
v___y_1236_ = v_a_1254_;
v___y_1237_ = v_a_1268_;
v___y_1238_ = v_a_1269_;
v___y_1239_ = v___x_1276_;
goto v___jp_1233_;
}
else
{
lean_object* v_a_1277_; lean_object* v_a_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_a_1277_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1277_);
v_a_1278_ = lean_ctor_get(v___x_1267_, 1);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1267_, 2);
v___x_1279_ = l_System_FilePath_normalize(v_buildDir_1259_);
v___x_1280_ = l_Lake_joinRelative(v_dir_1222_, v___x_1279_);
v___x_1281_ = l_System_FilePath_normalize(v_nativeLibDir_1260_);
v___x_1282_ = l_Lake_joinRelative(v___x_1280_, v___x_1281_);
v___x_1283_ = l_Lake_LeanLib_libName(v_self_1223_);
v___x_1284_ = 0;
v___x_1285_ = l_Lake_nameToStaticLib(v___x_1283_, v___x_1284_);
v___x_1286_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_1287_ = l_System_FilePath_addExtension(v___x_1285_, v___x_1286_);
v___x_1288_ = l_Lake_joinRelative(v___x_1282_, v___x_1287_);
v___y_1234_ = v___x_1265_;
v___y_1235_ = v_bootstrap_1258_;
v___y_1236_ = v_a_1254_;
v___y_1237_ = v_a_1277_;
v___y_1238_ = v_a_1278_;
v___y_1239_ = v___x_1288_;
goto v___jp_1233_;
}
}
else
{
lean_object* v_a_1289_; lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v_nativeLibDir_1260_);
lean_dec_ref(v_buildDir_1259_);
lean_dec_ref(v_a_1254_);
lean_dec_ref(v___y_1226_);
lean_dec_ref(v_self_1223_);
lean_dec_ref(v_dir_1222_);
lean_dec(v___x_1219_);
lean_dec(v___x_1218_);
lean_dec_ref(v___x_1217_);
v_a_1289_ = lean_ctor_get(v___x_1267_, 0);
v_a_1290_ = lean_ctor_get(v___x_1267_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1267_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_inc(v_a_1289_);
lean_dec(v___x_1267_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1289_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed(lean_object** _args){
lean_object* v_config_1341_ = _args[0];
lean_object* v_config_1342_ = _args[1];
lean_object* v_shouldExport_1343_ = _args[2];
lean_object* v___x_1344_ = _args[3];
lean_object* v___x_1345_ = _args[4];
lean_object* v___x_1346_ = _args[5];
lean_object* v___x_1347_ = _args[6];
lean_object* v___x_1348_ = _args[7];
lean_object* v___f_1349_ = _args[8];
lean_object* v_dir_1350_ = _args[9];
lean_object* v_self_1351_ = _args[10];
lean_object* v___x_1352_ = _args[11];
lean_object* v___f_1353_ = _args[12];
lean_object* v___y_1354_ = _args[13];
lean_object* v___y_1355_ = _args[14];
lean_object* v___y_1356_ = _args[15];
lean_object* v___y_1357_ = _args[16];
lean_object* v___y_1358_ = _args[17];
lean_object* v___y_1359_ = _args[18];
lean_object* v___y_1360_ = _args[19];
_start:
{
uint8_t v_shouldExport_boxed_1361_; uint8_t v___x_190839__boxed_1362_; lean_object* v_res_1363_; 
v_shouldExport_boxed_1361_ = lean_unbox(v_shouldExport_1343_);
v___x_190839__boxed_1362_ = lean_unbox(v___x_1344_);
v_res_1363_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(v_config_1341_, v_config_1342_, v_shouldExport_boxed_1361_, v___x_190839__boxed_1362_, v___x_1345_, v___x_1346_, v___x_1347_, v___x_1348_, v___f_1349_, v_dir_1350_, v_self_1351_, v___x_1352_, v___f_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec(v_config_1342_);
return v_res_1363_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0(void){
_start:
{
uint8_t v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = 2;
v___x_1365_ = l_Lake_Verbosity_ctorIdx(v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object* v_self_1369_, uint8_t v_shouldExport_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v___x_1378_; lean_object* v_toApplicative_1379_; lean_object* v_toBind_1380_; lean_object* v_toFunctor_1381_; lean_object* v_toPure_1382_; lean_object* v___f_1383_; lean_object* v___f_1384_; lean_object* v___f_1385_; lean_object* v___f_1386_; lean_object* v___x_1387_; lean_object* v___f_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v_toBuildConfig_1396_; lean_object* v_registeredJobs_1397_; uint8_t v_verbosity_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___f_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; uint8_t v___x_1405_; lean_object* v___y_1407_; 
v___x_1378_ = l_instMonadBaseIO;
v_toApplicative_1379_ = lean_ctor_get(v___x_1378_, 0);
v_toBind_1380_ = lean_ctor_get(v___x_1378_, 1);
v_toFunctor_1381_ = lean_ctor_get(v_toApplicative_1379_, 0);
v_toPure_1382_ = lean_ctor_get(v_toApplicative_1379_, 1);
lean_inc_n(v_toBind_1380_, 3);
lean_inc_n(v_toPure_1382_, 5);
v___f_1383_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1383_, 0, v_toPure_1382_);
lean_closure_set(v___f_1383_, 1, v_toBind_1380_);
v___f_1384_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1384_, 0, v_toPure_1382_);
lean_closure_set(v___f_1384_, 1, v_toBind_1380_);
lean_inc_ref(v___f_1383_);
v___f_1385_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1385_, 0, v_toPure_1382_);
lean_closure_set(v___f_1385_, 1, v___f_1383_);
lean_inc_ref_n(v_toFunctor_1381_, 2);
v___f_1386_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1386_, 0, v_toFunctor_1381_);
lean_closure_set(v___f_1386_, 1, v_toPure_1382_);
lean_closure_set(v___f_1386_, 2, v_toBind_1380_);
v___x_1387_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1381_);
v___f_1388_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1388_, 0, v_toPure_1382_);
v___x_1389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1387_);
lean_ctor_set(v___x_1389_, 1, v___f_1388_);
lean_ctor_set(v___x_1389_, 2, v___f_1386_);
lean_ctor_set(v___x_1389_, 3, v___f_1385_);
lean_ctor_set(v___x_1389_, 4, v___f_1384_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v___f_1383_);
v___x_1391_ = l_ReaderT_instMonad___redArg(v___x_1390_);
v___x_1392_ = l_StateRefT_x27_instMonad___redArg(v___x_1391_);
v___x_1393_ = l_ReaderT_instMonad___redArg(v___x_1392_);
v___x_1394_ = l_ReaderT_instMonad___redArg(v___x_1393_);
v___x_1395_ = l_Lake_EquipT_instMonad___redArg(v___x_1394_);
v_toBuildConfig_1396_ = lean_ctor_get(v_a_1375_, 0);
v_registeredJobs_1397_ = lean_ctor_get(v_a_1375_, 4);
v_verbosity_1398_ = lean_ctor_get_uint8(v_toBuildConfig_1396_, sizeof(void*)*5 + 4);
v___x_1399_ = l_Lake_instDataKindFilePath;
v___x_1400_ = lean_box(v_shouldExport_1370_);
lean_inc_ref(v___x_1395_);
v___f_1401_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1401_, 0, v___x_1400_);
lean_closure_set(v___f_1401_, 1, v___x_1395_);
v___x_1402_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1398_);
v___x_1403_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0);
v___x_1404_ = lean_nat_dec_eq(v___x_1402_, v___x_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = 1;
if (v___x_1404_ == 0)
{
lean_object* v___x_1453_; 
v___x_1453_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_1407_ = v___x_1453_;
goto v___jp_1406_;
}
else
{
if (v_shouldExport_1370_ == 0)
{
lean_object* v___x_1454_; 
v___x_1454_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_1407_ = v___x_1454_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1455_; 
v___x_1455_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3));
v___y_1407_ = v___x_1455_;
goto v___jp_1406_;
}
}
v___jp_1406_:
{
lean_object* v_pkg_1408_; lean_object* v_name_1409_; lean_object* v_config_1410_; lean_object* v_keyName_1411_; lean_object* v_dir_1412_; lean_object* v_config_1413_; lean_object* v___f_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___f_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; 
v_pkg_1408_ = lean_ctor_get(v_self_1369_, 0);
v_name_1409_ = lean_ctor_get(v_self_1369_, 1);
v_config_1410_ = lean_ctor_get(v_self_1369_, 2);
lean_inc(v_config_1410_);
v_keyName_1411_ = lean_ctor_get(v_pkg_1408_, 2);
v_dir_1412_ = lean_ctor_get(v_pkg_1408_, 4);
lean_inc_ref(v_dir_1412_);
v_config_1413_ = lean_ctor_get(v_pkg_1408_, 6);
lean_inc_ref(v_config_1413_);
lean_inc_ref_n(v_pkg_1408_, 2);
v___f_1414_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(v___f_1414_, 0, v___x_1399_);
lean_closure_set(v___f_1414_, 1, v_pkg_1408_);
lean_inc_n(v_name_1409_, 2);
v___x_1415_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1409_, v___x_1405_);
v___x_1416_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___x_1417_ = lean_string_append(v___x_1415_, v___x_1416_);
v___x_1418_ = lean_string_append(v___x_1417_, v___y_1407_);
v___x_1419_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_1411_);
v___x_1420_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1420_, 0, v_keyName_1411_);
lean_ctor_set(v___x_1420_, 1, v_name_1409_);
v___x_1421_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_1369_);
v___x_1422_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
lean_ctor_set(v___x_1422_, 2, v_self_1369_);
lean_ctor_set(v___x_1422_, 3, v___x_1419_);
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v_pkg_1408_);
v___x_1424_ = lean_box(v_shouldExport_1370_);
v___x_1425_ = lean_box(v___x_1405_);
lean_inc_ref(v___x_1395_);
v___f_1426_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed), 20, 13);
lean_closure_set(v___f_1426_, 0, v_config_1413_);
lean_closure_set(v___f_1426_, 1, v_config_1410_);
lean_closure_set(v___f_1426_, 2, v___x_1424_);
lean_closure_set(v___f_1426_, 3, v___x_1425_);
lean_closure_set(v___f_1426_, 4, v___x_1395_);
lean_closure_set(v___f_1426_, 5, v___x_1399_);
lean_closure_set(v___f_1426_, 6, v___x_1423_);
lean_closure_set(v___f_1426_, 7, v___x_1395_);
lean_closure_set(v___f_1426_, 8, v___f_1414_);
lean_closure_set(v___f_1426_, 9, v_dir_1412_);
lean_closure_set(v___f_1426_, 10, v_self_1369_);
lean_closure_set(v___f_1426_, 11, v___x_1422_);
lean_closure_set(v___f_1426_, 12, v___f_1401_);
v___x_1427_ = 0;
v___x_1428_ = l_Lake_ensureJob___redArg(v___x_1399_, v___f_1426_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1452_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_a_1430_ = lean_ctor_get(v___x_1428_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1432_ = v___x_1428_;
v_isShared_1433_ = v_isSharedCheck_1452_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1452_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v_task_1434_; lean_object* v_kind_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1450_; 
v_task_1434_ = lean_ctor_get(v_a_1429_, 0);
v_kind_1435_ = lean_ctor_get(v_a_1429_, 1);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_a_1429_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; 
v_unused_1451_ = lean_ctor_get(v_a_1429_, 2);
lean_dec(v_unused_1451_);
v___x_1437_ = v_a_1429_;
v_isShared_1438_ = v_isSharedCheck_1450_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_kind_1435_);
lean_inc(v_task_1434_);
lean_dec(v_a_1429_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1450_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v_job_1440_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 2, v___x_1418_);
v_job_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_task_1434_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_kind_1435_);
lean_ctor_set(v_reuseFailAlloc_1449_, 2, v___x_1418_);
v_job_1440_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; 
lean_ctor_set_uint8(v_job_1440_, sizeof(void*)*3, v___x_1427_);
v___x_1441_ = lean_st_ref_take(v_registeredJobs_1397_);
lean_inc_ref(v_job_1440_);
v___x_1442_ = l_Lake_Job_toOpaque___redArg(v_job_1440_);
v___x_1443_ = lean_array_push(v___x_1441_, v___x_1442_);
v___x_1444_ = lean_st_ref_put(v_registeredJobs_1397_, v___x_1443_);
v___x_1445_ = l_Lake_Job_renew___redArg(v_job_1440_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1445_);
v___x_1447_ = v___x_1432_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_a_1430_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1418_);
return v___x_1428_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object* v_self_1456_, lean_object* v_shouldExport_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
uint8_t v_shouldExport_boxed_1465_; lean_object* v_res_1466_; 
v_shouldExport_boxed_1465_ = lean_unbox(v_shouldExport_1457_);
v_res_1466_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1456_, v_shouldExport_boxed_1465_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec_ref(v_a_1462_);
lean_dec(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec(v_a_1459_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t v_fmt_1467_, lean_object* v_a_1468_){
_start:
{
if (v_fmt_1467_ == 0)
{
return v_a_1468_;
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = l_Lake_mkRelPathString(v_a_1468_);
v___x_1470_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
v___x_1471_ = l_Lean_Json_compress(v___x_1470_);
return v___x_1471_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object* v_fmt_1472_, lean_object* v_a_1473_){
_start:
{
uint8_t v_fmt_boxed_1474_; lean_object* v_res_1475_; 
v_fmt_boxed_1474_ = lean_unbox(v_fmt_1472_);
v_res_1475_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_boxed_1474_, v_a_1473_);
return v_res_1475_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2(void){
_start:
{
uint8_t v___x_1478_; lean_object* v_name_1479_; lean_object* v___x_1480_; 
v___x_1478_ = 1;
v_name_1479_ = l_Lake_instDataKindFilePath;
v___x_1480_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1479_, v___x_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* v_defaultPkg_1484_, lean_object* v_self_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_name_1493_; uint8_t v___x_1494_; lean_object* v___x_1495_; 
v_name_1493_ = l_Lake_instDataKindFilePath;
v___x_1494_ = 1;
lean_inc_ref_n(v_self_1485_, 2);
v___x_1495_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1484_, v_self_1485_, v_self_1485_, v___x_1494_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1537_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_a_1497_ = lean_ctor_get(v___x_1495_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1499_ = v___x_1495_;
v_isShared_1500_ = v_isSharedCheck_1537_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1537_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___y_1502_; lean_object* v_snd_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1535_; 
v_snd_1520_ = lean_ctor_get(v_a_1496_, 1);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_a_1496_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; 
v_unused_1536_ = lean_ctor_get(v_a_1496_, 0);
lean_dec(v_unused_1536_);
v___x_1522_ = v_a_1496_;
v_isShared_1523_ = v_isSharedCheck_1535_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_snd_1520_);
lean_dec(v_a_1496_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1535_;
goto v_resetjp_1521_;
}
v___jp_1501_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1503_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1504_ = l_Lake_PartialBuildKey_toString(v_self_1485_);
v___x_1505_ = lean_string_append(v___x_1503_, v___x_1504_);
lean_dec_ref(v___x_1504_);
v___x_1506_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1507_ = lean_string_append(v___x_1505_, v___x_1506_);
v___x_1508_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
v___x_1509_ = lean_string_append(v___x_1507_, v___x_1508_);
v___x_1510_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1511_ = lean_string_append(v___x_1509_, v___x_1510_);
v___x_1512_ = lean_string_append(v___x_1511_, v___y_1502_);
lean_dec_ref(v___y_1502_);
v___x_1513_ = 3;
v___x_1514_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set_uint8(v___x_1514_, sizeof(void*)*1, v___x_1513_);
v___x_1515_ = lean_array_get_size(v_a_1497_);
v___x_1516_ = lean_array_push(v_a_1497_, v___x_1514_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set_tag(v___x_1499_, 1);
lean_ctor_set(v___x_1499_, 1, v___x_1516_);
lean_ctor_set(v___x_1499_, 0, v___x_1515_);
v___x_1518_ = v___x_1499_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1515_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
v_resetjp_1521_:
{
lean_object* v_kind_1524_; uint8_t v___x_1525_; 
v_kind_1524_ = lean_ctor_get(v_snd_1520_, 1);
v___x_1525_ = lean_name_eq(v_kind_1524_, v_name_1493_);
if (v___x_1525_ == 0)
{
uint8_t v___x_1526_; 
lean_inc(v_kind_1524_);
lean_del_object(v___x_1522_);
lean_dec(v_snd_1520_);
v___x_1526_ = l_Lean_Name_isAnonymous(v_kind_1524_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1527_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1528_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1524_, v___x_1494_);
v___x_1529_ = lean_string_append(v___x_1527_, v___x_1528_);
lean_dec_ref(v___x_1528_);
v___x_1530_ = lean_string_append(v___x_1529_, v___x_1527_);
v___y_1502_ = v___x_1530_;
goto v___jp_1501_;
}
else
{
lean_object* v___x_1531_; 
lean_dec(v_kind_1524_);
v___x_1531_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1502_ = v___x_1531_;
goto v___jp_1501_;
}
}
else
{
lean_object* v___x_1533_; 
lean_del_object(v___x_1499_);
lean_dec_ref(v_self_1485_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 1, v_a_1497_);
lean_ctor_set(v___x_1522_, 0, v_snd_1520_);
v___x_1533_ = v___x_1522_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_snd_1520_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v_a_1497_);
v___x_1533_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
return v___x_1533_;
}
}
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref(v_self_1485_);
v_a_1538_ = lean_ctor_get(v___x_1495_, 0);
v_a_1539_ = lean_ctor_get(v___x_1495_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1495_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_inc(v_a_1538_);
lean_dec(v___x_1495_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1538_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* v_defaultPkg_1547_, lean_object* v_self_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1547_, v_self_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec(v_a_1550_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* v___x_1557_, size_t v_sz_1558_, size_t v_i_1559_, lean_object* v_bs_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
uint8_t v___x_1568_; 
v___x_1568_ = lean_usize_dec_lt(v_i_1559_, v_sz_1558_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; 
lean_dec_ref(v___y_1561_);
lean_dec_ref(v___x_1557_);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_bs_1560_);
lean_ctor_set(v___x_1569_, 1, v___y_1566_);
return v___x_1569_;
}
else
{
lean_object* v_v_1570_; lean_object* v___x_1571_; lean_object* v_bs_x27_1572_; lean_object* v___x_1573_; 
v_v_1570_ = lean_array_uget(v_bs_1560_, v_i_1559_);
v___x_1571_ = lean_unsigned_to_nat(0u);
v_bs_x27_1572_ = lean_array_uset(v_bs_1560_, v_i_1559_, v___x_1571_);
lean_inc_ref(v___y_1561_);
lean_inc_ref(v___x_1557_);
v___x_1573_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1557_, v_v_1570_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v_a_1575_; size_t v___x_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
v_a_1575_ = lean_ctor_get(v___x_1573_, 1);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1573_, 2);
v___x_1576_ = ((size_t)1ULL);
v___x_1577_ = lean_usize_add(v_i_1559_, v___x_1576_);
v___x_1578_ = lean_array_uset(v_bs_x27_1572_, v_i_1559_, v_a_1574_);
v_i_1559_ = v___x_1577_;
v_bs_1560_ = v___x_1578_;
v___y_1566_ = v_a_1575_;
goto _start;
}
else
{
lean_object* v_a_1580_; lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_dec_ref(v_bs_x27_1572_);
lean_dec_ref(v___y_1561_);
lean_dec_ref(v___x_1557_);
v_a_1580_ = lean_ctor_get(v___x_1573_, 0);
v_a_1581_ = lean_ctor_get(v___x_1573_, 1);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1573_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_inc(v_a_1580_);
lean_dec(v___x_1573_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1580_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* v___x_1589_, lean_object* v_sz_1590_, lean_object* v_i_1591_, lean_object* v_bs_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
size_t v_sz_boxed_1600_; size_t v_i_boxed_1601_; lean_object* v_res_1602_; 
v_sz_boxed_1600_ = lean_unbox_usize(v_sz_1590_);
lean_dec(v_sz_1590_);
v_i_boxed_1601_ = lean_unbox_usize(v_i_1591_);
lean_dec(v_i_1591_);
v_res_1602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1589_, v_sz_boxed_1600_, v_i_boxed_1601_, v_bs_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec(v___y_1594_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(lean_object* v_a_1603_, lean_object* v_as_1604_, size_t v_i_1605_, size_t v_stop_1606_, lean_object* v_b_1607_, lean_object* v___y_1608_){
_start:
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_usize_dec_eq(v_i_1605_, v_stop_1606_);
if (v___x_1610_ == 0)
{
lean_object* v_log_1611_; uint8_t v_action_1612_; uint8_t v_wantsRebuild_1613_; uint8_t v_canceled_1614_; lean_object* v_trace_1615_; lean_object* v_buildTime_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_log_1611_ = lean_ctor_get(v___y_1608_, 0);
v_action_1612_ = lean_ctor_get_uint8(v___y_1608_, sizeof(void*)*3);
v_wantsRebuild_1613_ = lean_ctor_get_uint8(v___y_1608_, sizeof(void*)*3 + 1);
v_canceled_1614_ = lean_ctor_get_uint8(v___y_1608_, sizeof(void*)*3 + 2);
v_trace_1615_ = lean_ctor_get(v___y_1608_, 1);
v_buildTime_1616_ = lean_ctor_get(v___y_1608_, 2);
v___x_1617_ = lean_array_uget_borrowed(v_as_1604_, v_i_1605_);
v___x_1618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
lean_inc(v___x_1617_);
v___x_1619_ = lean_string_append(v___x_1617_, v___x_1618_);
v___x_1620_ = lean_io_prim_handle_put_str(v_a_1603_, v___x_1619_);
lean_dec_ref(v___x_1619_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; size_t v___x_1622_; size_t v___x_1623_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v___x_1622_ = ((size_t)1ULL);
v___x_1623_ = lean_usize_add(v_i_1605_, v___x_1622_);
v_i_1605_ = v___x_1623_;
v_b_1607_ = v_a_1621_;
goto _start;
}
else
{
lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1638_; 
lean_inc(v_buildTime_1616_);
lean_inc_ref(v_trace_1615_);
lean_inc_ref(v_log_1611_);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___y_1608_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; lean_object* v_unused_1640_; lean_object* v_unused_1641_; 
v_unused_1639_ = lean_ctor_get(v___y_1608_, 2);
lean_dec(v_unused_1639_);
v_unused_1640_ = lean_ctor_get(v___y_1608_, 1);
lean_dec(v_unused_1640_);
v_unused_1641_ = lean_ctor_get(v___y_1608_, 0);
lean_dec(v_unused_1641_);
v___x_1626_ = v___y_1608_;
v_isShared_1627_ = v_isSharedCheck_1638_;
goto v_resetjp_1625_;
}
else
{
lean_dec(v___y_1608_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1638_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v_a_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
v_a_1628_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1620_, 1);
v___x_1629_ = lean_io_error_to_string(v_a_1628_);
v___x_1630_ = 3;
v___x_1631_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*1, v___x_1630_);
v___x_1632_ = lean_array_get_size(v_log_1611_);
v___x_1633_ = lean_array_push(v_log_1611_, v___x_1631_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1633_);
v___x_1635_ = v___x_1626_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_trace_1615_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_buildTime_1616_);
lean_ctor_set_uint8(v_reuseFailAlloc_1637_, sizeof(void*)*3, v_action_1612_);
lean_ctor_set_uint8(v_reuseFailAlloc_1637_, sizeof(void*)*3 + 1, v_wantsRebuild_1613_);
lean_ctor_set_uint8(v_reuseFailAlloc_1637_, sizeof(void*)*3 + 2, v_canceled_1614_);
v___x_1635_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1632_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
return v___x_1636_;
}
}
}
}
else
{
lean_object* v___x_1642_; 
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_b_1607_);
lean_ctor_set(v___x_1642_, 1, v___y_1608_);
return v___x_1642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(lean_object* v_a_1643_, lean_object* v_as_1644_, lean_object* v_i_1645_, lean_object* v_stop_1646_, lean_object* v_b_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
size_t v_i_boxed_1650_; size_t v_stop_boxed_1651_; lean_object* v_res_1652_; 
v_i_boxed_1650_ = lean_unbox_usize(v_i_1645_);
lean_dec(v_i_1645_);
v_stop_boxed_1651_ = lean_unbox_usize(v_stop_1646_);
lean_dec(v_stop_1646_);
v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1643_, v_as_1644_, v_i_boxed_1650_, v_stop_boxed_1651_, v_b_1647_, v___y_1648_);
lean_dec_ref(v_as_1644_);
lean_dec(v_a_1643_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(uint8_t v_bootstrap_1653_, lean_object* v___y_1654_, lean_object* v_oFiles_1655_, uint8_t v_shouldExport_1656_, uint8_t v___x_1657_, size_t v___x_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
if (v_bootstrap_1653_ == 0)
{
lean_object* v_toContext_1666_; lean_object* v_lakeEnv_1667_; lean_object* v_lean_1668_; lean_object* v_log_1669_; uint8_t v_action_1670_; uint8_t v_wantsRebuild_1671_; uint8_t v_canceled_1672_; lean_object* v_trace_1673_; lean_object* v_buildTime_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1704_; 
v_toContext_1666_ = lean_ctor_get(v___y_1663_, 1);
v_lakeEnv_1667_ = lean_ctor_get(v_toContext_1666_, 0);
v_lean_1668_ = lean_ctor_get(v_lakeEnv_1667_, 1);
v_log_1669_ = lean_ctor_get(v___y_1664_, 0);
v_action_1670_ = lean_ctor_get_uint8(v___y_1664_, sizeof(void*)*3);
v_wantsRebuild_1671_ = lean_ctor_get_uint8(v___y_1664_, sizeof(void*)*3 + 1);
v_canceled_1672_ = lean_ctor_get_uint8(v___y_1664_, sizeof(void*)*3 + 2);
v_trace_1673_ = lean_ctor_get(v___y_1664_, 1);
v_buildTime_1674_ = lean_ctor_get(v___y_1664_, 2);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___y_1664_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1676_ = v___y_1664_;
v_isShared_1677_ = v_isSharedCheck_1704_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_buildTime_1674_);
lean_inc(v_trace_1673_);
lean_inc(v_log_1669_);
lean_dec(v___y_1664_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1704_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v_ar_1678_; lean_object* v___x_1679_; 
v_ar_1678_ = lean_ctor_get(v_lean_1668_, 13);
lean_inc_ref(v_ar_1678_);
v___x_1679_ = l_Lake_compileStaticLib(v___y_1654_, v_oFiles_1655_, v_ar_1678_, v_bootstrap_1653_, v_log_1669_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1691_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_a_1681_ = lean_ctor_get(v___x_1679_, 1);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1683_ = v___x_1679_;
v_isShared_1684_ = v_isSharedCheck_1691_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1691_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 0, v_a_1681_);
v___x_1686_ = v___x_1676_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1681_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_trace_1673_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_buildTime_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, sizeof(void*)*3, v_action_1670_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, sizeof(void*)*3 + 1, v_wantsRebuild_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1690_, sizeof(void*)*3 + 2, v_canceled_1672_);
v___x_1686_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1688_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 1, v___x_1686_);
v___x_1688_ = v___x_1683_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1680_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1703_; 
v_a_1692_ = lean_ctor_get(v___x_1679_, 0);
v_a_1693_ = lean_ctor_get(v___x_1679_, 1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1695_ = v___x_1679_;
v_isShared_1696_ = v_isSharedCheck_1703_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_inc(v_a_1692_);
lean_dec(v___x_1679_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1703_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 0, v_a_1693_);
v___x_1698_ = v___x_1676_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1693_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_trace_1673_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v_buildTime_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*3, v_action_1670_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*3 + 1, v_wantsRebuild_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*3 + 2, v_canceled_1672_);
v___x_1698_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
lean_object* v___x_1700_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 1, v___x_1698_);
v___x_1700_ = v___x_1695_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1692_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
}
else
{
uint8_t v___x_1705_; 
v___x_1705_ = l_System_Platform_isOSX;
if (v___x_1705_ == 0)
{
uint8_t v___x_1706_; 
v___x_1706_ = l_System_Platform_isWindows;
if (v___x_1706_ == 0)
{
lean_object* v_toContext_1707_; lean_object* v_lakeEnv_1708_; lean_object* v_lean_1709_; lean_object* v_log_1710_; uint8_t v_action_1711_; uint8_t v_wantsRebuild_1712_; uint8_t v_canceled_1713_; lean_object* v_trace_1714_; lean_object* v_buildTime_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1745_; 
v_toContext_1707_ = lean_ctor_get(v___y_1663_, 1);
v_lakeEnv_1708_ = lean_ctor_get(v_toContext_1707_, 0);
v_lean_1709_ = lean_ctor_get(v_lakeEnv_1708_, 1);
v_log_1710_ = lean_ctor_get(v___y_1664_, 0);
v_action_1711_ = lean_ctor_get_uint8(v___y_1664_, sizeof(void*)*3);
v_wantsRebuild_1712_ = lean_ctor_get_uint8(v___y_1664_, sizeof(void*)*3 + 1);
v_canceled_1713_ = lean_ctor_get_uint8(v___y_1664_, sizeof(void*)*3 + 2);
v_trace_1714_ = lean_ctor_get(v___y_1664_, 1);
v_buildTime_1715_ = lean_ctor_get(v___y_1664_, 2);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___y_1664_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1717_ = v___y_1664_;
v_isShared_1718_ = v_isSharedCheck_1745_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_buildTime_1715_);
lean_inc(v_trace_1714_);
lean_inc(v_log_1710_);
lean_dec(v___y_1664_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1745_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v_ar_1719_; lean_object* v___x_1720_; 
v_ar_1719_ = lean_ctor_get(v_lean_1709_, 13);
lean_inc_ref(v_ar_1719_);
v___x_1720_ = l_Lake_compileStaticLib(v___y_1654_, v_oFiles_1655_, v_ar_1719_, v___x_1706_, v_log_1710_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1732_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
v_a_1722_ = lean_ctor_get(v___x_1720_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1724_ = v___x_1720_;
v_isShared_1725_ = v_isSharedCheck_1732_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_inc(v_a_1721_);
lean_dec(v___x_1720_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1732_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v_a_1722_);
v___x_1727_ = v___x_1717_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1722_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_trace_1714_);
lean_ctor_set(v_reuseFailAlloc_1731_, 2, v_buildTime_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1731_, sizeof(void*)*3, v_action_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1731_, sizeof(void*)*3 + 1, v_wantsRebuild_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1731_, sizeof(void*)*3 + 2, v_canceled_1713_);
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
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_1733_; lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1744_; 
v_a_1733_ = lean_ctor_get(v___x_1720_, 0);
v_a_1734_ = lean_ctor_get(v___x_1720_, 1);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1736_ = v___x_1720_;
v_isShared_1737_ = v_isSharedCheck_1744_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_inc(v_a_1733_);
lean_dec(v___x_1720_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1744_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v_a_1734_);
v___x_1739_ = v___x_1717_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1734_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_trace_1714_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_buildTime_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*3, v_action_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*3 + 1, v_wantsRebuild_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1743_, sizeof(void*)*3 + 2, v_canceled_1713_);
v___x_1739_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1741_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v___x_1739_);
v___x_1741_ = v___x_1736_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1733_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1746_; lean_object* v_lakeEnv_1747_; lean_object* v_lean_1748_; lean_object* v_log_1749_; uint8_t v_action_1750_; uint8_t v_wantsRebuild_1751_; uint8_t v_canceled_1752_; lean_object* v_trace_1753_; lean_object* v_buildTime_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1784_; 
v_toContext_1746_ = lean_ctor_get(v___y_1663_, 1);
v_lakeEnv_1747_ = lean_ctor_get(v_toContext_1746_, 0);
v_lean_1748_ = lean_ctor_get(v_lakeEnv_1747_, 1);
v_log_1749_ = lean_ctor_get(v___y_1664_, 0);
v_action_1750_ = lean_ctor_get_uint8(v___y_1664_, sizeof(void*)*3);
v_wantsRebuild_1751_ = lean_ctor_get_uint8(v___y_1664_, sizeof(void*)*3 + 1);
v_canceled_1752_ = lean_ctor_get_uint8(v___y_1664_, sizeof(void*)*3 + 2);
v_trace_1753_ = lean_ctor_get(v___y_1664_, 1);
v_buildTime_1754_ = lean_ctor_get(v___y_1664_, 2);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___y_1664_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1756_ = v___y_1664_;
v_isShared_1757_ = v_isSharedCheck_1784_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_buildTime_1754_);
lean_inc(v_trace_1753_);
lean_inc(v_log_1749_);
lean_dec(v___y_1664_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1784_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_ar_1758_; lean_object* v___x_1759_; 
v_ar_1758_ = lean_ctor_get(v_lean_1748_, 13);
lean_inc_ref(v_ar_1758_);
v___x_1759_ = l_Lake_compileStaticLib(v___y_1654_, v_oFiles_1655_, v_ar_1758_, v_shouldExport_1656_, v_log_1749_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1771_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_a_1761_ = lean_ctor_get(v___x_1759_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1763_ = v___x_1759_;
v_isShared_1764_ = v_isSharedCheck_1771_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1771_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v_a_1761_);
v___x_1766_ = v___x_1756_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1761_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_trace_1753_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_buildTime_1754_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*3, v_action_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*3 + 1, v_wantsRebuild_1751_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*3 + 2, v_canceled_1752_);
v___x_1766_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1768_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 1, v___x_1766_);
v___x_1768_ = v___x_1763_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1760_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1783_; 
v_a_1772_ = lean_ctor_get(v___x_1759_, 0);
v_a_1773_ = lean_ctor_get(v___x_1759_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1775_ = v___x_1759_;
v_isShared_1776_ = v_isSharedCheck_1783_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_inc(v_a_1772_);
lean_dec(v___x_1759_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1783_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v_a_1773_);
v___x_1778_ = v___x_1756_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1773_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_trace_1753_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v_buildTime_1754_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*3, v_action_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*3 + 1, v_wantsRebuild_1751_);
lean_ctor_set_uint8(v_reuseFailAlloc_1782_, sizeof(void*)*3 + 2, v_canceled_1752_);
v___x_1778_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1780_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 1, v___x_1778_);
v___x_1780_ = v___x_1775_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1772_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v___x_1778_);
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
}
}
}
else
{
lean_object* v_log_1785_; uint8_t v_action_1786_; uint8_t v_wantsRebuild_1787_; uint8_t v_canceled_1788_; lean_object* v_trace_1789_; lean_object* v_buildTime_1790_; lean_object* v___x_1791_; 
v_log_1785_ = lean_ctor_get(v___y_1664_, 0);
v_action_1786_ = lean_ctor_get_uint8(v___y_1664_, sizeof(void*)*3);
v_wantsRebuild_1787_ = lean_ctor_get_uint8(v___y_1664_, sizeof(void*)*3 + 1);
v_canceled_1788_ = lean_ctor_get_uint8(v___y_1664_, sizeof(void*)*3 + 2);
v_trace_1789_ = lean_ctor_get(v___y_1664_, 1);
v_buildTime_1790_ = lean_ctor_get(v___y_1664_, 2);
lean_inc_ref(v___y_1654_);
v___x_1791_ = l_Lake_createParentDirs(v___y_1654_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v_a_1795_; uint8_t v___x_1844_; lean_object* v___x_1845_; 
lean_dec_ref_known(v___x_1791_, 1);
v___x_1792_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1654_);
v___x_1793_ = l_System_FilePath_addExtension(v___y_1654_, v___x_1792_);
v___x_1844_ = 1;
v___x_1845_ = lean_io_prim_handle_mk(v___x_1793_, v___x_1844_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = lean_array_get_size(v_oFiles_1655_);
v___x_1849_ = lean_nat_dec_lt(v___x_1847_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_dec(v_a_1846_);
lean_dec_ref(v_oFiles_1655_);
v_a_1795_ = v___y_1664_;
goto v___jp_1794_;
}
else
{
lean_object* v___x_1850_; size_t v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = lean_box(0);
v___x_1851_ = lean_usize_of_nat(v___x_1848_);
v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1846_, v_oFiles_1655_, v___x_1658_, v___x_1851_, v___x_1850_, v___y_1664_);
lean_dec_ref(v_oFiles_1655_);
lean_dec(v_a_1846_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 1);
lean_inc(v_a_1853_);
lean_dec_ref_known(v___x_1852_, 2);
v_a_1795_ = v_a_1853_;
goto v___jp_1794_;
}
else
{
lean_dec_ref(v___x_1793_);
lean_dec_ref(v___y_1654_);
return v___x_1852_;
}
}
}
else
{
lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1867_; 
lean_inc(v_buildTime_1790_);
lean_inc_ref(v_trace_1789_);
lean_inc_ref(v_log_1785_);
lean_dec_ref(v___x_1793_);
lean_dec_ref(v_oFiles_1655_);
lean_dec_ref(v___y_1654_);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___y_1664_);
if (v_isSharedCheck_1867_ == 0)
{
lean_object* v_unused_1868_; lean_object* v_unused_1869_; lean_object* v_unused_1870_; 
v_unused_1868_ = lean_ctor_get(v___y_1664_, 2);
lean_dec(v_unused_1868_);
v_unused_1869_ = lean_ctor_get(v___y_1664_, 1);
lean_dec(v_unused_1869_);
v_unused_1870_ = lean_ctor_get(v___y_1664_, 0);
lean_dec(v_unused_1870_);
v___x_1855_ = v___y_1664_;
v_isShared_1856_ = v_isSharedCheck_1867_;
goto v_resetjp_1854_;
}
else
{
lean_dec(v___y_1664_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1867_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_a_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
v_a_1857_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1857_);
lean_dec_ref_known(v___x_1845_, 1);
v___x_1858_ = lean_io_error_to_string(v_a_1857_);
v___x_1859_ = 3;
v___x_1860_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set_uint8(v___x_1860_, sizeof(void*)*1, v___x_1859_);
v___x_1861_ = lean_array_get_size(v_log_1785_);
v___x_1862_ = lean_array_push(v_log_1785_, v___x_1860_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v___x_1862_);
v___x_1864_ = v___x_1855_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1862_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_trace_1789_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_buildTime_1790_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*3, v_action_1786_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*3 + 1, v_wantsRebuild_1787_);
lean_ctor_set_uint8(v_reuseFailAlloc_1866_, sizeof(void*)*3 + 2, v_canceled_1788_);
v___x_1864_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; 
v___x_1865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1861_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
return v___x_1865_;
}
}
}
v___jp_1794_:
{
lean_object* v___x_1796_; lean_object* v_log_1797_; uint8_t v_action_1798_; uint8_t v_wantsRebuild_1799_; uint8_t v_canceled_1800_; lean_object* v_trace_1801_; lean_object* v_buildTime_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1843_; 
v___x_1796_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1797_ = lean_ctor_get(v_a_1795_, 0);
v_action_1798_ = lean_ctor_get_uint8(v_a_1795_, sizeof(void*)*3);
v_wantsRebuild_1799_ = lean_ctor_get_uint8(v_a_1795_, sizeof(void*)*3 + 1);
v_canceled_1800_ = lean_ctor_get_uint8(v_a_1795_, sizeof(void*)*3 + 2);
v_trace_1801_ = lean_ctor_get(v_a_1795_, 1);
v_buildTime_1802_ = lean_ctor_get(v_a_1795_, 2);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_a_1795_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1804_ = v_a_1795_;
v_isShared_1805_ = v_isSharedCheck_1843_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_buildTime_1802_);
lean_inc(v_trace_1801_);
lean_inc(v_log_1797_);
lean_dec(v_a_1795_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1843_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1806_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1807_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1808_ = lean_unsigned_to_nat(5u);
v___x_1809_ = lean_mk_empty_array_with_capacity(v___x_1808_);
lean_dec_ref(v___x_1809_);
v___x_1810_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1811_ = lean_array_push(v___x_1810_, v___y_1654_);
v___x_1812_ = lean_array_push(v___x_1811_, v___x_1807_);
v___x_1813_ = lean_array_push(v___x_1812_, v___x_1793_);
v___x_1814_ = lean_box(0);
v___x_1815_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1816_ = 0;
v___x_1817_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1817_, 0, v___x_1796_);
lean_ctor_set(v___x_1817_, 1, v___x_1806_);
lean_ctor_set(v___x_1817_, 2, v___x_1813_);
lean_ctor_set(v___x_1817_, 3, v___x_1814_);
lean_ctor_set(v___x_1817_, 4, v___x_1815_);
lean_ctor_set_uint8(v___x_1817_, sizeof(void*)*5, v___x_1657_);
lean_ctor_set_uint8(v___x_1817_, sizeof(void*)*5 + 1, v___x_1816_);
v___x_1818_ = l_Lake_proc(v___x_1817_, v___x_1816_, v___x_1814_, v_log_1797_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1830_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_a_1820_ = lean_ctor_get(v___x_1818_, 1);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1822_ = v___x_1818_;
v_isShared_1823_ = v_isSharedCheck_1830_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1830_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v_a_1820_);
v___x_1825_ = v___x_1804_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1820_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_trace_1801_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_buildTime_1802_);
lean_ctor_set_uint8(v_reuseFailAlloc_1829_, sizeof(void*)*3, v_action_1798_);
lean_ctor_set_uint8(v_reuseFailAlloc_1829_, sizeof(void*)*3 + 1, v_wantsRebuild_1799_);
lean_ctor_set_uint8(v_reuseFailAlloc_1829_, sizeof(void*)*3 + 2, v_canceled_1800_);
v___x_1825_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1827_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 1, v___x_1825_);
v___x_1827_ = v___x_1822_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1819_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1842_; 
v_a_1831_ = lean_ctor_get(v___x_1818_, 0);
v_a_1832_ = lean_ctor_get(v___x_1818_, 1);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1834_ = v___x_1818_;
v_isShared_1835_ = v_isSharedCheck_1842_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_inc(v_a_1831_);
lean_dec(v___x_1818_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1842_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v_a_1832_);
v___x_1837_ = v___x_1804_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1832_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_trace_1801_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_buildTime_1802_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*3, v_action_1798_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*3 + 1, v_wantsRebuild_1799_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*3 + 2, v_canceled_1800_);
v___x_1837_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1839_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v___x_1837_);
v___x_1839_ = v___x_1834_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1831_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1884_; 
lean_inc(v_buildTime_1790_);
lean_inc_ref(v_trace_1789_);
lean_inc_ref(v_log_1785_);
lean_dec_ref(v_oFiles_1655_);
lean_dec_ref(v___y_1654_);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___y_1664_);
if (v_isSharedCheck_1884_ == 0)
{
lean_object* v_unused_1885_; lean_object* v_unused_1886_; lean_object* v_unused_1887_; 
v_unused_1885_ = lean_ctor_get(v___y_1664_, 2);
lean_dec(v_unused_1885_);
v_unused_1886_ = lean_ctor_get(v___y_1664_, 1);
lean_dec(v_unused_1886_);
v_unused_1887_ = lean_ctor_get(v___y_1664_, 0);
lean_dec(v_unused_1887_);
v___x_1872_ = v___y_1664_;
v_isShared_1873_ = v_isSharedCheck_1884_;
goto v_resetjp_1871_;
}
else
{
lean_dec(v___y_1664_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1884_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v_a_1874_; lean_object* v___x_1875_; uint8_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1881_; 
v_a_1874_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1791_, 1);
v___x_1875_ = lean_io_error_to_string(v_a_1874_);
v___x_1876_ = 3;
v___x_1877_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set_uint8(v___x_1877_, sizeof(void*)*1, v___x_1876_);
v___x_1878_ = lean_array_get_size(v_log_1785_);
v___x_1879_ = lean_array_push(v_log_1785_, v___x_1877_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1879_);
v___x_1881_ = v___x_1872_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_trace_1789_);
lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_buildTime_1790_);
lean_ctor_set_uint8(v_reuseFailAlloc_1883_, sizeof(void*)*3, v_action_1786_);
lean_ctor_set_uint8(v_reuseFailAlloc_1883_, sizeof(void*)*3 + 1, v_wantsRebuild_1787_);
lean_ctor_set_uint8(v_reuseFailAlloc_1883_, sizeof(void*)*3 + 2, v_canceled_1788_);
v___x_1881_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1878_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
return v___x_1882_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object* v_bootstrap_1888_, lean_object* v___y_1889_, lean_object* v_oFiles_1890_, lean_object* v_shouldExport_1891_, lean_object* v___x_1892_, lean_object* v___x_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
uint8_t v_bootstrap_boxed_1901_; uint8_t v_shouldExport_boxed_1902_; uint8_t v___x_5833__boxed_1903_; size_t v___x_5834__boxed_1904_; lean_object* v_res_1905_; 
v_bootstrap_boxed_1901_ = lean_unbox(v_bootstrap_1888_);
v_shouldExport_boxed_1902_ = lean_unbox(v_shouldExport_1891_);
v___x_5833__boxed_1903_ = lean_unbox(v___x_1892_);
v___x_5834__boxed_1904_ = lean_unbox_usize(v___x_1893_);
lean_dec(v___x_1893_);
v_res_1905_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_boxed_1901_, v___y_1889_, v_oFiles_1890_, v_shouldExport_boxed_1902_, v___x_5833__boxed_1903_, v___x_5834__boxed_1904_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t v_bootstrap_1906_, lean_object* v___y_1907_, uint8_t v_shouldExport_1908_, uint8_t v___x_1909_, size_t v___x_1910_, lean_object* v_oFiles_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___y_1923_; uint8_t v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1919_ = lean_box(v_bootstrap_1906_);
v___x_1920_ = lean_box(v_shouldExport_1908_);
v___x_1921_ = lean_box(v___x_1909_);
v___x_1922_ = lean_box_usize(v___x_1910_);
lean_inc_ref(v___y_1907_);
v___y_1923_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed), 13, 6);
lean_closure_set(v___y_1923_, 0, v___x_1919_);
lean_closure_set(v___y_1923_, 1, v___y_1907_);
lean_closure_set(v___y_1923_, 2, v_oFiles_1911_);
lean_closure_set(v___y_1923_, 3, v___x_1920_);
lean_closure_set(v___y_1923_, 4, v___x_1921_);
lean_closure_set(v___y_1923_, 5, v___x_1922_);
v___x_1924_ = 0;
v___x_1925_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1926_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1907_, v___y_1923_, v___x_1924_, v___x_1925_, v___x_1909_, v___x_1924_, v___x_1924_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1936_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
v_a_1928_ = lean_ctor_get(v___x_1926_, 1);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1930_ = v___x_1926_;
v_isShared_1931_ = v_isSharedCheck_1936_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_inc(v_a_1927_);
lean_dec(v___x_1926_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1936_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v_path_1932_; lean_object* v___x_1934_; 
v_path_1932_ = lean_ctor_get(v_a_1927_, 1);
lean_inc_ref(v_path_1932_);
lean_dec(v_a_1927_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v_path_1932_);
v___x_1934_ = v___x_1930_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_path_1932_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_a_1928_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
v_a_1937_ = lean_ctor_get(v___x_1926_, 0);
v_a_1938_ = lean_ctor_get(v___x_1926_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1926_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_inc(v_a_1937_);
lean_dec(v___x_1926_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1937_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* v_bootstrap_1946_, lean_object* v___y_1947_, lean_object* v_shouldExport_1948_, lean_object* v___x_1949_, lean_object* v___x_1950_, lean_object* v_oFiles_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
uint8_t v_bootstrap_boxed_1959_; uint8_t v_shouldExport_boxed_1960_; uint8_t v___x_6233__boxed_1961_; size_t v___x_6234__boxed_1962_; lean_object* v_res_1963_; 
v_bootstrap_boxed_1959_ = lean_unbox(v_bootstrap_1946_);
v_shouldExport_boxed_1960_ = lean_unbox(v_shouldExport_1948_);
v___x_6233__boxed_1961_ = lean_unbox(v___x_1949_);
v___x_6234__boxed_1962_ = lean_unbox_usize(v___x_1950_);
lean_dec(v___x_1950_);
v_res_1963_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_boxed_1959_, v___y_1947_, v_shouldExport_boxed_1960_, v___x_6233__boxed_1961_, v___x_6234__boxed_1962_, v_oFiles_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec(v___y_1953_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* v_a_1964_, size_t v_sz_1965_, size_t v_i_1966_, lean_object* v_bs_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
uint8_t v___x_1975_; 
v___x_1975_ = lean_usize_dec_lt(v_i_1966_, v_sz_1965_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; 
lean_dec_ref(v___y_1968_);
lean_dec_ref(v_a_1964_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_bs_1967_);
lean_ctor_set(v___x_1976_, 1, v___y_1973_);
return v___x_1976_;
}
else
{
lean_object* v_v_1977_; lean_object* v___x_1978_; lean_object* v_bs_x27_1979_; lean_object* v___x_1980_; 
v_v_1977_ = lean_array_uget(v_bs_1967_, v_i_1966_);
v___x_1978_ = lean_unsigned_to_nat(0u);
v_bs_x27_1979_ = lean_array_uset(v_bs_1967_, v_i_1966_, v___x_1978_);
lean_inc_ref(v___y_1968_);
lean_inc_ref(v_a_1964_);
v___x_1980_ = l_Lake_ModuleFacet_fetch___redArg(v_v_1977_, v_a_1964_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v_a_1982_; size_t v___x_1983_; size_t v___x_1984_; lean_object* v___x_1985_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
v_a_1982_ = lean_ctor_get(v___x_1980_, 1);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1980_, 2);
v___x_1983_ = ((size_t)1ULL);
v___x_1984_ = lean_usize_add(v_i_1966_, v___x_1983_);
v___x_1985_ = lean_array_uset(v_bs_x27_1979_, v_i_1966_, v_a_1981_);
v_i_1966_ = v___x_1984_;
v_bs_1967_ = v___x_1985_;
v___y_1973_ = v_a_1982_;
goto _start;
}
else
{
lean_object* v_a_1987_; lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v_bs_x27_1979_);
lean_dec_ref(v___y_1968_);
lean_dec_ref(v_a_1964_);
v_a_1987_ = lean_ctor_get(v___x_1980_, 0);
v_a_1988_ = lean_ctor_get(v___x_1980_, 1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1980_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_inc(v_a_1987_);
lean_dec(v___x_1980_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1987_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object* v_a_1996_, lean_object* v_sz_1997_, lean_object* v_i_1998_, lean_object* v_bs_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
size_t v_sz_boxed_2007_; size_t v_i_boxed_2008_; lean_object* v_res_2009_; 
v_sz_boxed_2007_ = lean_unbox_usize(v_sz_1997_);
lean_dec(v_sz_1997_);
v_i_boxed_2008_ = lean_unbox_usize(v_i_1998_);
lean_dec(v_i_1998_);
v_res_2009_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_1996_, v_sz_boxed_2007_, v_i_boxed_2008_, v_bs_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec(v___y_2001_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(uint8_t v_shouldExport_2010_, lean_object* v_as_2011_, size_t v_i_2012_, size_t v_stop_2013_, lean_object* v_b_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
uint8_t v___x_2022_; 
v___x_2022_ = lean_usize_dec_eq(v_i_2012_, v_stop_2013_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; lean_object* v_lib_2024_; lean_object* v_config_2025_; lean_object* v_nativeFacets_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; size_t v_sz_2029_; size_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2023_ = lean_array_uget_borrowed(v_as_2011_, v_i_2012_);
v_lib_2024_ = lean_ctor_get(v___x_2023_, 0);
v_config_2025_ = lean_ctor_get(v_lib_2024_, 2);
v_nativeFacets_2026_ = lean_ctor_get(v_config_2025_, 8);
v___x_2027_ = lean_box(v_shouldExport_2010_);
lean_inc_ref(v_nativeFacets_2026_);
v___x_2028_ = lean_apply_1(v_nativeFacets_2026_, v___x_2027_);
v_sz_2029_ = lean_array_size(v___x_2028_);
v___x_2030_ = ((size_t)0ULL);
lean_inc_ref(v___y_2015_);
lean_inc(v___x_2023_);
v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2023_, v_sz_2029_, v___x_2030_, v___x_2028_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v_a_2033_; lean_object* v___x_2034_; size_t v___x_2035_; size_t v___x_2036_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
v_a_2033_ = lean_ctor_get(v___x_2031_, 1);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2031_, 2);
v___x_2034_ = l_Array_append___redArg(v_b_2014_, v_a_2032_);
lean_dec(v_a_2032_);
v___x_2035_ = ((size_t)1ULL);
v___x_2036_ = lean_usize_add(v_i_2012_, v___x_2035_);
v_i_2012_ = v___x_2036_;
v_b_2014_ = v___x_2034_;
v___y_2020_ = v_a_2033_;
goto _start;
}
else
{
lean_dec_ref(v___y_2015_);
lean_dec_ref(v_b_2014_);
return v___x_2031_;
}
}
else
{
lean_object* v___x_2038_; 
lean_dec_ref(v___y_2015_);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v_b_2014_);
lean_ctor_set(v___x_2038_, 1, v___y_2020_);
return v___x_2038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(lean_object* v_shouldExport_2039_, lean_object* v_as_2040_, lean_object* v_i_2041_, lean_object* v_stop_2042_, lean_object* v_b_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
uint8_t v_shouldExport_boxed_2051_; size_t v_i_boxed_2052_; size_t v_stop_boxed_2053_; lean_object* v_res_2054_; 
v_shouldExport_boxed_2051_ = lean_unbox(v_shouldExport_2039_);
v_i_boxed_2052_ = lean_unbox_usize(v_i_2041_);
lean_dec(v_i_2041_);
v_stop_boxed_2053_ = lean_unbox_usize(v_stop_2042_);
lean_dec(v_stop_2042_);
v_res_2054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_boxed_2051_, v_as_2040_, v_i_boxed_2052_, v_stop_boxed_2053_, v_b_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v_as_2040_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object* v_config_2055_, lean_object* v_config_2056_, uint8_t v_shouldExport_2057_, uint8_t v___x_2058_, lean_object* v___x_2059_, lean_object* v___x_2060_, lean_object* v_pkg_2061_, lean_object* v_dir_2062_, lean_object* v_self_2063_, lean_object* v___x_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
uint8_t v___y_2073_; size_t v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v_a_2093_; lean_object* v_a_2094_; lean_object* v___x_2136_; 
lean_inc_ref(v___y_2065_);
lean_inc_ref(v___y_2069_);
lean_inc(v___y_2068_);
lean_inc(v___y_2067_);
lean_inc(v___x_2060_);
v___x_2136_ = lean_apply_7(v___y_2065_, v___x_2064_, v___x_2060_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, lean_box(0));
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
v_a_2138_ = lean_ctor_get(v___x_2136_, 1);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2136_, 2);
v___x_2139_ = l_Lake_Job_await___redArg(v_a_2137_, v_a_2138_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v_a_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
v_a_2141_ = lean_ctor_get(v___x_2139_, 1);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2139_, 2);
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_2144_ = lean_array_get_size(v_a_2140_);
v___x_2145_ = lean_nat_dec_lt(v___x_2142_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_dec(v_a_2140_);
v_a_2093_ = v___x_2143_;
v_a_2094_ = v_a_2141_;
goto v___jp_2092_;
}
else
{
size_t v___x_2146_; size_t v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = ((size_t)0ULL);
v___x_2147_ = lean_usize_of_nat(v___x_2144_);
lean_inc_ref(v___y_2065_);
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2057_, v_a_2140_, v___x_2146_, v___x_2147_, v___x_2143_, v___y_2065_, v___x_2060_, v___y_2067_, v___y_2068_, v___y_2069_, v_a_2141_);
lean_dec(v_a_2140_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v_a_2150_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
v_a_2150_ = lean_ctor_get(v___x_2148_, 1);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2148_, 2);
v_a_2093_ = v_a_2149_;
v_a_2094_ = v_a_2150_;
goto v___jp_2092_;
}
else
{
lean_object* v_a_2151_; lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec_ref(v___y_2065_);
lean_dec_ref(v_self_2063_);
lean_dec_ref(v_dir_2062_);
lean_dec_ref(v_pkg_2061_);
lean_dec(v___x_2060_);
lean_dec(v___x_2059_);
lean_dec_ref(v_config_2055_);
v_a_2151_ = lean_ctor_get(v___x_2148_, 0);
v_a_2152_ = lean_ctor_get(v___x_2148_, 1);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2148_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_inc(v_a_2151_);
lean_dec(v___x_2148_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2151_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_dec_ref(v___y_2065_);
lean_dec_ref(v_self_2063_);
lean_dec_ref(v_dir_2062_);
lean_dec_ref(v_pkg_2061_);
lean_dec(v___x_2060_);
lean_dec(v___x_2059_);
lean_dec_ref(v_config_2055_);
v_a_2160_ = lean_ctor_get(v___x_2139_, 0);
v_a_2161_ = lean_ctor_get(v___x_2139_, 1);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2139_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_inc(v_a_2160_);
lean_dec(v___x_2139_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2160_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec_ref(v___y_2065_);
lean_dec_ref(v_self_2063_);
lean_dec_ref(v_dir_2062_);
lean_dec_ref(v_pkg_2061_);
lean_dec(v___x_2060_);
lean_dec(v___x_2059_);
lean_dec_ref(v_config_2055_);
v_a_2169_ = lean_ctor_get(v___x_2136_, 0);
v_a_2170_ = lean_ctor_get(v___x_2136_, 1);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2136_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_inc(v_a_2169_);
lean_dec(v___x_2136_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2169_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
v___jp_2072_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___f_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2079_ = lean_box(v___y_2073_);
v___x_2080_ = lean_box(v_shouldExport_2057_);
v___x_2081_ = lean_box(v___x_2058_);
v___x_2082_ = lean_box_usize(v___y_2074_);
v___f_2083_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2083_, 0, v___x_2079_);
lean_closure_set(v___f_2083_, 1, v___y_2078_);
lean_closure_set(v___f_2083_, 2, v___x_2080_);
lean_closure_set(v___f_2083_, 3, v___x_2081_);
lean_closure_set(v___f_2083_, 4, v___x_2082_);
v___x_2084_ = l_Array_append___redArg(v___y_2077_, v___y_2076_);
lean_dec_ref(v___y_2076_);
v___x_2085_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_2086_ = l_Lake_Job_collectArray___redArg(v___x_2084_, v___x_2085_);
lean_dec_ref(v___x_2084_);
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = 0;
v___x_2089_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_2090_ = l_Lake_Job_mapM___redArg(v___x_2059_, v___x_2086_, v___f_2083_, v___x_2087_, v___x_2088_, v___y_2065_, v___x_2060_, v___y_2067_, v___y_2068_, v___y_2069_, v___x_2089_);
lean_dec(v___x_2060_);
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
lean_ctor_set(v___x_2091_, 1, v___y_2075_);
return v___x_2091_;
}
v___jp_2092_:
{
lean_object* v_toLeanConfig_2095_; lean_object* v_toLeanConfig_2096_; uint8_t v_bootstrap_2097_; lean_object* v_buildDir_2098_; lean_object* v_nativeLibDir_2099_; lean_object* v_moreLinkObjs_2100_; lean_object* v_moreLinkObjs_2101_; lean_object* v___x_2102_; size_t v_sz_2103_; size_t v___x_2104_; lean_object* v___x_2105_; 
v_toLeanConfig_2095_ = lean_ctor_get(v_config_2055_, 1);
lean_inc_ref(v_toLeanConfig_2095_);
v_toLeanConfig_2096_ = lean_ctor_get(v_config_2056_, 0);
v_bootstrap_2097_ = lean_ctor_get_uint8(v_config_2055_, sizeof(void*)*28);
v_buildDir_2098_ = lean_ctor_get(v_config_2055_, 5);
lean_inc_ref(v_buildDir_2098_);
v_nativeLibDir_2099_ = lean_ctor_get(v_config_2055_, 7);
lean_inc_ref(v_nativeLibDir_2099_);
lean_dec_ref(v_config_2055_);
v_moreLinkObjs_2100_ = lean_ctor_get(v_toLeanConfig_2095_, 6);
lean_inc_ref(v_moreLinkObjs_2100_);
lean_dec_ref(v_toLeanConfig_2095_);
v_moreLinkObjs_2101_ = lean_ctor_get(v_toLeanConfig_2096_, 6);
v___x_2102_ = l_Array_append___redArg(v_moreLinkObjs_2100_, v_moreLinkObjs_2101_);
v_sz_2103_ = lean_array_size(v___x_2102_);
v___x_2104_ = ((size_t)0ULL);
lean_inc_ref(v___y_2065_);
v___x_2105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_2061_, v_sz_2103_, v___x_2104_, v___x_2102_, v___y_2065_, v___x_2060_, v___y_2067_, v___y_2068_, v___y_2069_, v_a_2094_);
if (lean_obj_tag(v___x_2105_) == 0)
{
if (v_shouldExport_2057_ == 0)
{
lean_object* v_a_2106_; lean_object* v_a_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
v_a_2107_ = lean_ctor_get(v___x_2105_, 1);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2105_, 2);
v___x_2108_ = l_System_FilePath_normalize(v_buildDir_2098_);
v___x_2109_ = l_Lake_joinRelative(v_dir_2062_, v___x_2108_);
v___x_2110_ = l_System_FilePath_normalize(v_nativeLibDir_2099_);
v___x_2111_ = l_Lake_joinRelative(v___x_2109_, v___x_2110_);
v___x_2112_ = l_Lake_LeanLib_libName(v_self_2063_);
v___x_2113_ = l_Lake_nameToStaticLib(v___x_2112_, v_shouldExport_2057_);
v___x_2114_ = l_Lake_joinRelative(v___x_2111_, v___x_2113_);
v___y_2073_ = v_bootstrap_2097_;
v___y_2074_ = v___x_2104_;
v___y_2075_ = v_a_2107_;
v___y_2076_ = v_a_2106_;
v___y_2077_ = v_a_2093_;
v___y_2078_ = v___x_2114_;
goto v___jp_2072_;
}
else
{
lean_object* v_a_2115_; lean_object* v_a_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v_a_2115_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2115_);
v_a_2116_ = lean_ctor_get(v___x_2105_, 1);
lean_inc(v_a_2116_);
lean_dec_ref_known(v___x_2105_, 2);
v___x_2117_ = l_System_FilePath_normalize(v_buildDir_2098_);
v___x_2118_ = l_Lake_joinRelative(v_dir_2062_, v___x_2117_);
v___x_2119_ = l_System_FilePath_normalize(v_nativeLibDir_2099_);
v___x_2120_ = l_Lake_joinRelative(v___x_2118_, v___x_2119_);
v___x_2121_ = l_Lake_LeanLib_libName(v_self_2063_);
v___x_2122_ = 0;
v___x_2123_ = l_Lake_nameToStaticLib(v___x_2121_, v___x_2122_);
v___x_2124_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_2125_ = l_System_FilePath_addExtension(v___x_2123_, v___x_2124_);
v___x_2126_ = l_Lake_joinRelative(v___x_2120_, v___x_2125_);
v___y_2073_ = v_bootstrap_2097_;
v___y_2074_ = v___x_2104_;
v___y_2075_ = v_a_2116_;
v___y_2076_ = v_a_2115_;
v___y_2077_ = v_a_2093_;
v___y_2078_ = v___x_2126_;
goto v___jp_2072_;
}
}
else
{
lean_object* v_a_2127_; lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec_ref(v_nativeLibDir_2099_);
lean_dec_ref(v_buildDir_2098_);
lean_dec_ref(v_a_2093_);
lean_dec_ref(v___y_2065_);
lean_dec_ref(v_self_2063_);
lean_dec_ref(v_dir_2062_);
lean_dec(v___x_2060_);
lean_dec(v___x_2059_);
v_a_2127_ = lean_ctor_get(v___x_2105_, 0);
v_a_2128_ = lean_ctor_get(v___x_2105_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2105_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_inc(v_a_2127_);
lean_dec(v___x_2105_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2127_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(lean_object** _args){
lean_object* v_config_2178_ = _args[0];
lean_object* v_config_2179_ = _args[1];
lean_object* v_shouldExport_2180_ = _args[2];
lean_object* v___x_2181_ = _args[3];
lean_object* v___x_2182_ = _args[4];
lean_object* v___x_2183_ = _args[5];
lean_object* v_pkg_2184_ = _args[6];
lean_object* v_dir_2185_ = _args[7];
lean_object* v_self_2186_ = _args[8];
lean_object* v___x_2187_ = _args[9];
lean_object* v___y_2188_ = _args[10];
lean_object* v___y_2189_ = _args[11];
lean_object* v___y_2190_ = _args[12];
lean_object* v___y_2191_ = _args[13];
lean_object* v___y_2192_ = _args[14];
lean_object* v___y_2193_ = _args[15];
lean_object* v___y_2194_ = _args[16];
_start:
{
uint8_t v_shouldExport_boxed_2195_; uint8_t v___x_6431__boxed_2196_; lean_object* v_res_2197_; 
v_shouldExport_boxed_2195_ = lean_unbox(v_shouldExport_2180_);
v___x_6431__boxed_2196_ = lean_unbox(v___x_2181_);
v_res_2197_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v_config_2178_, v_config_2179_, v_shouldExport_boxed_2195_, v___x_6431__boxed_2196_, v___x_2182_, v___x_2183_, v_pkg_2184_, v_dir_2185_, v_self_2186_, v___x_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec(v_config_2179_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object* v___y_2198_, lean_object* v_self_2199_, uint8_t v_shouldExport_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v_toBuildConfig_2207_; lean_object* v_registeredJobs_2208_; uint8_t v_verbosity_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; uint8_t v___x_2214_; lean_object* v___y_2216_; 
v_toBuildConfig_2207_ = lean_ctor_get(v_a_2204_, 0);
v_registeredJobs_2208_ = lean_ctor_get(v_a_2204_, 4);
v_verbosity_2209_ = lean_ctor_get_uint8(v_toBuildConfig_2207_, sizeof(void*)*5 + 4);
v___x_2210_ = l_Lake_instDataKindFilePath;
v___x_2211_ = l_Lake_Verbosity_ctorIdx(v_verbosity_2209_);
v___x_2212_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0);
v___x_2213_ = lean_nat_dec_eq(v___x_2211_, v___x_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = 1;
if (v___x_2213_ == 0)
{
lean_object* v___x_2261_; 
v___x_2261_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_2216_ = v___x_2261_;
goto v___jp_2215_;
}
else
{
if (v_shouldExport_2200_ == 0)
{
lean_object* v___x_2262_; 
v___x_2262_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_2216_ = v___x_2262_;
goto v___jp_2215_;
}
else
{
lean_object* v___x_2263_; 
v___x_2263_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3));
v___y_2216_ = v___x_2263_;
goto v___jp_2215_;
}
}
v___jp_2215_:
{
lean_object* v_pkg_2217_; lean_object* v_name_2218_; lean_object* v_config_2219_; lean_object* v_keyName_2220_; lean_object* v_dir_2221_; lean_object* v_config_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___f_2234_; uint8_t v___x_2235_; lean_object* v___x_2236_; 
v_pkg_2217_ = lean_ctor_get(v_self_2199_, 0);
lean_inc_ref_n(v_pkg_2217_, 2);
v_name_2218_ = lean_ctor_get(v_self_2199_, 1);
v_config_2219_ = lean_ctor_get(v_self_2199_, 2);
lean_inc(v_config_2219_);
v_keyName_2220_ = lean_ctor_get(v_pkg_2217_, 2);
v_dir_2221_ = lean_ctor_get(v_pkg_2217_, 4);
lean_inc_ref(v_dir_2221_);
v_config_2222_ = lean_ctor_get(v_pkg_2217_, 6);
lean_inc_ref(v_config_2222_);
lean_inc_n(v_name_2218_, 2);
v___x_2223_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2218_, v___x_2214_);
v___x_2224_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___x_2225_ = lean_string_append(v___x_2223_, v___x_2224_);
v___x_2226_ = lean_string_append(v___x_2225_, v___y_2216_);
v___x_2227_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_2220_);
v___x_2228_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2228_, 0, v_keyName_2220_);
lean_ctor_set(v___x_2228_, 1, v_name_2218_);
v___x_2229_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_2199_);
v___x_2230_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2228_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
lean_ctor_set(v___x_2230_, 2, v_self_2199_);
lean_ctor_set(v___x_2230_, 3, v___x_2227_);
v___x_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2231_, 0, v_pkg_2217_);
v___x_2232_ = lean_box(v_shouldExport_2200_);
v___x_2233_ = lean_box(v___x_2214_);
v___f_2234_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed), 17, 10);
lean_closure_set(v___f_2234_, 0, v_config_2222_);
lean_closure_set(v___f_2234_, 1, v_config_2219_);
lean_closure_set(v___f_2234_, 2, v___x_2232_);
lean_closure_set(v___f_2234_, 3, v___x_2233_);
lean_closure_set(v___f_2234_, 4, v___x_2210_);
lean_closure_set(v___f_2234_, 5, v___x_2231_);
lean_closure_set(v___f_2234_, 6, v_pkg_2217_);
lean_closure_set(v___f_2234_, 7, v_dir_2221_);
lean_closure_set(v___f_2234_, 8, v_self_2199_);
lean_closure_set(v___f_2234_, 9, v___x_2230_);
v___x_2235_ = 0;
v___x_2236_ = l_Lake_ensureJob___redArg(v___x_2210_, v___f_2234_, v___y_2198_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2260_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
v_a_2238_ = lean_ctor_get(v___x_2236_, 1);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2240_ = v___x_2236_;
v_isShared_2241_ = v_isSharedCheck_2260_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_inc(v_a_2237_);
lean_dec(v___x_2236_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2260_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v_task_2242_; lean_object* v_kind_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2258_; 
v_task_2242_ = lean_ctor_get(v_a_2237_, 0);
v_kind_2243_ = lean_ctor_get(v_a_2237_, 1);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_a_2237_);
if (v_isSharedCheck_2258_ == 0)
{
lean_object* v_unused_2259_; 
v_unused_2259_ = lean_ctor_get(v_a_2237_, 2);
lean_dec(v_unused_2259_);
v___x_2245_ = v_a_2237_;
v_isShared_2246_ = v_isSharedCheck_2258_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_kind_2243_);
lean_inc(v_task_2242_);
lean_dec(v_a_2237_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2258_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v_job_2248_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 2, v___x_2226_);
v_job_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_task_2242_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_kind_2243_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v___x_2226_);
v_job_2248_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2255_; 
lean_ctor_set_uint8(v_job_2248_, sizeof(void*)*3, v___x_2235_);
v___x_2249_ = lean_st_ref_take(v_registeredJobs_2208_);
lean_inc_ref(v_job_2248_);
v___x_2250_ = l_Lake_Job_toOpaque___redArg(v_job_2248_);
v___x_2251_ = lean_array_push(v___x_2249_, v___x_2250_);
v___x_2252_ = lean_st_ref_put(v_registeredJobs_2208_, v___x_2251_);
v___x_2253_ = l_Lake_Job_renew___redArg(v_job_2248_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2253_);
v___x_2255_ = v___x_2240_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_a_2238_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2226_);
return v___x_2236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* v___y_2264_, lean_object* v_self_2265_, lean_object* v_shouldExport_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
uint8_t v_shouldExport_boxed_2273_; lean_object* v_res_2274_; 
v_shouldExport_boxed_2273_ = lean_unbox(v_shouldExport_2266_);
v_res_2274_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2264_, v_self_2265_, v_shouldExport_boxed_2273_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec(v_a_2268_);
lean_dec(v_a_2267_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* v_x_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
uint8_t v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = 0;
v___x_2284_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2276_, v_x_2275_, v___x_2283_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object* v_x_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec(v___y_2287_);
return v_res_2293_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2296_; uint8_t v___x_2297_; lean_object* v___x_2298_; lean_object* v___f_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___f_2296_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2297_ = 1;
v___x_2298_ = l_Lake_instDataKindFilePath;
v___f_2299_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__0));
v___x_2300_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2301_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
lean_ctor_set(v___x_2301_, 1, v___f_2299_);
lean_ctor_set(v___x_2301_, 2, v___x_2298_);
lean_ctor_set(v___x_2301_, 3, v___f_2296_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*4, v___x_2297_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*4 + 1, v___x_2297_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = lean_obj_once(&l_Lake_LeanLib_staticFacetConfig___closed__2, &l_Lake_LeanLib_staticFacetConfig___closed__2_once, _init_l_Lake_LeanLib_staticFacetConfig___closed__2);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(lean_object* v_a_2303_, lean_object* v_as_2304_, size_t v_i_2305_, size_t v_stop_2306_, lean_object* v_b_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2303_, v_as_2304_, v_i_2305_, v_stop_2306_, v_b_2307_, v___y_2313_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* v_a_2316_, lean_object* v_as_2317_, lean_object* v_i_2318_, lean_object* v_stop_2319_, lean_object* v_b_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
size_t v_i_boxed_2328_; size_t v_stop_boxed_2329_; lean_object* v_res_2330_; 
v_i_boxed_2328_ = lean_unbox_usize(v_i_2318_);
lean_dec(v_i_2318_);
v_stop_boxed_2329_ = lean_unbox_usize(v_stop_2319_);
lean_dec(v_stop_2319_);
v_res_2330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_2316_, v_as_2317_, v_i_boxed_2328_, v_stop_boxed_2329_, v_b_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec_ref(v_as_2317_);
lean_dec(v_a_2316_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* v_x_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
uint8_t v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = 1;
v___x_2340_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2332_, v_x_2331_, v___x_2339_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object* v_x_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec(v___y_2343_);
return v_res_2349_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2351_; uint8_t v___x_2352_; lean_object* v___x_2353_; lean_object* v___f_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___f_2351_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2352_ = 1;
v___x_2353_ = l_Lake_instDataKindFilePath;
v___f_2354_ = ((lean_object*)(l_Lake_LeanLib_staticExportFacetConfig___closed__0));
v___x_2355_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2356_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
lean_ctor_set(v___x_2356_, 1, v___f_2354_);
lean_ctor_set(v___x_2356_, 2, v___x_2353_);
lean_ctor_set(v___x_2356_, 3, v___f_2351_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*4, v___x_2352_);
lean_ctor_set_uint8(v___x_2356_, sizeof(void*)*4 + 1, v___x_2352_);
return v___x_2356_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig(void){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_obj_once(&l_Lake_LeanLib_staticExportFacetConfig___closed__1, &l_Lake_LeanLib_staticExportFacetConfig___closed__1_once, _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1);
return v___x_2357_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0(void){
_start:
{
uint8_t v___x_2358_; lean_object* v_name_2359_; lean_object* v___x_2360_; 
v___x_2358_ = 1;
v_name_2359_ = l_Lake_instDataKindDynlib;
v___x_2360_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2359_, v___x_2358_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object* v_defaultPkg_2361_, lean_object* v_self_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v_name_2370_; uint8_t v___x_2371_; lean_object* v___x_2372_; 
v_name_2370_ = l_Lake_instDataKindDynlib;
v___x_2371_ = 1;
lean_inc_ref_n(v_self_2362_, 2);
v___x_2372_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_2361_, v_self_2362_, v_self_2362_, v___x_2371_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2414_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
v_a_2374_ = lean_ctor_get(v___x_2372_, 1);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2376_ = v___x_2372_;
v_isShared_2377_ = v_isSharedCheck_2414_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_inc(v_a_2373_);
lean_dec(v___x_2372_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2414_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___y_2379_; lean_object* v_snd_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2412_; 
v_snd_2397_ = lean_ctor_get(v_a_2373_, 1);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_a_2373_);
if (v_isSharedCheck_2412_ == 0)
{
lean_object* v_unused_2413_; 
v_unused_2413_ = lean_ctor_get(v_a_2373_, 0);
lean_dec(v_unused_2413_);
v___x_2399_ = v_a_2373_;
v_isShared_2400_ = v_isSharedCheck_2412_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_snd_2397_);
lean_dec(v_a_2373_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2412_;
goto v_resetjp_2398_;
}
v___jp_2378_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2380_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_2381_ = l_Lake_PartialBuildKey_toString(v_self_2362_);
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
v___x_2392_ = lean_array_get_size(v_a_2374_);
v___x_2393_ = lean_array_push(v_a_2374_, v___x_2391_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set_tag(v___x_2376_, 1);
lean_ctor_set(v___x_2376_, 1, v___x_2393_);
lean_ctor_set(v___x_2376_, 0, v___x_2392_);
v___x_2395_ = v___x_2376_;
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
v_resetjp_2398_:
{
lean_object* v_kind_2401_; uint8_t v___x_2402_; 
v_kind_2401_ = lean_ctor_get(v_snd_2397_, 1);
v___x_2402_ = lean_name_eq(v_kind_2401_, v_name_2370_);
if (v___x_2402_ == 0)
{
uint8_t v___x_2403_; 
lean_inc(v_kind_2401_);
lean_del_object(v___x_2399_);
lean_dec(v_snd_2397_);
v___x_2403_ = l_Lean_Name_isAnonymous(v_kind_2401_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2404_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_2405_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2401_, v___x_2371_);
v___x_2406_ = lean_string_append(v___x_2404_, v___x_2405_);
lean_dec_ref(v___x_2405_);
v___x_2407_ = lean_string_append(v___x_2406_, v___x_2404_);
v___y_2379_ = v___x_2407_;
goto v___jp_2378_;
}
else
{
lean_object* v___x_2408_; 
lean_dec(v_kind_2401_);
v___x_2408_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_2379_ = v___x_2408_;
goto v___jp_2378_;
}
}
else
{
lean_object* v___x_2410_; 
lean_del_object(v___x_2376_);
lean_dec_ref(v_self_2362_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 1, v_a_2374_);
lean_ctor_set(v___x_2399_, 0, v_snd_2397_);
v___x_2410_ = v___x_2399_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_snd_2397_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v_a_2374_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec_ref(v_self_2362_);
v_a_2415_ = lean_ctor_get(v___x_2372_, 0);
v_a_2416_ = lean_ctor_get(v___x_2372_, 1);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2372_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_inc(v_a_2415_);
lean_dec(v___x_2372_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2415_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* v_defaultPkg_2424_, lean_object* v_self_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_2424_, v_self_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec(v_a_2427_);
return v_res_2433_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0));
v___x_2437_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
lean_ctor_set(v___x_2438_, 1, v___x_2436_);
return v___x_2438_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5(void){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object* v___x_2440_, lean_object* v_as_2441_, size_t v_i_2442_, size_t v_stop_2443_, lean_object* v_b_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
uint8_t v___x_2452_; 
v___x_2452_ = lean_usize_dec_eq(v_i_2442_, v_stop_2443_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_array_uget_borrowed(v_as_2441_, v_i_2442_);
lean_inc_ref(v___y_2445_);
lean_inc(v___x_2453_);
lean_inc_ref(v___x_2440_);
v___x_2454_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_2440_, v___x_2453_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v_a_2456_; lean_object* v___x_2457_; size_t v___x_2458_; size_t v___x_2459_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
v_a_2456_ = lean_ctor_get(v___x_2454_, 1);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2454_, 2);
v___x_2457_ = lean_array_push(v_b_2444_, v_a_2455_);
v___x_2458_ = ((size_t)1ULL);
v___x_2459_ = lean_usize_add(v_i_2442_, v___x_2458_);
v_i_2442_ = v___x_2459_;
v_b_2444_ = v___x_2457_;
v___y_2450_ = v_a_2456_;
goto _start;
}
else
{
lean_object* v_a_2461_; lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec_ref(v___y_2445_);
lean_dec_ref(v_b_2444_);
lean_dec_ref(v___x_2440_);
v_a_2461_ = lean_ctor_get(v___x_2454_, 0);
v_a_2462_ = lean_ctor_get(v___x_2454_, 1);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2454_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_inc(v_a_2461_);
lean_dec(v___x_2454_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2461_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
else
{
lean_object* v___x_2470_; 
lean_dec_ref(v___y_2445_);
lean_dec_ref(v___x_2440_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v_b_2444_);
lean_ctor_set(v___x_2470_, 1, v___y_2450_);
return v___x_2470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* v___x_2471_, lean_object* v_as_2472_, lean_object* v_i_2473_, lean_object* v_stop_2474_, lean_object* v_b_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
size_t v_i_boxed_2483_; size_t v_stop_boxed_2484_; lean_object* v_res_2485_; 
v_i_boxed_2483_ = lean_unbox_usize(v_i_2473_);
lean_dec(v_i_2473_);
v_stop_boxed_2484_ = lean_unbox_usize(v_stop_2474_);
lean_dec(v_stop_2474_);
v_res_2485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_2471_, v_as_2472_, v_i_boxed_2483_, v_stop_boxed_2484_, v_b_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v_as_2472_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object* v_self_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v_toHashSet_2488_; lean_object* v_toArray_2489_; uint8_t v___x_2490_; 
v_toHashSet_2488_ = lean_ctor_get(v_self_2486_, 0);
v_toArray_2489_ = lean_ctor_get(v_self_2486_, 1);
v___x_2490_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_2488_, v_a_2487_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2500_; 
lean_inc_ref(v_toArray_2489_);
lean_inc_ref(v_toHashSet_2488_);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_self_2486_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; lean_object* v_unused_2502_; 
v_unused_2501_ = lean_ctor_get(v_self_2486_, 1);
lean_dec(v_unused_2501_);
v_unused_2502_ = lean_ctor_get(v_self_2486_, 0);
lean_dec(v_unused_2502_);
v___x_2492_ = v_self_2486_;
v_isShared_2493_ = v_isSharedCheck_2500_;
goto v_resetjp_2491_;
}
else
{
lean_dec(v_self_2486_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2500_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2498_; 
v___x_2494_ = lean_box(0);
lean_inc_ref(v_a_2487_);
v___x_2495_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_toHashSet_2488_, v_a_2487_, v___x_2494_);
v___x_2496_ = lean_array_push(v_toArray_2489_, v_a_2487_);
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 1, v___x_2496_);
lean_ctor_set(v___x_2492_, 0, v___x_2495_);
v___x_2498_ = v___x_2492_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2495_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v___x_2496_);
v___x_2498_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2497_;
}
v_reusejp_2497_:
{
return v___x_2498_;
}
}
}
else
{
lean_dec_ref(v_a_2487_);
return v_self_2486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object* v_as_2503_, size_t v_i_2504_, size_t v_stop_2505_, lean_object* v_b_2506_){
_start:
{
uint8_t v___x_2507_; 
v___x_2507_ = lean_usize_dec_eq(v_i_2504_, v_stop_2505_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; size_t v___x_2510_; size_t v___x_2511_; 
v___x_2508_ = lean_array_uget_borrowed(v_as_2503_, v_i_2504_);
lean_inc(v___x_2508_);
v___x_2509_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_2506_, v___x_2508_);
v___x_2510_ = ((size_t)1ULL);
v___x_2511_ = lean_usize_add(v_i_2504_, v___x_2510_);
v_i_2504_ = v___x_2511_;
v_b_2506_ = v___x_2509_;
goto _start;
}
else
{
return v_b_2506_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object* v_as_2513_, lean_object* v_i_2514_, lean_object* v_stop_2515_, lean_object* v_b_2516_){
_start:
{
size_t v_i_boxed_2517_; size_t v_stop_boxed_2518_; lean_object* v_res_2519_; 
v_i_boxed_2517_ = lean_unbox_usize(v_i_2514_);
lean_dec(v_i_2514_);
v_stop_boxed_2518_ = lean_unbox_usize(v_stop_2515_);
lean_dec(v_stop_2515_);
v_res_2519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_2513_, v_i_boxed_2517_, v_stop_boxed_2518_, v_b_2516_);
lean_dec_ref(v_as_2513_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object* v_self_2520_, lean_object* v_arr_2521_){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v___x_2522_ = lean_unsigned_to_nat(0u);
v___x_2523_ = lean_array_get_size(v_arr_2521_);
v___x_2524_ = lean_nat_dec_lt(v___x_2522_, v___x_2523_);
if (v___x_2524_ == 0)
{
return v_self_2520_;
}
else
{
size_t v___x_2525_; size_t v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = ((size_t)0ULL);
v___x_2526_ = lean_usize_of_nat(v___x_2523_);
v___x_2527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2521_, v___x_2525_, v___x_2526_, v_self_2520_);
return v___x_2527_;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(lean_object* v_self_2837_, lean_object* v_dir_2838_, lean_object* v___x_2839_, lean_object* v_targetDecls_2840_, lean_object* v_pkg_2841_, lean_object* v_name_2842_, lean_object* v___x_2843_, lean_object* v_config_2844_, lean_object* v_config_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_a_2854_; lean_object* v_a_2855_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v_a_2865_; lean_object* v_a_2866_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v_a_2926_; lean_object* v_a_2927_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v_snd_2959_; lean_object* v_a_2960_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v_a_2982_; lean_object* v_a_2983_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___x_3022_; 
lean_inc_ref(v___y_2846_);
lean_inc_ref(v___y_2850_);
lean_inc(v___y_2849_);
lean_inc(v___y_2848_);
lean_inc(v___x_2839_);
v___x_3022_ = lean_apply_7(v___y_2846_, v___x_2843_, v___x_2839_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, lean_box(0));
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v_a_3024_; lean_object* v___x_3025_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
v_a_3024_ = lean_ctor_get(v___x_3022_, 1);
lean_inc(v_a_3024_);
lean_dec_ref_known(v___x_3022_, 2);
v___x_3025_ = l_Lake_Job_await___redArg(v_a_3023_, v_a_3024_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v_a_3027_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v_a_3038_; lean_object* v_a_3039_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v_a_3073_; lean_object* v_a_3074_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
v_a_3027_ = lean_ctor_get(v___x_3025_, 1);
lean_inc(v_a_3027_);
lean_dec_ref_known(v___x_3025_, 2);
v___x_3098_ = lean_unsigned_to_nat(0u);
v___x_3099_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_3100_ = lean_array_get_size(v_a_3026_);
v___x_3101_ = lean_nat_dec_lt(v___x_3098_, v___x_3100_);
if (v___x_3101_ == 0)
{
v_a_3073_ = v___x_3099_;
v_a_3074_ = v_a_3027_;
goto v___jp_3072_;
}
else
{
size_t v___x_3102_; size_t v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = ((size_t)0ULL);
v___x_3103_ = lean_usize_of_nat(v___x_3100_);
lean_inc_ref(v___y_2846_);
v___x_3104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3026_, v___x_3102_, v___x_3103_, v___x_3099_, v___y_2846_, v___x_2839_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_3027_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v_a_3106_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
v_a_3106_ = lean_ctor_get(v___x_3104_, 1);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3104_, 2);
v_a_3073_ = v_a_3105_;
v_a_3074_ = v_a_3106_;
goto v___jp_3072_;
}
else
{
lean_object* v_a_3107_; lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec(v_a_3026_);
lean_dec_ref(v___y_2846_);
lean_dec_ref(v_config_2844_);
lean_dec(v_name_2842_);
lean_dec_ref(v_pkg_2841_);
lean_dec(v___x_2839_);
lean_dec_ref(v_dir_2838_);
lean_dec_ref(v_self_2837_);
v_a_3107_ = lean_ctor_get(v___x_3104_, 0);
v_a_3108_ = lean_ctor_get(v___x_3104_, 1);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3104_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_inc(v_a_3107_);
lean_dec(v___x_3104_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3107_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
v___jp_3028_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3040_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
v___x_3041_ = lean_array_get_size(v_a_3026_);
v___x_3042_ = lean_nat_dec_lt(v___y_3035_, v___x_3041_);
if (v___x_3042_ == 0)
{
lean_dec(v_a_3026_);
v___y_2972_ = v___y_3029_;
v___y_2973_ = v___y_3030_;
v___y_2974_ = v___y_3031_;
v___y_2975_ = v___y_3032_;
v___y_2976_ = v___y_3033_;
v___y_2977_ = v_a_3038_;
v___y_2978_ = v___y_3034_;
v___y_2979_ = v___y_3035_;
v___y_2980_ = v___y_3036_;
v___y_2981_ = v___y_3037_;
v_a_2982_ = v___x_3040_;
v_a_2983_ = v_a_3039_;
goto v___jp_2971_;
}
else
{
uint8_t v___x_3043_; 
v___x_3043_ = lean_nat_dec_le(v___x_3041_, v___x_3041_);
if (v___x_3043_ == 0)
{
if (v___x_3042_ == 0)
{
lean_dec(v_a_3026_);
v___y_2972_ = v___y_3029_;
v___y_2973_ = v___y_3030_;
v___y_2974_ = v___y_3031_;
v___y_2975_ = v___y_3032_;
v___y_2976_ = v___y_3033_;
v___y_2977_ = v_a_3038_;
v___y_2978_ = v___y_3034_;
v___y_2979_ = v___y_3035_;
v___y_2980_ = v___y_3036_;
v___y_2981_ = v___y_3037_;
v_a_2982_ = v___x_3040_;
v_a_2983_ = v_a_3039_;
goto v___jp_2971_;
}
else
{
size_t v___x_3044_; size_t v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = ((size_t)0ULL);
v___x_3045_ = lean_usize_of_nat(v___x_3041_);
lean_inc_ref(v___y_2846_);
v___x_3046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3026_, v___x_3044_, v___x_3045_, v___x_3040_, v___y_2846_, v___x_2839_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_3039_);
lean_dec(v_a_3026_);
v___y_3007_ = v___y_3030_;
v___y_3008_ = v___y_3029_;
v___y_3009_ = v___y_3031_;
v___y_3010_ = v___y_3032_;
v___y_3011_ = v___y_3033_;
v___y_3012_ = v___y_3034_;
v___y_3013_ = v_a_3038_;
v___y_3014_ = v___y_3035_;
v___y_3015_ = v___y_3036_;
v___y_3016_ = v___y_3037_;
v___y_3017_ = v___x_3046_;
goto v___jp_3006_;
}
}
else
{
size_t v___x_3047_; size_t v___x_3048_; lean_object* v___x_3049_; 
v___x_3047_ = ((size_t)0ULL);
v___x_3048_ = lean_usize_of_nat(v___x_3041_);
lean_inc_ref(v___y_2846_);
v___x_3049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3026_, v___x_3047_, v___x_3048_, v___x_3040_, v___y_2846_, v___x_2839_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_3039_);
lean_dec(v_a_3026_);
v___y_3007_ = v___y_3030_;
v___y_3008_ = v___y_3029_;
v___y_3009_ = v___y_3031_;
v___y_3010_ = v___y_3032_;
v___y_3011_ = v___y_3033_;
v___y_3012_ = v___y_3034_;
v___y_3013_ = v_a_3038_;
v___y_3014_ = v___y_3035_;
v___y_3015_ = v___y_3036_;
v___y_3016_ = v___y_3037_;
v___y_3017_ = v___x_3049_;
goto v___jp_3006_;
}
}
}
v___jp_3050_:
{
if (lean_obj_tag(v___y_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v_a_3062_; 
v_a_3061_ = lean_ctor_get(v___y_3060_, 0);
lean_inc(v_a_3061_);
v_a_3062_ = lean_ctor_get(v___y_3060_, 1);
lean_inc(v_a_3062_);
lean_dec_ref_known(v___y_3060_, 2);
v___y_3029_ = v___y_3052_;
v___y_3030_ = v___y_3051_;
v___y_3031_ = v___y_3053_;
v___y_3032_ = v___y_3054_;
v___y_3033_ = v___y_3055_;
v___y_3034_ = v___y_3056_;
v___y_3035_ = v___y_3057_;
v___y_3036_ = v___y_3058_;
v___y_3037_ = v___y_3059_;
v_a_3038_ = v_a_3061_;
v_a_3039_ = v_a_3062_;
goto v___jp_3028_;
}
else
{
lean_object* v_a_3063_; lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec_ref(v___y_3056_);
lean_dec_ref(v___y_3054_);
lean_dec_ref(v___y_3052_);
lean_dec(v_a_3026_);
lean_dec_ref(v___y_2846_);
lean_dec(v_name_2842_);
lean_dec_ref(v_pkg_2841_);
lean_dec(v___x_2839_);
lean_dec_ref(v_dir_2838_);
lean_dec_ref(v_self_2837_);
v_a_3063_ = lean_ctor_get(v___y_3060_, 0);
v_a_3064_ = lean_ctor_get(v___y_3060_, 1);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___y_3060_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___y_3060_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_inc(v_a_3063_);
lean_dec(v___y_3060_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3063_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
v___jp_3072_:
{
lean_object* v_toLeanConfig_3075_; lean_object* v_toLeanConfig_3076_; lean_object* v_buildDir_3077_; lean_object* v_nativeLibDir_3078_; lean_object* v_moreLinkObjs_3079_; lean_object* v_moreLinkLibs_3080_; lean_object* v_moreLinkArgs_3081_; lean_object* v_weakLinkArgs_3082_; lean_object* v_moreLinkObjs_3083_; lean_object* v_moreLinkLibs_3084_; lean_object* v_moreLinkArgs_3085_; lean_object* v_weakLinkArgs_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; 
v_toLeanConfig_3075_ = lean_ctor_get(v_config_2844_, 1);
lean_inc_ref(v_toLeanConfig_3075_);
v_toLeanConfig_3076_ = lean_ctor_get(v_config_2845_, 0);
v_buildDir_3077_ = lean_ctor_get(v_config_2844_, 5);
lean_inc_ref(v_buildDir_3077_);
v_nativeLibDir_3078_ = lean_ctor_get(v_config_2844_, 7);
lean_inc_ref(v_nativeLibDir_3078_);
lean_dec_ref(v_config_2844_);
v_moreLinkObjs_3079_ = lean_ctor_get(v_toLeanConfig_3075_, 6);
lean_inc_ref(v_moreLinkObjs_3079_);
v_moreLinkLibs_3080_ = lean_ctor_get(v_toLeanConfig_3075_, 7);
lean_inc_ref(v_moreLinkLibs_3080_);
v_moreLinkArgs_3081_ = lean_ctor_get(v_toLeanConfig_3075_, 8);
lean_inc_ref(v_moreLinkArgs_3081_);
v_weakLinkArgs_3082_ = lean_ctor_get(v_toLeanConfig_3075_, 9);
lean_inc_ref(v_weakLinkArgs_3082_);
lean_dec_ref(v_toLeanConfig_3075_);
v_moreLinkObjs_3083_ = lean_ctor_get(v_toLeanConfig_3076_, 6);
v_moreLinkLibs_3084_ = lean_ctor_get(v_toLeanConfig_3076_, 7);
v_moreLinkArgs_3085_ = lean_ctor_get(v_toLeanConfig_3076_, 8);
v_weakLinkArgs_3086_ = lean_ctor_get(v_toLeanConfig_3076_, 9);
v___x_3087_ = l_Array_append___redArg(v_moreLinkObjs_3079_, v_moreLinkObjs_3083_);
v___x_3088_ = lean_unsigned_to_nat(0u);
v___x_3089_ = lean_array_get_size(v___x_3087_);
v___x_3090_ = lean_nat_dec_lt(v___x_3088_, v___x_3089_);
if (v___x_3090_ == 0)
{
lean_dec_ref(v___x_3087_);
v___y_3029_ = v_moreLinkLibs_3080_;
v___y_3030_ = v_moreLinkArgs_3085_;
v___y_3031_ = v_weakLinkArgs_3086_;
v___y_3032_ = v_buildDir_3077_;
v___y_3033_ = v_moreLinkLibs_3084_;
v___y_3034_ = v_nativeLibDir_3078_;
v___y_3035_ = v___x_3088_;
v___y_3036_ = v_weakLinkArgs_3082_;
v___y_3037_ = v_moreLinkArgs_3081_;
v_a_3038_ = v_a_3073_;
v_a_3039_ = v_a_3074_;
goto v___jp_3028_;
}
else
{
uint8_t v___x_3091_; 
v___x_3091_ = lean_nat_dec_le(v___x_3089_, v___x_3089_);
if (v___x_3091_ == 0)
{
if (v___x_3090_ == 0)
{
lean_dec_ref(v___x_3087_);
v___y_3029_ = v_moreLinkLibs_3080_;
v___y_3030_ = v_moreLinkArgs_3085_;
v___y_3031_ = v_weakLinkArgs_3086_;
v___y_3032_ = v_buildDir_3077_;
v___y_3033_ = v_moreLinkLibs_3084_;
v___y_3034_ = v_nativeLibDir_3078_;
v___y_3035_ = v___x_3088_;
v___y_3036_ = v_weakLinkArgs_3082_;
v___y_3037_ = v_moreLinkArgs_3081_;
v_a_3038_ = v_a_3073_;
v_a_3039_ = v_a_3074_;
goto v___jp_3028_;
}
else
{
size_t v___x_3092_; size_t v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = ((size_t)0ULL);
v___x_3093_ = lean_usize_of_nat(v___x_3089_);
lean_inc_ref(v___y_2846_);
lean_inc_ref(v_pkg_2841_);
v___x_3094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2841_, v___x_3087_, v___x_3092_, v___x_3093_, v_a_3073_, v___y_2846_, v___x_2839_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_3074_);
lean_dec_ref(v___x_3087_);
v___y_3051_ = v_moreLinkArgs_3085_;
v___y_3052_ = v_moreLinkLibs_3080_;
v___y_3053_ = v_weakLinkArgs_3086_;
v___y_3054_ = v_buildDir_3077_;
v___y_3055_ = v_moreLinkLibs_3084_;
v___y_3056_ = v_nativeLibDir_3078_;
v___y_3057_ = v___x_3088_;
v___y_3058_ = v_weakLinkArgs_3082_;
v___y_3059_ = v_moreLinkArgs_3081_;
v___y_3060_ = v___x_3094_;
goto v___jp_3050_;
}
}
else
{
size_t v___x_3095_; size_t v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = ((size_t)0ULL);
v___x_3096_ = lean_usize_of_nat(v___x_3089_);
lean_inc_ref(v___y_2846_);
lean_inc_ref(v_pkg_2841_);
v___x_3097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2841_, v___x_3087_, v___x_3095_, v___x_3096_, v_a_3073_, v___y_2846_, v___x_2839_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_3074_);
lean_dec_ref(v___x_3087_);
v___y_3051_ = v_moreLinkArgs_3085_;
v___y_3052_ = v_moreLinkLibs_3080_;
v___y_3053_ = v_weakLinkArgs_3086_;
v___y_3054_ = v_buildDir_3077_;
v___y_3055_ = v_moreLinkLibs_3084_;
v___y_3056_ = v_nativeLibDir_3078_;
v___y_3057_ = v___x_3088_;
v___y_3058_ = v_weakLinkArgs_3082_;
v___y_3059_ = v_moreLinkArgs_3081_;
v___y_3060_ = v___x_3097_;
goto v___jp_3050_;
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref(v___y_2846_);
lean_dec_ref(v_config_2844_);
lean_dec(v_name_2842_);
lean_dec_ref(v_pkg_2841_);
lean_dec(v___x_2839_);
lean_dec_ref(v_dir_2838_);
lean_dec_ref(v_self_2837_);
v_a_3116_ = lean_ctor_get(v___x_3025_, 0);
v_a_3117_ = lean_ctor_get(v___x_3025_, 1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3025_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_inc(v_a_3116_);
lean_dec(v___x_3025_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3116_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
else
{
lean_object* v_a_3125_; lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v___y_2846_);
lean_dec_ref(v_config_2844_);
lean_dec(v_name_2842_);
lean_dec_ref(v_pkg_2841_);
lean_dec(v___x_2839_);
lean_dec_ref(v_dir_2838_);
lean_dec_ref(v_self_2837_);
v_a_3125_ = lean_ctor_get(v___x_3022_, 0);
v_a_3126_ = lean_ctor_get(v___x_3022_, 1);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3022_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_inc(v_a_3125_);
lean_dec(v___x_3022_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3125_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
v___jp_2853_:
{
lean_object* v___x_2856_; 
v___x_2856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2856_, 0, v_a_2854_);
lean_ctor_set(v___x_2856_, 1, v_a_2855_);
return v___x_2856_;
}
v___jp_2857_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
lean_inc_ref(v_self_2837_);
v___x_2867_ = l_Lake_LeanLib_libName(v_self_2837_);
v___x_2868_ = l_System_FilePath_normalize(v___y_2860_);
v___x_2869_ = l_Lake_joinRelative(v_dir_2838_, v___x_2868_);
v___x_2870_ = l_System_FilePath_normalize(v___y_2862_);
v___x_2871_ = l_Lake_joinRelative(v___x_2869_, v___x_2870_);
v___x_2872_ = 0;
v___x_2873_ = l_Lake_nameToSharedLib(v___x_2867_, v___x_2872_);
v___x_2874_ = l_Lake_joinRelative(v___x_2871_, v___x_2873_);
v___x_2875_ = l_Array_append___redArg(v___y_2863_, v___y_2859_);
v___x_2876_ = l_Array_append___redArg(v___y_2864_, v___y_2858_);
v___x_2877_ = l_Lake_LeanLib_isPlugin(v_self_2837_);
v___x_2878_ = l_System_Platform_isWindows;
v___x_2879_ = lean_box(0);
v___x_2880_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_2881_ = l_Lake_buildLeanSharedLib(v___x_2867_, v___x_2874_, v___y_2861_, v_a_2865_, v___x_2875_, v___x_2876_, v___x_2877_, v___x_2878_, v___x_2879_, v___y_2846_, v___x_2839_, v___y_2848_, v___y_2849_, v___y_2850_, v___x_2880_);
lean_dec(v___x_2839_);
lean_dec_ref(v___y_2861_);
v___x_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v_a_2866_);
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
v___y_2858_ = v___y_2884_;
v___y_2859_ = v___y_2885_;
v___y_2860_ = v___y_2886_;
v___y_2861_ = v___y_2888_;
v___y_2862_ = v___y_2887_;
v___y_2863_ = v___y_2889_;
v___y_2864_ = v___y_2890_;
v_a_2865_ = v_a_2892_;
v_a_2866_ = v_a_2893_;
goto v___jp_2857_;
}
else
{
lean_object* v_a_2894_; lean_object* v_a_2895_; 
lean_dec_ref(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2846_);
lean_dec(v___x_2839_);
lean_dec_ref(v_dir_2838_);
lean_dec_ref(v_self_2837_);
v_a_2894_ = lean_ctor_get(v___y_2891_, 0);
lean_inc(v_a_2894_);
v_a_2895_ = lean_ctor_get(v___y_2891_, 1);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___y_2891_, 2);
v_a_2854_ = v_a_2894_;
v_a_2855_ = v_a_2895_;
goto v___jp_2853_;
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
v___y_2858_ = v___y_2897_;
v___y_2859_ = v___y_2898_;
v___y_2860_ = v___y_2900_;
v___y_2861_ = v___y_2903_;
v___y_2862_ = v___y_2902_;
v___y_2863_ = v___y_2905_;
v___y_2864_ = v___y_2906_;
v_a_2865_ = v___y_2899_;
v_a_2866_ = v___y_2901_;
goto v___jp_2857_;
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
v___y_2858_ = v___y_2897_;
v___y_2859_ = v___y_2898_;
v___y_2860_ = v___y_2900_;
v___y_2861_ = v___y_2903_;
v___y_2862_ = v___y_2902_;
v___y_2863_ = v___y_2905_;
v___y_2864_ = v___y_2906_;
v_a_2865_ = v___y_2899_;
v_a_2866_ = v___y_2901_;
goto v___jp_2857_;
}
else
{
size_t v___x_2911_; size_t v___x_2912_; lean_object* v___x_2913_; 
v___x_2911_ = ((size_t)0ULL);
v___x_2912_ = lean_usize_of_nat(v___x_2908_);
lean_inc_ref(v___y_2846_);
v___x_2913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2907_, v___x_2911_, v___x_2912_, v___y_2899_, v___y_2846_, v___x_2839_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2901_);
lean_dec_ref(v___y_2907_);
v___y_2884_ = v___y_2897_;
v___y_2885_ = v___y_2898_;
v___y_2886_ = v___y_2900_;
v___y_2887_ = v___y_2902_;
v___y_2888_ = v___y_2903_;
v___y_2889_ = v___y_2905_;
v___y_2890_ = v___y_2906_;
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
v___x_2916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2907_, v___x_2914_, v___x_2915_, v___y_2899_, v___y_2846_, v___x_2839_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2901_);
lean_dec_ref(v___y_2907_);
v___y_2884_ = v___y_2897_;
v___y_2885_ = v___y_2898_;
v___y_2886_ = v___y_2900_;
v___y_2887_ = v___y_2902_;
v___y_2888_ = v___y_2903_;
v___y_2889_ = v___y_2905_;
v___y_2890_ = v___y_2906_;
v___y_2891_ = v___x_2916_;
goto v___jp_2883_;
}
}
}
v___jp_2917_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; uint8_t v___x_2930_; 
v___x_2928_ = lean_mk_empty_array_with_capacity(v___y_2923_);
v___x_2929_ = lean_array_get_size(v_targetDecls_2840_);
v___x_2930_ = lean_nat_dec_lt(v___y_2923_, v___x_2929_);
if (v___x_2930_ == 0)
{
lean_dec_ref(v_pkg_2841_);
v___y_2897_ = v___y_2918_;
v___y_2898_ = v___y_2919_;
v___y_2899_ = v_a_2926_;
v___y_2900_ = v___y_2920_;
v___y_2901_ = v_a_2927_;
v___y_2902_ = v___y_2922_;
v___y_2903_ = v___y_2921_;
v___y_2904_ = v___y_2923_;
v___y_2905_ = v___y_2924_;
v___y_2906_ = v___y_2925_;
v___y_2907_ = v___x_2928_;
goto v___jp_2896_;
}
else
{
size_t v___x_2931_; size_t v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = ((size_t)0ULL);
v___x_2932_ = lean_usize_of_nat(v___x_2929_);
v___x_2933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2841_, v_targetDecls_2840_, v___x_2931_, v___x_2932_, v___x_2928_);
v___y_2897_ = v___y_2918_;
v___y_2898_ = v___y_2919_;
v___y_2899_ = v_a_2926_;
v___y_2900_ = v___y_2920_;
v___y_2901_ = v_a_2927_;
v___y_2902_ = v___y_2922_;
v___y_2903_ = v___y_2921_;
v___y_2904_ = v___y_2923_;
v___y_2905_ = v___y_2924_;
v___y_2906_ = v___y_2925_;
v___y_2907_ = v___x_2933_;
goto v___jp_2896_;
}
}
v___jp_2934_:
{
if (lean_obj_tag(v___y_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v_a_2945_; 
v_a_2944_ = lean_ctor_get(v___y_2943_, 0);
lean_inc(v_a_2944_);
v_a_2945_ = lean_ctor_get(v___y_2943_, 1);
lean_inc(v_a_2945_);
lean_dec_ref_known(v___y_2943_, 2);
v___y_2918_ = v___y_2935_;
v___y_2919_ = v___y_2936_;
v___y_2920_ = v___y_2937_;
v___y_2921_ = v___y_2939_;
v___y_2922_ = v___y_2938_;
v___y_2923_ = v___y_2940_;
v___y_2924_ = v___y_2941_;
v___y_2925_ = v___y_2942_;
v_a_2926_ = v_a_2944_;
v_a_2927_ = v_a_2945_;
goto v___jp_2917_;
}
else
{
lean_object* v_a_2946_; lean_object* v_a_2947_; 
lean_dec_ref(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec_ref(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec_ref(v___y_2846_);
lean_dec_ref(v_pkg_2841_);
lean_dec(v___x_2839_);
lean_dec_ref(v_dir_2838_);
lean_dec_ref(v_self_2837_);
v_a_2946_ = lean_ctor_get(v___y_2943_, 0);
lean_inc(v_a_2946_);
v_a_2947_ = lean_ctor_get(v___y_2943_, 1);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___y_2943_, 2);
v_a_2854_ = v_a_2946_;
v_a_2855_ = v_a_2947_;
goto v___jp_2853_;
}
}
v___jp_2948_:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2961_ = l_Array_append___redArg(v___y_2950_, v___y_2953_);
v___x_2962_ = lean_array_get_size(v___x_2961_);
v___x_2963_ = lean_nat_dec_lt(v___y_2956_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_dec_ref(v___x_2961_);
v___y_2918_ = v___y_2949_;
v___y_2919_ = v___y_2951_;
v___y_2920_ = v___y_2952_;
v___y_2921_ = v___y_2955_;
v___y_2922_ = v___y_2954_;
v___y_2923_ = v___y_2956_;
v___y_2924_ = v___y_2957_;
v___y_2925_ = v___y_2958_;
v_a_2926_ = v_snd_2959_;
v_a_2927_ = v_a_2960_;
goto v___jp_2917_;
}
else
{
uint8_t v___x_2964_; 
v___x_2964_ = lean_nat_dec_le(v___x_2962_, v___x_2962_);
if (v___x_2964_ == 0)
{
if (v___x_2963_ == 0)
{
lean_dec_ref(v___x_2961_);
v___y_2918_ = v___y_2949_;
v___y_2919_ = v___y_2951_;
v___y_2920_ = v___y_2952_;
v___y_2921_ = v___y_2955_;
v___y_2922_ = v___y_2954_;
v___y_2923_ = v___y_2956_;
v___y_2924_ = v___y_2957_;
v___y_2925_ = v___y_2958_;
v_a_2926_ = v_snd_2959_;
v_a_2927_ = v_a_2960_;
goto v___jp_2917_;
}
else
{
size_t v___x_2965_; size_t v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = ((size_t)0ULL);
v___x_2966_ = lean_usize_of_nat(v___x_2962_);
lean_inc_ref(v___y_2846_);
lean_inc_ref(v_pkg_2841_);
v___x_2967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2841_, v___x_2961_, v___x_2965_, v___x_2966_, v_snd_2959_, v___y_2846_, v___x_2839_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_2960_);
lean_dec_ref(v___x_2961_);
v___y_2935_ = v___y_2949_;
v___y_2936_ = v___y_2951_;
v___y_2937_ = v___y_2952_;
v___y_2938_ = v___y_2954_;
v___y_2939_ = v___y_2955_;
v___y_2940_ = v___y_2956_;
v___y_2941_ = v___y_2957_;
v___y_2942_ = v___y_2958_;
v___y_2943_ = v___x_2967_;
goto v___jp_2934_;
}
}
else
{
size_t v___x_2968_; size_t v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = ((size_t)0ULL);
v___x_2969_ = lean_usize_of_nat(v___x_2962_);
lean_inc_ref(v___y_2846_);
lean_inc_ref(v_pkg_2841_);
v___x_2970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2841_, v___x_2961_, v___x_2968_, v___x_2969_, v_snd_2959_, v___y_2846_, v___x_2839_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_2960_);
lean_dec_ref(v___x_2961_);
v___y_2935_ = v___y_2949_;
v___y_2936_ = v___y_2951_;
v___y_2937_ = v___y_2952_;
v___y_2938_ = v___y_2954_;
v___y_2939_ = v___y_2955_;
v___y_2940_ = v___y_2956_;
v___y_2941_ = v___y_2957_;
v___y_2942_ = v___y_2958_;
v___y_2943_ = v___x_2970_;
goto v___jp_2934_;
}
}
}
v___jp_2971_:
{
lean_object* v_toArray_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3004_; 
v_toArray_2984_ = lean_ctor_get(v_a_2982_, 1);
v_isSharedCheck_3004_ = !lean_is_exclusive(v_a_2982_);
if (v_isSharedCheck_3004_ == 0)
{
lean_object* v_unused_3005_; 
v_unused_3005_ = lean_ctor_get(v_a_2982_, 0);
lean_dec(v_unused_3005_);
v___x_2986_ = v_a_2982_;
v_isShared_2987_ = v_isSharedCheck_3004_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_toArray_2984_);
lean_dec(v_a_2982_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3004_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2988_ = lean_mk_empty_array_with_capacity(v___y_2979_);
v___x_2989_ = lean_array_get_size(v_toArray_2984_);
v___x_2990_ = lean_nat_dec_lt(v___y_2979_, v___x_2989_);
if (v___x_2990_ == 0)
{
lean_del_object(v___x_2986_);
lean_dec_ref(v_toArray_2984_);
lean_dec(v_name_2842_);
v___y_2949_ = v___y_2973_;
v___y_2950_ = v___y_2972_;
v___y_2951_ = v___y_2974_;
v___y_2952_ = v___y_2975_;
v___y_2953_ = v___y_2976_;
v___y_2954_ = v___y_2978_;
v___y_2955_ = v___y_2977_;
v___y_2956_ = v___y_2979_;
v___y_2957_ = v___y_2980_;
v___y_2958_ = v___y_2981_;
v_snd_2959_ = v___x_2988_;
v_a_2960_ = v_a_2983_;
goto v___jp_2948_;
}
else
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2991_ = l_Lean_NameSet_empty;
v___x_2992_ = l_Lean_NameSet_insert(v___x_2991_, v_name_2842_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 1, v___x_2988_);
lean_ctor_set(v___x_2986_, 0, v___x_2992_);
v___x_2994_ = v___x_2986_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v___x_2988_);
v___x_2994_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
size_t v___x_2995_; size_t v___x_2996_; lean_object* v___x_2997_; 
v___x_2995_ = ((size_t)0ULL);
v___x_2996_ = lean_usize_of_nat(v___x_2989_);
lean_inc_ref(v___y_2846_);
v___x_2997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_2984_, v___x_2995_, v___x_2996_, v___x_2994_, v___y_2846_, v___x_2839_, v___y_2848_, v___y_2849_, v___y_2850_, v_a_2983_);
lean_dec_ref(v_toArray_2984_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v_a_2999_; lean_object* v_snd_3000_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
v_a_2999_ = lean_ctor_get(v___x_2997_, 1);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___x_2997_, 2);
v_snd_3000_ = lean_ctor_get(v_a_2998_, 1);
lean_inc(v_snd_3000_);
lean_dec(v_a_2998_);
v___y_2949_ = v___y_2973_;
v___y_2950_ = v___y_2972_;
v___y_2951_ = v___y_2974_;
v___y_2952_ = v___y_2975_;
v___y_2953_ = v___y_2976_;
v___y_2954_ = v___y_2978_;
v___y_2955_ = v___y_2977_;
v___y_2956_ = v___y_2979_;
v___y_2957_ = v___y_2980_;
v___y_2958_ = v___y_2981_;
v_snd_2959_ = v_snd_3000_;
v_a_2960_ = v_a_2999_;
goto v___jp_2948_;
}
else
{
lean_object* v_a_3001_; lean_object* v_a_3002_; 
lean_dec_ref(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec_ref(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec_ref(v___y_2975_);
lean_dec_ref(v___y_2972_);
lean_dec_ref(v___y_2846_);
lean_dec_ref(v_pkg_2841_);
lean_dec(v___x_2839_);
lean_dec_ref(v_dir_2838_);
lean_dec_ref(v_self_2837_);
v_a_3001_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_3001_);
v_a_3002_ = lean_ctor_get(v___x_2997_, 1);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_2997_, 2);
v_a_2854_ = v_a_3001_;
v_a_2855_ = v_a_3002_;
goto v___jp_2853_;
}
}
}
}
}
v___jp_3006_:
{
if (lean_obj_tag(v___y_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v_a_3019_; 
v_a_3018_ = lean_ctor_get(v___y_3017_, 0);
lean_inc(v_a_3018_);
v_a_3019_ = lean_ctor_get(v___y_3017_, 1);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___y_3017_, 2);
v___y_2972_ = v___y_3008_;
v___y_2973_ = v___y_3007_;
v___y_2974_ = v___y_3009_;
v___y_2975_ = v___y_3010_;
v___y_2976_ = v___y_3011_;
v___y_2977_ = v___y_3013_;
v___y_2978_ = v___y_3012_;
v___y_2979_ = v___y_3014_;
v___y_2980_ = v___y_3015_;
v___y_2981_ = v___y_3016_;
v_a_2982_ = v_a_3018_;
v_a_2983_ = v_a_3019_;
goto v___jp_2971_;
}
else
{
lean_object* v_a_3020_; lean_object* v_a_3021_; 
lean_dec_ref(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec_ref(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec_ref(v___y_3010_);
lean_dec_ref(v___y_3008_);
lean_dec_ref(v___y_2846_);
lean_dec(v_name_2842_);
lean_dec_ref(v_pkg_2841_);
lean_dec(v___x_2839_);
lean_dec_ref(v_dir_2838_);
lean_dec_ref(v_self_2837_);
v_a_3020_ = lean_ctor_get(v___y_3017_, 0);
lean_inc(v_a_3020_);
v_a_3021_ = lean_ctor_get(v___y_3017_, 1);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___y_3017_, 2);
v_a_2854_ = v_a_3020_;
v_a_2855_ = v_a_3021_;
goto v___jp_2853_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* v_self_3134_, lean_object* v_dir_3135_, lean_object* v___x_3136_, lean_object* v_targetDecls_3137_, lean_object* v_pkg_3138_, lean_object* v_name_3139_, lean_object* v___x_3140_, lean_object* v_config_3141_, lean_object* v_config_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v_self_3134_, v_dir_3135_, v___x_3136_, v_targetDecls_3137_, v_pkg_3138_, v_name_3139_, v___x_3140_, v_config_3141_, v_config_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec(v_config_3142_);
lean_dec_ref(v_targetDecls_3137_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object* v_self_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_){
_start:
{
lean_object* v_pkg_3160_; lean_object* v_name_3161_; lean_object* v_config_3162_; lean_object* v_keyName_3163_; lean_object* v_dir_3164_; lean_object* v_config_3165_; lean_object* v_targetDecls_3166_; lean_object* v___x_3167_; uint8_t v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___f_3177_; uint8_t v___x_3178_; lean_object* v___x_3179_; 
v_pkg_3160_ = lean_ctor_get(v_self_3152_, 0);
lean_inc_ref_n(v_pkg_3160_, 2);
v_name_3161_ = lean_ctor_get(v_self_3152_, 1);
lean_inc_n(v_name_3161_, 3);
v_config_3162_ = lean_ctor_get(v_self_3152_, 2);
lean_inc(v_config_3162_);
v_keyName_3163_ = lean_ctor_get(v_pkg_3160_, 2);
v_dir_3164_ = lean_ctor_get(v_pkg_3160_, 4);
lean_inc_ref(v_dir_3164_);
v_config_3165_ = lean_ctor_get(v_pkg_3160_, 6);
lean_inc_ref(v_config_3165_);
v_targetDecls_3166_ = lean_ctor_get(v_pkg_3160_, 15);
lean_inc_ref(v_targetDecls_3166_);
v___x_3167_ = l_Lake_instDataKindDynlib;
v___x_3168_ = 1;
v___x_3169_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3161_, v___x_3168_);
v___x_3170_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0));
v___x_3171_ = lean_string_append(v___x_3169_, v___x_3170_);
v___x_3172_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_3163_);
v___x_3173_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3173_, 0, v_keyName_3163_);
lean_ctor_set(v___x_3173_, 1, v_name_3161_);
v___x_3174_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3152_);
v___x_3175_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
lean_ctor_set(v___x_3175_, 2, v_self_3152_);
lean_ctor_set(v___x_3175_, 3, v___x_3172_);
v___x_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3176_, 0, v_pkg_3160_);
v___f_3177_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3177_, 0, v_self_3152_);
lean_closure_set(v___f_3177_, 1, v_dir_3164_);
lean_closure_set(v___f_3177_, 2, v___x_3176_);
lean_closure_set(v___f_3177_, 3, v_targetDecls_3166_);
lean_closure_set(v___f_3177_, 4, v_pkg_3160_);
lean_closure_set(v___f_3177_, 5, v_name_3161_);
lean_closure_set(v___f_3177_, 6, v___x_3175_);
lean_closure_set(v___f_3177_, 7, v_config_3165_);
lean_closure_set(v___f_3177_, 8, v_config_3162_);
v___x_3178_ = 0;
v___x_3179_ = l_Lake_ensureJob___redArg(v___x_3167_, v___f_3177_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3204_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
v_a_3181_ = lean_ctor_get(v___x_3179_, 1);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3183_ = v___x_3179_;
v_isShared_3184_ = v_isSharedCheck_3204_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_inc(v_a_3180_);
lean_dec(v___x_3179_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3204_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v_task_3185_; lean_object* v_kind_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3202_; 
v_task_3185_ = lean_ctor_get(v_a_3180_, 0);
v_kind_3186_ = lean_ctor_get(v_a_3180_, 1);
v_isSharedCheck_3202_ = !lean_is_exclusive(v_a_3180_);
if (v_isSharedCheck_3202_ == 0)
{
lean_object* v_unused_3203_; 
v_unused_3203_ = lean_ctor_get(v_a_3180_, 2);
lean_dec(v_unused_3203_);
v___x_3188_ = v_a_3180_;
v_isShared_3189_ = v_isSharedCheck_3202_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_kind_3186_);
lean_inc(v_task_3185_);
lean_dec(v_a_3180_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3202_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v_registeredJobs_3190_; lean_object* v_job_3192_; 
v_registeredJobs_3190_ = lean_ctor_get(v_a_3157_, 4);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 2, v___x_3171_);
v_job_3192_ = v___x_3188_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_task_3185_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v_kind_3186_);
lean_ctor_set(v_reuseFailAlloc_3201_, 2, v___x_3171_);
v_job_3192_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3199_; 
lean_ctor_set_uint8(v_job_3192_, sizeof(void*)*3, v___x_3178_);
v___x_3193_ = lean_st_ref_take(v_registeredJobs_3190_);
lean_inc_ref(v_job_3192_);
v___x_3194_ = l_Lake_Job_toOpaque___redArg(v_job_3192_);
v___x_3195_ = lean_array_push(v___x_3193_, v___x_3194_);
v___x_3196_ = lean_st_ref_put(v_registeredJobs_3190_, v___x_3195_);
v___x_3197_ = l_Lake_Job_renew___redArg(v_job_3192_);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v___x_3197_);
v___x_3199_ = v___x_3183_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v_a_3181_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3171_);
return v___x_3179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object* v_self_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
lean_dec_ref(v_a_3210_);
lean_dec(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec(v_a_3207_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t v_fmt_3214_, lean_object* v_a_3215_){
_start:
{
if (v_fmt_3214_ == 0)
{
lean_object* v_path_3216_; 
v_path_3216_ = lean_ctor_get(v_a_3215_, 0);
lean_inc_ref(v_path_3216_);
return v_path_3216_;
}
else
{
lean_object* v_path_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v_path_3217_ = lean_ctor_get(v_a_3215_, 0);
lean_inc_ref(v_path_3217_);
v___x_3218_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3218_, 0, v_path_3217_);
v___x_3219_ = l_Lean_Json_compress(v___x_3218_);
return v___x_3219_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* v_fmt_3220_, lean_object* v_a_3221_){
_start:
{
uint8_t v_fmt_boxed_3222_; lean_object* v_res_3223_; 
v_fmt_boxed_3222_ = lean_unbox(v_fmt_3220_);
v_res_3223_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_boxed_3222_, v_a_3221_);
lean_dec_ref(v_a_3221_);
return v_res_3223_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3226_; uint8_t v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___f_3226_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__0));
v___x_3227_ = 1;
v___x_3228_ = l_Lake_instDataKindDynlib;
v___x_3229_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__1));
v___x_3230_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3231_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
lean_ctor_set(v___x_3231_, 1, v___x_3229_);
lean_ctor_set(v___x_3231_, 2, v___x_3228_);
lean_ctor_set(v___x_3231_, 3, v___f_3226_);
lean_ctor_set_uint8(v___x_3231_, sizeof(void*)*4, v___x_3227_);
lean_ctor_set_uint8(v___x_3231_, sizeof(void*)*4 + 1, v___x_3227_);
return v___x_3231_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_obj_once(&l_Lake_LeanLib_sharedFacetConfig___closed__2, &l_Lake_LeanLib_sharedFacetConfig___closed__2_once, _init_l_Lake_LeanLib_sharedFacetConfig___closed__2);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* v___x_3233_, lean_object* v_as_3234_, size_t v_sz_3235_, size_t v_i_3236_, lean_object* v_b_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
uint8_t v___x_3245_; 
v___x_3245_ = lean_usize_dec_lt(v_i_3236_, v_sz_3235_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; 
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___x_3233_);
v___x_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3246_, 0, v_b_3237_);
lean_ctor_set(v___x_3246_, 1, v___y_3243_);
return v___x_3246_;
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3248_; 
v_a_3247_ = lean_array_uget_borrowed(v_as_3234_, v_i_3236_);
lean_inc_ref(v___y_3238_);
lean_inc_n(v_a_3247_, 2);
lean_inc_ref(v___x_3233_);
v___x_3248_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v___x_3233_, v_a_3247_, v_a_3247_, v___x_3245_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v_a_3250_; lean_object* v_snd_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; size_t v___x_3254_; size_t v___x_3255_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
v_a_3250_ = lean_ctor_get(v___x_3248_, 1);
lean_inc(v_a_3250_);
lean_dec_ref_known(v___x_3248_, 2);
v_snd_3251_ = lean_ctor_get(v_a_3249_, 1);
lean_inc(v_snd_3251_);
lean_dec(v_a_3249_);
v___x_3252_ = l_Lake_Job_toOpaque___redArg(v_snd_3251_);
v___x_3253_ = l_Lake_Job_mix___redArg(v_b_3237_, v___x_3252_);
v___x_3254_ = ((size_t)1ULL);
v___x_3255_ = lean_usize_add(v_i_3236_, v___x_3254_);
v_i_3236_ = v___x_3255_;
v_b_3237_ = v___x_3253_;
v___y_3243_ = v_a_3250_;
goto _start;
}
else
{
lean_object* v_a_3257_; lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v___y_3238_);
lean_dec_ref(v_b_3237_);
lean_dec_ref(v___x_3233_);
v_a_3257_ = lean_ctor_get(v___x_3248_, 0);
v_a_3258_ = lean_ctor_get(v___x_3248_, 1);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3248_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_inc(v_a_3257_);
lean_dec(v___x_3248_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3257_);
lean_ctor_set(v_reuseFailAlloc_3264_, 1, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* v___x_3266_, lean_object* v_as_3267_, lean_object* v_sz_3268_, lean_object* v_i_3269_, lean_object* v_b_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
size_t v_sz_boxed_3278_; size_t v_i_boxed_3279_; lean_object* v_res_3280_; 
v_sz_boxed_3278_ = lean_unbox_usize(v_sz_3268_);
lean_dec(v_sz_3268_);
v_i_boxed_3279_ = lean_unbox_usize(v_i_3269_);
lean_dec(v_i_3269_);
v_res_3280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_3266_, v_as_3267_, v_sz_boxed_3278_, v_i_boxed_3279_, v_b_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v_as_3267_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* v___x_3281_, lean_object* v_as_3282_, size_t v_sz_3283_, size_t v_i_3284_, lean_object* v_b_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
uint8_t v___x_3293_; 
v___x_3293_ = lean_usize_dec_lt(v_i_3284_, v_sz_3283_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; 
lean_dec_ref(v___y_3286_);
lean_dec_ref(v___x_3281_);
v___x_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3294_, 0, v_b_3285_);
lean_ctor_set(v___x_3294_, 1, v___y_3291_);
return v___x_3294_;
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3296_; 
v_a_3295_ = lean_array_uget_borrowed(v_as_3282_, v_i_3284_);
lean_inc_ref(v___y_3286_);
lean_inc(v_a_3295_);
lean_inc_ref(v___x_3281_);
v___x_3296_ = l_Lake_Package_fetchTargetJob(v___x_3281_, v_a_3295_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v_a_3298_; lean_object* v___x_3299_; size_t v___x_3300_; size_t v___x_3301_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
v_a_3298_ = lean_ctor_get(v___x_3296_, 1);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3296_, 2);
v___x_3299_ = l_Lake_Job_mix___redArg(v_b_3285_, v_a_3297_);
v___x_3300_ = ((size_t)1ULL);
v___x_3301_ = lean_usize_add(v_i_3284_, v___x_3300_);
v_i_3284_ = v___x_3301_;
v_b_3285_ = v___x_3299_;
v___y_3291_ = v_a_3298_;
goto _start;
}
else
{
lean_object* v_a_3303_; lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3311_; 
lean_dec_ref(v___y_3286_);
lean_dec_ref(v_b_3285_);
lean_dec_ref(v___x_3281_);
v_a_3303_ = lean_ctor_get(v___x_3296_, 0);
v_a_3304_ = lean_ctor_get(v___x_3296_, 1);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3306_ = v___x_3296_;
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_inc(v_a_3303_);
lean_dec(v___x_3296_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3309_; 
if (v_isShared_3307_ == 0)
{
v___x_3309_ = v___x_3306_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_a_3303_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_a_3304_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* v___x_3312_, lean_object* v_as_3313_, lean_object* v_sz_3314_, lean_object* v_i_3315_, lean_object* v_b_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
size_t v_sz_boxed_3324_; size_t v_i_boxed_3325_; lean_object* v_res_3326_; 
v_sz_boxed_3324_ = lean_unbox_usize(v_sz_3314_);
lean_dec(v_sz_3314_);
v_i_boxed_3325_ = lean_unbox_usize(v_i_3315_);
lean_dec(v_i_3315_);
v_res_3326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_3312_, v_as_3313_, v_sz_boxed_3324_, v_i_boxed_3325_, v_b_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v_as_3313_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object* v_self_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v_pkg_3337_; lean_object* v_name_3338_; lean_object* v_config_3339_; lean_object* v_baseName_3340_; lean_object* v_keyName_3341_; uint8_t v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v_job_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v_pkg_3337_ = lean_ctor_get(v_self_3329_, 0);
lean_inc_ref_n(v_pkg_3337_, 2);
v_name_3338_ = lean_ctor_get(v_self_3329_, 1);
lean_inc(v_name_3338_);
v_config_3339_ = lean_ctor_get(v_self_3329_, 2);
lean_inc(v_config_3339_);
lean_dec_ref(v_self_3329_);
v_baseName_3340_ = lean_ctor_get(v_pkg_3337_, 1);
v_keyName_3341_ = lean_ctor_get(v_pkg_3337_, 2);
v___x_3342_ = 1;
lean_inc(v_baseName_3340_);
v___x_3343_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3340_, v___x_3342_);
v___x_3344_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0));
v___x_3345_ = lean_string_append(v___x_3343_, v___x_3344_);
v___x_3346_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3338_, v___x_3342_);
v___x_3347_ = lean_string_append(v___x_3345_, v___x_3346_);
lean_dec_ref(v___x_3346_);
v___x_3348_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1));
v___x_3349_ = lean_string_append(v___x_3347_, v___x_3348_);
v___x_3350_ = lean_box(0);
v___x_3351_ = lean_box(0);
v___x_3352_ = lean_unsigned_to_nat(0u);
v___x_3353_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v___x_3354_ = 0;
v___x_3355_ = 0;
v___x_3356_ = l_Lake_BuildTrace_nil(v___x_3349_);
v___x_3357_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3357_, 0, v___x_3353_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
lean_ctor_set(v___x_3357_, 2, v___x_3352_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*3, v___x_3354_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*3 + 1, v___x_3355_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*3 + 2, v___x_3355_);
v___x_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3350_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
v___x_3359_ = lean_task_pure(v___x_3358_);
v___x_3360_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v_job_3361_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_3361_, 0, v___x_3359_);
lean_ctor_set(v_job_3361_, 1, v___x_3351_);
lean_ctor_set(v_job_3361_, 2, v___x_3360_);
lean_ctor_set_uint8(v_job_3361_, sizeof(void*)*3, v___x_3355_);
v___x_3362_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_3341_);
v___x_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3363_, 0, v_keyName_3341_);
v___x_3364_ = l_Lake_Package_keyword;
v___x_3365_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3363_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
lean_ctor_set(v___x_3365_, 2, v_pkg_3337_);
lean_ctor_set(v___x_3365_, 3, v___x_3362_);
lean_inc_ref(v_a_3330_);
lean_inc_ref(v_a_3334_);
lean_inc(v_a_3333_);
lean_inc(v_a_3332_);
lean_inc(v_a_3331_);
v___x_3366_ = lean_apply_7(v_a_3330_, v___x_3365_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, lean_box(0));
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v_a_3368_; lean_object* v_needs_3369_; lean_object* v_extraDepTargets_3370_; lean_object* v___x_3371_; size_t v_sz_3372_; size_t v___x_3373_; lean_object* v___x_3374_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
v_a_3368_ = lean_ctor_get(v___x_3366_, 1);
lean_inc(v_a_3368_);
lean_dec_ref_known(v___x_3366_, 2);
v_needs_3369_ = lean_ctor_get(v_config_3339_, 5);
lean_inc_ref(v_needs_3369_);
v_extraDepTargets_3370_ = lean_ctor_get(v_config_3339_, 6);
lean_inc_ref(v_extraDepTargets_3370_);
lean_dec(v_config_3339_);
v___x_3371_ = l_Lake_Job_mix___redArg(v_job_3361_, v_a_3367_);
v_sz_3372_ = lean_array_size(v_extraDepTargets_3370_);
v___x_3373_ = ((size_t)0ULL);
lean_inc_ref(v_a_3330_);
lean_inc_ref(v_pkg_3337_);
v___x_3374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_3337_, v_extraDepTargets_3370_, v_sz_3372_, v___x_3373_, v___x_3371_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3368_);
lean_dec_ref(v_extraDepTargets_3370_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v_a_3376_; size_t v_sz_3377_; lean_object* v___x_3378_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
v_a_3376_ = lean_ctor_get(v___x_3374_, 1);
lean_inc(v_a_3376_);
lean_dec_ref_known(v___x_3374_, 2);
v_sz_3377_ = lean_array_size(v_needs_3369_);
v___x_3378_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_3337_, v_needs_3369_, v_sz_3377_, v___x_3373_, v_a_3375_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3376_);
lean_dec_ref(v_needs_3369_);
return v___x_3378_;
}
else
{
lean_dec_ref(v_needs_3369_);
lean_dec_ref(v_pkg_3337_);
lean_dec_ref(v_a_3330_);
return v___x_3374_;
}
}
else
{
lean_dec_ref_known(v_job_3361_, 3);
lean_dec(v_config_3339_);
lean_dec_ref(v_pkg_3337_);
lean_dec_ref(v_a_3330_);
return v___x_3366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object* v_self_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_);
lean_dec_ref(v_a_3384_);
lean_dec(v_a_3383_);
lean_dec(v_a_3382_);
lean_dec(v_a_3381_);
return v_res_3387_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3389_; uint8_t v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___f_3389_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3390_ = 1;
v___x_3391_ = l_Lake_instDataKindUnit;
v___x_3392_ = ((lean_object*)(l_Lake_LeanLib_extraDepFacetConfig___closed__0));
v___x_3393_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3394_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
lean_ctor_set(v___x_3394_, 1, v___x_3392_);
lean_ctor_set(v___x_3394_, 2, v___x_3391_);
lean_ctor_set(v___x_3394_, 3, v___f_3389_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*4, v___x_3390_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*4 + 1, v___x_3390_);
return v___x_3394_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = lean_obj_once(&l_Lake_LeanLib_extraDepFacetConfig___closed__1, &l_Lake_LeanLib_extraDepFacetConfig___closed__1_once, _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* v_self_3396_, size_t v_sz_3397_, size_t v_i_3398_, lean_object* v_bs_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
uint8_t v___x_3407_; 
v___x_3407_ = lean_usize_dec_lt(v_i_3398_, v_sz_3397_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; 
lean_dec_ref(v___y_3400_);
lean_dec_ref(v_self_3396_);
v___x_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3408_, 0, v_bs_3399_);
lean_ctor_set(v___x_3408_, 1, v___y_3405_);
return v___x_3408_;
}
else
{
lean_object* v_pkg_3409_; lean_object* v_name_3410_; lean_object* v_keyName_3411_; lean_object* v_v_3412_; lean_object* v___x_3413_; lean_object* v_bs_x27_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v_pkg_3409_ = lean_ctor_get(v_self_3396_, 0);
v_name_3410_ = lean_ctor_get(v_self_3396_, 1);
v_keyName_3411_ = lean_ctor_get(v_pkg_3409_, 2);
v_v_3412_ = lean_array_uget(v_bs_3399_, v_i_3398_);
v___x_3413_ = lean_unsigned_to_nat(0u);
v_bs_x27_3414_ = lean_array_uset(v_bs_3399_, v_i_3398_, v___x_3413_);
lean_inc(v_name_3410_);
lean_inc(v_keyName_3411_);
v___x_3415_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3415_, 0, v_keyName_3411_);
lean_ctor_set(v___x_3415_, 1, v_name_3410_);
v___x_3416_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3396_);
v___x_3417_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3415_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
lean_ctor_set(v___x_3417_, 2, v_self_3396_);
lean_ctor_set(v___x_3417_, 3, v_v_3412_);
lean_inc_ref(v___y_3400_);
lean_inc_ref(v___y_3404_);
lean_inc(v___y_3403_);
lean_inc(v___y_3402_);
lean_inc(v___y_3401_);
v___x_3418_ = lean_apply_7(v___y_3400_, v___x_3417_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, lean_box(0));
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v_a_3420_; lean_object* v___x_3421_; size_t v___x_3422_; size_t v___x_3423_; lean_object* v___x_3424_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
v_a_3420_ = lean_ctor_get(v___x_3418_, 1);
lean_inc(v_a_3420_);
lean_dec_ref_known(v___x_3418_, 2);
v___x_3421_ = l_Lake_Job_toOpaque___redArg(v_a_3419_);
v___x_3422_ = ((size_t)1ULL);
v___x_3423_ = lean_usize_add(v_i_3398_, v___x_3422_);
v___x_3424_ = lean_array_uset(v_bs_x27_3414_, v_i_3398_, v___x_3421_);
v_i_3398_ = v___x_3423_;
v_bs_3399_ = v___x_3424_;
v___y_3405_ = v_a_3420_;
goto _start;
}
else
{
lean_object* v_a_3426_; lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec_ref(v_bs_x27_3414_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v_self_3396_);
v_a_3426_ = lean_ctor_get(v___x_3418_, 0);
v_a_3427_ = lean_ctor_get(v___x_3418_, 1);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3418_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_inc(v_a_3426_);
lean_dec(v___x_3418_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3426_);
lean_ctor_set(v_reuseFailAlloc_3433_, 1, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* v_self_3435_, lean_object* v_sz_3436_, lean_object* v_i_3437_, lean_object* v_bs_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
size_t v_sz_boxed_3446_; size_t v_i_boxed_3447_; lean_object* v_res_3448_; 
v_sz_boxed_3446_ = lean_unbox_usize(v_sz_3436_);
lean_dec(v_sz_3436_);
v_i_boxed_3447_ = lean_unbox_usize(v_i_3437_);
lean_dec(v_i_3437_);
v_res_3448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3435_, v_sz_boxed_3446_, v_i_boxed_3447_, v_bs_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec(v___y_3440_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object* v_self_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_){
_start:
{
lean_object* v_config_3458_; lean_object* v_defaultFacets_3459_; size_t v_sz_3460_; size_t v___x_3461_; lean_object* v___x_3462_; 
v_config_3458_ = lean_ctor_get(v_self_3450_, 2);
v_defaultFacets_3459_ = lean_ctor_get(v_config_3458_, 7);
lean_inc_ref(v_defaultFacets_3459_);
v_sz_3460_ = lean_array_size(v_defaultFacets_3459_);
v___x_3461_ = ((size_t)0ULL);
v___x_3462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3450_, v_sz_3460_, v___x_3461_, v_defaultFacets_3459_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3473_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_a_3464_ = lean_ctor_get(v___x_3462_, 1);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3466_ = v___x_3462_;
v_isShared_3467_ = v_isSharedCheck_3473_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3473_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3468_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0));
v___x_3469_ = l_Lake_Job_mixArray___redArg(v_a_3463_, v___x_3468_);
lean_dec(v_a_3463_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v___x_3469_);
v___x_3471_ = v___x_3466_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
lean_ctor_set(v_reuseFailAlloc_3472_, 1, v_a_3464_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3482_; 
v_a_3474_ = lean_ctor_get(v___x_3462_, 0);
v_a_3475_ = lean_ctor_get(v___x_3462_, 1);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3477_ = v___x_3462_;
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_inc(v_a_3474_);
lean_dec(v___x_3462_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3482_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___x_3480_; 
if (v_isShared_3478_ == 0)
{
v___x_3480_ = v___x_3477_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3474_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_a_3475_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object* v_self_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_);
lean_dec_ref(v_a_3488_);
lean_dec(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec(v_a_3485_);
return v_res_3491_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3493_; uint8_t v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___f_3493_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3494_ = 1;
v___x_3495_ = l_Lake_instDataKindUnit;
v___x_3496_ = ((lean_object*)(l_Lake_LeanLib_defaultFacetConfig___closed__0));
v___x_3497_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3498_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
lean_ctor_set(v___x_3498_, 1, v___x_3496_);
lean_ctor_set(v___x_3498_, 2, v___x_3495_);
lean_ctor_set(v___x_3498_, 3, v___f_3493_);
lean_ctor_set_uint8(v___x_3498_, sizeof(void*)*4, v___x_3494_);
lean_ctor_set_uint8(v___x_3498_, sizeof(void*)*4 + 1, v___x_3494_);
return v___x_3498_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = lean_obj_once(&l_Lake_LeanLib_defaultFacetConfig___closed__1, &l_Lake_LeanLib_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanLib_defaultFacetConfig___closed__1);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_3500_, lean_object* v_v_3501_, lean_object* v_t_3502_){
_start:
{
if (lean_obj_tag(v_t_3502_) == 0)
{
lean_object* v_size_3503_; lean_object* v_k_3504_; lean_object* v_v_3505_; lean_object* v_l_3506_; lean_object* v_r_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3787_; 
v_size_3503_ = lean_ctor_get(v_t_3502_, 0);
v_k_3504_ = lean_ctor_get(v_t_3502_, 1);
v_v_3505_ = lean_ctor_get(v_t_3502_, 2);
v_l_3506_ = lean_ctor_get(v_t_3502_, 3);
v_r_3507_ = lean_ctor_get(v_t_3502_, 4);
v_isSharedCheck_3787_ = !lean_is_exclusive(v_t_3502_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3509_ = v_t_3502_;
v_isShared_3510_ = v_isSharedCheck_3787_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_r_3507_);
lean_inc(v_l_3506_);
lean_inc(v_v_3505_);
lean_inc(v_k_3504_);
lean_inc(v_size_3503_);
lean_dec(v_t_3502_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3787_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
uint8_t v___x_3511_; 
v___x_3511_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3500_, v_k_3504_);
switch(v___x_3511_)
{
case 0:
{
lean_object* v_impl_3512_; lean_object* v___x_3513_; 
lean_dec(v_size_3503_);
v_impl_3512_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3500_, v_v_3501_, v_l_3506_);
v___x_3513_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3507_) == 0)
{
lean_object* v_size_3514_; lean_object* v_size_3515_; lean_object* v_k_3516_; lean_object* v_v_3517_; lean_object* v_l_3518_; lean_object* v_r_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v_size_3514_ = lean_ctor_get(v_r_3507_, 0);
v_size_3515_ = lean_ctor_get(v_impl_3512_, 0);
lean_inc(v_size_3515_);
v_k_3516_ = lean_ctor_get(v_impl_3512_, 1);
lean_inc(v_k_3516_);
v_v_3517_ = lean_ctor_get(v_impl_3512_, 2);
lean_inc(v_v_3517_);
v_l_3518_ = lean_ctor_get(v_impl_3512_, 3);
lean_inc(v_l_3518_);
v_r_3519_ = lean_ctor_get(v_impl_3512_, 4);
lean_inc(v_r_3519_);
v___x_3520_ = lean_unsigned_to_nat(3u);
v___x_3521_ = lean_nat_mul(v___x_3520_, v_size_3514_);
v___x_3522_ = lean_nat_dec_lt(v___x_3521_, v_size_3515_);
lean_dec(v___x_3521_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3526_; 
lean_dec(v_r_3519_);
lean_dec(v_l_3518_);
lean_dec(v_v_3517_);
lean_dec(v_k_3516_);
v___x_3523_ = lean_nat_add(v___x_3513_, v_size_3515_);
lean_dec(v_size_3515_);
v___x_3524_ = lean_nat_add(v___x_3523_, v_size_3514_);
lean_dec(v___x_3523_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 3, v_impl_3512_);
lean_ctor_set(v___x_3509_, 0, v___x_3524_);
v___x_3526_ = v___x_3509_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_k_3504_);
lean_ctor_set(v_reuseFailAlloc_3527_, 2, v_v_3505_);
lean_ctor_set(v_reuseFailAlloc_3527_, 3, v_impl_3512_);
lean_ctor_set(v_reuseFailAlloc_3527_, 4, v_r_3507_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
else
{
lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3593_; 
v_isSharedCheck_3593_ = !lean_is_exclusive(v_impl_3512_);
if (v_isSharedCheck_3593_ == 0)
{
lean_object* v_unused_3594_; lean_object* v_unused_3595_; lean_object* v_unused_3596_; lean_object* v_unused_3597_; lean_object* v_unused_3598_; 
v_unused_3594_ = lean_ctor_get(v_impl_3512_, 4);
lean_dec(v_unused_3594_);
v_unused_3595_ = lean_ctor_get(v_impl_3512_, 3);
lean_dec(v_unused_3595_);
v_unused_3596_ = lean_ctor_get(v_impl_3512_, 2);
lean_dec(v_unused_3596_);
v_unused_3597_ = lean_ctor_get(v_impl_3512_, 1);
lean_dec(v_unused_3597_);
v_unused_3598_ = lean_ctor_get(v_impl_3512_, 0);
lean_dec(v_unused_3598_);
v___x_3529_ = v_impl_3512_;
v_isShared_3530_ = v_isSharedCheck_3593_;
goto v_resetjp_3528_;
}
else
{
lean_dec(v_impl_3512_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3593_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v_size_3531_; lean_object* v_size_3532_; lean_object* v_k_3533_; lean_object* v_v_3534_; lean_object* v_l_3535_; lean_object* v_r_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v_size_3531_ = lean_ctor_get(v_l_3518_, 0);
v_size_3532_ = lean_ctor_get(v_r_3519_, 0);
v_k_3533_ = lean_ctor_get(v_r_3519_, 1);
v_v_3534_ = lean_ctor_get(v_r_3519_, 2);
v_l_3535_ = lean_ctor_get(v_r_3519_, 3);
v_r_3536_ = lean_ctor_get(v_r_3519_, 4);
v___x_3537_ = lean_unsigned_to_nat(2u);
v___x_3538_ = lean_nat_mul(v___x_3537_, v_size_3531_);
v___x_3539_ = lean_nat_dec_lt(v_size_3532_, v___x_3538_);
lean_dec(v___x_3538_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3568_; 
lean_inc(v_r_3536_);
lean_inc(v_l_3535_);
lean_inc(v_v_3534_);
lean_inc(v_k_3533_);
v_isSharedCheck_3568_ = !lean_is_exclusive(v_r_3519_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; lean_object* v_unused_3570_; lean_object* v_unused_3571_; lean_object* v_unused_3572_; lean_object* v_unused_3573_; 
v_unused_3569_ = lean_ctor_get(v_r_3519_, 4);
lean_dec(v_unused_3569_);
v_unused_3570_ = lean_ctor_get(v_r_3519_, 3);
lean_dec(v_unused_3570_);
v_unused_3571_ = lean_ctor_get(v_r_3519_, 2);
lean_dec(v_unused_3571_);
v_unused_3572_ = lean_ctor_get(v_r_3519_, 1);
lean_dec(v_unused_3572_);
v_unused_3573_ = lean_ctor_get(v_r_3519_, 0);
lean_dec(v_unused_3573_);
v___x_3541_ = v_r_3519_;
v_isShared_3542_ = v_isSharedCheck_3568_;
goto v_resetjp_3540_;
}
else
{
lean_dec(v_r_3519_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3568_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___x_3556_; lean_object* v___y_3558_; 
v___x_3543_ = lean_nat_add(v___x_3513_, v_size_3515_);
lean_dec(v_size_3515_);
v___x_3544_ = lean_nat_add(v___x_3543_, v_size_3514_);
lean_dec(v___x_3543_);
v___x_3556_ = lean_nat_add(v___x_3513_, v_size_3531_);
if (lean_obj_tag(v_l_3535_) == 0)
{
lean_object* v_size_3566_; 
v_size_3566_ = lean_ctor_get(v_l_3535_, 0);
lean_inc(v_size_3566_);
v___y_3558_ = v_size_3566_;
goto v___jp_3557_;
}
else
{
lean_object* v___x_3567_; 
v___x_3567_ = lean_unsigned_to_nat(0u);
v___y_3558_ = v___x_3567_;
goto v___jp_3557_;
}
v___jp_3545_:
{
lean_object* v___x_3549_; lean_object* v___x_3551_; 
v___x_3549_ = lean_nat_add(v___y_3546_, v___y_3548_);
lean_dec(v___y_3548_);
lean_dec(v___y_3546_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 4, v_r_3507_);
lean_ctor_set(v___x_3541_, 3, v_r_3536_);
lean_ctor_set(v___x_3541_, 2, v_v_3505_);
lean_ctor_set(v___x_3541_, 1, v_k_3504_);
lean_ctor_set(v___x_3541_, 0, v___x_3549_);
v___x_3551_ = v___x_3541_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3555_, 1, v_k_3504_);
lean_ctor_set(v_reuseFailAlloc_3555_, 2, v_v_3505_);
lean_ctor_set(v_reuseFailAlloc_3555_, 3, v_r_3536_);
lean_ctor_set(v_reuseFailAlloc_3555_, 4, v_r_3507_);
v___x_3551_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3553_; 
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 4, v___x_3551_);
lean_ctor_set(v___x_3529_, 3, v___y_3547_);
lean_ctor_set(v___x_3529_, 2, v_v_3534_);
lean_ctor_set(v___x_3529_, 1, v_k_3533_);
lean_ctor_set(v___x_3529_, 0, v___x_3544_);
v___x_3553_ = v___x_3529_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3544_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_k_3533_);
lean_ctor_set(v_reuseFailAlloc_3554_, 2, v_v_3534_);
lean_ctor_set(v_reuseFailAlloc_3554_, 3, v___y_3547_);
lean_ctor_set(v_reuseFailAlloc_3554_, 4, v___x_3551_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
v___jp_3557_:
{
lean_object* v___x_3559_; lean_object* v___x_3561_; 
v___x_3559_ = lean_nat_add(v___x_3556_, v___y_3558_);
lean_dec(v___y_3558_);
lean_dec(v___x_3556_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 4, v_l_3535_);
lean_ctor_set(v___x_3509_, 3, v_l_3518_);
lean_ctor_set(v___x_3509_, 2, v_v_3517_);
lean_ctor_set(v___x_3509_, 1, v_k_3516_);
lean_ctor_set(v___x_3509_, 0, v___x_3559_);
v___x_3561_ = v___x_3509_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3559_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_k_3516_);
lean_ctor_set(v_reuseFailAlloc_3565_, 2, v_v_3517_);
lean_ctor_set(v_reuseFailAlloc_3565_, 3, v_l_3518_);
lean_ctor_set(v_reuseFailAlloc_3565_, 4, v_l_3535_);
v___x_3561_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3562_; 
v___x_3562_ = lean_nat_add(v___x_3513_, v_size_3514_);
if (lean_obj_tag(v_r_3536_) == 0)
{
lean_object* v_size_3563_; 
v_size_3563_ = lean_ctor_get(v_r_3536_, 0);
lean_inc(v_size_3563_);
v___y_3546_ = v___x_3562_;
v___y_3547_ = v___x_3561_;
v___y_3548_ = v_size_3563_;
goto v___jp_3545_;
}
else
{
lean_object* v___x_3564_; 
v___x_3564_ = lean_unsigned_to_nat(0u);
v___y_3546_ = v___x_3562_;
v___y_3547_ = v___x_3561_;
v___y_3548_ = v___x_3564_;
goto v___jp_3545_;
}
}
}
}
}
else
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3579_; 
lean_del_object(v___x_3509_);
v___x_3574_ = lean_nat_add(v___x_3513_, v_size_3515_);
lean_dec(v_size_3515_);
v___x_3575_ = lean_nat_add(v___x_3574_, v_size_3514_);
lean_dec(v___x_3574_);
v___x_3576_ = lean_nat_add(v___x_3513_, v_size_3514_);
v___x_3577_ = lean_nat_add(v___x_3576_, v_size_3532_);
lean_dec(v___x_3576_);
lean_inc_ref(v_r_3507_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 4, v_r_3507_);
lean_ctor_set(v___x_3529_, 3, v_r_3519_);
lean_ctor_set(v___x_3529_, 2, v_v_3505_);
lean_ctor_set(v___x_3529_, 1, v_k_3504_);
lean_ctor_set(v___x_3529_, 0, v___x_3577_);
v___x_3579_ = v___x_3529_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3577_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v_k_3504_);
lean_ctor_set(v_reuseFailAlloc_3592_, 2, v_v_3505_);
lean_ctor_set(v_reuseFailAlloc_3592_, 3, v_r_3519_);
lean_ctor_set(v_reuseFailAlloc_3592_, 4, v_r_3507_);
v___x_3579_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
v_isSharedCheck_3586_ = !lean_is_exclusive(v_r_3507_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; lean_object* v_unused_3588_; lean_object* v_unused_3589_; lean_object* v_unused_3590_; lean_object* v_unused_3591_; 
v_unused_3587_ = lean_ctor_get(v_r_3507_, 4);
lean_dec(v_unused_3587_);
v_unused_3588_ = lean_ctor_get(v_r_3507_, 3);
lean_dec(v_unused_3588_);
v_unused_3589_ = lean_ctor_get(v_r_3507_, 2);
lean_dec(v_unused_3589_);
v_unused_3590_ = lean_ctor_get(v_r_3507_, 1);
lean_dec(v_unused_3590_);
v_unused_3591_ = lean_ctor_get(v_r_3507_, 0);
lean_dec(v_unused_3591_);
v___x_3581_ = v_r_3507_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_dec(v_r_3507_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 4, v___x_3579_);
lean_ctor_set(v___x_3581_, 3, v_l_3518_);
lean_ctor_set(v___x_3581_, 2, v_v_3517_);
lean_ctor_set(v___x_3581_, 1, v_k_3516_);
lean_ctor_set(v___x_3581_, 0, v___x_3575_);
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3575_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_k_3516_);
lean_ctor_set(v_reuseFailAlloc_3585_, 2, v_v_3517_);
lean_ctor_set(v_reuseFailAlloc_3585_, 3, v_l_3518_);
lean_ctor_set(v_reuseFailAlloc_3585_, 4, v___x_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3599_; 
v_l_3599_ = lean_ctor_get(v_impl_3512_, 3);
lean_inc(v_l_3599_);
if (lean_obj_tag(v_l_3599_) == 0)
{
lean_object* v_r_3600_; lean_object* v_k_3601_; lean_object* v_v_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3613_; 
v_r_3600_ = lean_ctor_get(v_impl_3512_, 4);
v_k_3601_ = lean_ctor_get(v_impl_3512_, 1);
v_v_3602_ = lean_ctor_get(v_impl_3512_, 2);
v_isSharedCheck_3613_ = !lean_is_exclusive(v_impl_3512_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; lean_object* v_unused_3615_; 
v_unused_3614_ = lean_ctor_get(v_impl_3512_, 3);
lean_dec(v_unused_3614_);
v_unused_3615_ = lean_ctor_get(v_impl_3512_, 0);
lean_dec(v_unused_3615_);
v___x_3604_ = v_impl_3512_;
v_isShared_3605_ = v_isSharedCheck_3613_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_r_3600_);
lean_inc(v_v_3602_);
lean_inc(v_k_3601_);
lean_dec(v_impl_3512_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3613_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3606_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3600_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 3, v_r_3600_);
lean_ctor_set(v___x_3604_, 2, v_v_3505_);
lean_ctor_set(v___x_3604_, 1, v_k_3504_);
lean_ctor_set(v___x_3604_, 0, v___x_3513_);
v___x_3608_ = v___x_3604_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_k_3504_);
lean_ctor_set(v_reuseFailAlloc_3612_, 2, v_v_3505_);
lean_ctor_set(v_reuseFailAlloc_3612_, 3, v_r_3600_);
lean_ctor_set(v_reuseFailAlloc_3612_, 4, v_r_3600_);
v___x_3608_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3610_; 
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 4, v___x_3608_);
lean_ctor_set(v___x_3509_, 3, v_l_3599_);
lean_ctor_set(v___x_3509_, 2, v_v_3602_);
lean_ctor_set(v___x_3509_, 1, v_k_3601_);
lean_ctor_set(v___x_3509_, 0, v___x_3606_);
v___x_3610_ = v___x_3509_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3606_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_k_3601_);
lean_ctor_set(v_reuseFailAlloc_3611_, 2, v_v_3602_);
lean_ctor_set(v_reuseFailAlloc_3611_, 3, v_l_3599_);
lean_ctor_set(v_reuseFailAlloc_3611_, 4, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
else
{
lean_object* v_r_3616_; 
v_r_3616_ = lean_ctor_get(v_impl_3512_, 4);
lean_inc(v_r_3616_);
if (lean_obj_tag(v_r_3616_) == 0)
{
lean_object* v_k_3617_; lean_object* v_v_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3641_; 
v_k_3617_ = lean_ctor_get(v_impl_3512_, 1);
v_v_3618_ = lean_ctor_get(v_impl_3512_, 2);
v_isSharedCheck_3641_ = !lean_is_exclusive(v_impl_3512_);
if (v_isSharedCheck_3641_ == 0)
{
lean_object* v_unused_3642_; lean_object* v_unused_3643_; lean_object* v_unused_3644_; 
v_unused_3642_ = lean_ctor_get(v_impl_3512_, 4);
lean_dec(v_unused_3642_);
v_unused_3643_ = lean_ctor_get(v_impl_3512_, 3);
lean_dec(v_unused_3643_);
v_unused_3644_ = lean_ctor_get(v_impl_3512_, 0);
lean_dec(v_unused_3644_);
v___x_3620_ = v_impl_3512_;
v_isShared_3621_ = v_isSharedCheck_3641_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_v_3618_);
lean_inc(v_k_3617_);
lean_dec(v_impl_3512_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3641_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v_k_3622_; lean_object* v_v_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3637_; 
v_k_3622_ = lean_ctor_get(v_r_3616_, 1);
v_v_3623_ = lean_ctor_get(v_r_3616_, 2);
v_isSharedCheck_3637_ = !lean_is_exclusive(v_r_3616_);
if (v_isSharedCheck_3637_ == 0)
{
lean_object* v_unused_3638_; lean_object* v_unused_3639_; lean_object* v_unused_3640_; 
v_unused_3638_ = lean_ctor_get(v_r_3616_, 4);
lean_dec(v_unused_3638_);
v_unused_3639_ = lean_ctor_get(v_r_3616_, 3);
lean_dec(v_unused_3639_);
v_unused_3640_ = lean_ctor_get(v_r_3616_, 0);
lean_dec(v_unused_3640_);
v___x_3625_ = v_r_3616_;
v_isShared_3626_ = v_isSharedCheck_3637_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_v_3623_);
lean_inc(v_k_3622_);
lean_dec(v_r_3616_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3637_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3627_; lean_object* v___x_3629_; 
v___x_3627_ = lean_unsigned_to_nat(3u);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 4, v_l_3599_);
lean_ctor_set(v___x_3625_, 3, v_l_3599_);
lean_ctor_set(v___x_3625_, 2, v_v_3618_);
lean_ctor_set(v___x_3625_, 1, v_k_3617_);
lean_ctor_set(v___x_3625_, 0, v___x_3513_);
v___x_3629_ = v___x_3625_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v_k_3617_);
lean_ctor_set(v_reuseFailAlloc_3636_, 2, v_v_3618_);
lean_ctor_set(v_reuseFailAlloc_3636_, 3, v_l_3599_);
lean_ctor_set(v_reuseFailAlloc_3636_, 4, v_l_3599_);
v___x_3629_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
lean_object* v___x_3631_; 
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 4, v_l_3599_);
lean_ctor_set(v___x_3620_, 2, v_v_3505_);
lean_ctor_set(v___x_3620_, 1, v_k_3504_);
lean_ctor_set(v___x_3620_, 0, v___x_3513_);
v___x_3631_ = v___x_3620_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_k_3504_);
lean_ctor_set(v_reuseFailAlloc_3635_, 2, v_v_3505_);
lean_ctor_set(v_reuseFailAlloc_3635_, 3, v_l_3599_);
lean_ctor_set(v_reuseFailAlloc_3635_, 4, v_l_3599_);
v___x_3631_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3633_; 
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 4, v___x_3631_);
lean_ctor_set(v___x_3509_, 3, v___x_3629_);
lean_ctor_set(v___x_3509_, 2, v_v_3623_);
lean_ctor_set(v___x_3509_, 1, v_k_3622_);
lean_ctor_set(v___x_3509_, 0, v___x_3627_);
v___x_3633_ = v___x_3509_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3627_);
lean_ctor_set(v_reuseFailAlloc_3634_, 1, v_k_3622_);
lean_ctor_set(v_reuseFailAlloc_3634_, 2, v_v_3623_);
lean_ctor_set(v_reuseFailAlloc_3634_, 3, v___x_3629_);
lean_ctor_set(v_reuseFailAlloc_3634_, 4, v___x_3631_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
}
else
{
lean_object* v___x_3645_; lean_object* v___x_3647_; 
v___x_3645_ = lean_unsigned_to_nat(2u);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 4, v_r_3616_);
lean_ctor_set(v___x_3509_, 3, v_impl_3512_);
lean_ctor_set(v___x_3509_, 0, v___x_3645_);
v___x_3647_ = v___x_3509_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_k_3504_);
lean_ctor_set(v_reuseFailAlloc_3648_, 2, v_v_3505_);
lean_ctor_set(v_reuseFailAlloc_3648_, 3, v_impl_3512_);
lean_ctor_set(v_reuseFailAlloc_3648_, 4, v_r_3616_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3650_; 
lean_dec(v_v_3505_);
lean_dec(v_k_3504_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 2, v_v_3501_);
lean_ctor_set(v___x_3509_, 1, v_k_3500_);
v___x_3650_ = v___x_3509_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_size_3503_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_k_3500_);
lean_ctor_set(v_reuseFailAlloc_3651_, 2, v_v_3501_);
lean_ctor_set(v_reuseFailAlloc_3651_, 3, v_l_3506_);
lean_ctor_set(v_reuseFailAlloc_3651_, 4, v_r_3507_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
default: 
{
lean_object* v_impl_3652_; lean_object* v___x_3653_; 
lean_dec(v_size_3503_);
v_impl_3652_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3500_, v_v_3501_, v_r_3507_);
v___x_3653_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3506_) == 0)
{
lean_object* v_size_3654_; lean_object* v_size_3655_; lean_object* v_k_3656_; lean_object* v_v_3657_; lean_object* v_l_3658_; lean_object* v_r_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
v_size_3654_ = lean_ctor_get(v_l_3506_, 0);
v_size_3655_ = lean_ctor_get(v_impl_3652_, 0);
lean_inc(v_size_3655_);
v_k_3656_ = lean_ctor_get(v_impl_3652_, 1);
lean_inc(v_k_3656_);
v_v_3657_ = lean_ctor_get(v_impl_3652_, 2);
lean_inc(v_v_3657_);
v_l_3658_ = lean_ctor_get(v_impl_3652_, 3);
lean_inc(v_l_3658_);
v_r_3659_ = lean_ctor_get(v_impl_3652_, 4);
lean_inc(v_r_3659_);
v___x_3660_ = lean_unsigned_to_nat(3u);
v___x_3661_ = lean_nat_mul(v___x_3660_, v_size_3654_);
v___x_3662_ = lean_nat_dec_lt(v___x_3661_, v_size_3655_);
lean_dec(v___x_3661_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3666_; 
lean_dec(v_r_3659_);
lean_dec(v_l_3658_);
lean_dec(v_v_3657_);
lean_dec(v_k_3656_);
v___x_3663_ = lean_nat_add(v___x_3653_, v_size_3654_);
v___x_3664_ = lean_nat_add(v___x_3663_, v_size_3655_);
lean_dec(v_size_3655_);
lean_dec(v___x_3663_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 4, v_impl_3652_);
lean_ctor_set(v___x_3509_, 0, v___x_3664_);
v___x_3666_ = v___x_3509_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_k_3504_);
lean_ctor_set(v_reuseFailAlloc_3667_, 2, v_v_3505_);
lean_ctor_set(v_reuseFailAlloc_3667_, 3, v_l_3506_);
lean_ctor_set(v_reuseFailAlloc_3667_, 4, v_impl_3652_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
else
{
lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3731_; 
v_isSharedCheck_3731_ = !lean_is_exclusive(v_impl_3652_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; lean_object* v_unused_3733_; lean_object* v_unused_3734_; lean_object* v_unused_3735_; lean_object* v_unused_3736_; 
v_unused_3732_ = lean_ctor_get(v_impl_3652_, 4);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_impl_3652_, 3);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_impl_3652_, 2);
lean_dec(v_unused_3734_);
v_unused_3735_ = lean_ctor_get(v_impl_3652_, 1);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_impl_3652_, 0);
lean_dec(v_unused_3736_);
v___x_3669_ = v_impl_3652_;
v_isShared_3670_ = v_isSharedCheck_3731_;
goto v_resetjp_3668_;
}
else
{
lean_dec(v_impl_3652_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3731_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v_size_3671_; lean_object* v_k_3672_; lean_object* v_v_3673_; lean_object* v_l_3674_; lean_object* v_r_3675_; lean_object* v_size_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; uint8_t v___x_3679_; 
v_size_3671_ = lean_ctor_get(v_l_3658_, 0);
v_k_3672_ = lean_ctor_get(v_l_3658_, 1);
v_v_3673_ = lean_ctor_get(v_l_3658_, 2);
v_l_3674_ = lean_ctor_get(v_l_3658_, 3);
v_r_3675_ = lean_ctor_get(v_l_3658_, 4);
v_size_3676_ = lean_ctor_get(v_r_3659_, 0);
v___x_3677_ = lean_unsigned_to_nat(2u);
v___x_3678_ = lean_nat_mul(v___x_3677_, v_size_3676_);
v___x_3679_ = lean_nat_dec_lt(v_size_3671_, v___x_3678_);
lean_dec(v___x_3678_);
if (v___x_3679_ == 0)
{
lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3707_; 
lean_inc(v_r_3675_);
lean_inc(v_l_3674_);
lean_inc(v_v_3673_);
lean_inc(v_k_3672_);
v_isSharedCheck_3707_ = !lean_is_exclusive(v_l_3658_);
if (v_isSharedCheck_3707_ == 0)
{
lean_object* v_unused_3708_; lean_object* v_unused_3709_; lean_object* v_unused_3710_; lean_object* v_unused_3711_; lean_object* v_unused_3712_; 
v_unused_3708_ = lean_ctor_get(v_l_3658_, 4);
lean_dec(v_unused_3708_);
v_unused_3709_ = lean_ctor_get(v_l_3658_, 3);
lean_dec(v_unused_3709_);
v_unused_3710_ = lean_ctor_get(v_l_3658_, 2);
lean_dec(v_unused_3710_);
v_unused_3711_ = lean_ctor_get(v_l_3658_, 1);
lean_dec(v_unused_3711_);
v_unused_3712_ = lean_ctor_get(v_l_3658_, 0);
lean_dec(v_unused_3712_);
v___x_3681_ = v_l_3658_;
v_isShared_3682_ = v_isSharedCheck_3707_;
goto v_resetjp_3680_;
}
else
{
lean_dec(v_l_3658_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3707_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3697_; 
v___x_3683_ = lean_nat_add(v___x_3653_, v_size_3654_);
v___x_3684_ = lean_nat_add(v___x_3683_, v_size_3655_);
lean_dec(v_size_3655_);
if (lean_obj_tag(v_l_3674_) == 0)
{
lean_object* v_size_3705_; 
v_size_3705_ = lean_ctor_get(v_l_3674_, 0);
lean_inc(v_size_3705_);
v___y_3697_ = v_size_3705_;
goto v___jp_3696_;
}
else
{
lean_object* v___x_3706_; 
v___x_3706_ = lean_unsigned_to_nat(0u);
v___y_3697_ = v___x_3706_;
goto v___jp_3696_;
}
v___jp_3685_:
{
lean_object* v___x_3689_; lean_object* v___x_3691_; 
v___x_3689_ = lean_nat_add(v___y_3686_, v___y_3688_);
lean_dec(v___y_3688_);
lean_dec(v___y_3686_);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 4, v_r_3659_);
lean_ctor_set(v___x_3681_, 3, v_r_3675_);
lean_ctor_set(v___x_3681_, 2, v_v_3657_);
lean_ctor_set(v___x_3681_, 1, v_k_3656_);
lean_ctor_set(v___x_3681_, 0, v___x_3689_);
v___x_3691_ = v___x_3681_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v_k_3656_);
lean_ctor_set(v_reuseFailAlloc_3695_, 2, v_v_3657_);
lean_ctor_set(v_reuseFailAlloc_3695_, 3, v_r_3675_);
lean_ctor_set(v_reuseFailAlloc_3695_, 4, v_r_3659_);
v___x_3691_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3693_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 4, v___x_3691_);
lean_ctor_set(v___x_3669_, 3, v___y_3687_);
lean_ctor_set(v___x_3669_, 2, v_v_3673_);
lean_ctor_set(v___x_3669_, 1, v_k_3672_);
lean_ctor_set(v___x_3669_, 0, v___x_3684_);
v___x_3693_ = v___x_3669_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3684_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_k_3672_);
lean_ctor_set(v_reuseFailAlloc_3694_, 2, v_v_3673_);
lean_ctor_set(v_reuseFailAlloc_3694_, 3, v___y_3687_);
lean_ctor_set(v_reuseFailAlloc_3694_, 4, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
v___jp_3696_:
{
lean_object* v___x_3698_; lean_object* v___x_3700_; 
v___x_3698_ = lean_nat_add(v___x_3683_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec(v___x_3683_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 4, v_l_3674_);
lean_ctor_set(v___x_3509_, 0, v___x_3698_);
v___x_3700_ = v___x_3509_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v_k_3504_);
lean_ctor_set(v_reuseFailAlloc_3704_, 2, v_v_3505_);
lean_ctor_set(v_reuseFailAlloc_3704_, 3, v_l_3506_);
lean_ctor_set(v_reuseFailAlloc_3704_, 4, v_l_3674_);
v___x_3700_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
lean_object* v___x_3701_; 
v___x_3701_ = lean_nat_add(v___x_3653_, v_size_3676_);
if (lean_obj_tag(v_r_3675_) == 0)
{
lean_object* v_size_3702_; 
v_size_3702_ = lean_ctor_get(v_r_3675_, 0);
lean_inc(v_size_3702_);
v___y_3686_ = v___x_3701_;
v___y_3687_ = v___x_3700_;
v___y_3688_ = v_size_3702_;
goto v___jp_3685_;
}
else
{
lean_object* v___x_3703_; 
v___x_3703_ = lean_unsigned_to_nat(0u);
v___y_3686_ = v___x_3701_;
v___y_3687_ = v___x_3700_;
v___y_3688_ = v___x_3703_;
goto v___jp_3685_;
}
}
}
}
}
else
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3717_; 
lean_del_object(v___x_3509_);
v___x_3713_ = lean_nat_add(v___x_3653_, v_size_3654_);
v___x_3714_ = lean_nat_add(v___x_3713_, v_size_3655_);
lean_dec(v_size_3655_);
v___x_3715_ = lean_nat_add(v___x_3713_, v_size_3671_);
lean_dec(v___x_3713_);
lean_inc_ref(v_l_3506_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 4, v_l_3658_);
lean_ctor_set(v___x_3669_, 3, v_l_3506_);
lean_ctor_set(v___x_3669_, 2, v_v_3505_);
lean_ctor_set(v___x_3669_, 1, v_k_3504_);
lean_ctor_set(v___x_3669_, 0, v___x_3715_);
v___x_3717_ = v___x_3669_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3715_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_k_3504_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v_v_3505_);
lean_ctor_set(v_reuseFailAlloc_3730_, 3, v_l_3506_);
lean_ctor_set(v_reuseFailAlloc_3730_, 4, v_l_3658_);
v___x_3717_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
v_isSharedCheck_3724_ = !lean_is_exclusive(v_l_3506_);
if (v_isSharedCheck_3724_ == 0)
{
lean_object* v_unused_3725_; lean_object* v_unused_3726_; lean_object* v_unused_3727_; lean_object* v_unused_3728_; lean_object* v_unused_3729_; 
v_unused_3725_ = lean_ctor_get(v_l_3506_, 4);
lean_dec(v_unused_3725_);
v_unused_3726_ = lean_ctor_get(v_l_3506_, 3);
lean_dec(v_unused_3726_);
v_unused_3727_ = lean_ctor_get(v_l_3506_, 2);
lean_dec(v_unused_3727_);
v_unused_3728_ = lean_ctor_get(v_l_3506_, 1);
lean_dec(v_unused_3728_);
v_unused_3729_ = lean_ctor_get(v_l_3506_, 0);
lean_dec(v_unused_3729_);
v___x_3719_ = v_l_3506_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_dec(v_l_3506_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 4, v_r_3659_);
lean_ctor_set(v___x_3719_, 3, v___x_3717_);
lean_ctor_set(v___x_3719_, 2, v_v_3657_);
lean_ctor_set(v___x_3719_, 1, v_k_3656_);
lean_ctor_set(v___x_3719_, 0, v___x_3714_);
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3714_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_k_3656_);
lean_ctor_set(v_reuseFailAlloc_3723_, 2, v_v_3657_);
lean_ctor_set(v_reuseFailAlloc_3723_, 3, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3723_, 4, v_r_3659_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3737_; 
v_l_3737_ = lean_ctor_get(v_impl_3652_, 3);
lean_inc(v_l_3737_);
if (lean_obj_tag(v_l_3737_) == 0)
{
lean_object* v_r_3738_; lean_object* v_k_3739_; lean_object* v_v_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3763_; 
v_r_3738_ = lean_ctor_get(v_impl_3652_, 4);
v_k_3739_ = lean_ctor_get(v_impl_3652_, 1);
v_v_3740_ = lean_ctor_get(v_impl_3652_, 2);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_impl_3652_);
if (v_isSharedCheck_3763_ == 0)
{
lean_object* v_unused_3764_; lean_object* v_unused_3765_; 
v_unused_3764_ = lean_ctor_get(v_impl_3652_, 3);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_impl_3652_, 0);
lean_dec(v_unused_3765_);
v___x_3742_ = v_impl_3652_;
v_isShared_3743_ = v_isSharedCheck_3763_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_r_3738_);
lean_inc(v_v_3740_);
lean_inc(v_k_3739_);
lean_dec(v_impl_3652_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3763_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v_k_3744_; lean_object* v_v_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3759_; 
v_k_3744_ = lean_ctor_get(v_l_3737_, 1);
v_v_3745_ = lean_ctor_get(v_l_3737_, 2);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_l_3737_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; lean_object* v_unused_3761_; lean_object* v_unused_3762_; 
v_unused_3760_ = lean_ctor_get(v_l_3737_, 4);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_l_3737_, 3);
lean_dec(v_unused_3761_);
v_unused_3762_ = lean_ctor_get(v_l_3737_, 0);
lean_dec(v_unused_3762_);
v___x_3747_ = v_l_3737_;
v_isShared_3748_ = v_isSharedCheck_3759_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_v_3745_);
lean_inc(v_k_3744_);
lean_dec(v_l_3737_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3759_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3749_; lean_object* v___x_3751_; 
v___x_3749_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3738_, 2);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 4, v_r_3738_);
lean_ctor_set(v___x_3747_, 3, v_r_3738_);
lean_ctor_set(v___x_3747_, 2, v_v_3505_);
lean_ctor_set(v___x_3747_, 1, v_k_3504_);
lean_ctor_set(v___x_3747_, 0, v___x_3653_);
v___x_3751_ = v___x_3747_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_k_3504_);
lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_v_3505_);
lean_ctor_set(v_reuseFailAlloc_3758_, 3, v_r_3738_);
lean_ctor_set(v_reuseFailAlloc_3758_, 4, v_r_3738_);
v___x_3751_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
lean_object* v___x_3753_; 
lean_inc(v_r_3738_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 3, v_r_3738_);
lean_ctor_set(v___x_3742_, 0, v___x_3653_);
v___x_3753_ = v___x_3742_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3757_, 1, v_k_3739_);
lean_ctor_set(v_reuseFailAlloc_3757_, 2, v_v_3740_);
lean_ctor_set(v_reuseFailAlloc_3757_, 3, v_r_3738_);
lean_ctor_set(v_reuseFailAlloc_3757_, 4, v_r_3738_);
v___x_3753_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
lean_object* v___x_3755_; 
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 4, v___x_3753_);
lean_ctor_set(v___x_3509_, 3, v___x_3751_);
lean_ctor_set(v___x_3509_, 2, v_v_3745_);
lean_ctor_set(v___x_3509_, 1, v_k_3744_);
lean_ctor_set(v___x_3509_, 0, v___x_3749_);
v___x_3755_ = v___x_3509_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3749_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_k_3744_);
lean_ctor_set(v_reuseFailAlloc_3756_, 2, v_v_3745_);
lean_ctor_set(v_reuseFailAlloc_3756_, 3, v___x_3751_);
lean_ctor_set(v_reuseFailAlloc_3756_, 4, v___x_3753_);
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
else
{
lean_object* v_r_3766_; 
v_r_3766_ = lean_ctor_get(v_impl_3652_, 4);
lean_inc(v_r_3766_);
if (lean_obj_tag(v_r_3766_) == 0)
{
lean_object* v_k_3767_; lean_object* v_v_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3779_; 
v_k_3767_ = lean_ctor_get(v_impl_3652_, 1);
v_v_3768_ = lean_ctor_get(v_impl_3652_, 2);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_impl_3652_);
if (v_isSharedCheck_3779_ == 0)
{
lean_object* v_unused_3780_; lean_object* v_unused_3781_; lean_object* v_unused_3782_; 
v_unused_3780_ = lean_ctor_get(v_impl_3652_, 4);
lean_dec(v_unused_3780_);
v_unused_3781_ = lean_ctor_get(v_impl_3652_, 3);
lean_dec(v_unused_3781_);
v_unused_3782_ = lean_ctor_get(v_impl_3652_, 0);
lean_dec(v_unused_3782_);
v___x_3770_ = v_impl_3652_;
v_isShared_3771_ = v_isSharedCheck_3779_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_v_3768_);
lean_inc(v_k_3767_);
lean_dec(v_impl_3652_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3779_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3772_; lean_object* v___x_3774_; 
v___x_3772_ = lean_unsigned_to_nat(3u);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 4, v_l_3737_);
lean_ctor_set(v___x_3770_, 2, v_v_3505_);
lean_ctor_set(v___x_3770_, 1, v_k_3504_);
lean_ctor_set(v___x_3770_, 0, v___x_3653_);
v___x_3774_ = v___x_3770_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_k_3504_);
lean_ctor_set(v_reuseFailAlloc_3778_, 2, v_v_3505_);
lean_ctor_set(v_reuseFailAlloc_3778_, 3, v_l_3737_);
lean_ctor_set(v_reuseFailAlloc_3778_, 4, v_l_3737_);
v___x_3774_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
lean_object* v___x_3776_; 
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 4, v_r_3766_);
lean_ctor_set(v___x_3509_, 3, v___x_3774_);
lean_ctor_set(v___x_3509_, 2, v_v_3768_);
lean_ctor_set(v___x_3509_, 1, v_k_3767_);
lean_ctor_set(v___x_3509_, 0, v___x_3772_);
v___x_3776_ = v___x_3509_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3772_);
lean_ctor_set(v_reuseFailAlloc_3777_, 1, v_k_3767_);
lean_ctor_set(v_reuseFailAlloc_3777_, 2, v_v_3768_);
lean_ctor_set(v_reuseFailAlloc_3777_, 3, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3777_, 4, v_r_3766_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
else
{
lean_object* v___x_3783_; lean_object* v___x_3785_; 
v___x_3783_ = lean_unsigned_to_nat(2u);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 4, v_impl_3652_);
lean_ctor_set(v___x_3509_, 3, v_r_3766_);
lean_ctor_set(v___x_3509_, 0, v___x_3783_);
v___x_3785_ = v___x_3509_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_k_3504_);
lean_ctor_set(v_reuseFailAlloc_3786_, 2, v_v_3505_);
lean_ctor_set(v_reuseFailAlloc_3786_, 3, v_r_3766_);
lean_ctor_set(v_reuseFailAlloc_3786_, 4, v_impl_3652_);
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
}
}
}
}
else
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3788_ = lean_unsigned_to_nat(1u);
v___x_3789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
lean_ctor_set(v___x_3789_, 1, v_k_3500_);
lean_ctor_set(v___x_3789_, 2, v_v_3501_);
lean_ctor_set(v___x_3789_, 3, v_t_3502_);
lean_ctor_set(v___x_3789_, 4, v_t_3502_);
return v___x_3789_;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3790_ = lean_box(1);
v___x_3791_ = l_Lake_LeanLib_defaultFacetConfig;
v___x_3792_ = l_Lake_LeanLib_defaultFacet;
v___x_3793_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3792_, v___x_3791_, v___x_3790_);
return v___x_3793_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3794_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__0, &l_Lake_LeanLib_initFacetConfigs___closed__0_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__0);
v___x_3795_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig));
v___x_3796_ = l_Lake_LeanLib_modulesFacet;
v___x_3797_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3796_, v___x_3795_, v___x_3794_);
return v___x_3797_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3798_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__1, &l_Lake_LeanLib_initFacetConfigs___closed__1_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__1);
v___x_3799_ = l_Lake_LeanLib_leanArtsFacetConfig;
v___x_3800_ = l_Lake_LeanLib_leanArtsFacet;
v___x_3801_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3800_, v___x_3799_, v___x_3798_);
return v___x_3801_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3802_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__2, &l_Lake_LeanLib_initFacetConfigs___closed__2_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__2);
v___x_3803_ = l_Lake_LeanLib_staticFacetConfig;
v___x_3804_ = l_Lake_LeanLib_staticFacet;
v___x_3805_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3804_, v___x_3803_, v___x_3802_);
return v___x_3805_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3806_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__3, &l_Lake_LeanLib_initFacetConfigs___closed__3_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__3);
v___x_3807_ = l_Lake_LeanLib_staticExportFacetConfig;
v___x_3808_ = l_Lake_LeanLib_staticExportFacet;
v___x_3809_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3808_, v___x_3807_, v___x_3806_);
return v___x_3809_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3810_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__4, &l_Lake_LeanLib_initFacetConfigs___closed__4_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__4);
v___x_3811_ = l_Lake_LeanLib_sharedFacetConfig;
v___x_3812_ = l_Lake_LeanLib_sharedFacet;
v___x_3813_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3812_, v___x_3811_, v___x_3810_);
return v___x_3813_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3814_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__5, &l_Lake_LeanLib_initFacetConfigs___closed__5_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__5);
v___x_3815_ = l_Lake_LeanLib_extraDepFacetConfig;
v___x_3816_ = l_Lake_LeanLib_extraDepFacet;
v___x_3817_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3816_, v___x_3815_, v___x_3814_);
return v___x_3817_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_3818_; 
v___x_3818_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__6, &l_Lake_LeanLib_initFacetConfigs___closed__6_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__6);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3819_, lean_object* v_k_3820_, lean_object* v_v_3821_, lean_object* v_t_3822_, lean_object* v_hl_3823_){
_start:
{
lean_object* v___x_3824_; 
v___x_3824_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3820_, v_v_3821_, v_t_3822_);
return v___x_3824_;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs(void){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = l_Lake_LeanLib_initFacetConfigs;
return v___x_3825_;
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
