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
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lake_Target_fetchIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lake_Module_elabArtsFacet;
lean_object* l_Lake_Job_mix___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanLib_elabArtsFacet;
extern lean_object* l_Lake_Module_irArtsFacet;
extern lean_object* l_Lake_LeanLib_irArtsFacet;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__0_value;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__1;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__2;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__3;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_elabArtsFacetConfig___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_elabArtsFacetConfig___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLib_elabArtsFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLib_elabArtsFacetConfig___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLib_elabArtsFacetConfig___closed__0 = (const lean_object*)&l_Lake_LeanLib_elabArtsFacetConfig___closed__0_value;
static const lean_closure_object l_Lake_LeanLib_elabArtsFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLib_elabArtsFacetConfig___closed__1 = (const lean_object*)&l_Lake_LeanLib_elabArtsFacetConfig___closed__1_value;
static lean_once_cell_t l_Lake_LeanLib_elabArtsFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_elabArtsFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_LeanLib_elabArtsFacetConfig;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLib_irArtsFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLib_irArtsFacetConfig___closed__0 = (const lean_object*)&l_Lake_LeanLib_irArtsFacetConfig___closed__0_value;
static lean_once_cell_t l_Lake_LeanLib_irArtsFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_irArtsFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLib_irArtsFacetConfig;
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanLib_leanArtsFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanLib_leanArtsFacetConfig___closed__0 = (const lean_object*)&l_Lake_LeanLib_leanArtsFacetConfig___closed__0_value;
static lean_once_cell_t l_Lake_LeanLib_leanArtsFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_leanArtsFacetConfig___closed__1;
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
static lean_once_cell_t l_Lake_LeanLib_initFacetConfigs___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__7;
static lean_once_cell_t l_Lake_LeanLib_initFacetConfigs___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanLib_initFacetConfigs___closed__8;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0(lean_object* v_as_566_, size_t v_i_567_, size_t v_stop_568_, lean_object* v_b_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
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
v___x_583_ = l_Lake_Module_elabArtsFacet;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0___boxed(lean_object* v_as_604_, lean_object* v_i_605_, lean_object* v_stop_606_, lean_object* v_b_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
size_t v_i_boxed_615_; size_t v_stop_boxed_616_; lean_object* v_res_617_; 
v_i_boxed_615_ = lean_unbox_usize(v_i_605_);
lean_dec(v_i_605_);
v_stop_boxed_616_ = lean_unbox_usize(v_stop_606_);
lean_dec(v_stop_606_);
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0(v_as_604_, v_i_boxed_615_, v_stop_boxed_616_, v_b_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v_as_604_);
return v_res_617_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__1(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_622_ = 0;
v___x_623_ = 0;
v___x_624_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__0));
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
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__2(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__1);
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_626_);
return v___x_628_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__3(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__2);
v___x_630_ = lean_task_pure(v___x_629_);
return v___x_630_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4(void){
_start:
{
uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_631_ = 0;
v___x_632_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_633_ = lean_box(0);
v___x_634_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__3);
v___x_635_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_633_);
lean_ctor_set(v___x_635_, 2, v___x_632_);
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*3, v___x_631_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts(lean_object* v_self_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
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
v___x_661_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4);
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
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0(v_a_655_, v___x_671_, v___x_672_, v___x_661_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_656_);
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
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0(v_a_655_, v___x_674_, v___x_675_, v___x_661_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_656_);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___boxed(lean_object* v_self_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts(v_self_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec(v_a_699_);
lean_dec(v_a_698_);
return v_res_704_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_box(0);
v___x_706_ = l_Lean_Json_compress(v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(uint8_t v_fmt_707_){
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
v___x_709_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_710_){
_start:
{
uint8_t v_fmt_boxed_711_; lean_object* v_res_712_; 
v_fmt_boxed_711_ = lean_unbox(v_fmt_710_);
v_res_712_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(v_fmt_boxed_711_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0(uint8_t v_fmt_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(v_fmt_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___boxed(lean_object* v_fmt_716_, lean_object* v_a_717_){
_start:
{
uint8_t v_fmt_boxed_718_; lean_object* v_res_719_; 
v_fmt_boxed_718_ = lean_unbox(v_fmt_716_);
v_res_719_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0(v_fmt_boxed_718_, v_a_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_elabArtsFacetConfig___lam__0(uint8_t v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(v___y_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_elabArtsFacetConfig___lam__0___boxed(lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
uint8_t v___y_68__boxed_725_; lean_object* v_res_726_; 
v___y_68__boxed_725_ = lean_unbox(v___y_723_);
v_res_726_ = l_Lake_LeanLib_elabArtsFacetConfig___lam__0(v___y_68__boxed_725_, v___y_724_);
return v_res_726_;
}
}
static lean_object* _init_l_Lake_LeanLib_elabArtsFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_729_; uint8_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___f_729_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_730_ = 1;
v___x_731_ = l_Lake_instDataKindUnit;
v___x_732_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__1));
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
static lean_object* _init_l_Lake_LeanLib_elabArtsFacetConfig(void){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_obj_once(&l_Lake_LeanLib_elabArtsFacetConfig___closed__2, &l_Lake_LeanLib_elabArtsFacetConfig___closed__2_once, _init_l_Lake_LeanLib_elabArtsFacetConfig___closed__2);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(lean_object* v_as_736_, size_t v_i_737_, size_t v_stop_738_, lean_object* v_b_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
uint8_t v___x_747_; 
v___x_747_ = lean_usize_dec_eq(v_i_737_, v_stop_738_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v_lib_749_; lean_object* v_pkg_750_; lean_object* v_name_751_; lean_object* v_keyName_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_748_ = lean_array_uget_borrowed(v_as_736_, v_i_737_);
v_lib_749_ = lean_ctor_get(v___x_748_, 0);
v_pkg_750_ = lean_ctor_get(v_lib_749_, 0);
v_name_751_ = lean_ctor_get(v___x_748_, 1);
v_keyName_752_ = lean_ctor_get(v_pkg_750_, 2);
v___x_753_ = l_Lake_Module_irArtsFacet;
lean_inc(v_name_751_);
lean_inc(v_keyName_752_);
v___x_754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_754_, 0, v_keyName_752_);
lean_ctor_set(v___x_754_, 1, v_name_751_);
v___x_755_ = l_Lake_Module_keyword;
lean_inc(v___x_748_);
v___x_756_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
lean_ctor_set(v___x_756_, 2, v___x_748_);
lean_ctor_set(v___x_756_, 3, v___x_753_);
lean_inc_ref(v___y_740_);
lean_inc_ref(v___y_744_);
lean_inc(v___y_743_);
lean_inc(v___y_742_);
lean_inc(v___y_741_);
v___x_757_ = lean_apply_7(v___y_740_, v___x_756_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, lean_box(0));
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v_a_759_; lean_object* v___x_760_; size_t v___x_761_; size_t v___x_762_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
v_a_759_ = lean_ctor_get(v___x_757_, 1);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_757_, 2);
v___x_760_ = l_Lake_Job_mix___redArg(v_b_739_, v_a_758_);
v___x_761_ = ((size_t)1ULL);
v___x_762_ = lean_usize_add(v_i_737_, v___x_761_);
v_i_737_ = v___x_762_;
v_b_739_ = v___x_760_;
v___y_745_ = v_a_759_;
goto _start;
}
else
{
lean_object* v_a_764_; lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec_ref(v___y_740_);
lean_dec_ref(v_b_739_);
v_a_764_ = lean_ctor_get(v___x_757_, 0);
v_a_765_ = lean_ctor_get(v___x_757_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_757_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_inc(v_a_764_);
lean_dec(v___x_757_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_764_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
else
{
lean_object* v___x_773_; 
lean_dec_ref(v___y_740_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_b_739_);
lean_ctor_set(v___x_773_, 1, v___y_745_);
return v___x_773_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0___boxed(lean_object* v_as_774_, lean_object* v_i_775_, lean_object* v_stop_776_, lean_object* v_b_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
size_t v_i_boxed_785_; size_t v_stop_boxed_786_; lean_object* v_res_787_; 
v_i_boxed_785_ = lean_unbox_usize(v_i_775_);
lean_dec(v_i_775_);
v_stop_boxed_786_ = lean_unbox_usize(v_stop_776_);
lean_dec(v_stop_776_);
v_res_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(v_as_774_, v_i_boxed_785_, v_stop_boxed_786_, v_b_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v_as_774_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts(lean_object* v_self_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_pkg_796_; lean_object* v_name_797_; lean_object* v_keyName_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_pkg_796_ = lean_ctor_get(v_self_788_, 0);
v_name_797_ = lean_ctor_get(v_self_788_, 1);
v_keyName_798_ = lean_ctor_get(v_pkg_796_, 2);
v___x_799_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_797_);
lean_inc(v_keyName_798_);
v___x_800_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_800_, 0, v_keyName_798_);
lean_ctor_set(v___x_800_, 1, v_name_797_);
v___x_801_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_802_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
lean_ctor_set(v___x_802_, 2, v_self_788_);
lean_ctor_set(v___x_802_, 3, v___x_799_);
lean_inc_ref(v_a_789_);
lean_inc_ref(v_a_793_);
lean_inc(v_a_792_);
lean_inc(v_a_791_);
lean_inc(v_a_790_);
v___x_803_ = lean_apply_7(v_a_789_, v___x_802_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, lean_box(0));
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v_a_805_; lean_object* v___x_806_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
v_a_805_ = lean_ctor_get(v___x_803_, 1);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_803_, 2);
v___x_806_ = l_Lake_Job_await___redArg(v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_829_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_a_808_ = lean_ctor_get(v___x_806_, 1);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_829_ == 0)
{
v___x_810_ = v___x_806_;
v_isShared_811_ = v_isSharedCheck_829_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_829_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4);
v___x_814_ = lean_array_get_size(v_a_807_);
v___x_815_ = lean_nat_dec_lt(v___x_812_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_817_; 
lean_dec(v_a_807_);
lean_dec_ref(v_a_789_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_813_);
v___x_817_ = v___x_810_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_a_808_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
else
{
uint8_t v___x_819_; 
v___x_819_ = lean_nat_dec_le(v___x_814_, v___x_814_);
if (v___x_819_ == 0)
{
if (v___x_815_ == 0)
{
lean_object* v___x_821_; 
lean_dec(v_a_807_);
lean_dec_ref(v_a_789_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_813_);
v___x_821_ = v___x_810_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_a_808_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
size_t v___x_823_; size_t v___x_824_; lean_object* v___x_825_; 
lean_del_object(v___x_810_);
v___x_823_ = ((size_t)0ULL);
v___x_824_ = lean_usize_of_nat(v___x_814_);
v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(v_a_807_, v___x_823_, v___x_824_, v___x_813_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_808_);
lean_dec(v_a_807_);
return v___x_825_;
}
}
else
{
size_t v___x_826_; size_t v___x_827_; lean_object* v___x_828_; 
lean_del_object(v___x_810_);
v___x_826_ = ((size_t)0ULL);
v___x_827_ = lean_usize_of_nat(v___x_814_);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(v_a_807_, v___x_826_, v___x_827_, v___x_813_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_808_);
lean_dec(v_a_807_);
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_830_; lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v_a_789_);
v_a_830_ = lean_ctor_get(v___x_806_, 0);
v_a_831_ = lean_ctor_get(v___x_806_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_806_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_inc(v_a_830_);
lean_dec(v___x_806_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_830_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
else
{
lean_object* v_a_839_; lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v_a_789_);
v_a_839_ = lean_ctor_get(v___x_803_, 0);
v_a_840_ = lean_ctor_get(v___x_803_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_803_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_inc(v_a_839_);
lean_dec(v___x_803_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_839_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts___boxed(lean_object* v_self_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts(v_self_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec(v_a_851_);
lean_dec(v_a_850_);
return v_res_856_;
}
}
static lean_object* _init_l_Lake_LeanLib_irArtsFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_858_; uint8_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___f_858_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_859_ = 1;
v___x_860_ = l_Lake_instDataKindUnit;
v___x_861_ = ((lean_object*)(l_Lake_LeanLib_irArtsFacetConfig___closed__0));
v___x_862_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_863_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v___x_861_);
lean_ctor_set(v___x_863_, 2, v___x_860_);
lean_ctor_set(v___x_863_, 3, v___f_858_);
lean_ctor_set_uint8(v___x_863_, sizeof(void*)*4, v___x_859_);
lean_ctor_set_uint8(v___x_863_, sizeof(void*)*4 + 1, v___x_859_);
return v___x_863_;
}
}
static lean_object* _init_l_Lake_LeanLib_irArtsFacetConfig(void){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = lean_obj_once(&l_Lake_LeanLib_irArtsFacetConfig___closed__1, &l_Lake_LeanLib_irArtsFacetConfig___closed__1_once, _init_l_Lake_LeanLib_irArtsFacetConfig___closed__1);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0(lean_object* v_x_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_pkg_873_; lean_object* v_name_874_; lean_object* v_keyName_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_pkg_873_ = lean_ctor_get(v_x_865_, 0);
v_name_874_ = lean_ctor_get(v_x_865_, 1);
v_keyName_875_ = lean_ctor_get(v_pkg_873_, 2);
v___x_876_ = l_Lake_LeanLib_irArtsFacet;
lean_inc(v_name_874_);
lean_inc(v_keyName_875_);
v___x_877_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_877_, 0, v_keyName_875_);
lean_ctor_set(v___x_877_, 1, v_name_874_);
v___x_878_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_879_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_879_, 0, v___x_877_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
lean_ctor_set(v___x_879_, 2, v_x_865_);
lean_ctor_set(v___x_879_, 3, v___x_876_);
lean_inc_ref(v___y_870_);
lean_inc(v___y_869_);
lean_inc(v___y_868_);
lean_inc(v___y_867_);
v___x_880_ = lean_apply_7(v___y_866_, v___x_879_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, lean_box(0));
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(lean_object* v_x_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lake_LeanLib_leanArtsFacetConfig___lam__0(v_x_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec(v___y_884_);
lean_dec(v___y_883_);
return v_res_889_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_891_; lean_object* v___f_892_; uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___f_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_891_ = 0;
v___f_892_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_893_ = 1;
v___x_894_ = l_Lake_instDataKindUnit;
v___f_895_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_896_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_897_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___f_895_);
lean_ctor_set(v___x_897_, 2, v___x_894_);
lean_ctor_set(v___x_897_, 3, v___f_892_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*4, v___x_893_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*4 + 1, v___x_891_);
return v___x_897_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig(void){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = lean_obj_once(&l_Lake_LeanLib_leanArtsFacetConfig___closed__1, &l_Lake_LeanLib_leanArtsFacetConfig___closed__1_once, _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__1);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(lean_object* v_a_899_, lean_object* v_x_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lake_ModuleFacet_fetch___redArg(v_x_900_, v_a_899_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object* v_a_909_, lean_object* v_x_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(v_a_909_, v_x_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec(v___y_913_);
lean_dec(v___y_912_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(uint8_t v_shouldExport_919_, lean_object* v___x_920_, lean_object* v_bs_921_, lean_object* v_a_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_lib_930_; lean_object* v_config_931_; lean_object* v_nativeFacets_932_; lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_935_; size_t v_sz_936_; size_t v___x_937_; lean_object* v___x_189790__overap_938_; lean_object* v___x_939_; 
v_lib_930_ = lean_ctor_get(v_a_922_, 0);
v_config_931_ = lean_ctor_get(v_lib_930_, 2);
v_nativeFacets_932_ = lean_ctor_get(v_config_931_, 8);
lean_inc_ref(v_nativeFacets_932_);
v___f_933_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed), 9, 1);
lean_closure_set(v___f_933_, 0, v_a_922_);
v___x_934_ = lean_box(v_shouldExport_919_);
v___x_935_ = lean_apply_1(v_nativeFacets_932_, v___x_934_);
v_sz_936_ = lean_array_size(v___x_935_);
v___x_937_ = ((size_t)0ULL);
v___x_189790__overap_938_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_920_, v___f_933_, v_sz_936_, v___x_937_, v___x_935_);
lean_inc_ref(v___y_927_);
lean_inc(v___y_926_);
lean_inc(v___y_925_);
lean_inc(v___y_924_);
v___x_939_ = lean_apply_7(v___x_189790__overap_938_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, lean_box(0));
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_949_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_a_941_ = lean_ctor_get(v___x_939_, 1);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_949_ == 0)
{
v___x_943_ = v___x_939_;
v_isShared_944_ = v_isSharedCheck_949_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_949_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_945_ = l_Array_append___redArg(v_bs_921_, v_a_940_);
lean_dec(v_a_940_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_945_);
v___x_947_ = v___x_943_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v_a_941_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
else
{
lean_dec_ref(v_bs_921_);
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed(lean_object* v_shouldExport_950_, lean_object* v___x_951_, lean_object* v_bs_952_, lean_object* v_a_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v_shouldExport_boxed_961_; lean_object* v_res_962_; 
v_shouldExport_boxed_961_ = lean_unbox(v_shouldExport_950_);
v_res_962_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(v_shouldExport_boxed_961_, v___x_951_, v_bs_952_, v_a_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec(v___y_956_);
lean_dec(v___y_955_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(lean_object* v___x_963_, lean_object* v_pkg_964_, lean_object* v_x_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lake_Target_fetchIn___redArg(v___x_963_, v_pkg_964_, v_x_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object* v___x_974_, lean_object* v_pkg_975_, lean_object* v_x_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(v___x_974_, v_pkg_975_, v_x_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec(v___y_979_);
lean_dec(v___y_978_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object* v_a_985_, lean_object* v_x_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_log_995_; uint8_t v_action_996_; uint8_t v_wantsRebuild_997_; uint8_t v_canceled_998_; lean_object* v_trace_999_; lean_object* v_buildTime_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_log_995_ = lean_ctor_get(v___y_993_, 0);
v_action_996_ = lean_ctor_get_uint8(v___y_993_, sizeof(void*)*3);
v_wantsRebuild_997_ = lean_ctor_get_uint8(v___y_993_, sizeof(void*)*3 + 1);
v_canceled_998_ = lean_ctor_get_uint8(v___y_993_, sizeof(void*)*3 + 2);
v_trace_999_ = lean_ctor_get(v___y_993_, 1);
v_buildTime_1000_ = lean_ctor_get(v___y_993_, 2);
v___x_1001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_1002_ = lean_string_append(v___y_987_, v___x_1001_);
v___x_1003_ = lean_io_prim_handle_put_str(v_a_985_, v___x_1002_);
lean_dec_ref(v___x_1002_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v_a_1004_);
lean_ctor_set(v___x_1005_, 1, v___y_993_);
return v___x_1005_;
}
else
{
lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1019_; 
lean_inc(v_buildTime_1000_);
lean_inc_ref(v_trace_999_);
lean_inc_ref(v_log_995_);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___y_993_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; lean_object* v_unused_1021_; lean_object* v_unused_1022_; 
v_unused_1020_ = lean_ctor_get(v___y_993_, 2);
lean_dec(v_unused_1020_);
v_unused_1021_ = lean_ctor_get(v___y_993_, 1);
lean_dec(v_unused_1021_);
v_unused_1022_ = lean_ctor_get(v___y_993_, 0);
lean_dec(v_unused_1022_);
v___x_1007_ = v___y_993_;
v_isShared_1008_ = v_isSharedCheck_1019_;
goto v_resetjp_1006_;
}
else
{
lean_dec(v___y_993_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1019_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_a_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v_a_1009_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1010_ = lean_io_error_to_string(v_a_1009_);
v___x_1011_ = 3;
v___x_1012_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set_uint8(v___x_1012_, sizeof(void*)*1, v___x_1011_);
v___x_1013_ = lean_array_get_size(v_log_995_);
v___x_1014_ = lean_array_push(v_log_995_, v___x_1012_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1014_);
v___x_1016_ = v___x_1007_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_trace_999_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v_buildTime_1000_);
lean_ctor_set_uint8(v_reuseFailAlloc_1018_, sizeof(void*)*3, v_action_996_);
lean_ctor_set_uint8(v_reuseFailAlloc_1018_, sizeof(void*)*3 + 1, v_wantsRebuild_997_);
lean_ctor_set_uint8(v_reuseFailAlloc_1018_, sizeof(void*)*3 + 2, v_canceled_998_);
v___x_1016_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1013_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
return v___x_1017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object* v_a_1023_, lean_object* v_x_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(v_a_1023_, v_x_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v_a_1023_);
return v_res_1033_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1041_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3));
v___x_1042_ = lean_unsigned_to_nat(5u);
v___x_1043_ = lean_mk_empty_array_with_capacity(v___x_1042_);
v___x_1044_ = lean_array_push(v___x_1043_, v___x_1041_);
return v___x_1044_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1045_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4));
v___x_1046_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6);
v___x_1047_ = lean_array_push(v___x_1046_, v___x_1045_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(uint8_t v_bootstrap_1050_, lean_object* v___y_1051_, lean_object* v_oFiles_1052_, uint8_t v_shouldExport_1053_, uint8_t v___x_1054_, lean_object* v___x_1055_, size_t v___x_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
if (v_bootstrap_1050_ == 0)
{
lean_object* v_toContext_1064_; lean_object* v_lakeEnv_1065_; lean_object* v_lean_1066_; lean_object* v_log_1067_; uint8_t v_action_1068_; uint8_t v_wantsRebuild_1069_; uint8_t v_canceled_1070_; lean_object* v_trace_1071_; lean_object* v_buildTime_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref(v___y_1057_);
lean_dec_ref(v___x_1055_);
v_toContext_1064_ = lean_ctor_get(v___y_1061_, 1);
v_lakeEnv_1065_ = lean_ctor_get(v_toContext_1064_, 0);
v_lean_1066_ = lean_ctor_get(v_lakeEnv_1065_, 1);
v_log_1067_ = lean_ctor_get(v___y_1062_, 0);
v_action_1068_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*3);
v_wantsRebuild_1069_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*3 + 1);
v_canceled_1070_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*3 + 2);
v_trace_1071_ = lean_ctor_get(v___y_1062_, 1);
v_buildTime_1072_ = lean_ctor_get(v___y_1062_, 2);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___y_1062_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1074_ = v___y_1062_;
v_isShared_1075_ = v_isSharedCheck_1102_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_buildTime_1072_);
lean_inc(v_trace_1071_);
lean_inc(v_log_1067_);
lean_dec(v___y_1062_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1102_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v_ar_1076_; lean_object* v___x_1077_; 
v_ar_1076_ = lean_ctor_get(v_lean_1066_, 13);
lean_inc_ref(v_ar_1076_);
v___x_1077_ = l_Lake_compileStaticLib(v___y_1051_, v_oFiles_1052_, v_ar_1076_, v_bootstrap_1050_, v_log_1067_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1089_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_a_1079_ = lean_ctor_get(v___x_1077_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1081_ = v___x_1077_;
v_isShared_1082_ = v_isSharedCheck_1089_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1089_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v_a_1079_);
v___x_1084_ = v___x_1074_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1079_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_trace_1071_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_buildTime_1072_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*3, v_action_1068_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*3 + 1, v_wantsRebuild_1069_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*3 + 2, v_canceled_1070_);
v___x_1084_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1086_; 
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 1, v___x_1084_);
v___x_1086_ = v___x_1081_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1078_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1101_; 
v_a_1090_ = lean_ctor_get(v___x_1077_, 0);
v_a_1091_ = lean_ctor_get(v___x_1077_, 1);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1093_ = v___x_1077_;
v_isShared_1094_ = v_isSharedCheck_1101_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_inc(v_a_1090_);
lean_dec(v___x_1077_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1101_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v_a_1091_);
v___x_1096_ = v___x_1074_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1091_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_trace_1071_);
lean_ctor_set(v_reuseFailAlloc_1100_, 2, v_buildTime_1072_);
lean_ctor_set_uint8(v_reuseFailAlloc_1100_, sizeof(void*)*3, v_action_1068_);
lean_ctor_set_uint8(v_reuseFailAlloc_1100_, sizeof(void*)*3 + 1, v_wantsRebuild_1069_);
lean_ctor_set_uint8(v_reuseFailAlloc_1100_, sizeof(void*)*3 + 2, v_canceled_1070_);
v___x_1096_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1098_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v___x_1096_);
v___x_1098_ = v___x_1093_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1090_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
}
else
{
uint8_t v___x_1103_; 
v___x_1103_ = l_System_Platform_isOSX;
if (v___x_1103_ == 0)
{
uint8_t v___x_1104_; 
lean_dec_ref(v___y_1057_);
lean_dec_ref(v___x_1055_);
v___x_1104_ = l_System_Platform_isWindows;
if (v___x_1104_ == 0)
{
lean_object* v_toContext_1105_; lean_object* v_lakeEnv_1106_; lean_object* v_lean_1107_; lean_object* v_log_1108_; uint8_t v_action_1109_; uint8_t v_wantsRebuild_1110_; uint8_t v_canceled_1111_; lean_object* v_trace_1112_; lean_object* v_buildTime_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1143_; 
v_toContext_1105_ = lean_ctor_get(v___y_1061_, 1);
v_lakeEnv_1106_ = lean_ctor_get(v_toContext_1105_, 0);
v_lean_1107_ = lean_ctor_get(v_lakeEnv_1106_, 1);
v_log_1108_ = lean_ctor_get(v___y_1062_, 0);
v_action_1109_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*3);
v_wantsRebuild_1110_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*3 + 1);
v_canceled_1111_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*3 + 2);
v_trace_1112_ = lean_ctor_get(v___y_1062_, 1);
v_buildTime_1113_ = lean_ctor_get(v___y_1062_, 2);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___y_1062_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1115_ = v___y_1062_;
v_isShared_1116_ = v_isSharedCheck_1143_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_buildTime_1113_);
lean_inc(v_trace_1112_);
lean_inc(v_log_1108_);
lean_dec(v___y_1062_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1143_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v_ar_1117_; lean_object* v___x_1118_; 
v_ar_1117_ = lean_ctor_get(v_lean_1107_, 13);
lean_inc_ref(v_ar_1117_);
v___x_1118_ = l_Lake_compileStaticLib(v___y_1051_, v_oFiles_1052_, v_ar_1117_, v___x_1104_, v_log_1108_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1130_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_a_1120_ = lean_ctor_get(v___x_1118_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1122_ = v___x_1118_;
v_isShared_1123_ = v_isSharedCheck_1130_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1130_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v_a_1120_);
v___x_1125_ = v___x_1115_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1120_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_trace_1112_);
lean_ctor_set(v_reuseFailAlloc_1129_, 2, v_buildTime_1113_);
lean_ctor_set_uint8(v_reuseFailAlloc_1129_, sizeof(void*)*3, v_action_1109_);
lean_ctor_set_uint8(v_reuseFailAlloc_1129_, sizeof(void*)*3 + 1, v_wantsRebuild_1110_);
lean_ctor_set_uint8(v_reuseFailAlloc_1129_, sizeof(void*)*3 + 2, v_canceled_1111_);
v___x_1125_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1127_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 1, v___x_1125_);
v___x_1127_ = v___x_1122_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1119_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1142_; 
v_a_1131_ = lean_ctor_get(v___x_1118_, 0);
v_a_1132_ = lean_ctor_get(v___x_1118_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1134_ = v___x_1118_;
v_isShared_1135_ = v_isSharedCheck_1142_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_inc(v_a_1131_);
lean_dec(v___x_1118_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1142_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v_a_1132_);
v___x_1137_ = v___x_1115_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1132_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_trace_1112_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_buildTime_1113_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*3, v_action_1109_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*3 + 1, v_wantsRebuild_1110_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*3 + 2, v_canceled_1111_);
v___x_1137_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1139_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v___x_1137_);
v___x_1139_ = v___x_1134_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1131_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1144_; lean_object* v_lakeEnv_1145_; lean_object* v_lean_1146_; lean_object* v_log_1147_; uint8_t v_action_1148_; uint8_t v_wantsRebuild_1149_; uint8_t v_canceled_1150_; lean_object* v_trace_1151_; lean_object* v_buildTime_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1182_; 
v_toContext_1144_ = lean_ctor_get(v___y_1061_, 1);
v_lakeEnv_1145_ = lean_ctor_get(v_toContext_1144_, 0);
v_lean_1146_ = lean_ctor_get(v_lakeEnv_1145_, 1);
v_log_1147_ = lean_ctor_get(v___y_1062_, 0);
v_action_1148_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*3);
v_wantsRebuild_1149_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*3 + 1);
v_canceled_1150_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*3 + 2);
v_trace_1151_ = lean_ctor_get(v___y_1062_, 1);
v_buildTime_1152_ = lean_ctor_get(v___y_1062_, 2);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___y_1062_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1154_ = v___y_1062_;
v_isShared_1155_ = v_isSharedCheck_1182_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_buildTime_1152_);
lean_inc(v_trace_1151_);
lean_inc(v_log_1147_);
lean_dec(v___y_1062_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1182_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_ar_1156_; lean_object* v___x_1157_; 
v_ar_1156_ = lean_ctor_get(v_lean_1146_, 13);
lean_inc_ref(v_ar_1156_);
v___x_1157_ = l_Lake_compileStaticLib(v___y_1051_, v_oFiles_1052_, v_ar_1156_, v_shouldExport_1053_, v_log_1147_);
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
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v_a_1159_);
v___x_1164_ = v___x_1154_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1159_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_trace_1151_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_buildTime_1152_);
lean_ctor_set_uint8(v_reuseFailAlloc_1168_, sizeof(void*)*3, v_action_1148_);
lean_ctor_set_uint8(v_reuseFailAlloc_1168_, sizeof(void*)*3 + 1, v_wantsRebuild_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1168_, sizeof(void*)*3 + 2, v_canceled_1150_);
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
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v_a_1171_);
v___x_1176_ = v___x_1154_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1171_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_trace_1151_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_buildTime_1152_);
lean_ctor_set_uint8(v_reuseFailAlloc_1180_, sizeof(void*)*3, v_action_1148_);
lean_ctor_set_uint8(v_reuseFailAlloc_1180_, sizeof(void*)*3 + 1, v_wantsRebuild_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1180_, sizeof(void*)*3 + 2, v_canceled_1150_);
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
}
else
{
lean_object* v_log_1183_; uint8_t v_action_1184_; uint8_t v_wantsRebuild_1185_; uint8_t v_canceled_1186_; lean_object* v_trace_1187_; lean_object* v_buildTime_1188_; lean_object* v___x_1189_; 
v_log_1183_ = lean_ctor_get(v___y_1062_, 0);
v_action_1184_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*3);
v_wantsRebuild_1185_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*3 + 1);
v_canceled_1186_ = lean_ctor_get_uint8(v___y_1062_, sizeof(void*)*3 + 2);
v_trace_1187_ = lean_ctor_get(v___y_1062_, 1);
v_buildTime_1188_ = lean_ctor_get(v___y_1062_, 2);
lean_inc_ref(v___y_1051_);
v___x_1189_ = l_Lake_createParentDirs(v___y_1051_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v_a_1193_; lean_object* v___y_1241_; uint8_t v___x_1243_; lean_object* v___x_1244_; 
lean_dec_ref_known(v___x_1189_, 1);
v___x_1190_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1051_);
v___x_1191_ = l_System_FilePath_addExtension(v___y_1051_, v___x_1190_);
v___x_1243_ = 1;
v___x_1244_ = lean_io_prim_handle_mk(v___x_1191_, v___x_1243_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = lean_array_get_size(v_oFiles_1052_);
v___x_1248_ = lean_nat_dec_lt(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_dec(v_a_1245_);
lean_dec_ref(v___y_1057_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_oFiles_1052_);
v_a_1193_ = v___y_1062_;
goto v___jp_1192_;
}
else
{
lean_object* v___f_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___f_1249_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1249_, 0, v_a_1245_);
v___x_1250_ = lean_box(0);
v___x_1251_ = lean_nat_dec_le(v___x_1247_, v___x_1247_);
if (v___x_1251_ == 0)
{
if (v___x_1248_ == 0)
{
lean_dec_ref(v___f_1249_);
lean_dec_ref(v___y_1057_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_oFiles_1052_);
v_a_1193_ = v___y_1062_;
goto v___jp_1192_;
}
else
{
size_t v___x_1252_; lean_object* v___x_189948__overap_1253_; lean_object* v___x_1254_; 
v___x_1252_ = lean_usize_of_nat(v___x_1247_);
v___x_189948__overap_1253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1055_, v___f_1249_, v_oFiles_1052_, v___x_1056_, v___x_1252_, v___x_1250_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc(v___y_1059_);
lean_inc(v___y_1058_);
v___x_1254_ = lean_apply_7(v___x_189948__overap_1253_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, lean_box(0));
v___y_1241_ = v___x_1254_;
goto v___jp_1240_;
}
}
else
{
size_t v___x_1255_; lean_object* v___x_189950__overap_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_usize_of_nat(v___x_1247_);
v___x_189950__overap_1256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1055_, v___f_1249_, v_oFiles_1052_, v___x_1056_, v___x_1255_, v___x_1250_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc(v___y_1059_);
lean_inc(v___y_1058_);
v___x_1257_ = lean_apply_7(v___x_189950__overap_1256_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, lean_box(0));
v___y_1241_ = v___x_1257_;
goto v___jp_1240_;
}
}
}
else
{
lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1271_; 
lean_inc(v_buildTime_1188_);
lean_inc_ref(v_trace_1187_);
lean_inc_ref(v_log_1183_);
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___y_1057_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_oFiles_1052_);
lean_dec_ref(v___y_1051_);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___y_1062_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; lean_object* v_unused_1273_; lean_object* v_unused_1274_; 
v_unused_1272_ = lean_ctor_get(v___y_1062_, 2);
lean_dec(v_unused_1272_);
v_unused_1273_ = lean_ctor_get(v___y_1062_, 1);
lean_dec(v_unused_1273_);
v_unused_1274_ = lean_ctor_get(v___y_1062_, 0);
lean_dec(v_unused_1274_);
v___x_1259_ = v___y_1062_;
v_isShared_1260_ = v_isSharedCheck_1271_;
goto v_resetjp_1258_;
}
else
{
lean_dec(v___y_1062_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1271_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v_a_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
v_a_1261_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1244_, 1);
v___x_1262_ = lean_io_error_to_string(v_a_1261_);
v___x_1263_ = 3;
v___x_1264_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1264_, 0, v___x_1262_);
lean_ctor_set_uint8(v___x_1264_, sizeof(void*)*1, v___x_1263_);
v___x_1265_ = lean_array_get_size(v_log_1183_);
v___x_1266_ = lean_array_push(v_log_1183_, v___x_1264_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1266_);
v___x_1268_ = v___x_1259_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_trace_1187_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_buildTime_1188_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*3, v_action_1184_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*3 + 1, v_wantsRebuild_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*3 + 2, v_canceled_1186_);
v___x_1268_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1265_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
return v___x_1269_;
}
}
}
v___jp_1192_:
{
lean_object* v___x_1194_; lean_object* v_log_1195_; uint8_t v_action_1196_; uint8_t v_wantsRebuild_1197_; uint8_t v_canceled_1198_; lean_object* v_trace_1199_; lean_object* v_buildTime_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1239_; 
v___x_1194_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1195_ = lean_ctor_get(v_a_1193_, 0);
v_action_1196_ = lean_ctor_get_uint8(v_a_1193_, sizeof(void*)*3);
v_wantsRebuild_1197_ = lean_ctor_get_uint8(v_a_1193_, sizeof(void*)*3 + 1);
v_canceled_1198_ = lean_ctor_get_uint8(v_a_1193_, sizeof(void*)*3 + 2);
v_trace_1199_ = lean_ctor_get(v_a_1193_, 1);
v_buildTime_1200_ = lean_ctor_get(v_a_1193_, 2);
v_isSharedCheck_1239_ = !lean_is_exclusive(v_a_1193_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1202_ = v_a_1193_;
v_isShared_1203_ = v_isSharedCheck_1239_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_buildTime_1200_);
lean_inc(v_trace_1199_);
lean_inc(v_log_1195_);
lean_dec(v_a_1193_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1239_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1204_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1205_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1206_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1207_ = lean_array_push(v___x_1206_, v___y_1051_);
v___x_1208_ = lean_array_push(v___x_1207_, v___x_1205_);
v___x_1209_ = lean_array_push(v___x_1208_, v___x_1191_);
v___x_1210_ = lean_box(0);
v___x_1211_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1212_ = 0;
v___x_1213_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1213_, 0, v___x_1194_);
lean_ctor_set(v___x_1213_, 1, v___x_1204_);
lean_ctor_set(v___x_1213_, 2, v___x_1209_);
lean_ctor_set(v___x_1213_, 3, v___x_1210_);
lean_ctor_set(v___x_1213_, 4, v___x_1211_);
lean_ctor_set_uint8(v___x_1213_, sizeof(void*)*5, v___x_1054_);
lean_ctor_set_uint8(v___x_1213_, sizeof(void*)*5 + 1, v___x_1212_);
v___x_1214_ = l_Lake_proc(v___x_1213_, v___x_1212_, v___x_1210_, v_log_1195_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1226_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_a_1216_ = lean_ctor_get(v___x_1214_, 1);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1218_ = v___x_1214_;
v_isShared_1219_ = v_isSharedCheck_1226_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1226_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v_a_1216_);
v___x_1221_ = v___x_1202_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1216_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_trace_1199_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_buildTime_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1225_, sizeof(void*)*3, v_action_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1225_, sizeof(void*)*3 + 1, v_wantsRebuild_1197_);
lean_ctor_set_uint8(v_reuseFailAlloc_1225_, sizeof(void*)*3 + 2, v_canceled_1198_);
v___x_1221_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1223_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 1, v___x_1221_);
v___x_1223_ = v___x_1218_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1215_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1227_; lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1238_; 
v_a_1227_ = lean_ctor_get(v___x_1214_, 0);
v_a_1228_ = lean_ctor_get(v___x_1214_, 1);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1230_ = v___x_1214_;
v_isShared_1231_ = v_isSharedCheck_1238_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_inc(v_a_1227_);
lean_dec(v___x_1214_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1238_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v_a_1228_);
v___x_1233_ = v___x_1202_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1228_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_trace_1199_);
lean_ctor_set(v_reuseFailAlloc_1237_, 2, v_buildTime_1200_);
lean_ctor_set_uint8(v_reuseFailAlloc_1237_, sizeof(void*)*3, v_action_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1237_, sizeof(void*)*3 + 1, v_wantsRebuild_1197_);
lean_ctor_set_uint8(v_reuseFailAlloc_1237_, sizeof(void*)*3 + 2, v_canceled_1198_);
v___x_1233_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1235_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 1, v___x_1233_);
v___x_1235_ = v___x_1230_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1227_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v___x_1233_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
}
v___jp_1240_:
{
if (lean_obj_tag(v___y_1241_) == 0)
{
lean_object* v_a_1242_; 
v_a_1242_ = lean_ctor_get(v___y_1241_, 1);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___y_1241_, 2);
v_a_1193_ = v_a_1242_;
goto v___jp_1192_;
}
else
{
lean_dec_ref(v___x_1191_);
lean_dec_ref(v___y_1051_);
return v___y_1241_;
}
}
}
else
{
lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1288_; 
lean_inc(v_buildTime_1188_);
lean_inc_ref(v_trace_1187_);
lean_inc_ref(v_log_1183_);
lean_dec_ref(v___y_1057_);
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_oFiles_1052_);
lean_dec_ref(v___y_1051_);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___y_1062_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; lean_object* v_unused_1290_; lean_object* v_unused_1291_; 
v_unused_1289_ = lean_ctor_get(v___y_1062_, 2);
lean_dec(v_unused_1289_);
v_unused_1290_ = lean_ctor_get(v___y_1062_, 1);
lean_dec(v_unused_1290_);
v_unused_1291_ = lean_ctor_get(v___y_1062_, 0);
lean_dec(v_unused_1291_);
v___x_1276_ = v___y_1062_;
v_isShared_1277_ = v_isSharedCheck_1288_;
goto v_resetjp_1275_;
}
else
{
lean_dec(v___y_1062_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1288_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v_a_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v_a_1278_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1189_, 1);
v___x_1279_ = lean_io_error_to_string(v_a_1278_);
v___x_1280_ = 3;
v___x_1281_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set_uint8(v___x_1281_, sizeof(void*)*1, v___x_1280_);
v___x_1282_ = lean_array_get_size(v_log_1183_);
v___x_1283_ = lean_array_push(v_log_1183_, v___x_1281_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v___x_1283_);
v___x_1285_ = v___x_1276_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_trace_1187_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_buildTime_1188_);
lean_ctor_set_uint8(v_reuseFailAlloc_1287_, sizeof(void*)*3, v_action_1184_);
lean_ctor_set_uint8(v_reuseFailAlloc_1287_, sizeof(void*)*3 + 1, v_wantsRebuild_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1287_, sizeof(void*)*3 + 2, v_canceled_1186_);
v___x_1285_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1282_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
return v___x_1286_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object* v_bootstrap_1292_, lean_object* v___y_1293_, lean_object* v_oFiles_1294_, lean_object* v_shouldExport_1295_, lean_object* v___x_1296_, lean_object* v___x_1297_, lean_object* v___x_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
uint8_t v_bootstrap_boxed_1306_; uint8_t v_shouldExport_boxed_1307_; uint8_t v___x_190318__boxed_1308_; size_t v___x_190320__boxed_1309_; lean_object* v_res_1310_; 
v_bootstrap_boxed_1306_ = lean_unbox(v_bootstrap_1292_);
v_shouldExport_boxed_1307_ = lean_unbox(v_shouldExport_1295_);
v___x_190318__boxed_1308_ = lean_unbox(v___x_1296_);
v___x_190320__boxed_1309_ = lean_unbox_usize(v___x_1298_);
lean_dec(v___x_1298_);
v_res_1310_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(v_bootstrap_boxed_1306_, v___y_1293_, v_oFiles_1294_, v_shouldExport_boxed_1307_, v___x_190318__boxed_1308_, v___x_1297_, v___x_190320__boxed_1309_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec(v___y_1300_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(uint8_t v_bootstrap_1312_, lean_object* v___y_1313_, uint8_t v_shouldExport_1314_, uint8_t v___x_1315_, lean_object* v___x_1316_, size_t v___x_1317_, lean_object* v_oFiles_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___y_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1326_ = lean_box(v_bootstrap_1312_);
v___x_1327_ = lean_box(v_shouldExport_1314_);
v___x_1328_ = lean_box(v___x_1315_);
v___x_1329_ = lean_box_usize(v___x_1317_);
lean_inc_ref(v___y_1313_);
v___y_1330_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed), 14, 7);
lean_closure_set(v___y_1330_, 0, v___x_1326_);
lean_closure_set(v___y_1330_, 1, v___y_1313_);
lean_closure_set(v___y_1330_, 2, v_oFiles_1318_);
lean_closure_set(v___y_1330_, 3, v___x_1327_);
lean_closure_set(v___y_1330_, 4, v___x_1328_);
lean_closure_set(v___y_1330_, 5, v___x_1316_);
lean_closure_set(v___y_1330_, 6, v___x_1329_);
v___x_1331_ = 0;
v___x_1332_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1333_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1313_, v___y_1330_, v___x_1331_, v___x_1332_, v___x_1315_, v___x_1331_, v___x_1331_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1343_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_a_1335_ = lean_ctor_get(v___x_1333_, 1);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1337_ = v___x_1333_;
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v_path_1339_; lean_object* v___x_1341_; 
v_path_1339_ = lean_ctor_get(v_a_1334_, 1);
lean_inc_ref(v_path_1339_);
lean_dec(v_a_1334_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v_path_1339_);
v___x_1341_ = v___x_1337_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_path_1339_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_a_1335_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
v_a_1344_ = lean_ctor_get(v___x_1333_, 0);
v_a_1345_ = lean_ctor_get(v___x_1333_, 1);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1333_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_inc(v_a_1344_);
lean_dec(v___x_1333_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1344_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object* v_bootstrap_1353_, lean_object* v___y_1354_, lean_object* v_shouldExport_1355_, lean_object* v___x_1356_, lean_object* v___x_1357_, lean_object* v___x_1358_, lean_object* v_oFiles_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
uint8_t v_bootstrap_boxed_1367_; uint8_t v_shouldExport_boxed_1368_; uint8_t v___x_190741__boxed_1369_; size_t v___x_190743__boxed_1370_; lean_object* v_res_1371_; 
v_bootstrap_boxed_1367_ = lean_unbox(v_bootstrap_1353_);
v_shouldExport_boxed_1368_ = lean_unbox(v_shouldExport_1355_);
v___x_190741__boxed_1369_ = lean_unbox(v___x_1356_);
v___x_190743__boxed_1370_ = lean_unbox_usize(v___x_1358_);
lean_dec(v___x_1358_);
v_res_1371_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(v_bootstrap_boxed_1367_, v___y_1354_, v_shouldExport_boxed_1368_, v___x_190741__boxed_1369_, v___x_1357_, v___x_190743__boxed_1370_, v_oFiles_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec(v___y_1361_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object* v_config_1376_, lean_object* v_config_1377_, uint8_t v_shouldExport_1378_, uint8_t v___x_1379_, lean_object* v___x_1380_, lean_object* v___x_1381_, lean_object* v___x_1382_, lean_object* v___x_1383_, lean_object* v___f_1384_, lean_object* v_dir_1385_, lean_object* v_self_1386_, lean_object* v___x_1387_, lean_object* v___f_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
size_t v___y_1397_; uint8_t v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v_a_1417_; lean_object* v_a_1418_; lean_object* v___x_1461_; 
lean_inc_ref(v___y_1389_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc(v___x_1382_);
v___x_1461_ = lean_apply_7(v___y_1389_, v___x_1387_, v___x_1382_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, lean_box(0));
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v_a_1463_; lean_object* v___x_1464_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
v_a_1463_ = lean_ctor_get(v___x_1461_, 1);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1461_, 2);
v___x_1464_ = l_Lake_Job_await___redArg(v_a_1462_, v_a_1463_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v_a_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
v_a_1466_ = lean_ctor_get(v___x_1464_, 1);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1464_, 2);
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_1469_ = lean_array_get_size(v_a_1465_);
v___x_1470_ = lean_nat_dec_lt(v___x_1467_, v___x_1469_);
if (v___x_1470_ == 0)
{
lean_dec(v_a_1465_);
lean_dec_ref(v___f_1388_);
v_a_1417_ = v___x_1468_;
v_a_1418_ = v_a_1466_;
goto v___jp_1416_;
}
else
{
size_t v___x_1471_; size_t v___x_1472_; lean_object* v___x_190078__overap_1473_; lean_object* v___x_1474_; 
v___x_1471_ = ((size_t)0ULL);
v___x_1472_ = lean_usize_of_nat(v___x_1469_);
lean_inc_ref(v___x_1383_);
v___x_190078__overap_1473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1383_, v___f_1388_, v_a_1465_, v___x_1471_, v___x_1472_, v___x_1468_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc(v___x_1382_);
lean_inc_ref(v___y_1389_);
v___x_1474_ = lean_apply_7(v___x_190078__overap_1473_, v___y_1389_, v___x_1382_, v___y_1391_, v___y_1392_, v___y_1393_, v_a_1466_, lean_box(0));
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v_a_1476_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
v_a_1476_ = lean_ctor_get(v___x_1474_, 1);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1474_, 2);
v_a_1417_ = v_a_1475_;
v_a_1418_ = v_a_1476_;
goto v___jp_1416_;
}
else
{
lean_object* v_a_1477_; lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec_ref(v___y_1389_);
lean_dec_ref(v_self_1386_);
lean_dec_ref(v_dir_1385_);
lean_dec_ref(v___f_1384_);
lean_dec_ref(v___x_1383_);
lean_dec(v___x_1382_);
lean_dec(v___x_1381_);
lean_dec_ref(v___x_1380_);
lean_dec_ref(v_config_1376_);
v_a_1477_ = lean_ctor_get(v___x_1474_, 0);
v_a_1478_ = lean_ctor_get(v___x_1474_, 1);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1474_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_inc(v_a_1477_);
lean_dec(v___x_1474_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1477_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v___y_1389_);
lean_dec_ref(v___f_1388_);
lean_dec_ref(v_self_1386_);
lean_dec_ref(v_dir_1385_);
lean_dec_ref(v___f_1384_);
lean_dec_ref(v___x_1383_);
lean_dec(v___x_1382_);
lean_dec(v___x_1381_);
lean_dec_ref(v___x_1380_);
lean_dec_ref(v_config_1376_);
v_a_1486_ = lean_ctor_get(v___x_1464_, 0);
v_a_1487_ = lean_ctor_get(v___x_1464_, 1);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1464_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_inc(v_a_1486_);
lean_dec(v___x_1464_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1486_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec_ref(v___y_1389_);
lean_dec_ref(v___f_1388_);
lean_dec_ref(v_self_1386_);
lean_dec_ref(v_dir_1385_);
lean_dec_ref(v___f_1384_);
lean_dec_ref(v___x_1383_);
lean_dec(v___x_1382_);
lean_dec(v___x_1381_);
lean_dec_ref(v___x_1380_);
lean_dec_ref(v_config_1376_);
v_a_1495_ = lean_ctor_get(v___x_1461_, 0);
v_a_1496_ = lean_ctor_get(v___x_1461_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1461_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_inc(v_a_1495_);
lean_dec(v___x_1461_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1495_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_a_1496_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
v___jp_1396_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___f_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1403_ = lean_box(v___y_1398_);
v___x_1404_ = lean_box(v_shouldExport_1378_);
v___x_1405_ = lean_box(v___x_1379_);
v___x_1406_ = lean_box_usize(v___y_1397_);
v___f_1407_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed), 14, 6);
lean_closure_set(v___f_1407_, 0, v___x_1403_);
lean_closure_set(v___f_1407_, 1, v___y_1402_);
lean_closure_set(v___f_1407_, 2, v___x_1404_);
lean_closure_set(v___f_1407_, 3, v___x_1405_);
lean_closure_set(v___f_1407_, 4, v___x_1380_);
lean_closure_set(v___f_1407_, 5, v___x_1406_);
v___x_1408_ = l_Array_append___redArg(v___y_1401_, v___y_1399_);
lean_dec_ref(v___y_1399_);
v___x_1409_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_1410_ = l_Lake_Job_collectArray___redArg(v___x_1408_, v___x_1409_);
lean_dec_ref(v___x_1408_);
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = 0;
v___x_1413_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_1414_ = l_Lake_Job_mapM___redArg(v___x_1381_, v___x_1410_, v___f_1407_, v___x_1411_, v___x_1412_, v___y_1389_, v___x_1382_, v___y_1391_, v___y_1392_, v___y_1393_, v___x_1413_);
lean_dec(v___x_1382_);
v___x_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
lean_ctor_set(v___x_1415_, 1, v___y_1400_);
return v___x_1415_;
}
v___jp_1416_:
{
lean_object* v_toLeanConfig_1419_; lean_object* v_toLeanConfig_1420_; uint8_t v_bootstrap_1421_; lean_object* v_buildDir_1422_; lean_object* v_nativeLibDir_1423_; lean_object* v_moreLinkObjs_1424_; lean_object* v_moreLinkObjs_1425_; lean_object* v___x_1426_; size_t v_sz_1427_; size_t v___x_1428_; lean_object* v___x_190036__overap_1429_; lean_object* v___x_1430_; 
v_toLeanConfig_1419_ = lean_ctor_get(v_config_1376_, 1);
lean_inc_ref(v_toLeanConfig_1419_);
v_toLeanConfig_1420_ = lean_ctor_get(v_config_1377_, 0);
v_bootstrap_1421_ = lean_ctor_get_uint8(v_config_1376_, sizeof(void*)*28);
v_buildDir_1422_ = lean_ctor_get(v_config_1376_, 5);
lean_inc_ref(v_buildDir_1422_);
v_nativeLibDir_1423_ = lean_ctor_get(v_config_1376_, 7);
lean_inc_ref(v_nativeLibDir_1423_);
lean_dec_ref(v_config_1376_);
v_moreLinkObjs_1424_ = lean_ctor_get(v_toLeanConfig_1419_, 6);
lean_inc_ref(v_moreLinkObjs_1424_);
lean_dec_ref(v_toLeanConfig_1419_);
v_moreLinkObjs_1425_ = lean_ctor_get(v_toLeanConfig_1420_, 6);
v___x_1426_ = l_Array_append___redArg(v_moreLinkObjs_1424_, v_moreLinkObjs_1425_);
v_sz_1427_ = lean_array_size(v___x_1426_);
v___x_1428_ = ((size_t)0ULL);
v___x_190036__overap_1429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1383_, v___f_1384_, v_sz_1427_, v___x_1428_, v___x_1426_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc(v___x_1382_);
lean_inc_ref(v___y_1389_);
v___x_1430_ = lean_apply_7(v___x_190036__overap_1429_, v___y_1389_, v___x_1382_, v___y_1391_, v___y_1392_, v___y_1393_, v_a_1418_, lean_box(0));
if (lean_obj_tag(v___x_1430_) == 0)
{
if (v_shouldExport_1378_ == 0)
{
lean_object* v_a_1431_; lean_object* v_a_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
v_a_1432_ = lean_ctor_get(v___x_1430_, 1);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1430_, 2);
v___x_1433_ = l_System_FilePath_normalize(v_buildDir_1422_);
v___x_1434_ = l_Lake_joinRelative(v_dir_1385_, v___x_1433_);
v___x_1435_ = l_System_FilePath_normalize(v_nativeLibDir_1423_);
v___x_1436_ = l_Lake_joinRelative(v___x_1434_, v___x_1435_);
v___x_1437_ = l_Lake_LeanLib_libName(v_self_1386_);
v___x_1438_ = l_Lake_nameToStaticLib(v___x_1437_, v_shouldExport_1378_);
v___x_1439_ = l_Lake_joinRelative(v___x_1436_, v___x_1438_);
v___y_1397_ = v___x_1428_;
v___y_1398_ = v_bootstrap_1421_;
v___y_1399_ = v_a_1431_;
v___y_1400_ = v_a_1432_;
v___y_1401_ = v_a_1417_;
v___y_1402_ = v___x_1439_;
goto v___jp_1396_;
}
else
{
lean_object* v_a_1440_; lean_object* v_a_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v_a_1440_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1440_);
v_a_1441_ = lean_ctor_get(v___x_1430_, 1);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1430_, 2);
v___x_1442_ = l_System_FilePath_normalize(v_buildDir_1422_);
v___x_1443_ = l_Lake_joinRelative(v_dir_1385_, v___x_1442_);
v___x_1444_ = l_System_FilePath_normalize(v_nativeLibDir_1423_);
v___x_1445_ = l_Lake_joinRelative(v___x_1443_, v___x_1444_);
v___x_1446_ = l_Lake_LeanLib_libName(v_self_1386_);
v___x_1447_ = 0;
v___x_1448_ = l_Lake_nameToStaticLib(v___x_1446_, v___x_1447_);
v___x_1449_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_1450_ = l_System_FilePath_addExtension(v___x_1448_, v___x_1449_);
v___x_1451_ = l_Lake_joinRelative(v___x_1445_, v___x_1450_);
v___y_1397_ = v___x_1428_;
v___y_1398_ = v_bootstrap_1421_;
v___y_1399_ = v_a_1440_;
v___y_1400_ = v_a_1441_;
v___y_1401_ = v_a_1417_;
v___y_1402_ = v___x_1451_;
goto v___jp_1396_;
}
}
else
{
lean_object* v_a_1452_; lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec_ref(v_nativeLibDir_1423_);
lean_dec_ref(v_buildDir_1422_);
lean_dec_ref(v_a_1417_);
lean_dec_ref(v___y_1389_);
lean_dec_ref(v_self_1386_);
lean_dec_ref(v_dir_1385_);
lean_dec(v___x_1382_);
lean_dec(v___x_1381_);
lean_dec_ref(v___x_1380_);
v_a_1452_ = lean_ctor_get(v___x_1430_, 0);
v_a_1453_ = lean_ctor_get(v___x_1430_, 1);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1430_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_inc(v_a_1452_);
lean_dec(v___x_1430_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1452_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed(lean_object** _args){
lean_object* v_config_1504_ = _args[0];
lean_object* v_config_1505_ = _args[1];
lean_object* v_shouldExport_1506_ = _args[2];
lean_object* v___x_1507_ = _args[3];
lean_object* v___x_1508_ = _args[4];
lean_object* v___x_1509_ = _args[5];
lean_object* v___x_1510_ = _args[6];
lean_object* v___x_1511_ = _args[7];
lean_object* v___f_1512_ = _args[8];
lean_object* v_dir_1513_ = _args[9];
lean_object* v_self_1514_ = _args[10];
lean_object* v___x_1515_ = _args[11];
lean_object* v___f_1516_ = _args[12];
lean_object* v___y_1517_ = _args[13];
lean_object* v___y_1518_ = _args[14];
lean_object* v___y_1519_ = _args[15];
lean_object* v___y_1520_ = _args[16];
lean_object* v___y_1521_ = _args[17];
lean_object* v___y_1522_ = _args[18];
lean_object* v___y_1523_ = _args[19];
_start:
{
uint8_t v_shouldExport_boxed_1524_; uint8_t v___x_190839__boxed_1525_; lean_object* v_res_1526_; 
v_shouldExport_boxed_1524_ = lean_unbox(v_shouldExport_1506_);
v___x_190839__boxed_1525_ = lean_unbox(v___x_1507_);
v_res_1526_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(v_config_1504_, v_config_1505_, v_shouldExport_boxed_1524_, v___x_190839__boxed_1525_, v___x_1508_, v___x_1509_, v___x_1510_, v___x_1511_, v___f_1512_, v_dir_1513_, v_self_1514_, v___x_1515_, v___f_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec(v_config_1505_);
return v_res_1526_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0(void){
_start:
{
uint8_t v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = 2;
v___x_1528_ = l_Lake_Verbosity_ctorIdx(v___x_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object* v_self_1532_, uint8_t v_shouldExport_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v___x_1541_; lean_object* v_toApplicative_1542_; lean_object* v_toBind_1543_; lean_object* v_toFunctor_1544_; lean_object* v_toPure_1545_; lean_object* v___f_1546_; lean_object* v___f_1547_; lean_object* v___f_1548_; lean_object* v___f_1549_; lean_object* v___x_1550_; lean_object* v___f_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v_toBuildConfig_1559_; lean_object* v_registeredJobs_1560_; uint8_t v_verbosity_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___f_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; uint8_t v___x_1568_; lean_object* v___y_1570_; 
v___x_1541_ = l_instMonadBaseIO;
v_toApplicative_1542_ = lean_ctor_get(v___x_1541_, 0);
v_toBind_1543_ = lean_ctor_get(v___x_1541_, 1);
v_toFunctor_1544_ = lean_ctor_get(v_toApplicative_1542_, 0);
v_toPure_1545_ = lean_ctor_get(v_toApplicative_1542_, 1);
lean_inc_n(v_toBind_1543_, 3);
lean_inc_n(v_toPure_1545_, 5);
v___f_1546_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1546_, 0, v_toPure_1545_);
lean_closure_set(v___f_1546_, 1, v_toBind_1543_);
v___f_1547_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1547_, 0, v_toPure_1545_);
lean_closure_set(v___f_1547_, 1, v_toBind_1543_);
lean_inc_ref(v___f_1546_);
v___f_1548_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1548_, 0, v_toPure_1545_);
lean_closure_set(v___f_1548_, 1, v___f_1546_);
lean_inc_ref_n(v_toFunctor_1544_, 2);
v___f_1549_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1549_, 0, v_toFunctor_1544_);
lean_closure_set(v___f_1549_, 1, v_toPure_1545_);
lean_closure_set(v___f_1549_, 2, v_toBind_1543_);
v___x_1550_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1544_);
v___f_1551_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1551_, 0, v_toPure_1545_);
v___x_1552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___f_1551_);
lean_ctor_set(v___x_1552_, 2, v___f_1549_);
lean_ctor_set(v___x_1552_, 3, v___f_1548_);
lean_ctor_set(v___x_1552_, 4, v___f_1547_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
lean_ctor_set(v___x_1553_, 1, v___f_1546_);
v___x_1554_ = l_ReaderT_instMonad___redArg(v___x_1553_);
v___x_1555_ = l_StateRefT_x27_instMonad___redArg(v___x_1554_);
v___x_1556_ = l_ReaderT_instMonad___redArg(v___x_1555_);
v___x_1557_ = l_ReaderT_instMonad___redArg(v___x_1556_);
v___x_1558_ = l_Lake_EquipT_instMonad___redArg(v___x_1557_);
v_toBuildConfig_1559_ = lean_ctor_get(v_a_1538_, 0);
v_registeredJobs_1560_ = lean_ctor_get(v_a_1538_, 4);
v_verbosity_1561_ = lean_ctor_get_uint8(v_toBuildConfig_1559_, sizeof(void*)*5 + 4);
v___x_1562_ = l_Lake_instDataKindFilePath;
v___x_1563_ = lean_box(v_shouldExport_1533_);
lean_inc_ref(v___x_1558_);
v___f_1564_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1564_, 0, v___x_1563_);
lean_closure_set(v___f_1564_, 1, v___x_1558_);
v___x_1565_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1561_);
v___x_1566_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0);
v___x_1567_ = lean_nat_dec_eq(v___x_1565_, v___x_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = 1;
if (v___x_1567_ == 0)
{
lean_object* v___x_1616_; 
v___x_1616_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_1570_ = v___x_1616_;
goto v___jp_1569_;
}
else
{
if (v_shouldExport_1533_ == 0)
{
lean_object* v___x_1617_; 
v___x_1617_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_1570_ = v___x_1617_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1618_; 
v___x_1618_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3));
v___y_1570_ = v___x_1618_;
goto v___jp_1569_;
}
}
v___jp_1569_:
{
lean_object* v_pkg_1571_; lean_object* v_name_1572_; lean_object* v_config_1573_; lean_object* v_keyName_1574_; lean_object* v_dir_1575_; lean_object* v_config_1576_; lean_object* v___f_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___f_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; 
v_pkg_1571_ = lean_ctor_get(v_self_1532_, 0);
v_name_1572_ = lean_ctor_get(v_self_1532_, 1);
v_config_1573_ = lean_ctor_get(v_self_1532_, 2);
lean_inc(v_config_1573_);
v_keyName_1574_ = lean_ctor_get(v_pkg_1571_, 2);
v_dir_1575_ = lean_ctor_get(v_pkg_1571_, 4);
lean_inc_ref(v_dir_1575_);
v_config_1576_ = lean_ctor_get(v_pkg_1571_, 6);
lean_inc_ref(v_config_1576_);
lean_inc_ref_n(v_pkg_1571_, 2);
v___f_1577_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(v___f_1577_, 0, v___x_1562_);
lean_closure_set(v___f_1577_, 1, v_pkg_1571_);
lean_inc_n(v_name_1572_, 2);
v___x_1578_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1572_, v___x_1568_);
v___x_1579_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___x_1580_ = lean_string_append(v___x_1578_, v___x_1579_);
v___x_1581_ = lean_string_append(v___x_1580_, v___y_1570_);
v___x_1582_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_1574_);
v___x_1583_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1583_, 0, v_keyName_1574_);
lean_ctor_set(v___x_1583_, 1, v_name_1572_);
v___x_1584_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_1532_);
v___x_1585_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
lean_ctor_set(v___x_1585_, 2, v_self_1532_);
lean_ctor_set(v___x_1585_, 3, v___x_1582_);
v___x_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1586_, 0, v_pkg_1571_);
v___x_1587_ = lean_box(v_shouldExport_1533_);
v___x_1588_ = lean_box(v___x_1568_);
lean_inc_ref(v___x_1558_);
v___f_1589_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed), 20, 13);
lean_closure_set(v___f_1589_, 0, v_config_1576_);
lean_closure_set(v___f_1589_, 1, v_config_1573_);
lean_closure_set(v___f_1589_, 2, v___x_1587_);
lean_closure_set(v___f_1589_, 3, v___x_1588_);
lean_closure_set(v___f_1589_, 4, v___x_1558_);
lean_closure_set(v___f_1589_, 5, v___x_1562_);
lean_closure_set(v___f_1589_, 6, v___x_1586_);
lean_closure_set(v___f_1589_, 7, v___x_1558_);
lean_closure_set(v___f_1589_, 8, v___f_1577_);
lean_closure_set(v___f_1589_, 9, v_dir_1575_);
lean_closure_set(v___f_1589_, 10, v_self_1532_);
lean_closure_set(v___f_1589_, 11, v___x_1585_);
lean_closure_set(v___f_1589_, 12, v___f_1564_);
v___x_1590_ = 0;
v___x_1591_ = l_Lake_ensureJob___redArg(v___x_1562_, v___f_1589_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1615_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
v_a_1593_ = lean_ctor_get(v___x_1591_, 1);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1595_ = v___x_1591_;
v_isShared_1596_ = v_isSharedCheck_1615_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_inc(v_a_1592_);
lean_dec(v___x_1591_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1615_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_task_1597_; lean_object* v_kind_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1613_; 
v_task_1597_ = lean_ctor_get(v_a_1592_, 0);
v_kind_1598_ = lean_ctor_get(v_a_1592_, 1);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_a_1592_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v_a_1592_, 2);
lean_dec(v_unused_1614_);
v___x_1600_ = v_a_1592_;
v_isShared_1601_ = v_isSharedCheck_1613_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_kind_1598_);
lean_inc(v_task_1597_);
lean_dec(v_a_1592_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1613_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v_job_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 2, v___x_1581_);
v_job_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_task_1597_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_kind_1598_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v___x_1581_);
v_job_1603_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1610_; 
lean_ctor_set_uint8(v_job_1603_, sizeof(void*)*3, v___x_1590_);
v___x_1604_ = lean_st_ref_take(v_registeredJobs_1560_);
lean_inc_ref(v_job_1603_);
v___x_1605_ = l_Lake_Job_toOpaque___redArg(v_job_1603_);
v___x_1606_ = lean_array_push(v___x_1604_, v___x_1605_);
v___x_1607_ = lean_st_ref_put(v_registeredJobs_1560_, v___x_1606_);
v___x_1608_ = l_Lake_Job_renew___redArg(v_job_1603_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1608_);
v___x_1610_ = v___x_1595_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_a_1593_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1581_);
return v___x_1591_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object* v_self_1619_, lean_object* v_shouldExport_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_){
_start:
{
uint8_t v_shouldExport_boxed_1628_; lean_object* v_res_1629_; 
v_shouldExport_boxed_1628_ = lean_unbox(v_shouldExport_1620_);
v_res_1629_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1619_, v_shouldExport_boxed_1628_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec(v_a_1622_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t v_fmt_1630_, lean_object* v_a_1631_){
_start:
{
if (v_fmt_1630_ == 0)
{
return v_a_1631_;
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = l_Lake_mkRelPathString(v_a_1631_);
v___x_1633_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
v___x_1634_ = l_Lean_Json_compress(v___x_1633_);
return v___x_1634_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object* v_fmt_1635_, lean_object* v_a_1636_){
_start:
{
uint8_t v_fmt_boxed_1637_; lean_object* v_res_1638_; 
v_fmt_boxed_1637_ = lean_unbox(v_fmt_1635_);
v_res_1638_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_boxed_1637_, v_a_1636_);
return v_res_1638_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2(void){
_start:
{
uint8_t v___x_1641_; lean_object* v_name_1642_; lean_object* v___x_1643_; 
v___x_1641_ = 1;
v_name_1642_ = l_Lake_instDataKindFilePath;
v___x_1643_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1642_, v___x_1641_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* v_defaultPkg_1647_, lean_object* v_self_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_name_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; 
v_name_1656_ = l_Lake_instDataKindFilePath;
v___x_1657_ = 1;
lean_inc_ref_n(v_self_1648_, 2);
v___x_1658_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1647_, v_self_1648_, v_self_1648_, v___x_1657_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1700_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_a_1660_ = lean_ctor_get(v___x_1658_, 1);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1662_ = v___x_1658_;
v_isShared_1663_ = v_isSharedCheck_1700_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1700_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___y_1665_; lean_object* v_snd_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1698_; 
v_snd_1683_ = lean_ctor_get(v_a_1659_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_a_1659_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; 
v_unused_1699_ = lean_ctor_get(v_a_1659_, 0);
lean_dec(v_unused_1699_);
v___x_1685_ = v_a_1659_;
v_isShared_1686_ = v_isSharedCheck_1698_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_snd_1683_);
lean_dec(v_a_1659_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1698_;
goto v_resetjp_1684_;
}
v___jp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1666_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1667_ = l_Lake_PartialBuildKey_toString(v_self_1648_);
v___x_1668_ = lean_string_append(v___x_1666_, v___x_1667_);
lean_dec_ref(v___x_1667_);
v___x_1669_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1670_ = lean_string_append(v___x_1668_, v___x_1669_);
v___x_1671_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
v___x_1672_ = lean_string_append(v___x_1670_, v___x_1671_);
v___x_1673_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1674_ = lean_string_append(v___x_1672_, v___x_1673_);
v___x_1675_ = lean_string_append(v___x_1674_, v___y_1665_);
lean_dec_ref(v___y_1665_);
v___x_1676_ = 3;
v___x_1677_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1677_, 0, v___x_1675_);
lean_ctor_set_uint8(v___x_1677_, sizeof(void*)*1, v___x_1676_);
v___x_1678_ = lean_array_get_size(v_a_1660_);
v___x_1679_ = lean_array_push(v_a_1660_, v___x_1677_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set_tag(v___x_1662_, 1);
lean_ctor_set(v___x_1662_, 1, v___x_1679_);
lean_ctor_set(v___x_1662_, 0, v___x_1678_);
v___x_1681_ = v___x_1662_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
v_resetjp_1684_:
{
lean_object* v_kind_1687_; uint8_t v___x_1688_; 
v_kind_1687_ = lean_ctor_get(v_snd_1683_, 1);
v___x_1688_ = lean_name_eq(v_kind_1687_, v_name_1656_);
if (v___x_1688_ == 0)
{
uint8_t v___x_1689_; 
lean_inc(v_kind_1687_);
lean_del_object(v___x_1685_);
lean_dec(v_snd_1683_);
v___x_1689_ = l_Lean_Name_isAnonymous(v_kind_1687_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1690_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1691_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1687_, v___x_1657_);
v___x_1692_ = lean_string_append(v___x_1690_, v___x_1691_);
lean_dec_ref(v___x_1691_);
v___x_1693_ = lean_string_append(v___x_1692_, v___x_1690_);
v___y_1665_ = v___x_1693_;
goto v___jp_1664_;
}
else
{
lean_object* v___x_1694_; 
lean_dec(v_kind_1687_);
v___x_1694_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1665_ = v___x_1694_;
goto v___jp_1664_;
}
}
else
{
lean_object* v___x_1696_; 
lean_del_object(v___x_1662_);
lean_dec_ref(v_self_1648_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 1, v_a_1660_);
lean_ctor_set(v___x_1685_, 0, v_snd_1683_);
v___x_1696_ = v___x_1685_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_snd_1683_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_a_1660_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec_ref(v_self_1648_);
v_a_1701_ = lean_ctor_get(v___x_1658_, 0);
v_a_1702_ = lean_ctor_get(v___x_1658_, 1);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1658_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_inc(v_a_1701_);
lean_dec(v___x_1658_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1701_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_a_1702_);
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
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* v_defaultPkg_1710_, lean_object* v_self_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1710_, v_self_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec(v_a_1713_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* v___x_1720_, size_t v_sz_1721_, size_t v_i_1722_, lean_object* v_bs_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
uint8_t v___x_1731_; 
v___x_1731_ = lean_usize_dec_lt(v_i_1722_, v_sz_1721_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; 
lean_dec_ref(v___y_1724_);
lean_dec_ref(v___x_1720_);
v___x_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1732_, 0, v_bs_1723_);
lean_ctor_set(v___x_1732_, 1, v___y_1729_);
return v___x_1732_;
}
else
{
lean_object* v_v_1733_; lean_object* v___x_1734_; lean_object* v_bs_x27_1735_; lean_object* v___x_1736_; 
v_v_1733_ = lean_array_uget(v_bs_1723_, v_i_1722_);
v___x_1734_ = lean_unsigned_to_nat(0u);
v_bs_x27_1735_ = lean_array_uset(v_bs_1723_, v_i_1722_, v___x_1734_);
lean_inc_ref(v___y_1724_);
lean_inc_ref(v___x_1720_);
v___x_1736_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1720_, v_v_1733_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v_a_1738_; size_t v___x_1739_; size_t v___x_1740_; lean_object* v___x_1741_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
v_a_1738_ = lean_ctor_get(v___x_1736_, 1);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1736_, 2);
v___x_1739_ = ((size_t)1ULL);
v___x_1740_ = lean_usize_add(v_i_1722_, v___x_1739_);
v___x_1741_ = lean_array_uset(v_bs_x27_1735_, v_i_1722_, v_a_1737_);
v_i_1722_ = v___x_1740_;
v_bs_1723_ = v___x_1741_;
v___y_1729_ = v_a_1738_;
goto _start;
}
else
{
lean_object* v_a_1743_; lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec_ref(v_bs_x27_1735_);
lean_dec_ref(v___y_1724_);
lean_dec_ref(v___x_1720_);
v_a_1743_ = lean_ctor_get(v___x_1736_, 0);
v_a_1744_ = lean_ctor_get(v___x_1736_, 1);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1736_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_inc(v_a_1743_);
lean_dec(v___x_1736_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1743_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_a_1744_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* v___x_1752_, lean_object* v_sz_1753_, lean_object* v_i_1754_, lean_object* v_bs_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
size_t v_sz_boxed_1763_; size_t v_i_boxed_1764_; lean_object* v_res_1765_; 
v_sz_boxed_1763_ = lean_unbox_usize(v_sz_1753_);
lean_dec(v_sz_1753_);
v_i_boxed_1764_ = lean_unbox_usize(v_i_1754_);
lean_dec(v_i_1754_);
v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1752_, v_sz_boxed_1763_, v_i_boxed_1764_, v_bs_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec(v___y_1757_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(lean_object* v_a_1766_, lean_object* v_as_1767_, size_t v_i_1768_, size_t v_stop_1769_, lean_object* v_b_1770_, lean_object* v___y_1771_){
_start:
{
uint8_t v___x_1773_; 
v___x_1773_ = lean_usize_dec_eq(v_i_1768_, v_stop_1769_);
if (v___x_1773_ == 0)
{
lean_object* v_log_1774_; uint8_t v_action_1775_; uint8_t v_wantsRebuild_1776_; uint8_t v_canceled_1777_; lean_object* v_trace_1778_; lean_object* v_buildTime_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_log_1774_ = lean_ctor_get(v___y_1771_, 0);
v_action_1775_ = lean_ctor_get_uint8(v___y_1771_, sizeof(void*)*3);
v_wantsRebuild_1776_ = lean_ctor_get_uint8(v___y_1771_, sizeof(void*)*3 + 1);
v_canceled_1777_ = lean_ctor_get_uint8(v___y_1771_, sizeof(void*)*3 + 2);
v_trace_1778_ = lean_ctor_get(v___y_1771_, 1);
v_buildTime_1779_ = lean_ctor_get(v___y_1771_, 2);
v___x_1780_ = lean_array_uget_borrowed(v_as_1767_, v_i_1768_);
v___x_1781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
lean_inc(v___x_1780_);
v___x_1782_ = lean_string_append(v___x_1780_, v___x_1781_);
v___x_1783_ = lean_io_prim_handle_put_str(v_a_1766_, v___x_1782_);
lean_dec_ref(v___x_1782_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; size_t v___x_1785_; size_t v___x_1786_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = ((size_t)1ULL);
v___x_1786_ = lean_usize_add(v_i_1768_, v___x_1785_);
v_i_1768_ = v___x_1786_;
v_b_1770_ = v_a_1784_;
goto _start;
}
else
{
lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1801_; 
lean_inc(v_buildTime_1779_);
lean_inc_ref(v_trace_1778_);
lean_inc_ref(v_log_1774_);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___y_1771_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; lean_object* v_unused_1803_; lean_object* v_unused_1804_; 
v_unused_1802_ = lean_ctor_get(v___y_1771_, 2);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v___y_1771_, 1);
lean_dec(v_unused_1803_);
v_unused_1804_ = lean_ctor_get(v___y_1771_, 0);
lean_dec(v_unused_1804_);
v___x_1789_ = v___y_1771_;
v_isShared_1790_ = v_isSharedCheck_1801_;
goto v_resetjp_1788_;
}
else
{
lean_dec(v___y_1771_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1801_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v_a_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v_a_1791_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1792_ = lean_io_error_to_string(v_a_1791_);
v___x_1793_ = 3;
v___x_1794_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1794_, 0, v___x_1792_);
lean_ctor_set_uint8(v___x_1794_, sizeof(void*)*1, v___x_1793_);
v___x_1795_ = lean_array_get_size(v_log_1774_);
v___x_1796_ = lean_array_push(v_log_1774_, v___x_1794_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1796_);
v___x_1798_ = v___x_1789_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_trace_1778_);
lean_ctor_set(v_reuseFailAlloc_1800_, 2, v_buildTime_1779_);
lean_ctor_set_uint8(v_reuseFailAlloc_1800_, sizeof(void*)*3, v_action_1775_);
lean_ctor_set_uint8(v_reuseFailAlloc_1800_, sizeof(void*)*3 + 1, v_wantsRebuild_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1800_, sizeof(void*)*3 + 2, v_canceled_1777_);
v___x_1798_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1795_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
return v___x_1799_;
}
}
}
}
else
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v_b_1770_);
lean_ctor_set(v___x_1805_, 1, v___y_1771_);
return v___x_1805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(lean_object* v_a_1806_, lean_object* v_as_1807_, lean_object* v_i_1808_, lean_object* v_stop_1809_, lean_object* v_b_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
size_t v_i_boxed_1813_; size_t v_stop_boxed_1814_; lean_object* v_res_1815_; 
v_i_boxed_1813_ = lean_unbox_usize(v_i_1808_);
lean_dec(v_i_1808_);
v_stop_boxed_1814_ = lean_unbox_usize(v_stop_1809_);
lean_dec(v_stop_1809_);
v_res_1815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1806_, v_as_1807_, v_i_boxed_1813_, v_stop_boxed_1814_, v_b_1810_, v___y_1811_);
lean_dec_ref(v_as_1807_);
lean_dec(v_a_1806_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(uint8_t v_bootstrap_1816_, lean_object* v___y_1817_, lean_object* v_oFiles_1818_, uint8_t v_shouldExport_1819_, uint8_t v___x_1820_, size_t v___x_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
if (v_bootstrap_1816_ == 0)
{
lean_object* v_toContext_1829_; lean_object* v_lakeEnv_1830_; lean_object* v_lean_1831_; lean_object* v_log_1832_; uint8_t v_action_1833_; uint8_t v_wantsRebuild_1834_; uint8_t v_canceled_1835_; lean_object* v_trace_1836_; lean_object* v_buildTime_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1867_; 
v_toContext_1829_ = lean_ctor_get(v___y_1826_, 1);
v_lakeEnv_1830_ = lean_ctor_get(v_toContext_1829_, 0);
v_lean_1831_ = lean_ctor_get(v_lakeEnv_1830_, 1);
v_log_1832_ = lean_ctor_get(v___y_1827_, 0);
v_action_1833_ = lean_ctor_get_uint8(v___y_1827_, sizeof(void*)*3);
v_wantsRebuild_1834_ = lean_ctor_get_uint8(v___y_1827_, sizeof(void*)*3 + 1);
v_canceled_1835_ = lean_ctor_get_uint8(v___y_1827_, sizeof(void*)*3 + 2);
v_trace_1836_ = lean_ctor_get(v___y_1827_, 1);
v_buildTime_1837_ = lean_ctor_get(v___y_1827_, 2);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___y_1827_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1839_ = v___y_1827_;
v_isShared_1840_ = v_isSharedCheck_1867_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_buildTime_1837_);
lean_inc(v_trace_1836_);
lean_inc(v_log_1832_);
lean_dec(v___y_1827_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1867_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v_ar_1841_; lean_object* v___x_1842_; 
v_ar_1841_ = lean_ctor_get(v_lean_1831_, 13);
lean_inc_ref(v_ar_1841_);
v___x_1842_ = l_Lake_compileStaticLib(v___y_1817_, v_oFiles_1818_, v_ar_1841_, v_bootstrap_1816_, v_log_1832_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1854_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_a_1844_ = lean_ctor_get(v___x_1842_, 1);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1846_ = v___x_1842_;
v_isShared_1847_ = v_isSharedCheck_1854_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1854_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v_a_1844_);
v___x_1849_ = v___x_1839_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1844_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_trace_1836_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_buildTime_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1853_, sizeof(void*)*3, v_action_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1853_, sizeof(void*)*3 + 1, v_wantsRebuild_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1853_, sizeof(void*)*3 + 2, v_canceled_1835_);
v___x_1849_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1851_; 
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v___x_1849_);
v___x_1851_ = v___x_1846_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1843_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1866_; 
v_a_1855_ = lean_ctor_get(v___x_1842_, 0);
v_a_1856_ = lean_ctor_get(v___x_1842_, 1);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1858_ = v___x_1842_;
v_isShared_1859_ = v_isSharedCheck_1866_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_inc(v_a_1855_);
lean_dec(v___x_1842_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1866_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v_a_1856_);
v___x_1861_ = v___x_1839_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1856_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_trace_1836_);
lean_ctor_set(v_reuseFailAlloc_1865_, 2, v_buildTime_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1865_, sizeof(void*)*3, v_action_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1865_, sizeof(void*)*3 + 1, v_wantsRebuild_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1865_, sizeof(void*)*3 + 2, v_canceled_1835_);
v___x_1861_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1863_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v___x_1861_);
v___x_1863_ = v___x_1858_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1855_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
}
else
{
uint8_t v___x_1868_; 
v___x_1868_ = l_System_Platform_isOSX;
if (v___x_1868_ == 0)
{
uint8_t v___x_1869_; 
v___x_1869_ = l_System_Platform_isWindows;
if (v___x_1869_ == 0)
{
lean_object* v_toContext_1870_; lean_object* v_lakeEnv_1871_; lean_object* v_lean_1872_; lean_object* v_log_1873_; uint8_t v_action_1874_; uint8_t v_wantsRebuild_1875_; uint8_t v_canceled_1876_; lean_object* v_trace_1877_; lean_object* v_buildTime_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1908_; 
v_toContext_1870_ = lean_ctor_get(v___y_1826_, 1);
v_lakeEnv_1871_ = lean_ctor_get(v_toContext_1870_, 0);
v_lean_1872_ = lean_ctor_get(v_lakeEnv_1871_, 1);
v_log_1873_ = lean_ctor_get(v___y_1827_, 0);
v_action_1874_ = lean_ctor_get_uint8(v___y_1827_, sizeof(void*)*3);
v_wantsRebuild_1875_ = lean_ctor_get_uint8(v___y_1827_, sizeof(void*)*3 + 1);
v_canceled_1876_ = lean_ctor_get_uint8(v___y_1827_, sizeof(void*)*3 + 2);
v_trace_1877_ = lean_ctor_get(v___y_1827_, 1);
v_buildTime_1878_ = lean_ctor_get(v___y_1827_, 2);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___y_1827_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1880_ = v___y_1827_;
v_isShared_1881_ = v_isSharedCheck_1908_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_buildTime_1878_);
lean_inc(v_trace_1877_);
lean_inc(v_log_1873_);
lean_dec(v___y_1827_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1908_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v_ar_1882_; lean_object* v___x_1883_; 
v_ar_1882_ = lean_ctor_get(v_lean_1872_, 13);
lean_inc_ref(v_ar_1882_);
v___x_1883_ = l_Lake_compileStaticLib(v___y_1817_, v_oFiles_1818_, v_ar_1882_, v___x_1869_, v_log_1873_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1895_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_a_1885_ = lean_ctor_get(v___x_1883_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1887_ = v___x_1883_;
v_isShared_1888_ = v_isSharedCheck_1895_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1895_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v_a_1885_);
v___x_1890_ = v___x_1880_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1885_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_trace_1877_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_buildTime_1878_);
lean_ctor_set_uint8(v_reuseFailAlloc_1894_, sizeof(void*)*3, v_action_1874_);
lean_ctor_set_uint8(v_reuseFailAlloc_1894_, sizeof(void*)*3 + 1, v_wantsRebuild_1875_);
lean_ctor_set_uint8(v_reuseFailAlloc_1894_, sizeof(void*)*3 + 2, v_canceled_1876_);
v___x_1890_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1892_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 1, v___x_1890_);
v___x_1892_ = v___x_1887_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1884_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1907_; 
v_a_1896_ = lean_ctor_get(v___x_1883_, 0);
v_a_1897_ = lean_ctor_get(v___x_1883_, 1);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1899_ = v___x_1883_;
v_isShared_1900_ = v_isSharedCheck_1907_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_inc(v_a_1896_);
lean_dec(v___x_1883_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1907_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v_a_1897_);
v___x_1902_ = v___x_1880_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1897_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_trace_1877_);
lean_ctor_set(v_reuseFailAlloc_1906_, 2, v_buildTime_1878_);
lean_ctor_set_uint8(v_reuseFailAlloc_1906_, sizeof(void*)*3, v_action_1874_);
lean_ctor_set_uint8(v_reuseFailAlloc_1906_, sizeof(void*)*3 + 1, v_wantsRebuild_1875_);
lean_ctor_set_uint8(v_reuseFailAlloc_1906_, sizeof(void*)*3 + 2, v_canceled_1876_);
v___x_1902_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
lean_object* v___x_1904_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v___x_1902_);
v___x_1904_ = v___x_1899_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1896_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1909_; lean_object* v_lakeEnv_1910_; lean_object* v_lean_1911_; lean_object* v_log_1912_; uint8_t v_action_1913_; uint8_t v_wantsRebuild_1914_; uint8_t v_canceled_1915_; lean_object* v_trace_1916_; lean_object* v_buildTime_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1947_; 
v_toContext_1909_ = lean_ctor_get(v___y_1826_, 1);
v_lakeEnv_1910_ = lean_ctor_get(v_toContext_1909_, 0);
v_lean_1911_ = lean_ctor_get(v_lakeEnv_1910_, 1);
v_log_1912_ = lean_ctor_get(v___y_1827_, 0);
v_action_1913_ = lean_ctor_get_uint8(v___y_1827_, sizeof(void*)*3);
v_wantsRebuild_1914_ = lean_ctor_get_uint8(v___y_1827_, sizeof(void*)*3 + 1);
v_canceled_1915_ = lean_ctor_get_uint8(v___y_1827_, sizeof(void*)*3 + 2);
v_trace_1916_ = lean_ctor_get(v___y_1827_, 1);
v_buildTime_1917_ = lean_ctor_get(v___y_1827_, 2);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___y_1827_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1919_ = v___y_1827_;
v_isShared_1920_ = v_isSharedCheck_1947_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_buildTime_1917_);
lean_inc(v_trace_1916_);
lean_inc(v_log_1912_);
lean_dec(v___y_1827_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1947_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v_ar_1921_; lean_object* v___x_1922_; 
v_ar_1921_ = lean_ctor_get(v_lean_1911_, 13);
lean_inc_ref(v_ar_1921_);
v___x_1922_ = l_Lake_compileStaticLib(v___y_1817_, v_oFiles_1818_, v_ar_1921_, v_shouldExport_1819_, v_log_1912_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1934_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_a_1924_ = lean_ctor_get(v___x_1922_, 1);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1926_ = v___x_1922_;
v_isShared_1927_ = v_isSharedCheck_1934_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1934_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v_a_1924_);
v___x_1929_ = v___x_1919_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1924_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_trace_1916_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v_buildTime_1917_);
lean_ctor_set_uint8(v_reuseFailAlloc_1933_, sizeof(void*)*3, v_action_1913_);
lean_ctor_set_uint8(v_reuseFailAlloc_1933_, sizeof(void*)*3 + 1, v_wantsRebuild_1914_);
lean_ctor_set_uint8(v_reuseFailAlloc_1933_, sizeof(void*)*3 + 2, v_canceled_1915_);
v___x_1929_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1931_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 1, v___x_1929_);
v___x_1931_ = v___x_1926_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1923_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1946_; 
v_a_1935_ = lean_ctor_get(v___x_1922_, 0);
v_a_1936_ = lean_ctor_get(v___x_1922_, 1);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1938_ = v___x_1922_;
v_isShared_1939_ = v_isSharedCheck_1946_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_inc(v_a_1935_);
lean_dec(v___x_1922_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1946_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v_a_1936_);
v___x_1941_ = v___x_1919_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1936_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_trace_1916_);
lean_ctor_set(v_reuseFailAlloc_1945_, 2, v_buildTime_1917_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*3, v_action_1913_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*3 + 1, v_wantsRebuild_1914_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*3 + 2, v_canceled_1915_);
v___x_1941_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1943_; 
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 1, v___x_1941_);
v___x_1943_ = v___x_1938_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1935_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v___x_1941_);
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
}
}
else
{
lean_object* v_log_1948_; uint8_t v_action_1949_; uint8_t v_wantsRebuild_1950_; uint8_t v_canceled_1951_; lean_object* v_trace_1952_; lean_object* v_buildTime_1953_; lean_object* v___x_1954_; 
v_log_1948_ = lean_ctor_get(v___y_1827_, 0);
v_action_1949_ = lean_ctor_get_uint8(v___y_1827_, sizeof(void*)*3);
v_wantsRebuild_1950_ = lean_ctor_get_uint8(v___y_1827_, sizeof(void*)*3 + 1);
v_canceled_1951_ = lean_ctor_get_uint8(v___y_1827_, sizeof(void*)*3 + 2);
v_trace_1952_ = lean_ctor_get(v___y_1827_, 1);
v_buildTime_1953_ = lean_ctor_get(v___y_1827_, 2);
lean_inc_ref(v___y_1817_);
v___x_1954_ = l_Lake_createParentDirs(v___y_1817_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v_a_1958_; uint8_t v___x_2007_; lean_object* v___x_2008_; 
lean_dec_ref_known(v___x_1954_, 1);
v___x_1955_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1817_);
v___x_1956_ = l_System_FilePath_addExtension(v___y_1817_, v___x_1955_);
v___x_2007_ = 1;
v___x_2008_ = lean_io_prim_handle_mk(v___x_1956_, v___x_2007_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
v___x_2010_ = lean_unsigned_to_nat(0u);
v___x_2011_ = lean_array_get_size(v_oFiles_1818_);
v___x_2012_ = lean_nat_dec_lt(v___x_2010_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_dec(v_a_2009_);
lean_dec_ref(v_oFiles_1818_);
v_a_1958_ = v___y_1827_;
goto v___jp_1957_;
}
else
{
lean_object* v___x_2013_; size_t v___x_2014_; lean_object* v___x_2015_; 
v___x_2013_ = lean_box(0);
v___x_2014_ = lean_usize_of_nat(v___x_2011_);
v___x_2015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2009_, v_oFiles_1818_, v___x_1821_, v___x_2014_, v___x_2013_, v___y_1827_);
lean_dec_ref(v_oFiles_1818_);
lean_dec(v_a_2009_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 1);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2015_, 2);
v_a_1958_ = v_a_2016_;
goto v___jp_1957_;
}
else
{
lean_dec_ref(v___x_1956_);
lean_dec_ref(v___y_1817_);
return v___x_2015_;
}
}
}
else
{
lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2030_; 
lean_inc(v_buildTime_1953_);
lean_inc_ref(v_trace_1952_);
lean_inc_ref(v_log_1948_);
lean_dec_ref(v___x_1956_);
lean_dec_ref(v_oFiles_1818_);
lean_dec_ref(v___y_1817_);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___y_1827_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; lean_object* v_unused_2032_; lean_object* v_unused_2033_; 
v_unused_2031_ = lean_ctor_get(v___y_1827_, 2);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v___y_1827_, 1);
lean_dec(v_unused_2032_);
v_unused_2033_ = lean_ctor_get(v___y_1827_, 0);
lean_dec(v_unused_2033_);
v___x_2018_ = v___y_1827_;
v_isShared_2019_ = v_isSharedCheck_2030_;
goto v_resetjp_2017_;
}
else
{
lean_dec(v___y_1827_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2030_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v_a_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
v_a_2020_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2008_, 1);
v___x_2021_ = lean_io_error_to_string(v_a_2020_);
v___x_2022_ = 3;
v___x_2023_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2023_, 0, v___x_2021_);
lean_ctor_set_uint8(v___x_2023_, sizeof(void*)*1, v___x_2022_);
v___x_2024_ = lean_array_get_size(v_log_1948_);
v___x_2025_ = lean_array_push(v_log_1948_, v___x_2023_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2025_);
v___x_2027_ = v___x_2018_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_trace_1952_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v_buildTime_1953_);
lean_ctor_set_uint8(v_reuseFailAlloc_2029_, sizeof(void*)*3, v_action_1949_);
lean_ctor_set_uint8(v_reuseFailAlloc_2029_, sizeof(void*)*3 + 1, v_wantsRebuild_1950_);
lean_ctor_set_uint8(v_reuseFailAlloc_2029_, sizeof(void*)*3 + 2, v_canceled_1951_);
v___x_2027_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2028_; 
v___x_2028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2024_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
return v___x_2028_;
}
}
}
v___jp_1957_:
{
lean_object* v___x_1959_; lean_object* v_log_1960_; uint8_t v_action_1961_; uint8_t v_wantsRebuild_1962_; uint8_t v_canceled_1963_; lean_object* v_trace_1964_; lean_object* v_buildTime_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_2006_; 
v___x_1959_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1960_ = lean_ctor_get(v_a_1958_, 0);
v_action_1961_ = lean_ctor_get_uint8(v_a_1958_, sizeof(void*)*3);
v_wantsRebuild_1962_ = lean_ctor_get_uint8(v_a_1958_, sizeof(void*)*3 + 1);
v_canceled_1963_ = lean_ctor_get_uint8(v_a_1958_, sizeof(void*)*3 + 2);
v_trace_1964_ = lean_ctor_get(v_a_1958_, 1);
v_buildTime_1965_ = lean_ctor_get(v_a_1958_, 2);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_a_1958_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1967_ = v_a_1958_;
v_isShared_1968_ = v_isSharedCheck_2006_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_buildTime_1965_);
lean_inc(v_trace_1964_);
lean_inc(v_log_1960_);
lean_dec(v_a_1958_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_2006_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1969_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1970_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1971_ = lean_unsigned_to_nat(5u);
v___x_1972_ = lean_mk_empty_array_with_capacity(v___x_1971_);
lean_dec_ref(v___x_1972_);
v___x_1973_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1974_ = lean_array_push(v___x_1973_, v___y_1817_);
v___x_1975_ = lean_array_push(v___x_1974_, v___x_1970_);
v___x_1976_ = lean_array_push(v___x_1975_, v___x_1956_);
v___x_1977_ = lean_box(0);
v___x_1978_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1979_ = 0;
v___x_1980_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1980_, 0, v___x_1959_);
lean_ctor_set(v___x_1980_, 1, v___x_1969_);
lean_ctor_set(v___x_1980_, 2, v___x_1976_);
lean_ctor_set(v___x_1980_, 3, v___x_1977_);
lean_ctor_set(v___x_1980_, 4, v___x_1978_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*5, v___x_1820_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*5 + 1, v___x_1979_);
v___x_1981_ = l_Lake_proc(v___x_1980_, v___x_1979_, v___x_1977_, v_log_1960_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1993_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_a_1983_ = lean_ctor_get(v___x_1981_, 1);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1985_ = v___x_1981_;
v_isShared_1986_ = v_isSharedCheck_1993_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1993_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v_a_1983_);
v___x_1988_ = v___x_1967_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1983_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_trace_1964_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_buildTime_1965_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*3, v_action_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*3 + 1, v_wantsRebuild_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*3 + 2, v_canceled_1963_);
v___x_1988_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1990_; 
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 1, v___x_1988_);
v___x_1990_ = v___x_1985_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1982_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v___x_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2005_; 
v_a_1994_ = lean_ctor_get(v___x_1981_, 0);
v_a_1995_ = lean_ctor_get(v___x_1981_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1997_ = v___x_1981_;
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_inc(v_a_1994_);
lean_dec(v___x_1981_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v_a_1995_);
v___x_2000_ = v___x_1967_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1995_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_trace_1964_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_buildTime_1965_);
lean_ctor_set_uint8(v_reuseFailAlloc_2004_, sizeof(void*)*3, v_action_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_2004_, sizeof(void*)*3 + 1, v_wantsRebuild_1962_);
lean_ctor_set_uint8(v_reuseFailAlloc_2004_, sizeof(void*)*3 + 2, v_canceled_1963_);
v___x_2000_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2002_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 1, v___x_2000_);
v___x_2002_ = v___x_1997_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1994_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2047_; 
lean_inc(v_buildTime_1953_);
lean_inc_ref(v_trace_1952_);
lean_inc_ref(v_log_1948_);
lean_dec_ref(v_oFiles_1818_);
lean_dec_ref(v___y_1817_);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___y_1827_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; lean_object* v_unused_2049_; lean_object* v_unused_2050_; 
v_unused_2048_ = lean_ctor_get(v___y_1827_, 2);
lean_dec(v_unused_2048_);
v_unused_2049_ = lean_ctor_get(v___y_1827_, 1);
lean_dec(v_unused_2049_);
v_unused_2050_ = lean_ctor_get(v___y_1827_, 0);
lean_dec(v_unused_2050_);
v___x_2035_ = v___y_1827_;
v_isShared_2036_ = v_isSharedCheck_2047_;
goto v_resetjp_2034_;
}
else
{
lean_dec(v___y_1827_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2047_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v_a_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v_a_2037_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_2038_ = lean_io_error_to_string(v_a_2037_);
v___x_2039_ = 3;
v___x_2040_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2040_, 0, v___x_2038_);
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*1, v___x_2039_);
v___x_2041_ = lean_array_get_size(v_log_1948_);
v___x_2042_ = lean_array_push(v_log_1948_, v___x_2040_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2042_);
v___x_2044_ = v___x_2035_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_trace_1952_);
lean_ctor_set(v_reuseFailAlloc_2046_, 2, v_buildTime_1953_);
lean_ctor_set_uint8(v_reuseFailAlloc_2046_, sizeof(void*)*3, v_action_1949_);
lean_ctor_set_uint8(v_reuseFailAlloc_2046_, sizeof(void*)*3 + 1, v_wantsRebuild_1950_);
lean_ctor_set_uint8(v_reuseFailAlloc_2046_, sizeof(void*)*3 + 2, v_canceled_1951_);
v___x_2044_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2041_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
return v___x_2045_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object* v_bootstrap_2051_, lean_object* v___y_2052_, lean_object* v_oFiles_2053_, lean_object* v_shouldExport_2054_, lean_object* v___x_2055_, lean_object* v___x_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
uint8_t v_bootstrap_boxed_2064_; uint8_t v_shouldExport_boxed_2065_; uint8_t v___x_5833__boxed_2066_; size_t v___x_5834__boxed_2067_; lean_object* v_res_2068_; 
v_bootstrap_boxed_2064_ = lean_unbox(v_bootstrap_2051_);
v_shouldExport_boxed_2065_ = lean_unbox(v_shouldExport_2054_);
v___x_5833__boxed_2066_ = lean_unbox(v___x_2055_);
v___x_5834__boxed_2067_ = lean_unbox_usize(v___x_2056_);
lean_dec(v___x_2056_);
v_res_2068_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_boxed_2064_, v___y_2052_, v_oFiles_2053_, v_shouldExport_boxed_2065_, v___x_5833__boxed_2066_, v___x_5834__boxed_2067_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t v_bootstrap_2069_, lean_object* v___y_2070_, uint8_t v_shouldExport_2071_, uint8_t v___x_2072_, size_t v___x_2073_, lean_object* v_oFiles_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___y_2086_; uint8_t v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2082_ = lean_box(v_bootstrap_2069_);
v___x_2083_ = lean_box(v_shouldExport_2071_);
v___x_2084_ = lean_box(v___x_2072_);
v___x_2085_ = lean_box_usize(v___x_2073_);
lean_inc_ref(v___y_2070_);
v___y_2086_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed), 13, 6);
lean_closure_set(v___y_2086_, 0, v___x_2082_);
lean_closure_set(v___y_2086_, 1, v___y_2070_);
lean_closure_set(v___y_2086_, 2, v_oFiles_2074_);
lean_closure_set(v___y_2086_, 3, v___x_2083_);
lean_closure_set(v___y_2086_, 4, v___x_2084_);
lean_closure_set(v___y_2086_, 5, v___x_2085_);
v___x_2087_ = 0;
v___x_2088_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_2089_ = l_Lake_buildArtifactUnlessUpToDate(v___y_2070_, v___y_2086_, v___x_2087_, v___x_2088_, v___x_2072_, v___x_2087_, v___x_2087_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2099_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_a_2091_ = lean_ctor_get(v___x_2089_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2093_ = v___x_2089_;
v_isShared_2094_ = v_isSharedCheck_2099_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2099_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v_path_2095_; lean_object* v___x_2097_; 
v_path_2095_ = lean_ctor_get(v_a_2090_, 1);
lean_inc_ref(v_path_2095_);
lean_dec(v_a_2090_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v_path_2095_);
v___x_2097_ = v___x_2093_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_path_2095_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_a_2091_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
else
{
lean_object* v_a_2100_; lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
v_a_2100_ = lean_ctor_get(v___x_2089_, 0);
v_a_2101_ = lean_ctor_get(v___x_2089_, 1);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2089_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_inc(v_a_2100_);
lean_dec(v___x_2089_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2100_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* v_bootstrap_2109_, lean_object* v___y_2110_, lean_object* v_shouldExport_2111_, lean_object* v___x_2112_, lean_object* v___x_2113_, lean_object* v_oFiles_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
uint8_t v_bootstrap_boxed_2122_; uint8_t v_shouldExport_boxed_2123_; uint8_t v___x_6233__boxed_2124_; size_t v___x_6234__boxed_2125_; lean_object* v_res_2126_; 
v_bootstrap_boxed_2122_ = lean_unbox(v_bootstrap_2109_);
v_shouldExport_boxed_2123_ = lean_unbox(v_shouldExport_2111_);
v___x_6233__boxed_2124_ = lean_unbox(v___x_2112_);
v___x_6234__boxed_2125_ = lean_unbox_usize(v___x_2113_);
lean_dec(v___x_2113_);
v_res_2126_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_boxed_2122_, v___y_2110_, v_shouldExport_boxed_2123_, v___x_6233__boxed_2124_, v___x_6234__boxed_2125_, v_oFiles_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec(v___y_2117_);
lean_dec(v___y_2116_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* v_a_2127_, size_t v_sz_2128_, size_t v_i_2129_, lean_object* v_bs_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
uint8_t v___x_2138_; 
v___x_2138_ = lean_usize_dec_lt(v_i_2129_, v_sz_2128_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; 
lean_dec_ref(v___y_2131_);
lean_dec_ref(v_a_2127_);
v___x_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2139_, 0, v_bs_2130_);
lean_ctor_set(v___x_2139_, 1, v___y_2136_);
return v___x_2139_;
}
else
{
lean_object* v_v_2140_; lean_object* v___x_2141_; lean_object* v_bs_x27_2142_; lean_object* v___x_2143_; 
v_v_2140_ = lean_array_uget(v_bs_2130_, v_i_2129_);
v___x_2141_ = lean_unsigned_to_nat(0u);
v_bs_x27_2142_ = lean_array_uset(v_bs_2130_, v_i_2129_, v___x_2141_);
lean_inc_ref(v___y_2131_);
lean_inc_ref(v_a_2127_);
v___x_2143_ = l_Lake_ModuleFacet_fetch___redArg(v_v_2140_, v_a_2127_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v_a_2145_; size_t v___x_2146_; size_t v___x_2147_; lean_object* v___x_2148_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
v_a_2145_ = lean_ctor_get(v___x_2143_, 1);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2143_, 2);
v___x_2146_ = ((size_t)1ULL);
v___x_2147_ = lean_usize_add(v_i_2129_, v___x_2146_);
v___x_2148_ = lean_array_uset(v_bs_x27_2142_, v_i_2129_, v_a_2144_);
v_i_2129_ = v___x_2147_;
v_bs_2130_ = v___x_2148_;
v___y_2136_ = v_a_2145_;
goto _start;
}
else
{
lean_object* v_a_2150_; lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v_bs_x27_2142_);
lean_dec_ref(v___y_2131_);
lean_dec_ref(v_a_2127_);
v_a_2150_ = lean_ctor_get(v___x_2143_, 0);
v_a_2151_ = lean_ctor_get(v___x_2143_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2143_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_inc(v_a_2150_);
lean_dec(v___x_2143_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object* v_a_2159_, lean_object* v_sz_2160_, lean_object* v_i_2161_, lean_object* v_bs_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
size_t v_sz_boxed_2170_; size_t v_i_boxed_2171_; lean_object* v_res_2172_; 
v_sz_boxed_2170_ = lean_unbox_usize(v_sz_2160_);
lean_dec(v_sz_2160_);
v_i_boxed_2171_ = lean_unbox_usize(v_i_2161_);
lean_dec(v_i_2161_);
v_res_2172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_2159_, v_sz_boxed_2170_, v_i_boxed_2171_, v_bs_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec(v___y_2164_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(uint8_t v_shouldExport_2173_, lean_object* v_as_2174_, size_t v_i_2175_, size_t v_stop_2176_, lean_object* v_b_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
uint8_t v___x_2185_; 
v___x_2185_ = lean_usize_dec_eq(v_i_2175_, v_stop_2176_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; lean_object* v_lib_2187_; lean_object* v_config_2188_; lean_object* v_nativeFacets_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; size_t v_sz_2192_; size_t v___x_2193_; lean_object* v___x_2194_; 
v___x_2186_ = lean_array_uget_borrowed(v_as_2174_, v_i_2175_);
v_lib_2187_ = lean_ctor_get(v___x_2186_, 0);
v_config_2188_ = lean_ctor_get(v_lib_2187_, 2);
v_nativeFacets_2189_ = lean_ctor_get(v_config_2188_, 8);
v___x_2190_ = lean_box(v_shouldExport_2173_);
lean_inc_ref(v_nativeFacets_2189_);
v___x_2191_ = lean_apply_1(v_nativeFacets_2189_, v___x_2190_);
v_sz_2192_ = lean_array_size(v___x_2191_);
v___x_2193_ = ((size_t)0ULL);
lean_inc_ref(v___y_2178_);
lean_inc(v___x_2186_);
v___x_2194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2186_, v_sz_2192_, v___x_2193_, v___x_2191_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v_a_2196_; lean_object* v___x_2197_; size_t v___x_2198_; size_t v___x_2199_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
v_a_2196_ = lean_ctor_get(v___x_2194_, 1);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2194_, 2);
v___x_2197_ = l_Array_append___redArg(v_b_2177_, v_a_2195_);
lean_dec(v_a_2195_);
v___x_2198_ = ((size_t)1ULL);
v___x_2199_ = lean_usize_add(v_i_2175_, v___x_2198_);
v_i_2175_ = v___x_2199_;
v_b_2177_ = v___x_2197_;
v___y_2183_ = v_a_2196_;
goto _start;
}
else
{
lean_dec_ref(v___y_2178_);
lean_dec_ref(v_b_2177_);
return v___x_2194_;
}
}
else
{
lean_object* v___x_2201_; 
lean_dec_ref(v___y_2178_);
v___x_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_b_2177_);
lean_ctor_set(v___x_2201_, 1, v___y_2183_);
return v___x_2201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(lean_object* v_shouldExport_2202_, lean_object* v_as_2203_, lean_object* v_i_2204_, lean_object* v_stop_2205_, lean_object* v_b_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
uint8_t v_shouldExport_boxed_2214_; size_t v_i_boxed_2215_; size_t v_stop_boxed_2216_; lean_object* v_res_2217_; 
v_shouldExport_boxed_2214_ = lean_unbox(v_shouldExport_2202_);
v_i_boxed_2215_ = lean_unbox_usize(v_i_2204_);
lean_dec(v_i_2204_);
v_stop_boxed_2216_ = lean_unbox_usize(v_stop_2205_);
lean_dec(v_stop_2205_);
v_res_2217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_boxed_2214_, v_as_2203_, v_i_boxed_2215_, v_stop_boxed_2216_, v_b_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v_as_2203_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object* v_config_2218_, lean_object* v_config_2219_, uint8_t v_shouldExport_2220_, uint8_t v___x_2221_, lean_object* v___x_2222_, lean_object* v___x_2223_, lean_object* v_pkg_2224_, lean_object* v_dir_2225_, lean_object* v_self_2226_, lean_object* v___x_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
size_t v___y_2236_; uint8_t v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v_a_2256_; lean_object* v_a_2257_; lean_object* v___x_2299_; 
lean_inc_ref(v___y_2228_);
lean_inc_ref(v___y_2232_);
lean_inc(v___y_2231_);
lean_inc(v___y_2230_);
lean_inc(v___x_2223_);
v___x_2299_ = lean_apply_7(v___y_2228_, v___x_2227_, v___x_2223_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, lean_box(0));
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v_a_2301_; lean_object* v___x_2302_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
v_a_2301_ = lean_ctor_get(v___x_2299_, 1);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2299_, 2);
v___x_2302_ = l_Lake_Job_await___redArg(v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v_a_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
v_a_2304_ = lean_ctor_get(v___x_2302_, 1);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2302_, 2);
v___x_2305_ = lean_unsigned_to_nat(0u);
v___x_2306_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_2307_ = lean_array_get_size(v_a_2303_);
v___x_2308_ = lean_nat_dec_lt(v___x_2305_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_dec(v_a_2303_);
v_a_2256_ = v___x_2306_;
v_a_2257_ = v_a_2304_;
goto v___jp_2255_;
}
else
{
size_t v___x_2309_; size_t v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = ((size_t)0ULL);
v___x_2310_ = lean_usize_of_nat(v___x_2307_);
lean_inc_ref(v___y_2228_);
v___x_2311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2220_, v_a_2303_, v___x_2309_, v___x_2310_, v___x_2306_, v___y_2228_, v___x_2223_, v___y_2230_, v___y_2231_, v___y_2232_, v_a_2304_);
lean_dec(v_a_2303_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v_a_2313_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
v_a_2313_ = lean_ctor_get(v___x_2311_, 1);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2311_, 2);
v_a_2256_ = v_a_2312_;
v_a_2257_ = v_a_2313_;
goto v___jp_2255_;
}
else
{
lean_object* v_a_2314_; lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec_ref(v___y_2228_);
lean_dec_ref(v_self_2226_);
lean_dec_ref(v_dir_2225_);
lean_dec_ref(v_pkg_2224_);
lean_dec(v___x_2223_);
lean_dec(v___x_2222_);
lean_dec_ref(v_config_2218_);
v_a_2314_ = lean_ctor_get(v___x_2311_, 0);
v_a_2315_ = lean_ctor_get(v___x_2311_, 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2311_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_inc(v_a_2314_);
lean_dec(v___x_2311_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2314_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v___y_2228_);
lean_dec_ref(v_self_2226_);
lean_dec_ref(v_dir_2225_);
lean_dec_ref(v_pkg_2224_);
lean_dec(v___x_2223_);
lean_dec(v___x_2222_);
lean_dec_ref(v_config_2218_);
v_a_2323_ = lean_ctor_get(v___x_2302_, 0);
v_a_2324_ = lean_ctor_get(v___x_2302_, 1);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2302_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_inc(v_a_2323_);
lean_dec(v___x_2302_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2323_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec_ref(v___y_2228_);
lean_dec_ref(v_self_2226_);
lean_dec_ref(v_dir_2225_);
lean_dec_ref(v_pkg_2224_);
lean_dec(v___x_2223_);
lean_dec(v___x_2222_);
lean_dec_ref(v_config_2218_);
v_a_2332_ = lean_ctor_get(v___x_2299_, 0);
v_a_2333_ = lean_ctor_get(v___x_2299_, 1);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2299_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_inc(v_a_2332_);
lean_dec(v___x_2299_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2332_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
v___jp_2235_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___f_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2242_ = lean_box(v___y_2237_);
v___x_2243_ = lean_box(v_shouldExport_2220_);
v___x_2244_ = lean_box(v___x_2221_);
v___x_2245_ = lean_box_usize(v___y_2236_);
v___f_2246_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2246_, 0, v___x_2242_);
lean_closure_set(v___f_2246_, 1, v___y_2241_);
lean_closure_set(v___f_2246_, 2, v___x_2243_);
lean_closure_set(v___f_2246_, 3, v___x_2244_);
lean_closure_set(v___f_2246_, 4, v___x_2245_);
v___x_2247_ = l_Array_append___redArg(v___y_2240_, v___y_2238_);
lean_dec_ref(v___y_2238_);
v___x_2248_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_2249_ = l_Lake_Job_collectArray___redArg(v___x_2247_, v___x_2248_);
lean_dec_ref(v___x_2247_);
v___x_2250_ = lean_unsigned_to_nat(0u);
v___x_2251_ = 0;
v___x_2252_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_2253_ = l_Lake_Job_mapM___redArg(v___x_2222_, v___x_2249_, v___f_2246_, v___x_2250_, v___x_2251_, v___y_2228_, v___x_2223_, v___y_2230_, v___y_2231_, v___y_2232_, v___x_2252_);
lean_dec(v___x_2223_);
v___x_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
lean_ctor_set(v___x_2254_, 1, v___y_2239_);
return v___x_2254_;
}
v___jp_2255_:
{
lean_object* v_toLeanConfig_2258_; lean_object* v_toLeanConfig_2259_; uint8_t v_bootstrap_2260_; lean_object* v_buildDir_2261_; lean_object* v_nativeLibDir_2262_; lean_object* v_moreLinkObjs_2263_; lean_object* v_moreLinkObjs_2264_; lean_object* v___x_2265_; size_t v_sz_2266_; size_t v___x_2267_; lean_object* v___x_2268_; 
v_toLeanConfig_2258_ = lean_ctor_get(v_config_2218_, 1);
lean_inc_ref(v_toLeanConfig_2258_);
v_toLeanConfig_2259_ = lean_ctor_get(v_config_2219_, 0);
v_bootstrap_2260_ = lean_ctor_get_uint8(v_config_2218_, sizeof(void*)*28);
v_buildDir_2261_ = lean_ctor_get(v_config_2218_, 5);
lean_inc_ref(v_buildDir_2261_);
v_nativeLibDir_2262_ = lean_ctor_get(v_config_2218_, 7);
lean_inc_ref(v_nativeLibDir_2262_);
lean_dec_ref(v_config_2218_);
v_moreLinkObjs_2263_ = lean_ctor_get(v_toLeanConfig_2258_, 6);
lean_inc_ref(v_moreLinkObjs_2263_);
lean_dec_ref(v_toLeanConfig_2258_);
v_moreLinkObjs_2264_ = lean_ctor_get(v_toLeanConfig_2259_, 6);
v___x_2265_ = l_Array_append___redArg(v_moreLinkObjs_2263_, v_moreLinkObjs_2264_);
v_sz_2266_ = lean_array_size(v___x_2265_);
v___x_2267_ = ((size_t)0ULL);
lean_inc_ref(v___y_2228_);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_2224_, v_sz_2266_, v___x_2267_, v___x_2265_, v___y_2228_, v___x_2223_, v___y_2230_, v___y_2231_, v___y_2232_, v_a_2257_);
if (lean_obj_tag(v___x_2268_) == 0)
{
if (v_shouldExport_2220_ == 0)
{
lean_object* v_a_2269_; lean_object* v_a_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
v_a_2270_ = lean_ctor_get(v___x_2268_, 1);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2268_, 2);
v___x_2271_ = l_System_FilePath_normalize(v_buildDir_2261_);
v___x_2272_ = l_Lake_joinRelative(v_dir_2225_, v___x_2271_);
v___x_2273_ = l_System_FilePath_normalize(v_nativeLibDir_2262_);
v___x_2274_ = l_Lake_joinRelative(v___x_2272_, v___x_2273_);
v___x_2275_ = l_Lake_LeanLib_libName(v_self_2226_);
v___x_2276_ = l_Lake_nameToStaticLib(v___x_2275_, v_shouldExport_2220_);
v___x_2277_ = l_Lake_joinRelative(v___x_2274_, v___x_2276_);
v___y_2236_ = v___x_2267_;
v___y_2237_ = v_bootstrap_2260_;
v___y_2238_ = v_a_2269_;
v___y_2239_ = v_a_2270_;
v___y_2240_ = v_a_2256_;
v___y_2241_ = v___x_2277_;
goto v___jp_2235_;
}
else
{
lean_object* v_a_2278_; lean_object* v_a_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v_a_2278_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2278_);
v_a_2279_ = lean_ctor_get(v___x_2268_, 1);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2268_, 2);
v___x_2280_ = l_System_FilePath_normalize(v_buildDir_2261_);
v___x_2281_ = l_Lake_joinRelative(v_dir_2225_, v___x_2280_);
v___x_2282_ = l_System_FilePath_normalize(v_nativeLibDir_2262_);
v___x_2283_ = l_Lake_joinRelative(v___x_2281_, v___x_2282_);
v___x_2284_ = l_Lake_LeanLib_libName(v_self_2226_);
v___x_2285_ = 0;
v___x_2286_ = l_Lake_nameToStaticLib(v___x_2284_, v___x_2285_);
v___x_2287_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_2288_ = l_System_FilePath_addExtension(v___x_2286_, v___x_2287_);
v___x_2289_ = l_Lake_joinRelative(v___x_2283_, v___x_2288_);
v___y_2236_ = v___x_2267_;
v___y_2237_ = v_bootstrap_2260_;
v___y_2238_ = v_a_2278_;
v___y_2239_ = v_a_2279_;
v___y_2240_ = v_a_2256_;
v___y_2241_ = v___x_2289_;
goto v___jp_2235_;
}
}
else
{
lean_object* v_a_2290_; lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v_nativeLibDir_2262_);
lean_dec_ref(v_buildDir_2261_);
lean_dec_ref(v_a_2256_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v_self_2226_);
lean_dec_ref(v_dir_2225_);
lean_dec(v___x_2223_);
lean_dec(v___x_2222_);
v_a_2290_ = lean_ctor_get(v___x_2268_, 0);
v_a_2291_ = lean_ctor_get(v___x_2268_, 1);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2268_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_inc(v_a_2290_);
lean_dec(v___x_2268_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2290_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(lean_object** _args){
lean_object* v_config_2341_ = _args[0];
lean_object* v_config_2342_ = _args[1];
lean_object* v_shouldExport_2343_ = _args[2];
lean_object* v___x_2344_ = _args[3];
lean_object* v___x_2345_ = _args[4];
lean_object* v___x_2346_ = _args[5];
lean_object* v_pkg_2347_ = _args[6];
lean_object* v_dir_2348_ = _args[7];
lean_object* v_self_2349_ = _args[8];
lean_object* v___x_2350_ = _args[9];
lean_object* v___y_2351_ = _args[10];
lean_object* v___y_2352_ = _args[11];
lean_object* v___y_2353_ = _args[12];
lean_object* v___y_2354_ = _args[13];
lean_object* v___y_2355_ = _args[14];
lean_object* v___y_2356_ = _args[15];
lean_object* v___y_2357_ = _args[16];
_start:
{
uint8_t v_shouldExport_boxed_2358_; uint8_t v___x_6431__boxed_2359_; lean_object* v_res_2360_; 
v_shouldExport_boxed_2358_ = lean_unbox(v_shouldExport_2343_);
v___x_6431__boxed_2359_ = lean_unbox(v___x_2344_);
v_res_2360_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v_config_2341_, v_config_2342_, v_shouldExport_boxed_2358_, v___x_6431__boxed_2359_, v___x_2345_, v___x_2346_, v_pkg_2347_, v_dir_2348_, v_self_2349_, v___x_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec(v_config_2342_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object* v___y_2361_, lean_object* v_self_2362_, uint8_t v_shouldExport_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v_toBuildConfig_2370_; lean_object* v_registeredJobs_2371_; uint8_t v_verbosity_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; uint8_t v___x_2377_; lean_object* v___y_2379_; 
v_toBuildConfig_2370_ = lean_ctor_get(v_a_2367_, 0);
v_registeredJobs_2371_ = lean_ctor_get(v_a_2367_, 4);
v_verbosity_2372_ = lean_ctor_get_uint8(v_toBuildConfig_2370_, sizeof(void*)*5 + 4);
v___x_2373_ = l_Lake_instDataKindFilePath;
v___x_2374_ = l_Lake_Verbosity_ctorIdx(v_verbosity_2372_);
v___x_2375_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0);
v___x_2376_ = lean_nat_dec_eq(v___x_2374_, v___x_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = 1;
if (v___x_2376_ == 0)
{
lean_object* v___x_2424_; 
v___x_2424_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_2379_ = v___x_2424_;
goto v___jp_2378_;
}
else
{
if (v_shouldExport_2363_ == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_2379_ = v___x_2425_;
goto v___jp_2378_;
}
else
{
lean_object* v___x_2426_; 
v___x_2426_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3));
v___y_2379_ = v___x_2426_;
goto v___jp_2378_;
}
}
v___jp_2378_:
{
lean_object* v_pkg_2380_; lean_object* v_name_2381_; lean_object* v_config_2382_; lean_object* v_keyName_2383_; lean_object* v_dir_2384_; lean_object* v_config_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___f_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; 
v_pkg_2380_ = lean_ctor_get(v_self_2362_, 0);
lean_inc_ref_n(v_pkg_2380_, 2);
v_name_2381_ = lean_ctor_get(v_self_2362_, 1);
v_config_2382_ = lean_ctor_get(v_self_2362_, 2);
lean_inc(v_config_2382_);
v_keyName_2383_ = lean_ctor_get(v_pkg_2380_, 2);
v_dir_2384_ = lean_ctor_get(v_pkg_2380_, 4);
lean_inc_ref(v_dir_2384_);
v_config_2385_ = lean_ctor_get(v_pkg_2380_, 6);
lean_inc_ref(v_config_2385_);
lean_inc_n(v_name_2381_, 2);
v___x_2386_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2381_, v___x_2377_);
v___x_2387_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___x_2388_ = lean_string_append(v___x_2386_, v___x_2387_);
v___x_2389_ = lean_string_append(v___x_2388_, v___y_2379_);
v___x_2390_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_2383_);
v___x_2391_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2391_, 0, v_keyName_2383_);
lean_ctor_set(v___x_2391_, 1, v_name_2381_);
v___x_2392_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_2362_);
v___x_2393_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
lean_ctor_set(v___x_2393_, 2, v_self_2362_);
lean_ctor_set(v___x_2393_, 3, v___x_2390_);
v___x_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2394_, 0, v_pkg_2380_);
v___x_2395_ = lean_box(v_shouldExport_2363_);
v___x_2396_ = lean_box(v___x_2377_);
v___f_2397_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed), 17, 10);
lean_closure_set(v___f_2397_, 0, v_config_2385_);
lean_closure_set(v___f_2397_, 1, v_config_2382_);
lean_closure_set(v___f_2397_, 2, v___x_2395_);
lean_closure_set(v___f_2397_, 3, v___x_2396_);
lean_closure_set(v___f_2397_, 4, v___x_2373_);
lean_closure_set(v___f_2397_, 5, v___x_2394_);
lean_closure_set(v___f_2397_, 6, v_pkg_2380_);
lean_closure_set(v___f_2397_, 7, v_dir_2384_);
lean_closure_set(v___f_2397_, 8, v_self_2362_);
lean_closure_set(v___f_2397_, 9, v___x_2393_);
v___x_2398_ = 0;
v___x_2399_ = l_Lake_ensureJob___redArg(v___x_2373_, v___f_2397_, v___y_2361_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2423_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
v_a_2401_ = lean_ctor_get(v___x_2399_, 1);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2403_ = v___x_2399_;
v_isShared_2404_ = v_isSharedCheck_2423_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_inc(v_a_2400_);
lean_dec(v___x_2399_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2423_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v_task_2405_; lean_object* v_kind_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2421_; 
v_task_2405_ = lean_ctor_get(v_a_2400_, 0);
v_kind_2406_ = lean_ctor_get(v_a_2400_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_a_2400_);
if (v_isSharedCheck_2421_ == 0)
{
lean_object* v_unused_2422_; 
v_unused_2422_ = lean_ctor_get(v_a_2400_, 2);
lean_dec(v_unused_2422_);
v___x_2408_ = v_a_2400_;
v_isShared_2409_ = v_isSharedCheck_2421_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_kind_2406_);
lean_inc(v_task_2405_);
lean_dec(v_a_2400_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2421_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v_job_2411_; 
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 2, v___x_2389_);
v_job_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_task_2405_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_kind_2406_);
lean_ctor_set(v_reuseFailAlloc_2420_, 2, v___x_2389_);
v_job_2411_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2418_; 
lean_ctor_set_uint8(v_job_2411_, sizeof(void*)*3, v___x_2398_);
v___x_2412_ = lean_st_ref_take(v_registeredJobs_2371_);
lean_inc_ref(v_job_2411_);
v___x_2413_ = l_Lake_Job_toOpaque___redArg(v_job_2411_);
v___x_2414_ = lean_array_push(v___x_2412_, v___x_2413_);
v___x_2415_ = lean_st_ref_put(v_registeredJobs_2371_, v___x_2414_);
v___x_2416_ = l_Lake_Job_renew___redArg(v_job_2411_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2416_);
v___x_2418_ = v___x_2403_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_a_2401_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2389_);
return v___x_2399_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* v___y_2427_, lean_object* v_self_2428_, lean_object* v_shouldExport_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
uint8_t v_shouldExport_boxed_2436_; lean_object* v_res_2437_; 
v_shouldExport_boxed_2436_ = lean_unbox(v_shouldExport_2429_);
v_res_2437_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2427_, v_self_2428_, v_shouldExport_boxed_2436_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec(v_a_2430_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* v_x_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
uint8_t v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = 0;
v___x_2447_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2439_, v_x_2438_, v___x_2446_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object* v_x_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec(v___y_2450_);
return v_res_2456_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2459_; uint8_t v___x_2460_; lean_object* v___x_2461_; lean_object* v___f_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___f_2459_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2460_ = 1;
v___x_2461_ = l_Lake_instDataKindFilePath;
v___f_2462_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__0));
v___x_2463_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2464_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v___f_2462_);
lean_ctor_set(v___x_2464_, 2, v___x_2461_);
lean_ctor_set(v___x_2464_, 3, v___f_2459_);
lean_ctor_set_uint8(v___x_2464_, sizeof(void*)*4, v___x_2460_);
lean_ctor_set_uint8(v___x_2464_, sizeof(void*)*4 + 1, v___x_2460_);
return v___x_2464_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = lean_obj_once(&l_Lake_LeanLib_staticFacetConfig___closed__2, &l_Lake_LeanLib_staticFacetConfig___closed__2_once, _init_l_Lake_LeanLib_staticFacetConfig___closed__2);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(lean_object* v_a_2466_, lean_object* v_as_2467_, size_t v_i_2468_, size_t v_stop_2469_, lean_object* v_b_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2466_, v_as_2467_, v_i_2468_, v_stop_2469_, v_b_2470_, v___y_2476_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* v_a_2479_, lean_object* v_as_2480_, lean_object* v_i_2481_, lean_object* v_stop_2482_, lean_object* v_b_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
size_t v_i_boxed_2491_; size_t v_stop_boxed_2492_; lean_object* v_res_2493_; 
v_i_boxed_2491_ = lean_unbox_usize(v_i_2481_);
lean_dec(v_i_2481_);
v_stop_boxed_2492_ = lean_unbox_usize(v_stop_2482_);
lean_dec(v_stop_2482_);
v_res_2493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_2479_, v_as_2480_, v_i_boxed_2491_, v_stop_boxed_2492_, v_b_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec_ref(v_as_2480_);
lean_dec(v_a_2479_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* v_x_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
uint8_t v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = 1;
v___x_2503_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2495_, v_x_2494_, v___x_2502_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object* v_x_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec(v___y_2506_);
return v_res_2512_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2514_; uint8_t v___x_2515_; lean_object* v___x_2516_; lean_object* v___f_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___f_2514_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2515_ = 1;
v___x_2516_ = l_Lake_instDataKindFilePath;
v___f_2517_ = ((lean_object*)(l_Lake_LeanLib_staticExportFacetConfig___closed__0));
v___x_2518_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2519_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
lean_ctor_set(v___x_2519_, 1, v___f_2517_);
lean_ctor_set(v___x_2519_, 2, v___x_2516_);
lean_ctor_set(v___x_2519_, 3, v___f_2514_);
lean_ctor_set_uint8(v___x_2519_, sizeof(void*)*4, v___x_2515_);
lean_ctor_set_uint8(v___x_2519_, sizeof(void*)*4 + 1, v___x_2515_);
return v___x_2519_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig(void){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_obj_once(&l_Lake_LeanLib_staticExportFacetConfig___closed__1, &l_Lake_LeanLib_staticExportFacetConfig___closed__1_once, _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1);
return v___x_2520_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0(void){
_start:
{
uint8_t v___x_2521_; lean_object* v_name_2522_; lean_object* v___x_2523_; 
v___x_2521_ = 1;
v_name_2522_ = l_Lake_instDataKindDynlib;
v___x_2523_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2522_, v___x_2521_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object* v_defaultPkg_2524_, lean_object* v_self_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_){
_start:
{
lean_object* v_name_2533_; uint8_t v___x_2534_; lean_object* v___x_2535_; 
v_name_2533_ = l_Lake_instDataKindDynlib;
v___x_2534_ = 1;
lean_inc_ref_n(v_self_2525_, 2);
v___x_2535_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_2524_, v_self_2525_, v_self_2525_, v___x_2534_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2577_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_a_2537_ = lean_ctor_get(v___x_2535_, 1);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2539_ = v___x_2535_;
v_isShared_2540_ = v_isSharedCheck_2577_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2577_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___y_2542_; lean_object* v_snd_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2575_; 
v_snd_2560_ = lean_ctor_get(v_a_2536_, 1);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_a_2536_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v_a_2536_, 0);
lean_dec(v_unused_2576_);
v___x_2562_ = v_a_2536_;
v_isShared_2563_ = v_isSharedCheck_2575_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_snd_2560_);
lean_dec(v_a_2536_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2575_;
goto v_resetjp_2561_;
}
v___jp_2541_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2543_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_2544_ = l_Lake_PartialBuildKey_toString(v_self_2525_);
v___x_2545_ = lean_string_append(v___x_2543_, v___x_2544_);
lean_dec_ref(v___x_2544_);
v___x_2546_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_2547_ = lean_string_append(v___x_2545_, v___x_2546_);
v___x_2548_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0);
v___x_2549_ = lean_string_append(v___x_2547_, v___x_2548_);
v___x_2550_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_2551_ = lean_string_append(v___x_2549_, v___x_2550_);
v___x_2552_ = lean_string_append(v___x_2551_, v___y_2542_);
lean_dec_ref(v___y_2542_);
v___x_2553_ = 3;
v___x_2554_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2554_, 0, v___x_2552_);
lean_ctor_set_uint8(v___x_2554_, sizeof(void*)*1, v___x_2553_);
v___x_2555_ = lean_array_get_size(v_a_2537_);
v___x_2556_ = lean_array_push(v_a_2537_, v___x_2554_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set_tag(v___x_2539_, 1);
lean_ctor_set(v___x_2539_, 1, v___x_2556_);
lean_ctor_set(v___x_2539_, 0, v___x_2555_);
v___x_2558_ = v___x_2539_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
v_resetjp_2561_:
{
lean_object* v_kind_2564_; uint8_t v___x_2565_; 
v_kind_2564_ = lean_ctor_get(v_snd_2560_, 1);
v___x_2565_ = lean_name_eq(v_kind_2564_, v_name_2533_);
if (v___x_2565_ == 0)
{
uint8_t v___x_2566_; 
lean_inc(v_kind_2564_);
lean_del_object(v___x_2562_);
lean_dec(v_snd_2560_);
v___x_2566_ = l_Lean_Name_isAnonymous(v_kind_2564_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2567_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_2568_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2564_, v___x_2534_);
v___x_2569_ = lean_string_append(v___x_2567_, v___x_2568_);
lean_dec_ref(v___x_2568_);
v___x_2570_ = lean_string_append(v___x_2569_, v___x_2567_);
v___y_2542_ = v___x_2570_;
goto v___jp_2541_;
}
else
{
lean_object* v___x_2571_; 
lean_dec(v_kind_2564_);
v___x_2571_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_2542_ = v___x_2571_;
goto v___jp_2541_;
}
}
else
{
lean_object* v___x_2573_; 
lean_del_object(v___x_2539_);
lean_dec_ref(v_self_2525_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 1, v_a_2537_);
lean_ctor_set(v___x_2562_, 0, v_snd_2560_);
v___x_2573_ = v___x_2562_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_snd_2560_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_a_2537_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec_ref(v_self_2525_);
v_a_2578_ = lean_ctor_get(v___x_2535_, 0);
v_a_2579_ = lean_ctor_get(v___x_2535_, 1);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2535_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_inc(v_a_2578_);
lean_dec(v___x_2535_);
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
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* v_defaultPkg_2587_, lean_object* v_self_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_2587_, v_self_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
lean_dec_ref(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec(v_a_2591_);
lean_dec(v_a_2590_);
return v_res_2596_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0));
v___x_2600_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v___x_2599_);
return v___x_2601_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5(void){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object* v___x_2603_, lean_object* v_as_2604_, size_t v_i_2605_, size_t v_stop_2606_, lean_object* v_b_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
uint8_t v___x_2615_; 
v___x_2615_ = lean_usize_dec_eq(v_i_2605_, v_stop_2606_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = lean_array_uget_borrowed(v_as_2604_, v_i_2605_);
lean_inc_ref(v___y_2608_);
lean_inc(v___x_2616_);
lean_inc_ref(v___x_2603_);
v___x_2617_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_2603_, v___x_2616_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v_a_2619_; lean_object* v___x_2620_; size_t v___x_2621_; size_t v___x_2622_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
v_a_2619_ = lean_ctor_get(v___x_2617_, 1);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2617_, 2);
v___x_2620_ = lean_array_push(v_b_2607_, v_a_2618_);
v___x_2621_ = ((size_t)1ULL);
v___x_2622_ = lean_usize_add(v_i_2605_, v___x_2621_);
v_i_2605_ = v___x_2622_;
v_b_2607_ = v___x_2620_;
v___y_2613_ = v_a_2619_;
goto _start;
}
else
{
lean_object* v_a_2624_; lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v___y_2608_);
lean_dec_ref(v_b_2607_);
lean_dec_ref(v___x_2603_);
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
lean_dec_ref(v___y_2608_);
lean_dec_ref(v___x_2603_);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v_b_2607_);
lean_ctor_set(v___x_2633_, 1, v___y_2613_);
return v___x_2633_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* v___x_2634_, lean_object* v_as_2635_, lean_object* v_i_2636_, lean_object* v_stop_2637_, lean_object* v_b_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
size_t v_i_boxed_2646_; size_t v_stop_boxed_2647_; lean_object* v_res_2648_; 
v_i_boxed_2646_ = lean_unbox_usize(v_i_2636_);
lean_dec(v_i_2636_);
v_stop_boxed_2647_ = lean_unbox_usize(v_stop_2637_);
lean_dec(v_stop_2637_);
v_res_2648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_2634_, v_as_2635_, v_i_boxed_2646_, v_stop_boxed_2647_, v_b_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v_as_2635_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object* v_self_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v_toHashSet_2651_; lean_object* v_toArray_2652_; uint8_t v___x_2653_; 
v_toHashSet_2651_ = lean_ctor_get(v_self_2649_, 0);
v_toArray_2652_ = lean_ctor_get(v_self_2649_, 1);
v___x_2653_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_2651_, v_a_2650_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2663_; 
lean_inc_ref(v_toArray_2652_);
lean_inc_ref(v_toHashSet_2651_);
v_isSharedCheck_2663_ = !lean_is_exclusive(v_self_2649_);
if (v_isSharedCheck_2663_ == 0)
{
lean_object* v_unused_2664_; lean_object* v_unused_2665_; 
v_unused_2664_ = lean_ctor_get(v_self_2649_, 1);
lean_dec(v_unused_2664_);
v_unused_2665_ = lean_ctor_get(v_self_2649_, 0);
lean_dec(v_unused_2665_);
v___x_2655_ = v_self_2649_;
v_isShared_2656_ = v_isSharedCheck_2663_;
goto v_resetjp_2654_;
}
else
{
lean_dec(v_self_2649_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2663_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2657_ = lean_box(0);
lean_inc_ref(v_a_2650_);
v___x_2658_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_toHashSet_2651_, v_a_2650_, v___x_2657_);
v___x_2659_ = lean_array_push(v_toArray_2652_, v_a_2650_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v___x_2659_);
lean_ctor_set(v___x_2655_, 0, v___x_2658_);
v___x_2661_ = v___x_2655_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
else
{
lean_dec_ref(v_a_2650_);
return v_self_2649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object* v_as_2666_, size_t v_i_2667_, size_t v_stop_2668_, lean_object* v_b_2669_){
_start:
{
uint8_t v___x_2670_; 
v___x_2670_ = lean_usize_dec_eq(v_i_2667_, v_stop_2668_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; lean_object* v___x_2672_; size_t v___x_2673_; size_t v___x_2674_; 
v___x_2671_ = lean_array_uget_borrowed(v_as_2666_, v_i_2667_);
lean_inc(v___x_2671_);
v___x_2672_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_2669_, v___x_2671_);
v___x_2673_ = ((size_t)1ULL);
v___x_2674_ = lean_usize_add(v_i_2667_, v___x_2673_);
v_i_2667_ = v___x_2674_;
v_b_2669_ = v___x_2672_;
goto _start;
}
else
{
return v_b_2669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object* v_as_2676_, lean_object* v_i_2677_, lean_object* v_stop_2678_, lean_object* v_b_2679_){
_start:
{
size_t v_i_boxed_2680_; size_t v_stop_boxed_2681_; lean_object* v_res_2682_; 
v_i_boxed_2680_ = lean_unbox_usize(v_i_2677_);
lean_dec(v_i_2677_);
v_stop_boxed_2681_ = lean_unbox_usize(v_stop_2678_);
lean_dec(v_stop_2678_);
v_res_2682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_2676_, v_i_boxed_2680_, v_stop_boxed_2681_, v_b_2679_);
lean_dec_ref(v_as_2676_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object* v_self_2683_, lean_object* v_arr_2684_){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2685_ = lean_unsigned_to_nat(0u);
v___x_2686_ = lean_array_get_size(v_arr_2684_);
v___x_2687_ = lean_nat_dec_lt(v___x_2685_, v___x_2686_);
if (v___x_2687_ == 0)
{
return v_self_2683_;
}
else
{
size_t v___x_2688_; size_t v___x_2689_; lean_object* v___x_2690_; 
v___x_2688_ = ((size_t)0ULL);
v___x_2689_ = lean_usize_of_nat(v___x_2686_);
v___x_2690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2684_, v___x_2688_, v___x_2689_, v_self_2683_);
return v___x_2690_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(lean_object* v_self_2691_, lean_object* v_arr_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_self_2691_, v_arr_2692_);
lean_dec_ref(v_arr_2692_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(lean_object* v_as_2694_, size_t v_i_2695_, size_t v_stop_2696_, lean_object* v_b_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
uint8_t v___x_2705_; 
v___x_2705_ = lean_usize_dec_eq(v_i_2695_, v_stop_2696_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; lean_object* v_lib_2707_; lean_object* v_pkg_2708_; lean_object* v_name_2709_; lean_object* v_keyName_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2706_ = lean_array_uget_borrowed(v_as_2694_, v_i_2695_);
v_lib_2707_ = lean_ctor_get(v___x_2706_, 0);
v_pkg_2708_ = lean_ctor_get(v_lib_2707_, 0);
v_name_2709_ = lean_ctor_get(v___x_2706_, 1);
v_keyName_2710_ = lean_ctor_get(v_pkg_2708_, 2);
v___x_2711_ = l_Lake_Module_transImportsFacet;
lean_inc(v_name_2709_);
lean_inc(v_keyName_2710_);
v___x_2712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2712_, 0, v_keyName_2710_);
lean_ctor_set(v___x_2712_, 1, v_name_2709_);
v___x_2713_ = l_Lake_Module_keyword;
lean_inc(v___x_2706_);
v___x_2714_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2712_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
lean_ctor_set(v___x_2714_, 2, v___x_2706_);
lean_ctor_set(v___x_2714_, 3, v___x_2711_);
lean_inc_ref(v___y_2698_);
lean_inc_ref(v___y_2702_);
lean_inc(v___y_2701_);
lean_inc(v___y_2700_);
lean_inc(v___y_2699_);
v___x_2715_ = lean_apply_7(v___y_2698_, v___x_2714_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, lean_box(0));
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v_a_2717_; lean_object* v___x_2718_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
v_a_2717_ = lean_ctor_get(v___x_2715_, 1);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2715_, 2);
v___x_2718_ = l_Lake_Job_await___redArg(v_a_2716_, v_a_2717_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v_a_2719_; lean_object* v_a_2720_; lean_object* v___x_2721_; size_t v___x_2722_; size_t v___x_2723_; 
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2719_);
v_a_2720_ = lean_ctor_get(v___x_2718_, 1);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2718_, 2);
v___x_2721_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_b_2697_, v_a_2719_);
lean_dec(v_a_2719_);
v___x_2722_ = ((size_t)1ULL);
v___x_2723_ = lean_usize_add(v_i_2695_, v___x_2722_);
v_i_2695_ = v___x_2723_;
v_b_2697_ = v___x_2721_;
v___y_2703_ = v_a_2720_;
goto _start;
}
else
{
lean_object* v_a_2725_; lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec_ref(v___y_2698_);
lean_dec_ref(v_b_2697_);
v_a_2725_ = lean_ctor_get(v___x_2718_, 0);
v_a_2726_ = lean_ctor_get(v___x_2718_, 1);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2718_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_inc(v_a_2725_);
lean_dec(v___x_2718_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2725_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec_ref(v___y_2698_);
lean_dec_ref(v_b_2697_);
v_a_2734_ = lean_ctor_get(v___x_2715_, 0);
v_a_2735_ = lean_ctor_get(v___x_2715_, 1);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2715_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_inc(v_a_2734_);
lean_dec(v___x_2715_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2734_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
else
{
lean_object* v___x_2743_; 
lean_dec_ref(v___y_2698_);
v___x_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2743_, 0, v_b_2697_);
lean_ctor_set(v___x_2743_, 1, v___y_2703_);
return v___x_2743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object* v_as_2744_, lean_object* v_i_2745_, lean_object* v_stop_2746_, lean_object* v_b_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
size_t v_i_boxed_2755_; size_t v_stop_boxed_2756_; lean_object* v_res_2757_; 
v_i_boxed_2755_ = lean_unbox_usize(v_i_2745_);
lean_dec(v_i_2745_);
v_stop_boxed_2756_ = lean_unbox_usize(v_stop_2746_);
lean_dec(v_stop_2746_);
v_res_2757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_as_2744_, v_i_boxed_2755_, v_stop_boxed_2756_, v_b_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v_as_2744_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(lean_object* v_as_2758_, size_t v_i_2759_, size_t v_stop_2760_, lean_object* v_b_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
uint8_t v___x_2769_; 
v___x_2769_ = lean_usize_dec_eq(v_i_2759_, v_stop_2760_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v_pkg_2771_; lean_object* v_name_2772_; lean_object* v_keyName_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2770_ = lean_array_uget_borrowed(v_as_2758_, v_i_2759_);
v_pkg_2771_ = lean_ctor_get(v___x_2770_, 0);
v_name_2772_ = lean_ctor_get(v___x_2770_, 1);
v_keyName_2773_ = lean_ctor_get(v_pkg_2771_, 2);
v___x_2774_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_2772_);
lean_inc(v_keyName_2773_);
v___x_2775_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2775_, 0, v_keyName_2773_);
lean_ctor_set(v___x_2775_, 1, v_name_2772_);
v___x_2776_ = l_Lake_ExternLib_keyword;
lean_inc(v___x_2770_);
v___x_2777_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
lean_ctor_set(v___x_2777_, 2, v___x_2770_);
lean_ctor_set(v___x_2777_, 3, v___x_2774_);
lean_inc_ref(v___y_2762_);
lean_inc_ref(v___y_2766_);
lean_inc(v___y_2765_);
lean_inc(v___y_2764_);
lean_inc(v___y_2763_);
v___x_2778_ = lean_apply_7(v___y_2762_, v___x_2777_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, lean_box(0));
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v_a_2780_; lean_object* v___x_2781_; size_t v___x_2782_; size_t v___x_2783_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
v_a_2780_ = lean_ctor_get(v___x_2778_, 1);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2778_, 2);
v___x_2781_ = lean_array_push(v_b_2761_, v_a_2779_);
v___x_2782_ = ((size_t)1ULL);
v___x_2783_ = lean_usize_add(v_i_2759_, v___x_2782_);
v_i_2759_ = v___x_2783_;
v_b_2761_ = v___x_2781_;
v___y_2767_ = v_a_2780_;
goto _start;
}
else
{
lean_object* v_a_2785_; lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec_ref(v___y_2762_);
lean_dec_ref(v_b_2761_);
v_a_2785_ = lean_ctor_get(v___x_2778_, 0);
v_a_2786_ = lean_ctor_get(v___x_2778_, 1);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2778_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_inc(v_a_2785_);
lean_dec(v___x_2778_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2785_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
else
{
lean_object* v___x_2794_; 
lean_dec_ref(v___y_2762_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v_b_2761_);
lean_ctor_set(v___x_2794_, 1, v___y_2767_);
return v___x_2794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(lean_object* v_as_2795_, lean_object* v_i_2796_, lean_object* v_stop_2797_, lean_object* v_b_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
size_t v_i_boxed_2806_; size_t v_stop_boxed_2807_; lean_object* v_res_2808_; 
v_i_boxed_2806_ = lean_unbox_usize(v_i_2796_);
lean_dec(v_i_2796_);
v_stop_boxed_2807_ = lean_unbox_usize(v_stop_2797_);
lean_dec(v_stop_2797_);
v_res_2808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v_as_2795_, v_i_boxed_2806_, v_stop_boxed_2807_, v_b_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v_as_2795_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(lean_object* v_as_2809_, size_t v_i_2810_, size_t v_stop_2811_, lean_object* v_b_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v_a_2821_; lean_object* v_a_2822_; uint8_t v___x_2826_; 
v___x_2826_ = lean_usize_dec_eq(v_i_2810_, v_stop_2811_);
if (v___x_2826_ == 0)
{
lean_object* v_fst_2827_; lean_object* v_snd_2828_; lean_object* v___x_2829_; lean_object* v_lib_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2867_; 
v_fst_2827_ = lean_ctor_get(v_b_2812_, 0);
v_snd_2828_ = lean_ctor_get(v_b_2812_, 1);
v___x_2829_ = lean_array_uget(v_as_2809_, v_i_2810_);
v_lib_2830_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2867_ == 0)
{
lean_object* v_unused_2868_; 
v_unused_2868_ = lean_ctor_get(v___x_2829_, 1);
lean_dec(v_unused_2868_);
v___x_2832_ = v___x_2829_;
v_isShared_2833_ = v_isSharedCheck_2867_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_lib_2830_);
lean_dec(v___x_2829_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2867_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v_pkg_2834_; lean_object* v_name_2835_; uint8_t v___x_2836_; 
v_pkg_2834_ = lean_ctor_get(v_lib_2830_, 0);
v_name_2835_ = lean_ctor_get(v_lib_2830_, 1);
lean_inc(v_name_2835_);
v___x_2836_ = l_Lean_NameSet_contains(v_fst_2827_, v_name_2835_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2864_; 
lean_inc(v_snd_2828_);
lean_inc(v_fst_2827_);
v_isSharedCheck_2864_ = !lean_is_exclusive(v_b_2812_);
if (v_isSharedCheck_2864_ == 0)
{
lean_object* v_unused_2865_; lean_object* v_unused_2866_; 
v_unused_2865_ = lean_ctor_get(v_b_2812_, 1);
lean_dec(v_unused_2865_);
v_unused_2866_ = lean_ctor_get(v_b_2812_, 0);
lean_dec(v_unused_2866_);
v___x_2838_ = v_b_2812_;
v_isShared_2839_ = v_isSharedCheck_2864_;
goto v_resetjp_2837_;
}
else
{
lean_dec(v_b_2812_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2864_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v_keyName_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
v_keyName_2840_ = lean_ctor_get(v_pkg_2834_, 2);
v___x_2841_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_2835_);
lean_inc(v_keyName_2840_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set_tag(v___x_2832_, 3);
lean_ctor_set(v___x_2832_, 1, v_name_2835_);
lean_ctor_set(v___x_2832_, 0, v_keyName_2840_);
v___x_2843_ = v___x_2832_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_keyName_2840_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_name_2835_);
v___x_2843_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2844_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2845_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2843_);
lean_ctor_set(v___x_2845_, 1, v___x_2844_);
lean_ctor_set(v___x_2845_, 2, v_lib_2830_);
lean_ctor_set(v___x_2845_, 3, v___x_2841_);
lean_inc_ref(v___y_2813_);
lean_inc_ref(v___y_2817_);
lean_inc(v___y_2816_);
lean_inc(v___y_2815_);
lean_inc(v___y_2814_);
v___x_2846_ = lean_apply_7(v___y_2813_, v___x_2845_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, lean_box(0));
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v_a_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2852_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
v_a_2848_ = lean_ctor_get(v___x_2846_, 1);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2846_, 2);
v___x_2849_ = lean_array_push(v_snd_2828_, v_a_2847_);
v___x_2850_ = l_Lean_NameSet_insert(v_fst_2827_, v_name_2835_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 1, v___x_2849_);
lean_ctor_set(v___x_2838_, 0, v___x_2850_);
v___x_2852_ = v___x_2838_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v___x_2849_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
v_a_2821_ = v___x_2852_;
v_a_2822_ = v_a_2848_;
goto v___jp_2820_;
}
}
else
{
lean_object* v_a_2854_; lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_del_object(v___x_2838_);
lean_dec(v_name_2835_);
lean_dec(v_snd_2828_);
lean_dec(v_fst_2827_);
lean_dec_ref(v___y_2813_);
v_a_2854_ = lean_ctor_get(v___x_2846_, 0);
v_a_2855_ = lean_ctor_get(v___x_2846_, 1);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2846_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_inc(v_a_2854_);
lean_dec(v___x_2846_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2854_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
}
}
else
{
lean_dec(v_name_2835_);
lean_del_object(v___x_2832_);
lean_dec_ref(v_lib_2830_);
v_a_2821_ = v_b_2812_;
v_a_2822_ = v___y_2818_;
goto v___jp_2820_;
}
}
}
else
{
lean_object* v___x_2869_; 
lean_dec_ref(v___y_2813_);
v___x_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2869_, 0, v_b_2812_);
lean_ctor_set(v___x_2869_, 1, v___y_2818_);
return v___x_2869_;
}
v___jp_2820_:
{
size_t v___x_2823_; size_t v___x_2824_; 
v___x_2823_ = ((size_t)1ULL);
v___x_2824_ = lean_usize_add(v_i_2810_, v___x_2823_);
v_i_2810_ = v___x_2824_;
v_b_2812_ = v_a_2821_;
v___y_2818_ = v_a_2822_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object* v_as_2870_, lean_object* v_i_2871_, lean_object* v_stop_2872_, lean_object* v_b_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
size_t v_i_boxed_2881_; size_t v_stop_boxed_2882_; lean_object* v_res_2883_; 
v_i_boxed_2881_ = lean_unbox_usize(v_i_2871_);
lean_dec(v_i_2871_);
v_stop_boxed_2882_ = lean_unbox_usize(v_stop_2872_);
lean_dec(v_stop_2872_);
v_res_2883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_as_2870_, v_i_boxed_2881_, v_stop_boxed_2882_, v_b_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v_as_2870_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(lean_object* v___x_2884_, lean_object* v_as_2885_, size_t v_i_2886_, size_t v_stop_2887_, lean_object* v_b_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_){
_start:
{
uint8_t v___x_2896_; 
v___x_2896_ = lean_usize_dec_eq(v_i_2886_, v_stop_2887_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = lean_array_uget_borrowed(v_as_2885_, v_i_2886_);
lean_inc_ref(v___y_2889_);
lean_inc(v___x_2897_);
lean_inc_ref(v___x_2884_);
v___x_2898_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v___x_2884_, v___x_2897_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v_a_2900_; lean_object* v___x_2901_; size_t v___x_2902_; size_t v___x_2903_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
v_a_2900_ = lean_ctor_get(v___x_2898_, 1);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2898_, 2);
v___x_2901_ = lean_array_push(v_b_2888_, v_a_2899_);
v___x_2902_ = ((size_t)1ULL);
v___x_2903_ = lean_usize_add(v_i_2886_, v___x_2902_);
v_i_2886_ = v___x_2903_;
v_b_2888_ = v___x_2901_;
v___y_2894_ = v_a_2900_;
goto _start;
}
else
{
lean_object* v_a_2905_; lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec_ref(v___y_2889_);
lean_dec_ref(v_b_2888_);
lean_dec_ref(v___x_2884_);
v_a_2905_ = lean_ctor_get(v___x_2898_, 0);
v_a_2906_ = lean_ctor_get(v___x_2898_, 1);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2898_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_inc(v_a_2905_);
lean_dec(v___x_2898_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2905_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v___x_2914_; 
lean_dec_ref(v___y_2889_);
lean_dec_ref(v___x_2884_);
v___x_2914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2914_, 0, v_b_2888_);
lean_ctor_set(v___x_2914_, 1, v___y_2894_);
return v___x_2914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object* v___x_2915_, lean_object* v_as_2916_, lean_object* v_i_2917_, lean_object* v_stop_2918_, lean_object* v_b_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
size_t v_i_boxed_2927_; size_t v_stop_boxed_2928_; lean_object* v_res_2929_; 
v_i_boxed_2927_ = lean_unbox_usize(v_i_2917_);
lean_dec(v_i_2917_);
v_stop_boxed_2928_ = lean_unbox_usize(v_stop_2918_);
lean_dec(v_stop_2918_);
v_res_2929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v___x_2915_, v_as_2916_, v_i_boxed_2927_, v_stop_boxed_2928_, v_b_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec(v___y_2921_);
lean_dec_ref(v_as_2916_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(lean_object* v___x_2930_, lean_object* v_as_2931_, size_t v_i_2932_, size_t v_stop_2933_, lean_object* v_b_2934_){
_start:
{
lean_object* v___y_2936_; uint8_t v___x_2940_; 
v___x_2940_ = lean_usize_dec_eq(v_i_2932_, v_stop_2933_);
if (v___x_2940_ == 0)
{
lean_object* v_toConfigDecl_2941_; lean_object* v_name_2942_; lean_object* v_kind_2943_; lean_object* v_config_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v_toConfigDecl_2941_ = lean_array_uget_borrowed(v_as_2931_, v_i_2932_);
v_name_2942_ = lean_ctor_get(v_toConfigDecl_2941_, 1);
v_kind_2943_ = lean_ctor_get(v_toConfigDecl_2941_, 2);
v_config_2944_ = lean_ctor_get(v_toConfigDecl_2941_, 3);
v___x_2945_ = l_Lake_ExternLib_keyword;
v___x_2946_ = lean_name_eq(v_kind_2943_, v___x_2945_);
if (v___x_2946_ == 0)
{
v___y_2936_ = v_b_2934_;
goto v___jp_2935_;
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
lean_inc(v_config_2944_);
lean_inc(v_name_2942_);
lean_inc_ref(v___x_2930_);
v___x_2947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2930_);
lean_ctor_set(v___x_2947_, 1, v_name_2942_);
lean_ctor_set(v___x_2947_, 2, v_config_2944_);
v___x_2948_ = lean_array_push(v_b_2934_, v___x_2947_);
v___y_2936_ = v___x_2948_;
goto v___jp_2935_;
}
}
else
{
lean_dec_ref(v___x_2930_);
return v_b_2934_;
}
v___jp_2935_:
{
size_t v___x_2937_; size_t v___x_2938_; 
v___x_2937_ = ((size_t)1ULL);
v___x_2938_ = lean_usize_add(v_i_2932_, v___x_2937_);
v_i_2932_ = v___x_2938_;
v_b_2934_ = v___y_2936_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(lean_object* v___x_2949_, lean_object* v_as_2950_, lean_object* v_i_2951_, lean_object* v_stop_2952_, lean_object* v_b_2953_){
_start:
{
size_t v_i_boxed_2954_; size_t v_stop_boxed_2955_; lean_object* v_res_2956_; 
v_i_boxed_2954_ = lean_unbox_usize(v_i_2951_);
lean_dec(v_i_2951_);
v_stop_boxed_2955_ = lean_unbox_usize(v_stop_2952_);
lean_dec(v_stop_2952_);
v_res_2956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v___x_2949_, v_as_2950_, v_i_boxed_2954_, v_stop_boxed_2955_, v_b_2953_);
lean_dec_ref(v_as_2950_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(lean_object* v_as_2957_, size_t v_i_2958_, size_t v_stop_2959_, lean_object* v_b_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
uint8_t v___x_2968_; 
v___x_2968_ = lean_usize_dec_eq(v_i_2958_, v_stop_2959_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; lean_object* v_lib_2970_; lean_object* v_config_2971_; lean_object* v_nativeFacets_2972_; uint8_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; size_t v_sz_2976_; size_t v___x_2977_; lean_object* v___x_2978_; 
v___x_2969_ = lean_array_uget_borrowed(v_as_2957_, v_i_2958_);
v_lib_2970_ = lean_ctor_get(v___x_2969_, 0);
v_config_2971_ = lean_ctor_get(v_lib_2970_, 2);
v_nativeFacets_2972_ = lean_ctor_get(v_config_2971_, 8);
v___x_2973_ = 1;
v___x_2974_ = lean_box(v___x_2973_);
lean_inc_ref(v_nativeFacets_2972_);
v___x_2975_ = lean_apply_1(v_nativeFacets_2972_, v___x_2974_);
v_sz_2976_ = lean_array_size(v___x_2975_);
v___x_2977_ = ((size_t)0ULL);
lean_inc_ref(v___y_2961_);
lean_inc(v___x_2969_);
v___x_2978_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2969_, v_sz_2976_, v___x_2977_, v___x_2975_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v_a_2980_; lean_object* v___x_2981_; size_t v___x_2982_; size_t v___x_2983_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
v_a_2980_ = lean_ctor_get(v___x_2978_, 1);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2978_, 2);
v___x_2981_ = l_Array_append___redArg(v_b_2960_, v_a_2979_);
lean_dec(v_a_2979_);
v___x_2982_ = ((size_t)1ULL);
v___x_2983_ = lean_usize_add(v_i_2958_, v___x_2982_);
v_i_2958_ = v___x_2983_;
v_b_2960_ = v___x_2981_;
v___y_2966_ = v_a_2980_;
goto _start;
}
else
{
lean_dec_ref(v___y_2961_);
lean_dec_ref(v_b_2960_);
return v___x_2978_;
}
}
else
{
lean_object* v___x_2985_; 
lean_dec_ref(v___y_2961_);
v___x_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2985_, 0, v_b_2960_);
lean_ctor_set(v___x_2985_, 1, v___y_2966_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object* v_as_2986_, lean_object* v_i_2987_, lean_object* v_stop_2988_, lean_object* v_b_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
size_t v_i_boxed_2997_; size_t v_stop_boxed_2998_; lean_object* v_res_2999_; 
v_i_boxed_2997_ = lean_unbox_usize(v_i_2987_);
lean_dec(v_i_2987_);
v_stop_boxed_2998_ = lean_unbox_usize(v_stop_2988_);
lean_dec(v_stop_2988_);
v_res_2999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_as_2986_, v_i_boxed_2997_, v_stop_boxed_2998_, v_b_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v_as_2986_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(lean_object* v_self_3000_, lean_object* v_dir_3001_, lean_object* v___x_3002_, lean_object* v_targetDecls_3003_, lean_object* v_pkg_3004_, lean_object* v_name_3005_, lean_object* v___x_3006_, lean_object* v_config_3007_, lean_object* v_config_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v_a_3017_; lean_object* v_a_3018_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v_a_3028_; lean_object* v_a_3029_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v_a_3089_; lean_object* v_a_3090_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v_snd_3122_; lean_object* v_a_3123_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v_a_3145_; lean_object* v_a_3146_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___x_3185_; 
lean_inc_ref(v___y_3009_);
lean_inc_ref(v___y_3013_);
lean_inc(v___y_3012_);
lean_inc(v___y_3011_);
lean_inc(v___x_3002_);
v___x_3185_ = lean_apply_7(v___y_3009_, v___x_3006_, v___x_3002_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, lean_box(0));
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v_a_3187_; lean_object* v___x_3188_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
v_a_3187_ = lean_ctor_get(v___x_3185_, 1);
lean_inc(v_a_3187_);
lean_dec_ref_known(v___x_3185_, 2);
v___x_3188_ = l_Lake_Job_await___redArg(v_a_3186_, v_a_3187_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v_a_3190_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v_a_3201_; lean_object* v_a_3202_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v_a_3236_; lean_object* v_a_3237_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
v_a_3190_ = lean_ctor_get(v___x_3188_, 1);
lean_inc(v_a_3190_);
lean_dec_ref_known(v___x_3188_, 2);
v___x_3261_ = lean_unsigned_to_nat(0u);
v___x_3262_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_3263_ = lean_array_get_size(v_a_3189_);
v___x_3264_ = lean_nat_dec_lt(v___x_3261_, v___x_3263_);
if (v___x_3264_ == 0)
{
v_a_3236_ = v___x_3262_;
v_a_3237_ = v_a_3190_;
goto v___jp_3235_;
}
else
{
size_t v___x_3265_; size_t v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = ((size_t)0ULL);
v___x_3266_ = lean_usize_of_nat(v___x_3263_);
lean_inc_ref(v___y_3009_);
v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3189_, v___x_3265_, v___x_3266_, v___x_3262_, v___y_3009_, v___x_3002_, v___y_3011_, v___y_3012_, v___y_3013_, v_a_3190_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3268_; lean_object* v_a_3269_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3268_);
v_a_3269_ = lean_ctor_get(v___x_3267_, 1);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3267_, 2);
v_a_3236_ = v_a_3268_;
v_a_3237_ = v_a_3269_;
goto v___jp_3235_;
}
else
{
lean_object* v_a_3270_; lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec(v_a_3189_);
lean_dec_ref(v___y_3009_);
lean_dec_ref(v_config_3007_);
lean_dec(v_name_3005_);
lean_dec_ref(v_pkg_3004_);
lean_dec(v___x_3002_);
lean_dec_ref(v_dir_3001_);
lean_dec_ref(v_self_3000_);
v_a_3270_ = lean_ctor_get(v___x_3267_, 0);
v_a_3271_ = lean_ctor_get(v___x_3267_, 1);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3267_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_inc(v_a_3270_);
lean_dec(v___x_3267_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3270_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
v___jp_3191_:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; uint8_t v___x_3205_; 
v___x_3203_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
v___x_3204_ = lean_array_get_size(v_a_3189_);
v___x_3205_ = lean_nat_dec_lt(v___y_3199_, v___x_3204_);
if (v___x_3205_ == 0)
{
lean_dec(v_a_3189_);
v___y_3135_ = v___y_3192_;
v___y_3136_ = v___y_3193_;
v___y_3137_ = v___y_3194_;
v___y_3138_ = v_a_3201_;
v___y_3139_ = v___y_3195_;
v___y_3140_ = v___y_3196_;
v___y_3141_ = v___y_3197_;
v___y_3142_ = v___y_3198_;
v___y_3143_ = v___y_3199_;
v___y_3144_ = v___y_3200_;
v_a_3145_ = v___x_3203_;
v_a_3146_ = v_a_3202_;
goto v___jp_3134_;
}
else
{
uint8_t v___x_3206_; 
v___x_3206_ = lean_nat_dec_le(v___x_3204_, v___x_3204_);
if (v___x_3206_ == 0)
{
if (v___x_3205_ == 0)
{
lean_dec(v_a_3189_);
v___y_3135_ = v___y_3192_;
v___y_3136_ = v___y_3193_;
v___y_3137_ = v___y_3194_;
v___y_3138_ = v_a_3201_;
v___y_3139_ = v___y_3195_;
v___y_3140_ = v___y_3196_;
v___y_3141_ = v___y_3197_;
v___y_3142_ = v___y_3198_;
v___y_3143_ = v___y_3199_;
v___y_3144_ = v___y_3200_;
v_a_3145_ = v___x_3203_;
v_a_3146_ = v_a_3202_;
goto v___jp_3134_;
}
else
{
size_t v___x_3207_; size_t v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = ((size_t)0ULL);
v___x_3208_ = lean_usize_of_nat(v___x_3204_);
lean_inc_ref(v___y_3009_);
v___x_3209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3189_, v___x_3207_, v___x_3208_, v___x_3203_, v___y_3009_, v___x_3002_, v___y_3011_, v___y_3012_, v___y_3013_, v_a_3202_);
lean_dec(v_a_3189_);
v___y_3170_ = v___y_3192_;
v___y_3171_ = v___y_3194_;
v___y_3172_ = v___y_3193_;
v___y_3173_ = v_a_3201_;
v___y_3174_ = v___y_3196_;
v___y_3175_ = v___y_3195_;
v___y_3176_ = v___y_3199_;
v___y_3177_ = v___y_3198_;
v___y_3178_ = v___y_3197_;
v___y_3179_ = v___y_3200_;
v___y_3180_ = v___x_3209_;
goto v___jp_3169_;
}
}
else
{
size_t v___x_3210_; size_t v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = ((size_t)0ULL);
v___x_3211_ = lean_usize_of_nat(v___x_3204_);
lean_inc_ref(v___y_3009_);
v___x_3212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3189_, v___x_3210_, v___x_3211_, v___x_3203_, v___y_3009_, v___x_3002_, v___y_3011_, v___y_3012_, v___y_3013_, v_a_3202_);
lean_dec(v_a_3189_);
v___y_3170_ = v___y_3192_;
v___y_3171_ = v___y_3194_;
v___y_3172_ = v___y_3193_;
v___y_3173_ = v_a_3201_;
v___y_3174_ = v___y_3196_;
v___y_3175_ = v___y_3195_;
v___y_3176_ = v___y_3199_;
v___y_3177_ = v___y_3198_;
v___y_3178_ = v___y_3197_;
v___y_3179_ = v___y_3200_;
v___y_3180_ = v___x_3212_;
goto v___jp_3169_;
}
}
}
v___jp_3213_:
{
if (lean_obj_tag(v___y_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v_a_3225_; 
v_a_3224_ = lean_ctor_get(v___y_3223_, 0);
lean_inc(v_a_3224_);
v_a_3225_ = lean_ctor_get(v___y_3223_, 1);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___y_3223_, 2);
v___y_3192_ = v___y_3214_;
v___y_3193_ = v___y_3216_;
v___y_3194_ = v___y_3215_;
v___y_3195_ = v___y_3218_;
v___y_3196_ = v___y_3217_;
v___y_3197_ = v___y_3221_;
v___y_3198_ = v___y_3220_;
v___y_3199_ = v___y_3219_;
v___y_3200_ = v___y_3222_;
v_a_3201_ = v_a_3224_;
v_a_3202_ = v_a_3225_;
goto v___jp_3191_;
}
else
{
lean_object* v_a_3226_; lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec_ref(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec_ref(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec_ref(v___y_3214_);
lean_dec(v_a_3189_);
lean_dec_ref(v___y_3009_);
lean_dec(v_name_3005_);
lean_dec_ref(v_pkg_3004_);
lean_dec(v___x_3002_);
lean_dec_ref(v_dir_3001_);
lean_dec_ref(v_self_3000_);
v_a_3226_ = lean_ctor_get(v___y_3223_, 0);
v_a_3227_ = lean_ctor_get(v___y_3223_, 1);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___y_3223_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___y_3223_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_inc(v_a_3226_);
lean_dec(v___y_3223_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3226_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
v___jp_3235_:
{
lean_object* v_toLeanConfig_3238_; lean_object* v_toLeanConfig_3239_; lean_object* v_buildDir_3240_; lean_object* v_nativeLibDir_3241_; lean_object* v_moreLinkObjs_3242_; lean_object* v_moreLinkLibs_3243_; lean_object* v_moreLinkArgs_3244_; lean_object* v_weakLinkArgs_3245_; lean_object* v_moreLinkObjs_3246_; lean_object* v_moreLinkLibs_3247_; lean_object* v_moreLinkArgs_3248_; lean_object* v_weakLinkArgs_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; uint8_t v___x_3253_; 
v_toLeanConfig_3238_ = lean_ctor_get(v_config_3007_, 1);
lean_inc_ref(v_toLeanConfig_3238_);
v_toLeanConfig_3239_ = lean_ctor_get(v_config_3008_, 0);
v_buildDir_3240_ = lean_ctor_get(v_config_3007_, 5);
lean_inc_ref(v_buildDir_3240_);
v_nativeLibDir_3241_ = lean_ctor_get(v_config_3007_, 7);
lean_inc_ref(v_nativeLibDir_3241_);
lean_dec_ref(v_config_3007_);
v_moreLinkObjs_3242_ = lean_ctor_get(v_toLeanConfig_3238_, 6);
lean_inc_ref(v_moreLinkObjs_3242_);
v_moreLinkLibs_3243_ = lean_ctor_get(v_toLeanConfig_3238_, 7);
lean_inc_ref(v_moreLinkLibs_3243_);
v_moreLinkArgs_3244_ = lean_ctor_get(v_toLeanConfig_3238_, 8);
lean_inc_ref(v_moreLinkArgs_3244_);
v_weakLinkArgs_3245_ = lean_ctor_get(v_toLeanConfig_3238_, 9);
lean_inc_ref(v_weakLinkArgs_3245_);
lean_dec_ref(v_toLeanConfig_3238_);
v_moreLinkObjs_3246_ = lean_ctor_get(v_toLeanConfig_3239_, 6);
v_moreLinkLibs_3247_ = lean_ctor_get(v_toLeanConfig_3239_, 7);
v_moreLinkArgs_3248_ = lean_ctor_get(v_toLeanConfig_3239_, 8);
v_weakLinkArgs_3249_ = lean_ctor_get(v_toLeanConfig_3239_, 9);
v___x_3250_ = l_Array_append___redArg(v_moreLinkObjs_3242_, v_moreLinkObjs_3246_);
v___x_3251_ = lean_unsigned_to_nat(0u);
v___x_3252_ = lean_array_get_size(v___x_3250_);
v___x_3253_ = lean_nat_dec_lt(v___x_3251_, v___x_3252_);
if (v___x_3253_ == 0)
{
lean_dec_ref(v___x_3250_);
v___y_3192_ = v_nativeLibDir_3241_;
v___y_3193_ = v_moreLinkLibs_3247_;
v___y_3194_ = v_moreLinkArgs_3248_;
v___y_3195_ = v_moreLinkLibs_3243_;
v___y_3196_ = v_weakLinkArgs_3245_;
v___y_3197_ = v_moreLinkArgs_3244_;
v___y_3198_ = v_buildDir_3240_;
v___y_3199_ = v___x_3251_;
v___y_3200_ = v_weakLinkArgs_3249_;
v_a_3201_ = v_a_3236_;
v_a_3202_ = v_a_3237_;
goto v___jp_3191_;
}
else
{
uint8_t v___x_3254_; 
v___x_3254_ = lean_nat_dec_le(v___x_3252_, v___x_3252_);
if (v___x_3254_ == 0)
{
if (v___x_3253_ == 0)
{
lean_dec_ref(v___x_3250_);
v___y_3192_ = v_nativeLibDir_3241_;
v___y_3193_ = v_moreLinkLibs_3247_;
v___y_3194_ = v_moreLinkArgs_3248_;
v___y_3195_ = v_moreLinkLibs_3243_;
v___y_3196_ = v_weakLinkArgs_3245_;
v___y_3197_ = v_moreLinkArgs_3244_;
v___y_3198_ = v_buildDir_3240_;
v___y_3199_ = v___x_3251_;
v___y_3200_ = v_weakLinkArgs_3249_;
v_a_3201_ = v_a_3236_;
v_a_3202_ = v_a_3237_;
goto v___jp_3191_;
}
else
{
size_t v___x_3255_; size_t v___x_3256_; lean_object* v___x_3257_; 
v___x_3255_ = ((size_t)0ULL);
v___x_3256_ = lean_usize_of_nat(v___x_3252_);
lean_inc_ref(v___y_3009_);
lean_inc_ref(v_pkg_3004_);
v___x_3257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_3004_, v___x_3250_, v___x_3255_, v___x_3256_, v_a_3236_, v___y_3009_, v___x_3002_, v___y_3011_, v___y_3012_, v___y_3013_, v_a_3237_);
lean_dec_ref(v___x_3250_);
v___y_3214_ = v_nativeLibDir_3241_;
v___y_3215_ = v_moreLinkArgs_3248_;
v___y_3216_ = v_moreLinkLibs_3247_;
v___y_3217_ = v_weakLinkArgs_3245_;
v___y_3218_ = v_moreLinkLibs_3243_;
v___y_3219_ = v___x_3251_;
v___y_3220_ = v_buildDir_3240_;
v___y_3221_ = v_moreLinkArgs_3244_;
v___y_3222_ = v_weakLinkArgs_3249_;
v___y_3223_ = v___x_3257_;
goto v___jp_3213_;
}
}
else
{
size_t v___x_3258_; size_t v___x_3259_; lean_object* v___x_3260_; 
v___x_3258_ = ((size_t)0ULL);
v___x_3259_ = lean_usize_of_nat(v___x_3252_);
lean_inc_ref(v___y_3009_);
lean_inc_ref(v_pkg_3004_);
v___x_3260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_3004_, v___x_3250_, v___x_3258_, v___x_3259_, v_a_3236_, v___y_3009_, v___x_3002_, v___y_3011_, v___y_3012_, v___y_3013_, v_a_3237_);
lean_dec_ref(v___x_3250_);
v___y_3214_ = v_nativeLibDir_3241_;
v___y_3215_ = v_moreLinkArgs_3248_;
v___y_3216_ = v_moreLinkLibs_3247_;
v___y_3217_ = v_weakLinkArgs_3245_;
v___y_3218_ = v_moreLinkLibs_3243_;
v___y_3219_ = v___x_3251_;
v___y_3220_ = v_buildDir_3240_;
v___y_3221_ = v_moreLinkArgs_3244_;
v___y_3222_ = v_weakLinkArgs_3249_;
v___y_3223_ = v___x_3260_;
goto v___jp_3213_;
}
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec_ref(v___y_3009_);
lean_dec_ref(v_config_3007_);
lean_dec(v_name_3005_);
lean_dec_ref(v_pkg_3004_);
lean_dec(v___x_3002_);
lean_dec_ref(v_dir_3001_);
lean_dec_ref(v_self_3000_);
v_a_3279_ = lean_ctor_get(v___x_3188_, 0);
v_a_3280_ = lean_ctor_get(v___x_3188_, 1);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3188_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_inc(v_a_3279_);
lean_dec(v___x_3188_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3279_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_dec_ref(v___y_3009_);
lean_dec_ref(v_config_3007_);
lean_dec(v_name_3005_);
lean_dec_ref(v_pkg_3004_);
lean_dec(v___x_3002_);
lean_dec_ref(v_dir_3001_);
lean_dec_ref(v_self_3000_);
v_a_3288_ = lean_ctor_get(v___x_3185_, 0);
v_a_3289_ = lean_ctor_get(v___x_3185_, 1);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3185_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_inc(v_a_3288_);
lean_dec(v___x_3185_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3288_);
lean_ctor_set(v_reuseFailAlloc_3295_, 1, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
v___jp_3016_:
{
lean_object* v___x_3019_; 
v___x_3019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3019_, 0, v_a_3017_);
lean_ctor_set(v___x_3019_, 1, v_a_3018_);
return v___x_3019_;
}
v___jp_3020_:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; uint8_t v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
lean_inc_ref(v_self_3000_);
v___x_3030_ = l_Lake_LeanLib_libName(v_self_3000_);
v___x_3031_ = l_System_FilePath_normalize(v___y_3026_);
v___x_3032_ = l_Lake_joinRelative(v_dir_3001_, v___x_3031_);
v___x_3033_ = l_System_FilePath_normalize(v___y_3021_);
v___x_3034_ = l_Lake_joinRelative(v___x_3032_, v___x_3033_);
v___x_3035_ = 0;
v___x_3036_ = l_Lake_nameToSharedLib(v___x_3030_, v___x_3035_);
v___x_3037_ = l_Lake_joinRelative(v___x_3034_, v___x_3036_);
v___x_3038_ = l_Array_append___redArg(v___y_3024_, v___y_3027_);
v___x_3039_ = l_Array_append___redArg(v___y_3025_, v___y_3022_);
v___x_3040_ = l_Lake_LeanLib_isPlugin(v_self_3000_);
v___x_3041_ = l_System_Platform_isWindows;
v___x_3042_ = lean_box(0);
v___x_3043_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_3044_ = l_Lake_buildLeanSharedLib(v___x_3030_, v___x_3037_, v___y_3023_, v_a_3028_, v___x_3038_, v___x_3039_, v___x_3040_, v___x_3041_, v___x_3042_, v___y_3009_, v___x_3002_, v___y_3011_, v___y_3012_, v___y_3013_, v___x_3043_);
lean_dec(v___x_3002_);
lean_dec_ref(v___y_3023_);
v___x_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set(v___x_3045_, 1, v_a_3029_);
return v___x_3045_;
}
v___jp_3046_:
{
if (lean_obj_tag(v___y_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v_a_3056_; 
v_a_3055_ = lean_ctor_get(v___y_3054_, 0);
lean_inc(v_a_3055_);
v_a_3056_ = lean_ctor_get(v___y_3054_, 1);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___y_3054_, 2);
v___y_3021_ = v___y_3047_;
v___y_3022_ = v___y_3048_;
v___y_3023_ = v___y_3049_;
v___y_3024_ = v___y_3050_;
v___y_3025_ = v___y_3052_;
v___y_3026_ = v___y_3051_;
v___y_3027_ = v___y_3053_;
v_a_3028_ = v_a_3055_;
v_a_3029_ = v_a_3056_;
goto v___jp_3020_;
}
else
{
lean_object* v_a_3057_; lean_object* v_a_3058_; 
lean_dec_ref(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec_ref(v___y_3047_);
lean_dec_ref(v___y_3009_);
lean_dec(v___x_3002_);
lean_dec_ref(v_dir_3001_);
lean_dec_ref(v_self_3000_);
v_a_3057_ = lean_ctor_get(v___y_3054_, 0);
lean_inc(v_a_3057_);
v_a_3058_ = lean_ctor_get(v___y_3054_, 1);
lean_inc(v_a_3058_);
lean_dec_ref_known(v___y_3054_, 2);
v_a_3017_ = v_a_3057_;
v_a_3018_ = v_a_3058_;
goto v___jp_3016_;
}
}
v___jp_3059_:
{
lean_object* v___x_3071_; uint8_t v___x_3072_; 
v___x_3071_ = lean_array_get_size(v___y_3070_);
v___x_3072_ = lean_nat_dec_lt(v___y_3066_, v___x_3071_);
if (v___x_3072_ == 0)
{
lean_dec_ref(v___y_3070_);
v___y_3021_ = v___y_3060_;
v___y_3022_ = v___y_3061_;
v___y_3023_ = v___y_3062_;
v___y_3024_ = v___y_3065_;
v___y_3025_ = v___y_3068_;
v___y_3026_ = v___y_3067_;
v___y_3027_ = v___y_3069_;
v_a_3028_ = v___y_3064_;
v_a_3029_ = v___y_3063_;
goto v___jp_3020_;
}
else
{
uint8_t v___x_3073_; 
v___x_3073_ = lean_nat_dec_le(v___x_3071_, v___x_3071_);
if (v___x_3073_ == 0)
{
if (v___x_3072_ == 0)
{
lean_dec_ref(v___y_3070_);
v___y_3021_ = v___y_3060_;
v___y_3022_ = v___y_3061_;
v___y_3023_ = v___y_3062_;
v___y_3024_ = v___y_3065_;
v___y_3025_ = v___y_3068_;
v___y_3026_ = v___y_3067_;
v___y_3027_ = v___y_3069_;
v_a_3028_ = v___y_3064_;
v_a_3029_ = v___y_3063_;
goto v___jp_3020_;
}
else
{
size_t v___x_3074_; size_t v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = ((size_t)0ULL);
v___x_3075_ = lean_usize_of_nat(v___x_3071_);
lean_inc_ref(v___y_3009_);
v___x_3076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_3070_, v___x_3074_, v___x_3075_, v___y_3064_, v___y_3009_, v___x_3002_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3063_);
lean_dec_ref(v___y_3070_);
v___y_3047_ = v___y_3060_;
v___y_3048_ = v___y_3061_;
v___y_3049_ = v___y_3062_;
v___y_3050_ = v___y_3065_;
v___y_3051_ = v___y_3067_;
v___y_3052_ = v___y_3068_;
v___y_3053_ = v___y_3069_;
v___y_3054_ = v___x_3076_;
goto v___jp_3046_;
}
}
else
{
size_t v___x_3077_; size_t v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = ((size_t)0ULL);
v___x_3078_ = lean_usize_of_nat(v___x_3071_);
lean_inc_ref(v___y_3009_);
v___x_3079_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_3070_, v___x_3077_, v___x_3078_, v___y_3064_, v___y_3009_, v___x_3002_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3063_);
lean_dec_ref(v___y_3070_);
v___y_3047_ = v___y_3060_;
v___y_3048_ = v___y_3061_;
v___y_3049_ = v___y_3062_;
v___y_3050_ = v___y_3065_;
v___y_3051_ = v___y_3067_;
v___y_3052_ = v___y_3068_;
v___y_3053_ = v___y_3069_;
v___y_3054_ = v___x_3079_;
goto v___jp_3046_;
}
}
}
v___jp_3080_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3091_ = lean_mk_empty_array_with_capacity(v___y_3087_);
v___x_3092_ = lean_array_get_size(v_targetDecls_3003_);
v___x_3093_ = lean_nat_dec_lt(v___y_3087_, v___x_3092_);
if (v___x_3093_ == 0)
{
lean_dec_ref(v_pkg_3004_);
v___y_3060_ = v___y_3081_;
v___y_3061_ = v___y_3082_;
v___y_3062_ = v___y_3083_;
v___y_3063_ = v_a_3090_;
v___y_3064_ = v_a_3089_;
v___y_3065_ = v___y_3084_;
v___y_3066_ = v___y_3087_;
v___y_3067_ = v___y_3086_;
v___y_3068_ = v___y_3085_;
v___y_3069_ = v___y_3088_;
v___y_3070_ = v___x_3091_;
goto v___jp_3059_;
}
else
{
size_t v___x_3094_; size_t v___x_3095_; lean_object* v___x_3096_; 
v___x_3094_ = ((size_t)0ULL);
v___x_3095_ = lean_usize_of_nat(v___x_3092_);
v___x_3096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_3004_, v_targetDecls_3003_, v___x_3094_, v___x_3095_, v___x_3091_);
v___y_3060_ = v___y_3081_;
v___y_3061_ = v___y_3082_;
v___y_3062_ = v___y_3083_;
v___y_3063_ = v_a_3090_;
v___y_3064_ = v_a_3089_;
v___y_3065_ = v___y_3084_;
v___y_3066_ = v___y_3087_;
v___y_3067_ = v___y_3086_;
v___y_3068_ = v___y_3085_;
v___y_3069_ = v___y_3088_;
v___y_3070_ = v___x_3096_;
goto v___jp_3059_;
}
}
v___jp_3097_:
{
if (lean_obj_tag(v___y_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v_a_3108_; 
v_a_3107_ = lean_ctor_get(v___y_3106_, 0);
lean_inc(v_a_3107_);
v_a_3108_ = lean_ctor_get(v___y_3106_, 1);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___y_3106_, 2);
v___y_3081_ = v___y_3098_;
v___y_3082_ = v___y_3099_;
v___y_3083_ = v___y_3100_;
v___y_3084_ = v___y_3101_;
v___y_3085_ = v___y_3104_;
v___y_3086_ = v___y_3103_;
v___y_3087_ = v___y_3102_;
v___y_3088_ = v___y_3105_;
v_a_3089_ = v_a_3107_;
v_a_3090_ = v_a_3108_;
goto v___jp_3080_;
}
else
{
lean_object* v_a_3109_; lean_object* v_a_3110_; 
lean_dec_ref(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec_ref(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec_ref(v___y_3098_);
lean_dec_ref(v___y_3009_);
lean_dec_ref(v_pkg_3004_);
lean_dec(v___x_3002_);
lean_dec_ref(v_dir_3001_);
lean_dec_ref(v_self_3000_);
v_a_3109_ = lean_ctor_get(v___y_3106_, 0);
lean_inc(v_a_3109_);
v_a_3110_ = lean_ctor_get(v___y_3106_, 1);
lean_inc(v_a_3110_);
lean_dec_ref_known(v___y_3106_, 2);
v_a_3017_ = v_a_3109_;
v_a_3018_ = v_a_3110_;
goto v___jp_3016_;
}
}
v___jp_3111_:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; uint8_t v___x_3126_; 
v___x_3124_ = l_Array_append___redArg(v___y_3117_, v___y_3114_);
v___x_3125_ = lean_array_get_size(v___x_3124_);
v___x_3126_ = lean_nat_dec_lt(v___y_3118_, v___x_3125_);
if (v___x_3126_ == 0)
{
lean_dec_ref(v___x_3124_);
v___y_3081_ = v___y_3112_;
v___y_3082_ = v___y_3113_;
v___y_3083_ = v___y_3115_;
v___y_3084_ = v___y_3116_;
v___y_3085_ = v___y_3120_;
v___y_3086_ = v___y_3119_;
v___y_3087_ = v___y_3118_;
v___y_3088_ = v___y_3121_;
v_a_3089_ = v_snd_3122_;
v_a_3090_ = v_a_3123_;
goto v___jp_3080_;
}
else
{
uint8_t v___x_3127_; 
v___x_3127_ = lean_nat_dec_le(v___x_3125_, v___x_3125_);
if (v___x_3127_ == 0)
{
if (v___x_3126_ == 0)
{
lean_dec_ref(v___x_3124_);
v___y_3081_ = v___y_3112_;
v___y_3082_ = v___y_3113_;
v___y_3083_ = v___y_3115_;
v___y_3084_ = v___y_3116_;
v___y_3085_ = v___y_3120_;
v___y_3086_ = v___y_3119_;
v___y_3087_ = v___y_3118_;
v___y_3088_ = v___y_3121_;
v_a_3089_ = v_snd_3122_;
v_a_3090_ = v_a_3123_;
goto v___jp_3080_;
}
else
{
size_t v___x_3128_; size_t v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = ((size_t)0ULL);
v___x_3129_ = lean_usize_of_nat(v___x_3125_);
lean_inc_ref(v___y_3009_);
lean_inc_ref(v_pkg_3004_);
v___x_3130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_3004_, v___x_3124_, v___x_3128_, v___x_3129_, v_snd_3122_, v___y_3009_, v___x_3002_, v___y_3011_, v___y_3012_, v___y_3013_, v_a_3123_);
lean_dec_ref(v___x_3124_);
v___y_3098_ = v___y_3112_;
v___y_3099_ = v___y_3113_;
v___y_3100_ = v___y_3115_;
v___y_3101_ = v___y_3116_;
v___y_3102_ = v___y_3118_;
v___y_3103_ = v___y_3119_;
v___y_3104_ = v___y_3120_;
v___y_3105_ = v___y_3121_;
v___y_3106_ = v___x_3130_;
goto v___jp_3097_;
}
}
else
{
size_t v___x_3131_; size_t v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = ((size_t)0ULL);
v___x_3132_ = lean_usize_of_nat(v___x_3125_);
lean_inc_ref(v___y_3009_);
lean_inc_ref(v_pkg_3004_);
v___x_3133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_3004_, v___x_3124_, v___x_3131_, v___x_3132_, v_snd_3122_, v___y_3009_, v___x_3002_, v___y_3011_, v___y_3012_, v___y_3013_, v_a_3123_);
lean_dec_ref(v___x_3124_);
v___y_3098_ = v___y_3112_;
v___y_3099_ = v___y_3113_;
v___y_3100_ = v___y_3115_;
v___y_3101_ = v___y_3116_;
v___y_3102_ = v___y_3118_;
v___y_3103_ = v___y_3119_;
v___y_3104_ = v___y_3120_;
v___y_3105_ = v___y_3121_;
v___y_3106_ = v___x_3133_;
goto v___jp_3097_;
}
}
}
v___jp_3134_:
{
lean_object* v_toArray_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3167_; 
v_toArray_3147_ = lean_ctor_get(v_a_3145_, 1);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_a_3145_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; 
v_unused_3168_ = lean_ctor_get(v_a_3145_, 0);
lean_dec(v_unused_3168_);
v___x_3149_ = v_a_3145_;
v_isShared_3150_ = v_isSharedCheck_3167_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_toArray_3147_);
lean_dec(v_a_3145_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3167_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3151_ = lean_mk_empty_array_with_capacity(v___y_3143_);
v___x_3152_ = lean_array_get_size(v_toArray_3147_);
v___x_3153_ = lean_nat_dec_lt(v___y_3143_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_del_object(v___x_3149_);
lean_dec_ref(v_toArray_3147_);
lean_dec(v_name_3005_);
v___y_3112_ = v___y_3135_;
v___y_3113_ = v___y_3137_;
v___y_3114_ = v___y_3136_;
v___y_3115_ = v___y_3138_;
v___y_3116_ = v___y_3140_;
v___y_3117_ = v___y_3139_;
v___y_3118_ = v___y_3143_;
v___y_3119_ = v___y_3142_;
v___y_3120_ = v___y_3141_;
v___y_3121_ = v___y_3144_;
v_snd_3122_ = v___x_3151_;
v_a_3123_ = v_a_3146_;
goto v___jp_3111_;
}
else
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3154_ = l_Lean_NameSet_empty;
v___x_3155_ = l_Lean_NameSet_insert(v___x_3154_, v_name_3005_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 1, v___x_3151_);
lean_ctor_set(v___x_3149_, 0, v___x_3155_);
v___x_3157_ = v___x_3149_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v___x_3155_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v___x_3151_);
v___x_3157_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
size_t v___x_3158_; size_t v___x_3159_; lean_object* v___x_3160_; 
v___x_3158_ = ((size_t)0ULL);
v___x_3159_ = lean_usize_of_nat(v___x_3152_);
lean_inc_ref(v___y_3009_);
v___x_3160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_3147_, v___x_3158_, v___x_3159_, v___x_3157_, v___y_3009_, v___x_3002_, v___y_3011_, v___y_3012_, v___y_3013_, v_a_3146_);
lean_dec_ref(v_toArray_3147_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v_a_3162_; lean_object* v_snd_3163_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
v_a_3162_ = lean_ctor_get(v___x_3160_, 1);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3160_, 2);
v_snd_3163_ = lean_ctor_get(v_a_3161_, 1);
lean_inc(v_snd_3163_);
lean_dec(v_a_3161_);
v___y_3112_ = v___y_3135_;
v___y_3113_ = v___y_3137_;
v___y_3114_ = v___y_3136_;
v___y_3115_ = v___y_3138_;
v___y_3116_ = v___y_3140_;
v___y_3117_ = v___y_3139_;
v___y_3118_ = v___y_3143_;
v___y_3119_ = v___y_3142_;
v___y_3120_ = v___y_3141_;
v___y_3121_ = v___y_3144_;
v_snd_3122_ = v_snd_3163_;
v_a_3123_ = v_a_3162_;
goto v___jp_3111_;
}
else
{
lean_object* v_a_3164_; lean_object* v_a_3165_; 
lean_dec_ref(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec_ref(v___y_3135_);
lean_dec_ref(v___y_3009_);
lean_dec_ref(v_pkg_3004_);
lean_dec(v___x_3002_);
lean_dec_ref(v_dir_3001_);
lean_dec_ref(v_self_3000_);
v_a_3164_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3164_);
v_a_3165_ = lean_ctor_get(v___x_3160_, 1);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3160_, 2);
v_a_3017_ = v_a_3164_;
v_a_3018_ = v_a_3165_;
goto v___jp_3016_;
}
}
}
}
}
v___jp_3169_:
{
if (lean_obj_tag(v___y_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v_a_3182_; 
v_a_3181_ = lean_ctor_get(v___y_3180_, 0);
lean_inc(v_a_3181_);
v_a_3182_ = lean_ctor_get(v___y_3180_, 1);
lean_inc(v_a_3182_);
lean_dec_ref_known(v___y_3180_, 2);
v___y_3135_ = v___y_3170_;
v___y_3136_ = v___y_3172_;
v___y_3137_ = v___y_3171_;
v___y_3138_ = v___y_3173_;
v___y_3139_ = v___y_3175_;
v___y_3140_ = v___y_3174_;
v___y_3141_ = v___y_3178_;
v___y_3142_ = v___y_3177_;
v___y_3143_ = v___y_3176_;
v___y_3144_ = v___y_3179_;
v_a_3145_ = v_a_3181_;
v_a_3146_ = v_a_3182_;
goto v___jp_3134_;
}
else
{
lean_object* v_a_3183_; lean_object* v_a_3184_; 
lean_dec_ref(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec_ref(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v___y_3170_);
lean_dec_ref(v___y_3009_);
lean_dec(v_name_3005_);
lean_dec_ref(v_pkg_3004_);
lean_dec(v___x_3002_);
lean_dec_ref(v_dir_3001_);
lean_dec_ref(v_self_3000_);
v_a_3183_ = lean_ctor_get(v___y_3180_, 0);
lean_inc(v_a_3183_);
v_a_3184_ = lean_ctor_get(v___y_3180_, 1);
lean_inc(v_a_3184_);
lean_dec_ref_known(v___y_3180_, 2);
v_a_3017_ = v_a_3183_;
v_a_3018_ = v_a_3184_;
goto v___jp_3016_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* v_self_3297_, lean_object* v_dir_3298_, lean_object* v___x_3299_, lean_object* v_targetDecls_3300_, lean_object* v_pkg_3301_, lean_object* v_name_3302_, lean_object* v___x_3303_, lean_object* v_config_3304_, lean_object* v_config_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v_self_3297_, v_dir_3298_, v___x_3299_, v_targetDecls_3300_, v_pkg_3301_, v_name_3302_, v___x_3303_, v_config_3304_, v_config_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec(v_config_3305_);
lean_dec_ref(v_targetDecls_3300_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object* v_self_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_pkg_3323_; lean_object* v_name_3324_; lean_object* v_config_3325_; lean_object* v_keyName_3326_; lean_object* v_dir_3327_; lean_object* v_config_3328_; lean_object* v_targetDecls_3329_; lean_object* v___x_3330_; uint8_t v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___f_3340_; uint8_t v___x_3341_; lean_object* v___x_3342_; 
v_pkg_3323_ = lean_ctor_get(v_self_3315_, 0);
lean_inc_ref_n(v_pkg_3323_, 2);
v_name_3324_ = lean_ctor_get(v_self_3315_, 1);
lean_inc_n(v_name_3324_, 3);
v_config_3325_ = lean_ctor_get(v_self_3315_, 2);
lean_inc(v_config_3325_);
v_keyName_3326_ = lean_ctor_get(v_pkg_3323_, 2);
v_dir_3327_ = lean_ctor_get(v_pkg_3323_, 4);
lean_inc_ref(v_dir_3327_);
v_config_3328_ = lean_ctor_get(v_pkg_3323_, 6);
lean_inc_ref(v_config_3328_);
v_targetDecls_3329_ = lean_ctor_get(v_pkg_3323_, 15);
lean_inc_ref(v_targetDecls_3329_);
v___x_3330_ = l_Lake_instDataKindDynlib;
v___x_3331_ = 1;
v___x_3332_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3324_, v___x_3331_);
v___x_3333_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0));
v___x_3334_ = lean_string_append(v___x_3332_, v___x_3333_);
v___x_3335_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_3326_);
v___x_3336_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3336_, 0, v_keyName_3326_);
lean_ctor_set(v___x_3336_, 1, v_name_3324_);
v___x_3337_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3315_);
v___x_3338_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3336_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
lean_ctor_set(v___x_3338_, 2, v_self_3315_);
lean_ctor_set(v___x_3338_, 3, v___x_3335_);
v___x_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3339_, 0, v_pkg_3323_);
v___f_3340_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3340_, 0, v_self_3315_);
lean_closure_set(v___f_3340_, 1, v_dir_3327_);
lean_closure_set(v___f_3340_, 2, v___x_3339_);
lean_closure_set(v___f_3340_, 3, v_targetDecls_3329_);
lean_closure_set(v___f_3340_, 4, v_pkg_3323_);
lean_closure_set(v___f_3340_, 5, v_name_3324_);
lean_closure_set(v___f_3340_, 6, v___x_3338_);
lean_closure_set(v___f_3340_, 7, v_config_3328_);
lean_closure_set(v___f_3340_, 8, v_config_3325_);
v___x_3341_ = 0;
v___x_3342_ = l_Lake_ensureJob___redArg(v___x_3330_, v___f_3340_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3367_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_a_3344_ = lean_ctor_get(v___x_3342_, 1);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3346_ = v___x_3342_;
v_isShared_3347_ = v_isSharedCheck_3367_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3367_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v_task_3348_; lean_object* v_kind_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3365_; 
v_task_3348_ = lean_ctor_get(v_a_3343_, 0);
v_kind_3349_ = lean_ctor_get(v_a_3343_, 1);
v_isSharedCheck_3365_ = !lean_is_exclusive(v_a_3343_);
if (v_isSharedCheck_3365_ == 0)
{
lean_object* v_unused_3366_; 
v_unused_3366_ = lean_ctor_get(v_a_3343_, 2);
lean_dec(v_unused_3366_);
v___x_3351_ = v_a_3343_;
v_isShared_3352_ = v_isSharedCheck_3365_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_kind_3349_);
lean_inc(v_task_3348_);
lean_dec(v_a_3343_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3365_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v_registeredJobs_3353_; lean_object* v_job_3355_; 
v_registeredJobs_3353_ = lean_ctor_get(v_a_3320_, 4);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 2, v___x_3334_);
v_job_3355_ = v___x_3351_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_task_3348_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_kind_3349_);
lean_ctor_set(v_reuseFailAlloc_3364_, 2, v___x_3334_);
v_job_3355_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3362_; 
lean_ctor_set_uint8(v_job_3355_, sizeof(void*)*3, v___x_3341_);
v___x_3356_ = lean_st_ref_take(v_registeredJobs_3353_);
lean_inc_ref(v_job_3355_);
v___x_3357_ = l_Lake_Job_toOpaque___redArg(v_job_3355_);
v___x_3358_ = lean_array_push(v___x_3356_, v___x_3357_);
v___x_3359_ = lean_st_ref_put(v_registeredJobs_3353_, v___x_3358_);
v___x_3360_ = l_Lake_Job_renew___redArg(v_job_3355_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3360_);
v___x_3362_ = v___x_3346_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_a_3344_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3334_);
return v___x_3342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object* v_self_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
lean_dec_ref(v_a_3373_);
lean_dec(v_a_3372_);
lean_dec(v_a_3371_);
lean_dec(v_a_3370_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t v_fmt_3377_, lean_object* v_a_3378_){
_start:
{
if (v_fmt_3377_ == 0)
{
lean_object* v_path_3379_; 
v_path_3379_ = lean_ctor_get(v_a_3378_, 0);
lean_inc_ref(v_path_3379_);
return v_path_3379_;
}
else
{
lean_object* v_path_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_path_3380_ = lean_ctor_get(v_a_3378_, 0);
lean_inc_ref(v_path_3380_);
v___x_3381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3381_, 0, v_path_3380_);
v___x_3382_ = l_Lean_Json_compress(v___x_3381_);
return v___x_3382_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* v_fmt_3383_, lean_object* v_a_3384_){
_start:
{
uint8_t v_fmt_boxed_3385_; lean_object* v_res_3386_; 
v_fmt_boxed_3385_ = lean_unbox(v_fmt_3383_);
v_res_3386_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_boxed_3385_, v_a_3384_);
lean_dec_ref(v_a_3384_);
return v_res_3386_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3389_; uint8_t v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___f_3389_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__0));
v___x_3390_ = 1;
v___x_3391_ = l_Lake_instDataKindDynlib;
v___x_3392_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__1));
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
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = lean_obj_once(&l_Lake_LeanLib_sharedFacetConfig___closed__2, &l_Lake_LeanLib_sharedFacetConfig___closed__2_once, _init_l_Lake_LeanLib_sharedFacetConfig___closed__2);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* v___x_3396_, lean_object* v_as_3397_, size_t v_sz_3398_, size_t v_i_3399_, lean_object* v_b_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
uint8_t v___x_3408_; 
v___x_3408_ = lean_usize_dec_lt(v_i_3399_, v_sz_3398_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; 
lean_dec_ref(v___y_3401_);
lean_dec_ref(v___x_3396_);
v___x_3409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3409_, 0, v_b_3400_);
lean_ctor_set(v___x_3409_, 1, v___y_3406_);
return v___x_3409_;
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3411_; 
v_a_3410_ = lean_array_uget_borrowed(v_as_3397_, v_i_3399_);
lean_inc_ref(v___y_3401_);
lean_inc_n(v_a_3410_, 2);
lean_inc_ref(v___x_3396_);
v___x_3411_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v___x_3396_, v_a_3410_, v_a_3410_, v___x_3408_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; lean_object* v_a_3413_; lean_object* v_snd_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; size_t v___x_3417_; size_t v___x_3418_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
v_a_3413_ = lean_ctor_get(v___x_3411_, 1);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___x_3411_, 2);
v_snd_3414_ = lean_ctor_get(v_a_3412_, 1);
lean_inc(v_snd_3414_);
lean_dec(v_a_3412_);
v___x_3415_ = l_Lake_Job_toOpaque___redArg(v_snd_3414_);
v___x_3416_ = l_Lake_Job_mix___redArg(v_b_3400_, v___x_3415_);
v___x_3417_ = ((size_t)1ULL);
v___x_3418_ = lean_usize_add(v_i_3399_, v___x_3417_);
v_i_3399_ = v___x_3418_;
v_b_3400_ = v___x_3416_;
v___y_3406_ = v_a_3413_;
goto _start;
}
else
{
lean_object* v_a_3420_; lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec_ref(v___y_3401_);
lean_dec_ref(v_b_3400_);
lean_dec_ref(v___x_3396_);
v_a_3420_ = lean_ctor_get(v___x_3411_, 0);
v_a_3421_ = lean_ctor_get(v___x_3411_, 1);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3411_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_inc(v_a_3420_);
lean_dec(v___x_3411_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3420_);
lean_ctor_set(v_reuseFailAlloc_3427_, 1, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* v___x_3429_, lean_object* v_as_3430_, lean_object* v_sz_3431_, lean_object* v_i_3432_, lean_object* v_b_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
size_t v_sz_boxed_3441_; size_t v_i_boxed_3442_; lean_object* v_res_3443_; 
v_sz_boxed_3441_ = lean_unbox_usize(v_sz_3431_);
lean_dec(v_sz_3431_);
v_i_boxed_3442_ = lean_unbox_usize(v_i_3432_);
lean_dec(v_i_3432_);
v_res_3443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_3429_, v_as_3430_, v_sz_boxed_3441_, v_i_boxed_3442_, v_b_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
lean_dec_ref(v___y_3438_);
lean_dec(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v_as_3430_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* v___x_3444_, lean_object* v_as_3445_, size_t v_sz_3446_, size_t v_i_3447_, lean_object* v_b_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
uint8_t v___x_3456_; 
v___x_3456_ = lean_usize_dec_lt(v_i_3447_, v_sz_3446_);
if (v___x_3456_ == 0)
{
lean_object* v___x_3457_; 
lean_dec_ref(v___y_3449_);
lean_dec_ref(v___x_3444_);
v___x_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3457_, 0, v_b_3448_);
lean_ctor_set(v___x_3457_, 1, v___y_3454_);
return v___x_3457_;
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3459_; 
v_a_3458_ = lean_array_uget_borrowed(v_as_3445_, v_i_3447_);
lean_inc_ref(v___y_3449_);
lean_inc(v_a_3458_);
lean_inc_ref(v___x_3444_);
v___x_3459_ = l_Lake_Package_fetchTargetJob(v___x_3444_, v_a_3458_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v_a_3461_; lean_object* v___x_3462_; size_t v___x_3463_; size_t v___x_3464_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
v_a_3461_ = lean_ctor_get(v___x_3459_, 1);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3459_, 2);
v___x_3462_ = l_Lake_Job_mix___redArg(v_b_3448_, v_a_3460_);
v___x_3463_ = ((size_t)1ULL);
v___x_3464_ = lean_usize_add(v_i_3447_, v___x_3463_);
v_i_3447_ = v___x_3464_;
v_b_3448_ = v___x_3462_;
v___y_3454_ = v_a_3461_;
goto _start;
}
else
{
lean_object* v_a_3466_; lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
lean_dec_ref(v___y_3449_);
lean_dec_ref(v_b_3448_);
lean_dec_ref(v___x_3444_);
v_a_3466_ = lean_ctor_get(v___x_3459_, 0);
v_a_3467_ = lean_ctor_get(v___x_3459_, 1);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3459_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_inc(v_a_3466_);
lean_dec(v___x_3459_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3466_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* v___x_3475_, lean_object* v_as_3476_, lean_object* v_sz_3477_, lean_object* v_i_3478_, lean_object* v_b_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
size_t v_sz_boxed_3487_; size_t v_i_boxed_3488_; lean_object* v_res_3489_; 
v_sz_boxed_3487_ = lean_unbox_usize(v_sz_3477_);
lean_dec(v_sz_3477_);
v_i_boxed_3488_ = lean_unbox_usize(v_i_3478_);
lean_dec(v_i_3478_);
v_res_3489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_3475_, v_as_3476_, v_sz_boxed_3487_, v_i_boxed_3488_, v_b_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v_as_3476_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object* v_self_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_){
_start:
{
lean_object* v_pkg_3500_; lean_object* v_name_3501_; lean_object* v_config_3502_; lean_object* v_baseName_3503_; lean_object* v_keyName_3504_; uint8_t v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; uint8_t v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v_job_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v_pkg_3500_ = lean_ctor_get(v_self_3492_, 0);
lean_inc_ref_n(v_pkg_3500_, 2);
v_name_3501_ = lean_ctor_get(v_self_3492_, 1);
lean_inc(v_name_3501_);
v_config_3502_ = lean_ctor_get(v_self_3492_, 2);
lean_inc(v_config_3502_);
lean_dec_ref(v_self_3492_);
v_baseName_3503_ = lean_ctor_get(v_pkg_3500_, 1);
v_keyName_3504_ = lean_ctor_get(v_pkg_3500_, 2);
v___x_3505_ = 1;
lean_inc(v_baseName_3503_);
v___x_3506_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3503_, v___x_3505_);
v___x_3507_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0));
v___x_3508_ = lean_string_append(v___x_3506_, v___x_3507_);
v___x_3509_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3501_, v___x_3505_);
v___x_3510_ = lean_string_append(v___x_3508_, v___x_3509_);
lean_dec_ref(v___x_3509_);
v___x_3511_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1));
v___x_3512_ = lean_string_append(v___x_3510_, v___x_3511_);
v___x_3513_ = lean_box(0);
v___x_3514_ = lean_box(0);
v___x_3515_ = lean_unsigned_to_nat(0u);
v___x_3516_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__0));
v___x_3517_ = 0;
v___x_3518_ = 0;
v___x_3519_ = l_Lake_BuildTrace_nil(v___x_3512_);
v___x_3520_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3520_, 0, v___x_3516_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
lean_ctor_set(v___x_3520_, 2, v___x_3515_);
lean_ctor_set_uint8(v___x_3520_, sizeof(void*)*3, v___x_3517_);
lean_ctor_set_uint8(v___x_3520_, sizeof(void*)*3 + 1, v___x_3518_);
lean_ctor_set_uint8(v___x_3520_, sizeof(void*)*3 + 2, v___x_3518_);
v___x_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3513_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = lean_task_pure(v___x_3521_);
v___x_3523_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v_job_3524_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_3524_, 0, v___x_3522_);
lean_ctor_set(v_job_3524_, 1, v___x_3514_);
lean_ctor_set(v_job_3524_, 2, v___x_3523_);
lean_ctor_set_uint8(v_job_3524_, sizeof(void*)*3, v___x_3518_);
v___x_3525_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_3504_);
v___x_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3526_, 0, v_keyName_3504_);
v___x_3527_ = l_Lake_Package_keyword;
v___x_3528_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3526_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
lean_ctor_set(v___x_3528_, 2, v_pkg_3500_);
lean_ctor_set(v___x_3528_, 3, v___x_3525_);
lean_inc_ref(v_a_3493_);
lean_inc_ref(v_a_3497_);
lean_inc(v_a_3496_);
lean_inc(v_a_3495_);
lean_inc(v_a_3494_);
v___x_3529_ = lean_apply_7(v_a_3493_, v___x_3528_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, lean_box(0));
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v_a_3531_; lean_object* v_needs_3532_; lean_object* v_extraDepTargets_3533_; lean_object* v___x_3534_; size_t v_sz_3535_; size_t v___x_3536_; lean_object* v___x_3537_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
v_a_3531_ = lean_ctor_get(v___x_3529_, 1);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3529_, 2);
v_needs_3532_ = lean_ctor_get(v_config_3502_, 5);
lean_inc_ref(v_needs_3532_);
v_extraDepTargets_3533_ = lean_ctor_get(v_config_3502_, 6);
lean_inc_ref(v_extraDepTargets_3533_);
lean_dec(v_config_3502_);
v___x_3534_ = l_Lake_Job_mix___redArg(v_job_3524_, v_a_3530_);
v_sz_3535_ = lean_array_size(v_extraDepTargets_3533_);
v___x_3536_ = ((size_t)0ULL);
lean_inc_ref(v_a_3493_);
lean_inc_ref(v_pkg_3500_);
v___x_3537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_3500_, v_extraDepTargets_3533_, v_sz_3535_, v___x_3536_, v___x_3534_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3531_);
lean_dec_ref(v_extraDepTargets_3533_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; lean_object* v_a_3539_; size_t v_sz_3540_; lean_object* v___x_3541_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3538_);
v_a_3539_ = lean_ctor_get(v___x_3537_, 1);
lean_inc(v_a_3539_);
lean_dec_ref_known(v___x_3537_, 2);
v_sz_3540_ = lean_array_size(v_needs_3532_);
v___x_3541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_3500_, v_needs_3532_, v_sz_3540_, v___x_3536_, v_a_3538_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3539_);
lean_dec_ref(v_needs_3532_);
return v___x_3541_;
}
else
{
lean_dec_ref(v_needs_3532_);
lean_dec_ref(v_pkg_3500_);
lean_dec_ref(v_a_3493_);
return v___x_3537_;
}
}
else
{
lean_dec_ref_known(v_job_3524_, 3);
lean_dec(v_config_3502_);
lean_dec_ref(v_pkg_3500_);
lean_dec_ref(v_a_3493_);
return v___x_3529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object* v_self_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_);
lean_dec_ref(v_a_3547_);
lean_dec(v_a_3546_);
lean_dec(v_a_3545_);
lean_dec(v_a_3544_);
return v_res_3550_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3552_; uint8_t v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___f_3552_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_3553_ = 1;
v___x_3554_ = l_Lake_instDataKindUnit;
v___x_3555_ = ((lean_object*)(l_Lake_LeanLib_extraDepFacetConfig___closed__0));
v___x_3556_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3557_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
lean_ctor_set(v___x_3557_, 1, v___x_3555_);
lean_ctor_set(v___x_3557_, 2, v___x_3554_);
lean_ctor_set(v___x_3557_, 3, v___f_3552_);
lean_ctor_set_uint8(v___x_3557_, sizeof(void*)*4, v___x_3553_);
lean_ctor_set_uint8(v___x_3557_, sizeof(void*)*4 + 1, v___x_3553_);
return v___x_3557_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = lean_obj_once(&l_Lake_LeanLib_extraDepFacetConfig___closed__1, &l_Lake_LeanLib_extraDepFacetConfig___closed__1_once, _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* v_self_3559_, size_t v_sz_3560_, size_t v_i_3561_, lean_object* v_bs_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
uint8_t v___x_3570_; 
v___x_3570_ = lean_usize_dec_lt(v_i_3561_, v_sz_3560_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; 
lean_dec_ref(v___y_3563_);
lean_dec_ref(v_self_3559_);
v___x_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3571_, 0, v_bs_3562_);
lean_ctor_set(v___x_3571_, 1, v___y_3568_);
return v___x_3571_;
}
else
{
lean_object* v_pkg_3572_; lean_object* v_name_3573_; lean_object* v_keyName_3574_; lean_object* v_v_3575_; lean_object* v___x_3576_; lean_object* v_bs_x27_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v_pkg_3572_ = lean_ctor_get(v_self_3559_, 0);
v_name_3573_ = lean_ctor_get(v_self_3559_, 1);
v_keyName_3574_ = lean_ctor_get(v_pkg_3572_, 2);
v_v_3575_ = lean_array_uget(v_bs_3562_, v_i_3561_);
v___x_3576_ = lean_unsigned_to_nat(0u);
v_bs_x27_3577_ = lean_array_uset(v_bs_3562_, v_i_3561_, v___x_3576_);
lean_inc(v_name_3573_);
lean_inc(v_keyName_3574_);
v___x_3578_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3578_, 0, v_keyName_3574_);
lean_ctor_set(v___x_3578_, 1, v_name_3573_);
v___x_3579_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3559_);
v___x_3580_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3578_);
lean_ctor_set(v___x_3580_, 1, v___x_3579_);
lean_ctor_set(v___x_3580_, 2, v_self_3559_);
lean_ctor_set(v___x_3580_, 3, v_v_3575_);
lean_inc_ref(v___y_3563_);
lean_inc_ref(v___y_3567_);
lean_inc(v___y_3566_);
lean_inc(v___y_3565_);
lean_inc(v___y_3564_);
v___x_3581_ = lean_apply_7(v___y_3563_, v___x_3580_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, lean_box(0));
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v_a_3583_; lean_object* v___x_3584_; size_t v___x_3585_; size_t v___x_3586_; lean_object* v___x_3587_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
v_a_3583_ = lean_ctor_get(v___x_3581_, 1);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3581_, 2);
v___x_3584_ = l_Lake_Job_toOpaque___redArg(v_a_3582_);
v___x_3585_ = ((size_t)1ULL);
v___x_3586_ = lean_usize_add(v_i_3561_, v___x_3585_);
v___x_3587_ = lean_array_uset(v_bs_x27_3577_, v_i_3561_, v___x_3584_);
v_i_3561_ = v___x_3586_;
v_bs_3562_ = v___x_3587_;
v___y_3568_ = v_a_3583_;
goto _start;
}
else
{
lean_object* v_a_3589_; lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec_ref(v_bs_x27_3577_);
lean_dec_ref(v___y_3563_);
lean_dec_ref(v_self_3559_);
v_a_3589_ = lean_ctor_get(v___x_3581_, 0);
v_a_3590_ = lean_ctor_get(v___x_3581_, 1);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3581_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_inc(v_a_3589_);
lean_dec(v___x_3581_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3589_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* v_self_3598_, lean_object* v_sz_3599_, lean_object* v_i_3600_, lean_object* v_bs_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
size_t v_sz_boxed_3609_; size_t v_i_boxed_3610_; lean_object* v_res_3611_; 
v_sz_boxed_3609_ = lean_unbox_usize(v_sz_3599_);
lean_dec(v_sz_3599_);
v_i_boxed_3610_ = lean_unbox_usize(v_i_3600_);
lean_dec(v_i_3600_);
v_res_3611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3598_, v_sz_boxed_3609_, v_i_boxed_3610_, v_bs_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec(v___y_3603_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object* v_self_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_){
_start:
{
lean_object* v_config_3621_; lean_object* v_defaultFacets_3622_; size_t v_sz_3623_; size_t v___x_3624_; lean_object* v___x_3625_; 
v_config_3621_ = lean_ctor_get(v_self_3613_, 2);
v_defaultFacets_3622_ = lean_ctor_get(v_config_3621_, 7);
lean_inc_ref(v_defaultFacets_3622_);
v_sz_3623_ = lean_array_size(v_defaultFacets_3622_);
v___x_3624_ = ((size_t)0ULL);
v___x_3625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3613_, v_sz_3623_, v___x_3624_, v_defaultFacets_3622_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3636_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
v_a_3627_ = lean_ctor_get(v___x_3625_, 1);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3629_ = v___x_3625_;
v_isShared_3630_ = v_isSharedCheck_3636_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_inc(v_a_3626_);
lean_dec(v___x_3625_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3636_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3634_; 
v___x_3631_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0));
v___x_3632_ = l_Lake_Job_mixArray___redArg(v_a_3626_, v___x_3631_);
lean_dec(v_a_3626_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3632_);
v___x_3634_ = v___x_3629_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3632_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_a_3627_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
else
{
lean_object* v_a_3637_; lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
v_a_3637_ = lean_ctor_get(v___x_3625_, 0);
v_a_3638_ = lean_ctor_get(v___x_3625_, 1);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3625_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_inc(v_a_3637_);
lean_dec(v___x_3625_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3637_);
lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_a_3638_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object* v_self_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_);
lean_dec_ref(v_a_3651_);
lean_dec(v_a_3650_);
lean_dec(v_a_3649_);
lean_dec(v_a_3648_);
return v_res_3654_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3656_; uint8_t v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___f_3656_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_3657_ = 1;
v___x_3658_ = l_Lake_instDataKindUnit;
v___x_3659_ = ((lean_object*)(l_Lake_LeanLib_defaultFacetConfig___closed__0));
v___x_3660_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3661_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
lean_ctor_set(v___x_3661_, 1, v___x_3659_);
lean_ctor_set(v___x_3661_, 2, v___x_3658_);
lean_ctor_set(v___x_3661_, 3, v___f_3656_);
lean_ctor_set_uint8(v___x_3661_, sizeof(void*)*4, v___x_3657_);
lean_ctor_set_uint8(v___x_3661_, sizeof(void*)*4 + 1, v___x_3657_);
return v___x_3661_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = lean_obj_once(&l_Lake_LeanLib_defaultFacetConfig___closed__1, &l_Lake_LeanLib_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanLib_defaultFacetConfig___closed__1);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_3663_, lean_object* v_v_3664_, lean_object* v_t_3665_){
_start:
{
if (lean_obj_tag(v_t_3665_) == 0)
{
lean_object* v_size_3666_; lean_object* v_k_3667_; lean_object* v_v_3668_; lean_object* v_l_3669_; lean_object* v_r_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3950_; 
v_size_3666_ = lean_ctor_get(v_t_3665_, 0);
v_k_3667_ = lean_ctor_get(v_t_3665_, 1);
v_v_3668_ = lean_ctor_get(v_t_3665_, 2);
v_l_3669_ = lean_ctor_get(v_t_3665_, 3);
v_r_3670_ = lean_ctor_get(v_t_3665_, 4);
v_isSharedCheck_3950_ = !lean_is_exclusive(v_t_3665_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3672_ = v_t_3665_;
v_isShared_3673_ = v_isSharedCheck_3950_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_r_3670_);
lean_inc(v_l_3669_);
lean_inc(v_v_3668_);
lean_inc(v_k_3667_);
lean_inc(v_size_3666_);
lean_dec(v_t_3665_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3950_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
uint8_t v___x_3674_; 
v___x_3674_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3663_, v_k_3667_);
switch(v___x_3674_)
{
case 0:
{
lean_object* v_impl_3675_; lean_object* v___x_3676_; 
lean_dec(v_size_3666_);
v_impl_3675_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3663_, v_v_3664_, v_l_3669_);
v___x_3676_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3670_) == 0)
{
lean_object* v_size_3677_; lean_object* v_size_3678_; lean_object* v_k_3679_; lean_object* v_v_3680_; lean_object* v_l_3681_; lean_object* v_r_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; 
v_size_3677_ = lean_ctor_get(v_r_3670_, 0);
v_size_3678_ = lean_ctor_get(v_impl_3675_, 0);
lean_inc(v_size_3678_);
v_k_3679_ = lean_ctor_get(v_impl_3675_, 1);
lean_inc(v_k_3679_);
v_v_3680_ = lean_ctor_get(v_impl_3675_, 2);
lean_inc(v_v_3680_);
v_l_3681_ = lean_ctor_get(v_impl_3675_, 3);
lean_inc(v_l_3681_);
v_r_3682_ = lean_ctor_get(v_impl_3675_, 4);
lean_inc(v_r_3682_);
v___x_3683_ = lean_unsigned_to_nat(3u);
v___x_3684_ = lean_nat_mul(v___x_3683_, v_size_3677_);
v___x_3685_ = lean_nat_dec_lt(v___x_3684_, v_size_3678_);
lean_dec(v___x_3684_);
if (v___x_3685_ == 0)
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3689_; 
lean_dec(v_r_3682_);
lean_dec(v_l_3681_);
lean_dec(v_v_3680_);
lean_dec(v_k_3679_);
v___x_3686_ = lean_nat_add(v___x_3676_, v_size_3678_);
lean_dec(v_size_3678_);
v___x_3687_ = lean_nat_add(v___x_3686_, v_size_3677_);
lean_dec(v___x_3686_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 3, v_impl_3675_);
lean_ctor_set(v___x_3672_, 0, v___x_3687_);
v___x_3689_ = v___x_3672_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3690_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3690_, 3, v_impl_3675_);
lean_ctor_set(v_reuseFailAlloc_3690_, 4, v_r_3670_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
else
{
lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3756_; 
v_isSharedCheck_3756_ = !lean_is_exclusive(v_impl_3675_);
if (v_isSharedCheck_3756_ == 0)
{
lean_object* v_unused_3757_; lean_object* v_unused_3758_; lean_object* v_unused_3759_; lean_object* v_unused_3760_; lean_object* v_unused_3761_; 
v_unused_3757_ = lean_ctor_get(v_impl_3675_, 4);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_impl_3675_, 3);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_impl_3675_, 2);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_impl_3675_, 1);
lean_dec(v_unused_3760_);
v_unused_3761_ = lean_ctor_get(v_impl_3675_, 0);
lean_dec(v_unused_3761_);
v___x_3692_ = v_impl_3675_;
v_isShared_3693_ = v_isSharedCheck_3756_;
goto v_resetjp_3691_;
}
else
{
lean_dec(v_impl_3675_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3756_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v_size_3694_; lean_object* v_size_3695_; lean_object* v_k_3696_; lean_object* v_v_3697_; lean_object* v_l_3698_; lean_object* v_r_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; uint8_t v___x_3702_; 
v_size_3694_ = lean_ctor_get(v_l_3681_, 0);
v_size_3695_ = lean_ctor_get(v_r_3682_, 0);
v_k_3696_ = lean_ctor_get(v_r_3682_, 1);
v_v_3697_ = lean_ctor_get(v_r_3682_, 2);
v_l_3698_ = lean_ctor_get(v_r_3682_, 3);
v_r_3699_ = lean_ctor_get(v_r_3682_, 4);
v___x_3700_ = lean_unsigned_to_nat(2u);
v___x_3701_ = lean_nat_mul(v___x_3700_, v_size_3694_);
v___x_3702_ = lean_nat_dec_lt(v_size_3695_, v___x_3701_);
lean_dec(v___x_3701_);
if (v___x_3702_ == 0)
{
lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3731_; 
lean_inc(v_r_3699_);
lean_inc(v_l_3698_);
lean_inc(v_v_3697_);
lean_inc(v_k_3696_);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_r_3682_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; lean_object* v_unused_3733_; lean_object* v_unused_3734_; lean_object* v_unused_3735_; lean_object* v_unused_3736_; 
v_unused_3732_ = lean_ctor_get(v_r_3682_, 4);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_r_3682_, 3);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_r_3682_, 2);
lean_dec(v_unused_3734_);
v_unused_3735_ = lean_ctor_get(v_r_3682_, 1);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_r_3682_, 0);
lean_dec(v_unused_3736_);
v___x_3704_ = v_r_3682_;
v_isShared_3705_ = v_isSharedCheck_3731_;
goto v_resetjp_3703_;
}
else
{
lean_dec(v_r_3682_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3731_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___x_3719_; lean_object* v___y_3721_; 
v___x_3706_ = lean_nat_add(v___x_3676_, v_size_3678_);
lean_dec(v_size_3678_);
v___x_3707_ = lean_nat_add(v___x_3706_, v_size_3677_);
lean_dec(v___x_3706_);
v___x_3719_ = lean_nat_add(v___x_3676_, v_size_3694_);
if (lean_obj_tag(v_l_3698_) == 0)
{
lean_object* v_size_3729_; 
v_size_3729_ = lean_ctor_get(v_l_3698_, 0);
lean_inc(v_size_3729_);
v___y_3721_ = v_size_3729_;
goto v___jp_3720_;
}
else
{
lean_object* v___x_3730_; 
v___x_3730_ = lean_unsigned_to_nat(0u);
v___y_3721_ = v___x_3730_;
goto v___jp_3720_;
}
v___jp_3708_:
{
lean_object* v___x_3712_; lean_object* v___x_3714_; 
v___x_3712_ = lean_nat_add(v___y_3709_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec(v___y_3709_);
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 4, v_r_3670_);
lean_ctor_set(v___x_3704_, 3, v_r_3699_);
lean_ctor_set(v___x_3704_, 2, v_v_3668_);
lean_ctor_set(v___x_3704_, 1, v_k_3667_);
lean_ctor_set(v___x_3704_, 0, v___x_3712_);
v___x_3714_ = v___x_3704_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3718_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3718_, 3, v_r_3699_);
lean_ctor_set(v_reuseFailAlloc_3718_, 4, v_r_3670_);
v___x_3714_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v___x_3716_; 
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 4, v___x_3714_);
lean_ctor_set(v___x_3692_, 3, v___y_3710_);
lean_ctor_set(v___x_3692_, 2, v_v_3697_);
lean_ctor_set(v___x_3692_, 1, v_k_3696_);
lean_ctor_set(v___x_3692_, 0, v___x_3707_);
v___x_3716_ = v___x_3692_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3707_);
lean_ctor_set(v_reuseFailAlloc_3717_, 1, v_k_3696_);
lean_ctor_set(v_reuseFailAlloc_3717_, 2, v_v_3697_);
lean_ctor_set(v_reuseFailAlloc_3717_, 3, v___y_3710_);
lean_ctor_set(v_reuseFailAlloc_3717_, 4, v___x_3714_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
v___jp_3720_:
{
lean_object* v___x_3722_; lean_object* v___x_3724_; 
v___x_3722_ = lean_nat_add(v___x_3719_, v___y_3721_);
lean_dec(v___y_3721_);
lean_dec(v___x_3719_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 4, v_l_3698_);
lean_ctor_set(v___x_3672_, 3, v_l_3681_);
lean_ctor_set(v___x_3672_, 2, v_v_3680_);
lean_ctor_set(v___x_3672_, 1, v_k_3679_);
lean_ctor_set(v___x_3672_, 0, v___x_3722_);
v___x_3724_ = v___x_3672_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_k_3679_);
lean_ctor_set(v_reuseFailAlloc_3728_, 2, v_v_3680_);
lean_ctor_set(v_reuseFailAlloc_3728_, 3, v_l_3681_);
lean_ctor_set(v_reuseFailAlloc_3728_, 4, v_l_3698_);
v___x_3724_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3725_; 
v___x_3725_ = lean_nat_add(v___x_3676_, v_size_3677_);
if (lean_obj_tag(v_r_3699_) == 0)
{
lean_object* v_size_3726_; 
v_size_3726_ = lean_ctor_get(v_r_3699_, 0);
lean_inc(v_size_3726_);
v___y_3709_ = v___x_3725_;
v___y_3710_ = v___x_3724_;
v___y_3711_ = v_size_3726_;
goto v___jp_3708_;
}
else
{
lean_object* v___x_3727_; 
v___x_3727_ = lean_unsigned_to_nat(0u);
v___y_3709_ = v___x_3725_;
v___y_3710_ = v___x_3724_;
v___y_3711_ = v___x_3727_;
goto v___jp_3708_;
}
}
}
}
}
else
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3742_; 
lean_del_object(v___x_3672_);
v___x_3737_ = lean_nat_add(v___x_3676_, v_size_3678_);
lean_dec(v_size_3678_);
v___x_3738_ = lean_nat_add(v___x_3737_, v_size_3677_);
lean_dec(v___x_3737_);
v___x_3739_ = lean_nat_add(v___x_3676_, v_size_3677_);
v___x_3740_ = lean_nat_add(v___x_3739_, v_size_3695_);
lean_dec(v___x_3739_);
lean_inc_ref(v_r_3670_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 4, v_r_3670_);
lean_ctor_set(v___x_3692_, 3, v_r_3682_);
lean_ctor_set(v___x_3692_, 2, v_v_3668_);
lean_ctor_set(v___x_3692_, 1, v_k_3667_);
lean_ctor_set(v___x_3692_, 0, v___x_3740_);
v___x_3742_ = v___x_3692_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v___x_3740_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3755_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3755_, 3, v_r_3682_);
lean_ctor_set(v_reuseFailAlloc_3755_, 4, v_r_3670_);
v___x_3742_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
v_isSharedCheck_3749_ = !lean_is_exclusive(v_r_3670_);
if (v_isSharedCheck_3749_ == 0)
{
lean_object* v_unused_3750_; lean_object* v_unused_3751_; lean_object* v_unused_3752_; lean_object* v_unused_3753_; lean_object* v_unused_3754_; 
v_unused_3750_ = lean_ctor_get(v_r_3670_, 4);
lean_dec(v_unused_3750_);
v_unused_3751_ = lean_ctor_get(v_r_3670_, 3);
lean_dec(v_unused_3751_);
v_unused_3752_ = lean_ctor_get(v_r_3670_, 2);
lean_dec(v_unused_3752_);
v_unused_3753_ = lean_ctor_get(v_r_3670_, 1);
lean_dec(v_unused_3753_);
v_unused_3754_ = lean_ctor_get(v_r_3670_, 0);
lean_dec(v_unused_3754_);
v___x_3744_ = v_r_3670_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_dec(v_r_3670_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 4, v___x_3742_);
lean_ctor_set(v___x_3744_, 3, v_l_3681_);
lean_ctor_set(v___x_3744_, 2, v_v_3680_);
lean_ctor_set(v___x_3744_, 1, v_k_3679_);
lean_ctor_set(v___x_3744_, 0, v___x_3738_);
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3738_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v_k_3679_);
lean_ctor_set(v_reuseFailAlloc_3748_, 2, v_v_3680_);
lean_ctor_set(v_reuseFailAlloc_3748_, 3, v_l_3681_);
lean_ctor_set(v_reuseFailAlloc_3748_, 4, v___x_3742_);
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
v_l_3762_ = lean_ctor_get(v_impl_3675_, 3);
lean_inc(v_l_3762_);
if (lean_obj_tag(v_l_3762_) == 0)
{
lean_object* v_r_3763_; lean_object* v_k_3764_; lean_object* v_v_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3776_; 
v_r_3763_ = lean_ctor_get(v_impl_3675_, 4);
v_k_3764_ = lean_ctor_get(v_impl_3675_, 1);
v_v_3765_ = lean_ctor_get(v_impl_3675_, 2);
v_isSharedCheck_3776_ = !lean_is_exclusive(v_impl_3675_);
if (v_isSharedCheck_3776_ == 0)
{
lean_object* v_unused_3777_; lean_object* v_unused_3778_; 
v_unused_3777_ = lean_ctor_get(v_impl_3675_, 3);
lean_dec(v_unused_3777_);
v_unused_3778_ = lean_ctor_get(v_impl_3675_, 0);
lean_dec(v_unused_3778_);
v___x_3767_ = v_impl_3675_;
v_isShared_3768_ = v_isSharedCheck_3776_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_r_3763_);
lean_inc(v_v_3765_);
lean_inc(v_k_3764_);
lean_dec(v_impl_3675_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3776_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3769_; lean_object* v___x_3771_; 
v___x_3769_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3763_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 3, v_r_3763_);
lean_ctor_set(v___x_3767_, 2, v_v_3668_);
lean_ctor_set(v___x_3767_, 1, v_k_3667_);
lean_ctor_set(v___x_3767_, 0, v___x_3676_);
v___x_3771_ = v___x_3767_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3775_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3775_, 3, v_r_3763_);
lean_ctor_set(v_reuseFailAlloc_3775_, 4, v_r_3763_);
v___x_3771_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
lean_object* v___x_3773_; 
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 4, v___x_3771_);
lean_ctor_set(v___x_3672_, 3, v_l_3762_);
lean_ctor_set(v___x_3672_, 2, v_v_3765_);
lean_ctor_set(v___x_3672_, 1, v_k_3764_);
lean_ctor_set(v___x_3672_, 0, v___x_3769_);
v___x_3773_ = v___x_3672_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3769_);
lean_ctor_set(v_reuseFailAlloc_3774_, 1, v_k_3764_);
lean_ctor_set(v_reuseFailAlloc_3774_, 2, v_v_3765_);
lean_ctor_set(v_reuseFailAlloc_3774_, 3, v_l_3762_);
lean_ctor_set(v_reuseFailAlloc_3774_, 4, v___x_3771_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
else
{
lean_object* v_r_3779_; 
v_r_3779_ = lean_ctor_get(v_impl_3675_, 4);
lean_inc(v_r_3779_);
if (lean_obj_tag(v_r_3779_) == 0)
{
lean_object* v_k_3780_; lean_object* v_v_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3804_; 
v_k_3780_ = lean_ctor_get(v_impl_3675_, 1);
v_v_3781_ = lean_ctor_get(v_impl_3675_, 2);
v_isSharedCheck_3804_ = !lean_is_exclusive(v_impl_3675_);
if (v_isSharedCheck_3804_ == 0)
{
lean_object* v_unused_3805_; lean_object* v_unused_3806_; lean_object* v_unused_3807_; 
v_unused_3805_ = lean_ctor_get(v_impl_3675_, 4);
lean_dec(v_unused_3805_);
v_unused_3806_ = lean_ctor_get(v_impl_3675_, 3);
lean_dec(v_unused_3806_);
v_unused_3807_ = lean_ctor_get(v_impl_3675_, 0);
lean_dec(v_unused_3807_);
v___x_3783_ = v_impl_3675_;
v_isShared_3784_ = v_isSharedCheck_3804_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_v_3781_);
lean_inc(v_k_3780_);
lean_dec(v_impl_3675_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3804_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v_k_3785_; lean_object* v_v_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3800_; 
v_k_3785_ = lean_ctor_get(v_r_3779_, 1);
v_v_3786_ = lean_ctor_get(v_r_3779_, 2);
v_isSharedCheck_3800_ = !lean_is_exclusive(v_r_3779_);
if (v_isSharedCheck_3800_ == 0)
{
lean_object* v_unused_3801_; lean_object* v_unused_3802_; lean_object* v_unused_3803_; 
v_unused_3801_ = lean_ctor_get(v_r_3779_, 4);
lean_dec(v_unused_3801_);
v_unused_3802_ = lean_ctor_get(v_r_3779_, 3);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_r_3779_, 0);
lean_dec(v_unused_3803_);
v___x_3788_ = v_r_3779_;
v_isShared_3789_ = v_isSharedCheck_3800_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_v_3786_);
lean_inc(v_k_3785_);
lean_dec(v_r_3779_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3800_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3790_; lean_object* v___x_3792_; 
v___x_3790_ = lean_unsigned_to_nat(3u);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 4, v_l_3762_);
lean_ctor_set(v___x_3788_, 3, v_l_3762_);
lean_ctor_set(v___x_3788_, 2, v_v_3781_);
lean_ctor_set(v___x_3788_, 1, v_k_3780_);
lean_ctor_set(v___x_3788_, 0, v___x_3676_);
v___x_3792_ = v___x_3788_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_k_3780_);
lean_ctor_set(v_reuseFailAlloc_3799_, 2, v_v_3781_);
lean_ctor_set(v_reuseFailAlloc_3799_, 3, v_l_3762_);
lean_ctor_set(v_reuseFailAlloc_3799_, 4, v_l_3762_);
v___x_3792_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
lean_object* v___x_3794_; 
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 4, v_l_3762_);
lean_ctor_set(v___x_3783_, 2, v_v_3668_);
lean_ctor_set(v___x_3783_, 1, v_k_3667_);
lean_ctor_set(v___x_3783_, 0, v___x_3676_);
v___x_3794_ = v___x_3783_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3798_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3798_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3798_, 3, v_l_3762_);
lean_ctor_set(v_reuseFailAlloc_3798_, 4, v_l_3762_);
v___x_3794_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3796_; 
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 4, v___x_3794_);
lean_ctor_set(v___x_3672_, 3, v___x_3792_);
lean_ctor_set(v___x_3672_, 2, v_v_3786_);
lean_ctor_set(v___x_3672_, 1, v_k_3785_);
lean_ctor_set(v___x_3672_, 0, v___x_3790_);
v___x_3796_ = v___x_3672_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3790_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_k_3785_);
lean_ctor_set(v_reuseFailAlloc_3797_, 2, v_v_3786_);
lean_ctor_set(v_reuseFailAlloc_3797_, 3, v___x_3792_);
lean_ctor_set(v_reuseFailAlloc_3797_, 4, v___x_3794_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
}
}
else
{
lean_object* v___x_3808_; lean_object* v___x_3810_; 
v___x_3808_ = lean_unsigned_to_nat(2u);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 4, v_r_3779_);
lean_ctor_set(v___x_3672_, 3, v_impl_3675_);
lean_ctor_set(v___x_3672_, 0, v___x_3808_);
v___x_3810_ = v___x_3672_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3808_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3811_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3811_, 3, v_impl_3675_);
lean_ctor_set(v_reuseFailAlloc_3811_, 4, v_r_3779_);
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
case 1:
{
lean_object* v___x_3813_; 
lean_dec(v_v_3668_);
lean_dec(v_k_3667_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 2, v_v_3664_);
lean_ctor_set(v___x_3672_, 1, v_k_3663_);
v___x_3813_ = v___x_3672_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_size_3666_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v_k_3663_);
lean_ctor_set(v_reuseFailAlloc_3814_, 2, v_v_3664_);
lean_ctor_set(v_reuseFailAlloc_3814_, 3, v_l_3669_);
lean_ctor_set(v_reuseFailAlloc_3814_, 4, v_r_3670_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
default: 
{
lean_object* v_impl_3815_; lean_object* v___x_3816_; 
lean_dec(v_size_3666_);
v_impl_3815_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3663_, v_v_3664_, v_r_3670_);
v___x_3816_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3669_) == 0)
{
lean_object* v_size_3817_; lean_object* v_size_3818_; lean_object* v_k_3819_; lean_object* v_v_3820_; lean_object* v_l_3821_; lean_object* v_r_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v_size_3817_ = lean_ctor_get(v_l_3669_, 0);
v_size_3818_ = lean_ctor_get(v_impl_3815_, 0);
lean_inc(v_size_3818_);
v_k_3819_ = lean_ctor_get(v_impl_3815_, 1);
lean_inc(v_k_3819_);
v_v_3820_ = lean_ctor_get(v_impl_3815_, 2);
lean_inc(v_v_3820_);
v_l_3821_ = lean_ctor_get(v_impl_3815_, 3);
lean_inc(v_l_3821_);
v_r_3822_ = lean_ctor_get(v_impl_3815_, 4);
lean_inc(v_r_3822_);
v___x_3823_ = lean_unsigned_to_nat(3u);
v___x_3824_ = lean_nat_mul(v___x_3823_, v_size_3817_);
v___x_3825_ = lean_nat_dec_lt(v___x_3824_, v_size_3818_);
lean_dec(v___x_3824_);
if (v___x_3825_ == 0)
{
lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3829_; 
lean_dec(v_r_3822_);
lean_dec(v_l_3821_);
lean_dec(v_v_3820_);
lean_dec(v_k_3819_);
v___x_3826_ = lean_nat_add(v___x_3816_, v_size_3817_);
v___x_3827_ = lean_nat_add(v___x_3826_, v_size_3818_);
lean_dec(v_size_3818_);
lean_dec(v___x_3826_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 4, v_impl_3815_);
lean_ctor_set(v___x_3672_, 0, v___x_3827_);
v___x_3829_ = v___x_3672_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3827_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3830_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3830_, 3, v_l_3669_);
lean_ctor_set(v_reuseFailAlloc_3830_, 4, v_impl_3815_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
else
{
lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3894_; 
v_isSharedCheck_3894_ = !lean_is_exclusive(v_impl_3815_);
if (v_isSharedCheck_3894_ == 0)
{
lean_object* v_unused_3895_; lean_object* v_unused_3896_; lean_object* v_unused_3897_; lean_object* v_unused_3898_; lean_object* v_unused_3899_; 
v_unused_3895_ = lean_ctor_get(v_impl_3815_, 4);
lean_dec(v_unused_3895_);
v_unused_3896_ = lean_ctor_get(v_impl_3815_, 3);
lean_dec(v_unused_3896_);
v_unused_3897_ = lean_ctor_get(v_impl_3815_, 2);
lean_dec(v_unused_3897_);
v_unused_3898_ = lean_ctor_get(v_impl_3815_, 1);
lean_dec(v_unused_3898_);
v_unused_3899_ = lean_ctor_get(v_impl_3815_, 0);
lean_dec(v_unused_3899_);
v___x_3832_ = v_impl_3815_;
v_isShared_3833_ = v_isSharedCheck_3894_;
goto v_resetjp_3831_;
}
else
{
lean_dec(v_impl_3815_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3894_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v_size_3834_; lean_object* v_k_3835_; lean_object* v_v_3836_; lean_object* v_l_3837_; lean_object* v_r_3838_; lean_object* v_size_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v_size_3834_ = lean_ctor_get(v_l_3821_, 0);
v_k_3835_ = lean_ctor_get(v_l_3821_, 1);
v_v_3836_ = lean_ctor_get(v_l_3821_, 2);
v_l_3837_ = lean_ctor_get(v_l_3821_, 3);
v_r_3838_ = lean_ctor_get(v_l_3821_, 4);
v_size_3839_ = lean_ctor_get(v_r_3822_, 0);
v___x_3840_ = lean_unsigned_to_nat(2u);
v___x_3841_ = lean_nat_mul(v___x_3840_, v_size_3839_);
v___x_3842_ = lean_nat_dec_lt(v_size_3834_, v___x_3841_);
lean_dec(v___x_3841_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3870_; 
lean_inc(v_r_3838_);
lean_inc(v_l_3837_);
lean_inc(v_v_3836_);
lean_inc(v_k_3835_);
v_isSharedCheck_3870_ = !lean_is_exclusive(v_l_3821_);
if (v_isSharedCheck_3870_ == 0)
{
lean_object* v_unused_3871_; lean_object* v_unused_3872_; lean_object* v_unused_3873_; lean_object* v_unused_3874_; lean_object* v_unused_3875_; 
v_unused_3871_ = lean_ctor_get(v_l_3821_, 4);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_l_3821_, 3);
lean_dec(v_unused_3872_);
v_unused_3873_ = lean_ctor_get(v_l_3821_, 2);
lean_dec(v_unused_3873_);
v_unused_3874_ = lean_ctor_get(v_l_3821_, 1);
lean_dec(v_unused_3874_);
v_unused_3875_ = lean_ctor_get(v_l_3821_, 0);
lean_dec(v_unused_3875_);
v___x_3844_ = v_l_3821_;
v_isShared_3845_ = v_isSharedCheck_3870_;
goto v_resetjp_3843_;
}
else
{
lean_dec(v_l_3821_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3870_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3860_; 
v___x_3846_ = lean_nat_add(v___x_3816_, v_size_3817_);
v___x_3847_ = lean_nat_add(v___x_3846_, v_size_3818_);
lean_dec(v_size_3818_);
if (lean_obj_tag(v_l_3837_) == 0)
{
lean_object* v_size_3868_; 
v_size_3868_ = lean_ctor_get(v_l_3837_, 0);
lean_inc(v_size_3868_);
v___y_3860_ = v_size_3868_;
goto v___jp_3859_;
}
else
{
lean_object* v___x_3869_; 
v___x_3869_ = lean_unsigned_to_nat(0u);
v___y_3860_ = v___x_3869_;
goto v___jp_3859_;
}
v___jp_3848_:
{
lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3852_ = lean_nat_add(v___y_3850_, v___y_3851_);
lean_dec(v___y_3851_);
lean_dec(v___y_3850_);
if (v_isShared_3845_ == 0)
{
lean_ctor_set(v___x_3844_, 4, v_r_3822_);
lean_ctor_set(v___x_3844_, 3, v_r_3838_);
lean_ctor_set(v___x_3844_, 2, v_v_3820_);
lean_ctor_set(v___x_3844_, 1, v_k_3819_);
lean_ctor_set(v___x_3844_, 0, v___x_3852_);
v___x_3854_ = v___x_3844_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v_k_3819_);
lean_ctor_set(v_reuseFailAlloc_3858_, 2, v_v_3820_);
lean_ctor_set(v_reuseFailAlloc_3858_, 3, v_r_3838_);
lean_ctor_set(v_reuseFailAlloc_3858_, 4, v_r_3822_);
v___x_3854_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3856_; 
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 4, v___x_3854_);
lean_ctor_set(v___x_3832_, 3, v___y_3849_);
lean_ctor_set(v___x_3832_, 2, v_v_3836_);
lean_ctor_set(v___x_3832_, 1, v_k_3835_);
lean_ctor_set(v___x_3832_, 0, v___x_3847_);
v___x_3856_ = v___x_3832_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3847_);
lean_ctor_set(v_reuseFailAlloc_3857_, 1, v_k_3835_);
lean_ctor_set(v_reuseFailAlloc_3857_, 2, v_v_3836_);
lean_ctor_set(v_reuseFailAlloc_3857_, 3, v___y_3849_);
lean_ctor_set(v_reuseFailAlloc_3857_, 4, v___x_3854_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
v___jp_3859_:
{
lean_object* v___x_3861_; lean_object* v___x_3863_; 
v___x_3861_ = lean_nat_add(v___x_3846_, v___y_3860_);
lean_dec(v___y_3860_);
lean_dec(v___x_3846_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 4, v_l_3837_);
lean_ctor_set(v___x_3672_, 0, v___x_3861_);
v___x_3863_ = v___x_3672_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v___x_3861_);
lean_ctor_set(v_reuseFailAlloc_3867_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3867_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3867_, 3, v_l_3669_);
lean_ctor_set(v_reuseFailAlloc_3867_, 4, v_l_3837_);
v___x_3863_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; 
v___x_3864_ = lean_nat_add(v___x_3816_, v_size_3839_);
if (lean_obj_tag(v_r_3838_) == 0)
{
lean_object* v_size_3865_; 
v_size_3865_ = lean_ctor_get(v_r_3838_, 0);
lean_inc(v_size_3865_);
v___y_3849_ = v___x_3863_;
v___y_3850_ = v___x_3864_;
v___y_3851_ = v_size_3865_;
goto v___jp_3848_;
}
else
{
lean_object* v___x_3866_; 
v___x_3866_ = lean_unsigned_to_nat(0u);
v___y_3849_ = v___x_3863_;
v___y_3850_ = v___x_3864_;
v___y_3851_ = v___x_3866_;
goto v___jp_3848_;
}
}
}
}
}
else
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3880_; 
lean_del_object(v___x_3672_);
v___x_3876_ = lean_nat_add(v___x_3816_, v_size_3817_);
v___x_3877_ = lean_nat_add(v___x_3876_, v_size_3818_);
lean_dec(v_size_3818_);
v___x_3878_ = lean_nat_add(v___x_3876_, v_size_3834_);
lean_dec(v___x_3876_);
lean_inc_ref(v_l_3669_);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 4, v_l_3821_);
lean_ctor_set(v___x_3832_, 3, v_l_3669_);
lean_ctor_set(v___x_3832_, 2, v_v_3668_);
lean_ctor_set(v___x_3832_, 1, v_k_3667_);
lean_ctor_set(v___x_3832_, 0, v___x_3878_);
v___x_3880_ = v___x_3832_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3878_);
lean_ctor_set(v_reuseFailAlloc_3893_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3893_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3893_, 3, v_l_3669_);
lean_ctor_set(v_reuseFailAlloc_3893_, 4, v_l_3821_);
v___x_3880_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
v_isSharedCheck_3887_ = !lean_is_exclusive(v_l_3669_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; lean_object* v_unused_3889_; lean_object* v_unused_3890_; lean_object* v_unused_3891_; lean_object* v_unused_3892_; 
v_unused_3888_ = lean_ctor_get(v_l_3669_, 4);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_l_3669_, 3);
lean_dec(v_unused_3889_);
v_unused_3890_ = lean_ctor_get(v_l_3669_, 2);
lean_dec(v_unused_3890_);
v_unused_3891_ = lean_ctor_get(v_l_3669_, 1);
lean_dec(v_unused_3891_);
v_unused_3892_ = lean_ctor_get(v_l_3669_, 0);
lean_dec(v_unused_3892_);
v___x_3882_ = v_l_3669_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_dec(v_l_3669_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 4, v_r_3822_);
lean_ctor_set(v___x_3882_, 3, v___x_3880_);
lean_ctor_set(v___x_3882_, 2, v_v_3820_);
lean_ctor_set(v___x_3882_, 1, v_k_3819_);
lean_ctor_set(v___x_3882_, 0, v___x_3877_);
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3877_);
lean_ctor_set(v_reuseFailAlloc_3886_, 1, v_k_3819_);
lean_ctor_set(v_reuseFailAlloc_3886_, 2, v_v_3820_);
lean_ctor_set(v_reuseFailAlloc_3886_, 3, v___x_3880_);
lean_ctor_set(v_reuseFailAlloc_3886_, 4, v_r_3822_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3900_; 
v_l_3900_ = lean_ctor_get(v_impl_3815_, 3);
lean_inc(v_l_3900_);
if (lean_obj_tag(v_l_3900_) == 0)
{
lean_object* v_r_3901_; lean_object* v_k_3902_; lean_object* v_v_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3926_; 
v_r_3901_ = lean_ctor_get(v_impl_3815_, 4);
v_k_3902_ = lean_ctor_get(v_impl_3815_, 1);
v_v_3903_ = lean_ctor_get(v_impl_3815_, 2);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_impl_3815_);
if (v_isSharedCheck_3926_ == 0)
{
lean_object* v_unused_3927_; lean_object* v_unused_3928_; 
v_unused_3927_ = lean_ctor_get(v_impl_3815_, 3);
lean_dec(v_unused_3927_);
v_unused_3928_ = lean_ctor_get(v_impl_3815_, 0);
lean_dec(v_unused_3928_);
v___x_3905_ = v_impl_3815_;
v_isShared_3906_ = v_isSharedCheck_3926_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_r_3901_);
lean_inc(v_v_3903_);
lean_inc(v_k_3902_);
lean_dec(v_impl_3815_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3926_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v_k_3907_; lean_object* v_v_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3922_; 
v_k_3907_ = lean_ctor_get(v_l_3900_, 1);
v_v_3908_ = lean_ctor_get(v_l_3900_, 2);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_l_3900_);
if (v_isSharedCheck_3922_ == 0)
{
lean_object* v_unused_3923_; lean_object* v_unused_3924_; lean_object* v_unused_3925_; 
v_unused_3923_ = lean_ctor_get(v_l_3900_, 4);
lean_dec(v_unused_3923_);
v_unused_3924_ = lean_ctor_get(v_l_3900_, 3);
lean_dec(v_unused_3924_);
v_unused_3925_ = lean_ctor_get(v_l_3900_, 0);
lean_dec(v_unused_3925_);
v___x_3910_ = v_l_3900_;
v_isShared_3911_ = v_isSharedCheck_3922_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_v_3908_);
lean_inc(v_k_3907_);
lean_dec(v_l_3900_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3922_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3912_; lean_object* v___x_3914_; 
v___x_3912_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3901_, 2);
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 4, v_r_3901_);
lean_ctor_set(v___x_3910_, 3, v_r_3901_);
lean_ctor_set(v___x_3910_, 2, v_v_3668_);
lean_ctor_set(v___x_3910_, 1, v_k_3667_);
lean_ctor_set(v___x_3910_, 0, v___x_3816_);
v___x_3914_ = v___x_3910_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3816_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3921_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3921_, 3, v_r_3901_);
lean_ctor_set(v_reuseFailAlloc_3921_, 4, v_r_3901_);
v___x_3914_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
lean_object* v___x_3916_; 
lean_inc(v_r_3901_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 3, v_r_3901_);
lean_ctor_set(v___x_3905_, 0, v___x_3816_);
v___x_3916_ = v___x_3905_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3816_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v_k_3902_);
lean_ctor_set(v_reuseFailAlloc_3920_, 2, v_v_3903_);
lean_ctor_set(v_reuseFailAlloc_3920_, 3, v_r_3901_);
lean_ctor_set(v_reuseFailAlloc_3920_, 4, v_r_3901_);
v___x_3916_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3918_; 
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 4, v___x_3916_);
lean_ctor_set(v___x_3672_, 3, v___x_3914_);
lean_ctor_set(v___x_3672_, 2, v_v_3908_);
lean_ctor_set(v___x_3672_, 1, v_k_3907_);
lean_ctor_set(v___x_3672_, 0, v___x_3912_);
v___x_3918_ = v___x_3672_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3912_);
lean_ctor_set(v_reuseFailAlloc_3919_, 1, v_k_3907_);
lean_ctor_set(v_reuseFailAlloc_3919_, 2, v_v_3908_);
lean_ctor_set(v_reuseFailAlloc_3919_, 3, v___x_3914_);
lean_ctor_set(v_reuseFailAlloc_3919_, 4, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
}
}
else
{
lean_object* v_r_3929_; 
v_r_3929_ = lean_ctor_get(v_impl_3815_, 4);
lean_inc(v_r_3929_);
if (lean_obj_tag(v_r_3929_) == 0)
{
lean_object* v_k_3930_; lean_object* v_v_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3942_; 
v_k_3930_ = lean_ctor_get(v_impl_3815_, 1);
v_v_3931_ = lean_ctor_get(v_impl_3815_, 2);
v_isSharedCheck_3942_ = !lean_is_exclusive(v_impl_3815_);
if (v_isSharedCheck_3942_ == 0)
{
lean_object* v_unused_3943_; lean_object* v_unused_3944_; lean_object* v_unused_3945_; 
v_unused_3943_ = lean_ctor_get(v_impl_3815_, 4);
lean_dec(v_unused_3943_);
v_unused_3944_ = lean_ctor_get(v_impl_3815_, 3);
lean_dec(v_unused_3944_);
v_unused_3945_ = lean_ctor_get(v_impl_3815_, 0);
lean_dec(v_unused_3945_);
v___x_3933_ = v_impl_3815_;
v_isShared_3934_ = v_isSharedCheck_3942_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_v_3931_);
lean_inc(v_k_3930_);
lean_dec(v_impl_3815_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3942_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; lean_object* v___x_3937_; 
v___x_3935_ = lean_unsigned_to_nat(3u);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 4, v_l_3900_);
lean_ctor_set(v___x_3933_, 2, v_v_3668_);
lean_ctor_set(v___x_3933_, 1, v_k_3667_);
lean_ctor_set(v___x_3933_, 0, v___x_3816_);
v___x_3937_ = v___x_3933_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3816_);
lean_ctor_set(v_reuseFailAlloc_3941_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3941_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3941_, 3, v_l_3900_);
lean_ctor_set(v_reuseFailAlloc_3941_, 4, v_l_3900_);
v___x_3937_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
lean_object* v___x_3939_; 
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 4, v_r_3929_);
lean_ctor_set(v___x_3672_, 3, v___x_3937_);
lean_ctor_set(v___x_3672_, 2, v_v_3931_);
lean_ctor_set(v___x_3672_, 1, v_k_3930_);
lean_ctor_set(v___x_3672_, 0, v___x_3935_);
v___x_3939_ = v___x_3672_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3935_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_k_3930_);
lean_ctor_set(v_reuseFailAlloc_3940_, 2, v_v_3931_);
lean_ctor_set(v_reuseFailAlloc_3940_, 3, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3940_, 4, v_r_3929_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
else
{
lean_object* v___x_3946_; lean_object* v___x_3948_; 
v___x_3946_ = lean_unsigned_to_nat(2u);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 4, v_impl_3815_);
lean_ctor_set(v___x_3672_, 3, v_r_3929_);
lean_ctor_set(v___x_3672_, 0, v___x_3946_);
v___x_3948_ = v___x_3672_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3946_);
lean_ctor_set(v_reuseFailAlloc_3949_, 1, v_k_3667_);
lean_ctor_set(v_reuseFailAlloc_3949_, 2, v_v_3668_);
lean_ctor_set(v_reuseFailAlloc_3949_, 3, v_r_3929_);
lean_ctor_set(v_reuseFailAlloc_3949_, 4, v_impl_3815_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
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
lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3951_ = lean_unsigned_to_nat(1u);
v___x_3952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
lean_ctor_set(v___x_3952_, 1, v_k_3663_);
lean_ctor_set(v___x_3952_, 2, v_v_3664_);
lean_ctor_set(v___x_3952_, 3, v_t_3665_);
lean_ctor_set(v___x_3952_, 4, v_t_3665_);
return v___x_3952_;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3953_ = lean_box(1);
v___x_3954_ = l_Lake_LeanLib_defaultFacetConfig;
v___x_3955_ = l_Lake_LeanLib_defaultFacet;
v___x_3956_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3955_, v___x_3954_, v___x_3953_);
return v___x_3956_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3957_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__0, &l_Lake_LeanLib_initFacetConfigs___closed__0_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__0);
v___x_3958_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig));
v___x_3959_ = l_Lake_LeanLib_modulesFacet;
v___x_3960_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3959_, v___x_3958_, v___x_3957_);
return v___x_3960_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3961_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__1, &l_Lake_LeanLib_initFacetConfigs___closed__1_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__1);
v___x_3962_ = l_Lake_LeanLib_elabArtsFacetConfig;
v___x_3963_ = l_Lake_LeanLib_elabArtsFacet;
v___x_3964_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3963_, v___x_3962_, v___x_3961_);
return v___x_3964_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3965_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__2, &l_Lake_LeanLib_initFacetConfigs___closed__2_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__2);
v___x_3966_ = l_Lake_LeanLib_irArtsFacetConfig;
v___x_3967_ = l_Lake_LeanLib_irArtsFacet;
v___x_3968_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3967_, v___x_3966_, v___x_3965_);
return v___x_3968_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3969_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__3, &l_Lake_LeanLib_initFacetConfigs___closed__3_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__3);
v___x_3970_ = l_Lake_LeanLib_leanArtsFacetConfig;
v___x_3971_ = l_Lake_LeanLib_leanArtsFacet;
v___x_3972_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3971_, v___x_3970_, v___x_3969_);
return v___x_3972_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3973_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__4, &l_Lake_LeanLib_initFacetConfigs___closed__4_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__4);
v___x_3974_ = l_Lake_LeanLib_staticFacetConfig;
v___x_3975_ = l_Lake_LeanLib_staticFacet;
v___x_3976_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3975_, v___x_3974_, v___x_3973_);
return v___x_3976_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3977_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__5, &l_Lake_LeanLib_initFacetConfigs___closed__5_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__5);
v___x_3978_ = l_Lake_LeanLib_staticExportFacetConfig;
v___x_3979_ = l_Lake_LeanLib_staticExportFacet;
v___x_3980_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3979_, v___x_3978_, v___x_3977_);
return v___x_3980_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3981_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__6, &l_Lake_LeanLib_initFacetConfigs___closed__6_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__6);
v___x_3982_ = l_Lake_LeanLib_sharedFacetConfig;
v___x_3983_ = l_Lake_LeanLib_sharedFacet;
v___x_3984_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3983_, v___x_3982_, v___x_3981_);
return v___x_3984_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3985_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__7, &l_Lake_LeanLib_initFacetConfigs___closed__7_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__7);
v___x_3986_ = l_Lake_LeanLib_extraDepFacetConfig;
v___x_3987_ = l_Lake_LeanLib_extraDepFacet;
v___x_3988_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3987_, v___x_3986_, v___x_3985_);
return v___x_3988_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_3989_; 
v___x_3989_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__8, &l_Lake_LeanLib_initFacetConfigs___closed__8_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__8);
return v___x_3989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3990_, lean_object* v_k_3991_, lean_object* v_v_3992_, lean_object* v_t_3993_, lean_object* v_hl_3994_){
_start:
{
lean_object* v___x_3995_; 
v___x_3995_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3991_, v_v_3992_, v_t_3993_);
return v___x_3995_;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs(void){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Lake_LeanLib_initFacetConfigs;
return v___x_3996_;
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
l_Lake_LeanLib_elabArtsFacetConfig = _init_l_Lake_LeanLib_elabArtsFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_elabArtsFacetConfig);
l_Lake_LeanLib_irArtsFacetConfig = _init_l_Lake_LeanLib_irArtsFacetConfig();
lean_mark_persistent(l_Lake_LeanLib_irArtsFacetConfig);
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
