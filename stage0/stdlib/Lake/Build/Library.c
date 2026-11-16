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
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_instDataKindFilePath;
lean_object* lean_obj_tag_nat(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lake_Target_fetchIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_Module_irArtsFacet;
lean_object* l_Lake_Job_mix___redArg(lean_object*, lean_object*);
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
extern lean_object* l_Lake_Module_elabArtsFacet;
extern lean_object* l_Lake_LeanLib_elabArtsFacet;
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
static const lean_array_object l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__1;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__2;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__3;
static lean_once_cell_t l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(v_a_150_);
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
lean_dec_ref(v___y_277_);
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
lean_dec_ref(v_a_291_);
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
lean_dec_ref(v___y_362_);
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
uint8_t v___x_7492__boxed_444_; lean_object* v_res_445_; 
v___x_7492__boxed_444_ = lean_unbox(v___x_435_);
v_res_445_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(v_self_432_, v_col_433_, v___x_434_, v___x_7492__boxed_444_, v___x_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec_ref(v___y_440_);
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
lean_dec_ref(v_a_477_);
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
lean_inc_ref(v___y_573_);
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
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v_as_604_);
return v_res_617_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__1(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_622_ = 0;
v___x_623_ = 0;
v___x_624_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__0));
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
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__2(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__1);
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_626_);
return v___x_628_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__3(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__2);
v___x_630_ = lean_task_pure(v___x_629_);
return v___x_630_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__4(void){
_start:
{
uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_631_ = 0;
v___x_632_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_633_ = lean_box(0);
v___x_634_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__3);
v___x_635_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_633_);
lean_ctor_set(v___x_635_, 2, v___x_632_);
lean_ctor_set_uint8(v___x_635_, sizeof(void*)*3, v___x_631_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0(lean_object* v___x_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v___x_644_; 
lean_inc_ref(v___y_637_);
lean_inc_ref(v___y_641_);
lean_inc_ref(v___y_640_);
lean_inc(v___y_639_);
lean_inc(v___y_638_);
v___x_644_ = lean_apply_7(v___y_637_, v___x_636_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, lean_box(0));
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
lean_object* v_a_648_; lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_663_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_a_649_ = lean_ctor_get(v___x_647_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_663_ == 0)
{
v___x_651_ = v___x_647_;
v_isShared_652_ = v_isSharedCheck_663_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_663_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__4);
v___x_655_ = lean_array_get_size(v_a_648_);
v___x_656_ = lean_nat_dec_lt(v___x_653_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_658_; 
lean_dec(v_a_648_);
lean_dec_ref(v___y_637_);
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
size_t v___x_660_; size_t v___x_661_; lean_object* v___x_662_; 
lean_del_object(v___x_651_);
v___x_660_ = ((size_t)0ULL);
v___x_661_ = lean_usize_of_nat(v___x_655_);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0(v_a_648_, v___x_660_, v___x_661_, v___x_654_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v_a_649_);
lean_dec(v_a_648_);
return v___x_662_;
}
}
}
else
{
lean_object* v_a_664_; lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v___y_637_);
v_a_664_ = lean_ctor_get(v___x_647_, 0);
v_a_665_ = lean_ctor_get(v___x_647_, 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_647_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_inc(v_a_664_);
lean_dec(v___x_647_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_664_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_object* v_a_673_; lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v___y_637_);
v_a_673_ = lean_ctor_get(v___x_644_, 0);
v_a_674_ = lean_ctor_get(v___x_644_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_644_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_inc(v_a_673_);
lean_dec(v___x_644_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_673_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___boxed(lean_object* v___x_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0(v___x_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec(v___y_684_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts(lean_object* v_self_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_pkg_699_; lean_object* v_name_700_; lean_object* v_keyName_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___f_707_; lean_object* v___x_708_; 
v_pkg_699_ = lean_ctor_get(v_self_691_, 0);
v_name_700_ = lean_ctor_get(v_self_691_, 1);
v_keyName_701_ = lean_ctor_get(v_pkg_699_, 2);
v___x_702_ = l_Lake_instDataKindUnit;
v___x_703_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_700_);
lean_inc(v_keyName_701_);
v___x_704_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_704_, 0, v_keyName_701_);
lean_ctor_set(v___x_704_, 1, v_name_700_);
v___x_705_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_706_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
lean_ctor_set(v___x_706_, 2, v_self_691_);
lean_ctor_set(v___x_706_, 3, v___x_703_);
v___f_707_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___boxed), 8, 1);
lean_closure_set(v___f_707_, 0, v___x_706_);
v___x_708_ = l_Lake_ensureJob___redArg(v___x_702_, v___f_707_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___boxed(lean_object* v_self_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts(v_self_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec(v_a_711_);
return v_res_717_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_box(0);
v___x_719_ = l_Lean_Json_compress(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(uint8_t v_fmt_720_){
_start:
{
if (v_fmt_720_ == 0)
{
lean_object* v___x_721_; 
v___x_721_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
return v___x_721_;
}
else
{
lean_object* v___x_722_; 
v___x_722_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0);
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_723_){
_start:
{
uint8_t v_fmt_boxed_724_; lean_object* v_res_725_; 
v_fmt_boxed_724_ = lean_unbox(v_fmt_723_);
v_res_725_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(v_fmt_boxed_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0(uint8_t v_fmt_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(v_fmt_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___boxed(lean_object* v_fmt_729_, lean_object* v_a_730_){
_start:
{
uint8_t v_fmt_boxed_731_; lean_object* v_res_732_; 
v_fmt_boxed_731_ = lean_unbox(v_fmt_729_);
v_res_732_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0(v_fmt_boxed_731_, v_a_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_elabArtsFacetConfig___lam__0(uint8_t v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(v___y_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_elabArtsFacetConfig___lam__0___boxed(lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
uint8_t v___y_68__boxed_738_; lean_object* v_res_739_; 
v___y_68__boxed_738_ = lean_unbox(v___y_736_);
v_res_739_ = l_Lake_LeanLib_elabArtsFacetConfig___lam__0(v___y_68__boxed_738_, v___y_737_);
return v_res_739_;
}
}
static lean_object* _init_l_Lake_LeanLib_elabArtsFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_742_; uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___f_742_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_743_ = 1;
v___x_744_ = l_Lake_instDataKindUnit;
v___x_745_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__1));
v___x_746_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_747_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v___x_745_);
lean_ctor_set(v___x_747_, 2, v___x_744_);
lean_ctor_set(v___x_747_, 3, v___f_742_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*4, v___x_743_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*4 + 1, v___x_743_);
return v___x_747_;
}
}
static lean_object* _init_l_Lake_LeanLib_elabArtsFacetConfig(void){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = lean_obj_once(&l_Lake_LeanLib_elabArtsFacetConfig___closed__2, &l_Lake_LeanLib_elabArtsFacetConfig___closed__2_once, _init_l_Lake_LeanLib_elabArtsFacetConfig___closed__2);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(lean_object* v_as_749_, size_t v_i_750_, size_t v_stop_751_, lean_object* v_b_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = lean_usize_dec_eq(v_i_750_, v_stop_751_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v_lib_762_; lean_object* v_pkg_763_; lean_object* v_name_764_; lean_object* v_keyName_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_761_ = lean_array_uget_borrowed(v_as_749_, v_i_750_);
v_lib_762_ = lean_ctor_get(v___x_761_, 0);
v_pkg_763_ = lean_ctor_get(v_lib_762_, 0);
v_name_764_ = lean_ctor_get(v___x_761_, 1);
v_keyName_765_ = lean_ctor_get(v_pkg_763_, 2);
v___x_766_ = l_Lake_Module_irArtsFacet;
lean_inc(v_name_764_);
lean_inc(v_keyName_765_);
v___x_767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_767_, 0, v_keyName_765_);
lean_ctor_set(v___x_767_, 1, v_name_764_);
v___x_768_ = l_Lake_Module_keyword;
lean_inc(v___x_761_);
v___x_769_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
lean_ctor_set(v___x_769_, 2, v___x_761_);
lean_ctor_set(v___x_769_, 3, v___x_766_);
lean_inc_ref(v___y_753_);
lean_inc_ref(v___y_757_);
lean_inc_ref(v___y_756_);
lean_inc(v___y_755_);
lean_inc(v___y_754_);
v___x_770_ = lean_apply_7(v___y_753_, v___x_769_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, lean_box(0));
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v_a_772_; lean_object* v___x_773_; size_t v___x_774_; size_t v___x_775_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
v_a_772_ = lean_ctor_get(v___x_770_, 1);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_770_, 2);
v___x_773_ = l_Lake_Job_mix___redArg(v_b_752_, v_a_771_);
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_750_, v___x_774_);
v_i_750_ = v___x_775_;
v_b_752_ = v___x_773_;
v___y_758_ = v_a_772_;
goto _start;
}
else
{
lean_object* v_a_777_; lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v___y_753_);
lean_dec_ref(v_b_752_);
v_a_777_ = lean_ctor_get(v___x_770_, 0);
v_a_778_ = lean_ctor_get(v___x_770_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_770_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_inc(v_a_777_);
lean_dec(v___x_770_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_777_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v___x_786_; 
lean_dec_ref(v___y_753_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v_b_752_);
lean_ctor_set(v___x_786_, 1, v___y_758_);
return v___x_786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0___boxed(lean_object* v_as_787_, lean_object* v_i_788_, lean_object* v_stop_789_, lean_object* v_b_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
size_t v_i_boxed_798_; size_t v_stop_boxed_799_; lean_object* v_res_800_; 
v_i_boxed_798_ = lean_unbox_usize(v_i_788_);
lean_dec(v_i_788_);
v_stop_boxed_799_ = lean_unbox_usize(v_stop_789_);
lean_dec(v_stop_789_);
v_res_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(v_as_787_, v_i_boxed_798_, v_stop_boxed_799_, v_b_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v_as_787_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts___lam__0(lean_object* v___x_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; 
lean_inc_ref(v___y_802_);
lean_inc_ref(v___y_806_);
lean_inc_ref(v___y_805_);
lean_inc(v___y_804_);
lean_inc(v___y_803_);
v___x_809_ = lean_apply_7(v___y_802_, v___x_801_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, lean_box(0));
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v_a_811_; lean_object* v___x_812_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
v_a_811_ = lean_ctor_get(v___x_809_, 1);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_809_, 2);
v___x_812_ = l_Lake_Job_await___redArg(v_a_810_, v_a_811_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_828_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_a_814_ = lean_ctor_get(v___x_812_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_828_ == 0)
{
v___x_816_ = v___x_812_;
v_isShared_817_ = v_isSharedCheck_828_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_828_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__4);
v___x_820_ = lean_array_get_size(v_a_813_);
v___x_821_ = lean_nat_dec_lt(v___x_818_, v___x_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_823_; 
lean_dec(v_a_813_);
lean_dec_ref(v___y_802_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_819_);
v___x_823_ = v___x_816_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_a_814_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
else
{
size_t v___x_825_; size_t v___x_826_; lean_object* v___x_827_; 
lean_del_object(v___x_816_);
v___x_825_ = ((size_t)0ULL);
v___x_826_ = lean_usize_of_nat(v___x_820_);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(v_a_813_, v___x_825_, v___x_826_, v___x_819_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v_a_814_);
lean_dec(v_a_813_);
return v___x_827_;
}
}
}
else
{
lean_object* v_a_829_; lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v___y_802_);
v_a_829_ = lean_ctor_get(v___x_812_, 0);
v_a_830_ = lean_ctor_get(v___x_812_, 1);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_812_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_inc(v_a_829_);
lean_dec(v___x_812_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_829_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_object* v_a_838_; lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec_ref(v___y_802_);
v_a_838_ = lean_ctor_get(v___x_809_, 0);
v_a_839_ = lean_ctor_get(v___x_809_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_809_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_inc(v_a_838_);
lean_dec(v___x_809_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_838_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts___lam__0___boxed(lean_object* v___x_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts___lam__0(v___x_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec(v___y_849_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts(lean_object* v_self_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_pkg_864_; lean_object* v_name_865_; lean_object* v_keyName_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___f_872_; lean_object* v___x_873_; 
v_pkg_864_ = lean_ctor_get(v_self_856_, 0);
v_name_865_ = lean_ctor_get(v_self_856_, 1);
v_keyName_866_ = lean_ctor_get(v_pkg_864_, 2);
v___x_867_ = l_Lake_instDataKindUnit;
v___x_868_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_865_);
lean_inc(v_keyName_866_);
v___x_869_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_869_, 0, v_keyName_866_);
lean_ctor_set(v___x_869_, 1, v_name_865_);
v___x_870_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_871_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
lean_ctor_set(v___x_871_, 2, v_self_856_);
lean_ctor_set(v___x_871_, 3, v___x_868_);
v___f_872_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts___lam__0___boxed), 8, 1);
lean_closure_set(v___f_872_, 0, v___x_871_);
v___x_873_ = l_Lake_ensureJob___redArg(v___x_867_, v___f_872_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts___boxed(lean_object* v_self_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts(v_self_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec(v_a_876_);
return v_res_882_;
}
}
static lean_object* _init_l_Lake_LeanLib_irArtsFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_884_; uint8_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___f_884_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_885_ = 1;
v___x_886_ = l_Lake_instDataKindUnit;
v___x_887_ = ((lean_object*)(l_Lake_LeanLib_irArtsFacetConfig___closed__0));
v___x_888_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_889_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_887_);
lean_ctor_set(v___x_889_, 2, v___x_886_);
lean_ctor_set(v___x_889_, 3, v___f_884_);
lean_ctor_set_uint8(v___x_889_, sizeof(void*)*4, v___x_885_);
lean_ctor_set_uint8(v___x_889_, sizeof(void*)*4 + 1, v___x_885_);
return v___x_889_;
}
}
static lean_object* _init_l_Lake_LeanLib_irArtsFacetConfig(void){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = lean_obj_once(&l_Lake_LeanLib_irArtsFacetConfig___closed__1, &l_Lake_LeanLib_irArtsFacetConfig___closed__1_once, _init_l_Lake_LeanLib_irArtsFacetConfig___closed__1);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0(lean_object* v_x_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v_pkg_899_; lean_object* v_name_900_; lean_object* v_keyName_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_pkg_899_ = lean_ctor_get(v_x_891_, 0);
v_name_900_ = lean_ctor_get(v_x_891_, 1);
v_keyName_901_ = lean_ctor_get(v_pkg_899_, 2);
v___x_902_ = l_Lake_LeanLib_irArtsFacet;
lean_inc(v_name_900_);
lean_inc(v_keyName_901_);
v___x_903_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_903_, 0, v_keyName_901_);
lean_ctor_set(v___x_903_, 1, v_name_900_);
v___x_904_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_905_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
lean_ctor_set(v___x_905_, 2, v_x_891_);
lean_ctor_set(v___x_905_, 3, v___x_902_);
lean_inc_ref(v___y_896_);
lean_inc_ref(v___y_895_);
lean_inc(v___y_894_);
lean_inc(v___y_893_);
v___x_906_ = lean_apply_7(v___y_892_, v___x_905_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, lean_box(0));
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(lean_object* v_x_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lake_LeanLib_leanArtsFacetConfig___lam__0(v_x_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec(v___y_909_);
return v_res_915_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_917_; lean_object* v___f_918_; uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___f_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_917_ = 0;
v___f_918_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_919_ = 1;
v___x_920_ = l_Lake_instDataKindUnit;
v___f_921_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_922_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_923_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___f_921_);
lean_ctor_set(v___x_923_, 2, v___x_920_);
lean_ctor_set(v___x_923_, 3, v___f_918_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*4, v___x_919_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*4 + 1, v___x_917_);
return v___x_923_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig(void){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_obj_once(&l_Lake_LeanLib_leanArtsFacetConfig___closed__1, &l_Lake_LeanLib_leanArtsFacetConfig___closed__1_once, _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__1);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(lean_object* v_a_925_, lean_object* v_x_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Lake_ModuleFacet_fetch___redArg(v_x_926_, v_a_925_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object* v_a_935_, lean_object* v_x_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(v_a_935_, v_x_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec(v___y_938_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(uint8_t v_shouldExport_945_, lean_object* v___x_946_, lean_object* v_bs_947_, lean_object* v_a_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_lib_956_; lean_object* v_config_957_; lean_object* v_nativeFacets_958_; lean_object* v___f_959_; lean_object* v___x_960_; lean_object* v___x_961_; size_t v_sz_962_; size_t v___x_963_; lean_object* v___x_195117__overap_964_; lean_object* v___x_965_; 
v_lib_956_ = lean_ctor_get(v_a_948_, 0);
v_config_957_ = lean_ctor_get(v_lib_956_, 2);
v_nativeFacets_958_ = lean_ctor_get(v_config_957_, 8);
lean_inc_ref(v_nativeFacets_958_);
v___f_959_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed), 9, 1);
lean_closure_set(v___f_959_, 0, v_a_948_);
v___x_960_ = lean_box(v_shouldExport_945_);
v___x_961_ = lean_apply_1(v_nativeFacets_958_, v___x_960_);
v_sz_962_ = lean_array_size(v___x_961_);
v___x_963_ = ((size_t)0ULL);
v___x_195117__overap_964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_946_, v___f_959_, v_sz_962_, v___x_963_, v___x_961_);
lean_inc_ref(v___y_953_);
lean_inc_ref(v___y_952_);
lean_inc(v___y_951_);
lean_inc(v___y_950_);
v___x_965_ = lean_apply_7(v___x_195117__overap_964_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, lean_box(0));
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_975_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_a_967_ = lean_ctor_get(v___x_965_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_975_ == 0)
{
v___x_969_ = v___x_965_;
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = l_Array_append___redArg(v_bs_947_, v_a_966_);
lean_dec(v_a_966_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_971_);
v___x_973_ = v___x_969_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_a_967_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
else
{
lean_dec_ref(v_bs_947_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed(lean_object* v_shouldExport_976_, lean_object* v___x_977_, lean_object* v_bs_978_, lean_object* v_a_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
uint8_t v_shouldExport_boxed_987_; lean_object* v_res_988_; 
v_shouldExport_boxed_987_ = lean_unbox(v_shouldExport_976_);
v_res_988_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(v_shouldExport_boxed_987_, v___x_977_, v_bs_978_, v_a_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec(v___y_981_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(lean_object* v___x_989_, lean_object* v_pkg_990_, lean_object* v_x_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l_Lake_Target_fetchIn___redArg(v___x_989_, v_pkg_990_, v_x_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object* v___x_1000_, lean_object* v_pkg_1001_, lean_object* v_x_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(v___x_1000_, v_pkg_1001_, v_x_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec(v___y_1004_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object* v_a_1011_, lean_object* v_x_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_log_1021_; uint8_t v_action_1022_; uint8_t v_wantsRebuild_1023_; uint8_t v_canceled_1024_; lean_object* v_trace_1025_; lean_object* v_buildTime_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_log_1021_ = lean_ctor_get(v___y_1019_, 0);
v_action_1022_ = lean_ctor_get_uint8(v___y_1019_, sizeof(void*)*3);
v_wantsRebuild_1023_ = lean_ctor_get_uint8(v___y_1019_, sizeof(void*)*3 + 1);
v_canceled_1024_ = lean_ctor_get_uint8(v___y_1019_, sizeof(void*)*3 + 2);
v_trace_1025_ = lean_ctor_get(v___y_1019_, 1);
v_buildTime_1026_ = lean_ctor_get(v___y_1019_, 2);
v___x_1027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_1028_ = lean_string_append(v___y_1013_, v___x_1027_);
v___x_1029_ = lean_io_prim_handle_put_str(v_a_1011_, v___x_1028_);
lean_dec_ref(v___x_1028_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1031_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v_a_1030_);
lean_ctor_set(v___x_1031_, 1, v___y_1019_);
return v___x_1031_;
}
else
{
lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1045_; 
lean_inc(v_buildTime_1026_);
lean_inc_ref(v_trace_1025_);
lean_inc_ref(v_log_1021_);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___y_1019_);
if (v_isSharedCheck_1045_ == 0)
{
lean_object* v_unused_1046_; lean_object* v_unused_1047_; lean_object* v_unused_1048_; 
v_unused_1046_ = lean_ctor_get(v___y_1019_, 2);
lean_dec(v_unused_1046_);
v_unused_1047_ = lean_ctor_get(v___y_1019_, 1);
lean_dec(v_unused_1047_);
v_unused_1048_ = lean_ctor_get(v___y_1019_, 0);
lean_dec(v_unused_1048_);
v___x_1033_ = v___y_1019_;
v_isShared_1034_ = v_isSharedCheck_1045_;
goto v_resetjp_1032_;
}
else
{
lean_dec(v___y_1019_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1045_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_a_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
v_a_1035_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1035_);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1036_ = lean_io_error_to_string(v_a_1035_);
v___x_1037_ = 3;
v___x_1038_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*1, v___x_1037_);
v___x_1039_ = lean_array_get_size(v_log_1021_);
v___x_1040_ = lean_array_push(v_log_1021_, v___x_1038_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1040_);
v___x_1042_ = v___x_1033_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_trace_1025_);
lean_ctor_set(v_reuseFailAlloc_1044_, 2, v_buildTime_1026_);
lean_ctor_set_uint8(v_reuseFailAlloc_1044_, sizeof(void*)*3, v_action_1022_);
lean_ctor_set_uint8(v_reuseFailAlloc_1044_, sizeof(void*)*3 + 1, v_wantsRebuild_1023_);
lean_ctor_set_uint8(v_reuseFailAlloc_1044_, sizeof(void*)*3 + 2, v_canceled_1024_);
v___x_1042_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1039_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
return v___x_1043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object* v_a_1049_, lean_object* v_x_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(v_a_1049_, v_x_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v_a_1049_);
return v_res_1059_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1067_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3));
v___x_1068_ = lean_unsigned_to_nat(5u);
v___x_1069_ = lean_mk_empty_array_with_capacity(v___x_1068_);
v___x_1070_ = lean_array_push(v___x_1069_, v___x_1067_);
return v___x_1070_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1071_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4));
v___x_1072_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6);
v___x_1073_ = lean_array_push(v___x_1072_, v___x_1071_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(uint8_t v_bootstrap_1076_, lean_object* v___y_1077_, lean_object* v_oFiles_1078_, uint8_t v_shouldExport_1079_, uint8_t v___x_1080_, lean_object* v___x_1081_, size_t v___x_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
if (v_bootstrap_1076_ == 0)
{
lean_object* v_toContext_1090_; lean_object* v_lakeEnv_1091_; lean_object* v_lean_1092_; lean_object* v_log_1093_; uint8_t v_action_1094_; uint8_t v_wantsRebuild_1095_; uint8_t v_canceled_1096_; lean_object* v_trace_1097_; lean_object* v_buildTime_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1128_; 
lean_dec_ref(v___y_1083_);
lean_dec_ref(v___x_1081_);
v_toContext_1090_ = lean_ctor_get(v___y_1087_, 1);
v_lakeEnv_1091_ = lean_ctor_get(v_toContext_1090_, 0);
v_lean_1092_ = lean_ctor_get(v_lakeEnv_1091_, 1);
v_log_1093_ = lean_ctor_get(v___y_1088_, 0);
v_action_1094_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3);
v_wantsRebuild_1095_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3 + 1);
v_canceled_1096_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3 + 2);
v_trace_1097_ = lean_ctor_get(v___y_1088_, 1);
v_buildTime_1098_ = lean_ctor_get(v___y_1088_, 2);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___y_1088_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1100_ = v___y_1088_;
v_isShared_1101_ = v_isSharedCheck_1128_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_buildTime_1098_);
lean_inc(v_trace_1097_);
lean_inc(v_log_1093_);
lean_dec(v___y_1088_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1128_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_ar_1102_; lean_object* v___x_1103_; 
v_ar_1102_ = lean_ctor_get(v_lean_1092_, 13);
lean_inc_ref(v_ar_1102_);
v___x_1103_ = l_Lake_compileStaticLib(v___y_1077_, v_oFiles_1078_, v_ar_1102_, v_bootstrap_1076_, v_log_1093_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1115_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_a_1105_ = lean_ctor_get(v___x_1103_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1107_ = v___x_1103_;
v_isShared_1108_ = v_isSharedCheck_1115_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1115_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v_a_1105_);
v___x_1110_ = v___x_1100_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1105_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_trace_1097_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_buildTime_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1114_, sizeof(void*)*3, v_action_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1114_, sizeof(void*)*3 + 1, v_wantsRebuild_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1114_, sizeof(void*)*3 + 2, v_canceled_1096_);
v___x_1110_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1112_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 1, v___x_1110_);
v___x_1112_ = v___x_1107_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1104_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v___x_1110_);
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
lean_object* v_a_1116_; lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1127_; 
v_a_1116_ = lean_ctor_get(v___x_1103_, 0);
v_a_1117_ = lean_ctor_get(v___x_1103_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1119_ = v___x_1103_;
v_isShared_1120_ = v_isSharedCheck_1127_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_inc(v_a_1116_);
lean_dec(v___x_1103_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1127_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v_a_1117_);
v___x_1122_ = v___x_1100_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1117_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_trace_1097_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_buildTime_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*3, v_action_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*3 + 1, v_wantsRebuild_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1126_, sizeof(void*)*3 + 2, v_canceled_1096_);
v___x_1122_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1124_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 1, v___x_1122_);
v___x_1124_ = v___x_1119_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1116_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
}
else
{
uint8_t v___x_1129_; 
v___x_1129_ = l_System_Platform_isOSX;
if (v___x_1129_ == 0)
{
uint8_t v___x_1130_; 
lean_dec_ref(v___y_1083_);
lean_dec_ref(v___x_1081_);
v___x_1130_ = l_System_Platform_isWindows;
if (v___x_1130_ == 0)
{
lean_object* v_toContext_1131_; lean_object* v_lakeEnv_1132_; lean_object* v_lean_1133_; lean_object* v_log_1134_; uint8_t v_action_1135_; uint8_t v_wantsRebuild_1136_; uint8_t v_canceled_1137_; lean_object* v_trace_1138_; lean_object* v_buildTime_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1169_; 
v_toContext_1131_ = lean_ctor_get(v___y_1087_, 1);
v_lakeEnv_1132_ = lean_ctor_get(v_toContext_1131_, 0);
v_lean_1133_ = lean_ctor_get(v_lakeEnv_1132_, 1);
v_log_1134_ = lean_ctor_get(v___y_1088_, 0);
v_action_1135_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3);
v_wantsRebuild_1136_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3 + 1);
v_canceled_1137_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3 + 2);
v_trace_1138_ = lean_ctor_get(v___y_1088_, 1);
v_buildTime_1139_ = lean_ctor_get(v___y_1088_, 2);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___y_1088_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1141_ = v___y_1088_;
v_isShared_1142_ = v_isSharedCheck_1169_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_buildTime_1139_);
lean_inc(v_trace_1138_);
lean_inc(v_log_1134_);
lean_dec(v___y_1088_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1169_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v_ar_1143_; lean_object* v___x_1144_; 
v_ar_1143_ = lean_ctor_get(v_lean_1133_, 13);
lean_inc_ref(v_ar_1143_);
v___x_1144_ = l_Lake_compileStaticLib(v___y_1077_, v_oFiles_1078_, v_ar_1143_, v___x_1130_, v_log_1134_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1156_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_a_1146_ = lean_ctor_get(v___x_1144_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1148_ = v___x_1144_;
v_isShared_1149_ = v_isSharedCheck_1156_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1156_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v_a_1146_);
v___x_1151_ = v___x_1141_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1146_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_trace_1138_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_buildTime_1139_);
lean_ctor_set_uint8(v_reuseFailAlloc_1155_, sizeof(void*)*3, v_action_1135_);
lean_ctor_set_uint8(v_reuseFailAlloc_1155_, sizeof(void*)*3 + 1, v_wantsRebuild_1136_);
lean_ctor_set_uint8(v_reuseFailAlloc_1155_, sizeof(void*)*3 + 2, v_canceled_1137_);
v___x_1151_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1153_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v___x_1151_);
v___x_1153_ = v___x_1148_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1145_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1168_; 
v_a_1157_ = lean_ctor_get(v___x_1144_, 0);
v_a_1158_ = lean_ctor_get(v___x_1144_, 1);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1160_ = v___x_1144_;
v_isShared_1161_ = v_isSharedCheck_1168_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_inc(v_a_1157_);
lean_dec(v___x_1144_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1168_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v_a_1158_);
v___x_1163_ = v___x_1141_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1158_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_trace_1138_);
lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_buildTime_1139_);
lean_ctor_set_uint8(v_reuseFailAlloc_1167_, sizeof(void*)*3, v_action_1135_);
lean_ctor_set_uint8(v_reuseFailAlloc_1167_, sizeof(void*)*3 + 1, v_wantsRebuild_1136_);
lean_ctor_set_uint8(v_reuseFailAlloc_1167_, sizeof(void*)*3 + 2, v_canceled_1137_);
v___x_1163_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v___x_1163_);
v___x_1165_ = v___x_1160_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1157_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1170_; lean_object* v_lakeEnv_1171_; lean_object* v_lean_1172_; lean_object* v_log_1173_; uint8_t v_action_1174_; uint8_t v_wantsRebuild_1175_; uint8_t v_canceled_1176_; lean_object* v_trace_1177_; lean_object* v_buildTime_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1208_; 
v_toContext_1170_ = lean_ctor_get(v___y_1087_, 1);
v_lakeEnv_1171_ = lean_ctor_get(v_toContext_1170_, 0);
v_lean_1172_ = lean_ctor_get(v_lakeEnv_1171_, 1);
v_log_1173_ = lean_ctor_get(v___y_1088_, 0);
v_action_1174_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3);
v_wantsRebuild_1175_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3 + 1);
v_canceled_1176_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3 + 2);
v_trace_1177_ = lean_ctor_get(v___y_1088_, 1);
v_buildTime_1178_ = lean_ctor_get(v___y_1088_, 2);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___y_1088_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1180_ = v___y_1088_;
v_isShared_1181_ = v_isSharedCheck_1208_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_buildTime_1178_);
lean_inc(v_trace_1177_);
lean_inc(v_log_1173_);
lean_dec(v___y_1088_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1208_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_ar_1182_; lean_object* v___x_1183_; 
v_ar_1182_ = lean_ctor_get(v_lean_1172_, 13);
lean_inc_ref(v_ar_1182_);
v___x_1183_ = l_Lake_compileStaticLib(v___y_1077_, v_oFiles_1078_, v_ar_1182_, v_shouldExport_1079_, v_log_1173_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1195_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
v_a_1185_ = lean_ctor_get(v___x_1183_, 1);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1187_ = v___x_1183_;
v_isShared_1188_ = v_isSharedCheck_1195_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_inc(v_a_1184_);
lean_dec(v___x_1183_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1195_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v_a_1185_);
v___x_1190_ = v___x_1180_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1185_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_trace_1177_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_buildTime_1178_);
lean_ctor_set_uint8(v_reuseFailAlloc_1194_, sizeof(void*)*3, v_action_1174_);
lean_ctor_set_uint8(v_reuseFailAlloc_1194_, sizeof(void*)*3 + 1, v_wantsRebuild_1175_);
lean_ctor_set_uint8(v_reuseFailAlloc_1194_, sizeof(void*)*3 + 2, v_canceled_1176_);
v___x_1190_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 1, v___x_1190_);
v___x_1192_ = v___x_1187_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1184_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1207_; 
v_a_1196_ = lean_ctor_get(v___x_1183_, 0);
v_a_1197_ = lean_ctor_get(v___x_1183_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1199_ = v___x_1183_;
v_isShared_1200_ = v_isSharedCheck_1207_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_inc(v_a_1196_);
lean_dec(v___x_1183_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1207_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v_a_1197_);
v___x_1202_ = v___x_1180_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1197_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_trace_1177_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_buildTime_1178_);
lean_ctor_set_uint8(v_reuseFailAlloc_1206_, sizeof(void*)*3, v_action_1174_);
lean_ctor_set_uint8(v_reuseFailAlloc_1206_, sizeof(void*)*3 + 1, v_wantsRebuild_1175_);
lean_ctor_set_uint8(v_reuseFailAlloc_1206_, sizeof(void*)*3 + 2, v_canceled_1176_);
v___x_1202_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1204_; 
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 1, v___x_1202_);
v___x_1204_ = v___x_1199_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1196_);
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
}
}
else
{
lean_object* v_log_1209_; uint8_t v_action_1210_; uint8_t v_wantsRebuild_1211_; uint8_t v_canceled_1212_; lean_object* v_trace_1213_; lean_object* v_buildTime_1214_; lean_object* v___x_1215_; 
v_log_1209_ = lean_ctor_get(v___y_1088_, 0);
v_action_1210_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3);
v_wantsRebuild_1211_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3 + 1);
v_canceled_1212_ = lean_ctor_get_uint8(v___y_1088_, sizeof(void*)*3 + 2);
v_trace_1213_ = lean_ctor_get(v___y_1088_, 1);
v_buildTime_1214_ = lean_ctor_get(v___y_1088_, 2);
lean_inc_ref(v___y_1077_);
v___x_1215_ = l_Lake_createParentDirs(v___y_1077_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v_a_1219_; uint8_t v___x_1266_; lean_object* v___x_1267_; 
lean_dec_ref_known(v___x_1215_, 1);
v___x_1216_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1077_);
v___x_1217_ = l_System_FilePath_addExtension(v___y_1077_, v___x_1216_);
v___x_1266_ = 1;
v___x_1267_ = lean_io_prim_handle_mk(v___x_1217_, v___x_1266_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1268_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1269_ = lean_unsigned_to_nat(0u);
v___x_1270_ = lean_array_get_size(v_oFiles_1078_);
v___x_1271_ = lean_nat_dec_lt(v___x_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_dec(v_a_1268_);
lean_dec_ref(v___y_1083_);
lean_dec_ref(v___x_1081_);
lean_dec_ref(v_oFiles_1078_);
v_a_1219_ = v___y_1088_;
goto v___jp_1218_;
}
else
{
lean_object* v___f_1272_; lean_object* v___x_1273_; size_t v___x_1274_; lean_object* v___x_195266__overap_1275_; lean_object* v___x_1276_; 
v___f_1272_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1272_, 0, v_a_1268_);
v___x_1273_ = lean_box(0);
v___x_1274_ = lean_usize_of_nat(v___x_1270_);
v___x_195266__overap_1275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1081_, v___f_1272_, v_oFiles_1078_, v___x_1082_, v___x_1274_, v___x_1273_);
lean_inc_ref(v___y_1087_);
lean_inc_ref(v___y_1086_);
lean_inc(v___y_1085_);
lean_inc(v___y_1084_);
v___x_1276_ = lean_apply_7(v___x_195266__overap_1275_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, lean_box(0));
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 1);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 2);
v_a_1219_ = v_a_1277_;
goto v___jp_1218_;
}
else
{
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___y_1077_);
return v___x_1276_;
}
}
}
else
{
lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1291_; 
lean_inc(v_buildTime_1214_);
lean_inc_ref(v_trace_1213_);
lean_inc_ref(v_log_1209_);
lean_dec_ref(v___x_1217_);
lean_dec_ref(v___y_1083_);
lean_dec_ref(v___x_1081_);
lean_dec_ref(v_oFiles_1078_);
lean_dec_ref(v___y_1077_);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___y_1088_);
if (v_isSharedCheck_1291_ == 0)
{
lean_object* v_unused_1292_; lean_object* v_unused_1293_; lean_object* v_unused_1294_; 
v_unused_1292_ = lean_ctor_get(v___y_1088_, 2);
lean_dec(v_unused_1292_);
v_unused_1293_ = lean_ctor_get(v___y_1088_, 1);
lean_dec(v_unused_1293_);
v_unused_1294_ = lean_ctor_get(v___y_1088_, 0);
lean_dec(v_unused_1294_);
v___x_1279_ = v___y_1088_;
v_isShared_1280_ = v_isSharedCheck_1291_;
goto v_resetjp_1278_;
}
else
{
lean_dec(v___y_1088_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1291_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_a_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v_a_1281_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1267_, 1);
v___x_1282_ = lean_io_error_to_string(v_a_1281_);
v___x_1283_ = 3;
v___x_1284_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set_uint8(v___x_1284_, sizeof(void*)*1, v___x_1283_);
v___x_1285_ = lean_array_get_size(v_log_1209_);
v___x_1286_ = lean_array_push(v_log_1209_, v___x_1284_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1286_);
v___x_1288_ = v___x_1279_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_trace_1213_);
lean_ctor_set(v_reuseFailAlloc_1290_, 2, v_buildTime_1214_);
lean_ctor_set_uint8(v_reuseFailAlloc_1290_, sizeof(void*)*3, v_action_1210_);
lean_ctor_set_uint8(v_reuseFailAlloc_1290_, sizeof(void*)*3 + 1, v_wantsRebuild_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1290_, sizeof(void*)*3 + 2, v_canceled_1212_);
v___x_1288_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; 
v___x_1289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1285_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
return v___x_1289_;
}
}
}
v___jp_1218_:
{
lean_object* v___x_1220_; lean_object* v_log_1221_; uint8_t v_action_1222_; uint8_t v_wantsRebuild_1223_; uint8_t v_canceled_1224_; lean_object* v_trace_1225_; lean_object* v_buildTime_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1265_; 
v___x_1220_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1221_ = lean_ctor_get(v_a_1219_, 0);
v_action_1222_ = lean_ctor_get_uint8(v_a_1219_, sizeof(void*)*3);
v_wantsRebuild_1223_ = lean_ctor_get_uint8(v_a_1219_, sizeof(void*)*3 + 1);
v_canceled_1224_ = lean_ctor_get_uint8(v_a_1219_, sizeof(void*)*3 + 2);
v_trace_1225_ = lean_ctor_get(v_a_1219_, 1);
v_buildTime_1226_ = lean_ctor_get(v_a_1219_, 2);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_a_1219_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1228_ = v_a_1219_;
v_isShared_1229_ = v_isSharedCheck_1265_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_buildTime_1226_);
lean_inc(v_trace_1225_);
lean_inc(v_log_1221_);
lean_dec(v_a_1219_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1265_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1230_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1231_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1232_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1233_ = lean_array_push(v___x_1232_, v___y_1077_);
v___x_1234_ = lean_array_push(v___x_1233_, v___x_1231_);
v___x_1235_ = lean_array_push(v___x_1234_, v___x_1217_);
v___x_1236_ = lean_box(0);
v___x_1237_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1238_ = 0;
v___x_1239_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1239_, 0, v___x_1220_);
lean_ctor_set(v___x_1239_, 1, v___x_1230_);
lean_ctor_set(v___x_1239_, 2, v___x_1235_);
lean_ctor_set(v___x_1239_, 3, v___x_1236_);
lean_ctor_set(v___x_1239_, 4, v___x_1237_);
lean_ctor_set_uint8(v___x_1239_, sizeof(void*)*5, v___x_1080_);
lean_ctor_set_uint8(v___x_1239_, sizeof(void*)*5 + 1, v___x_1238_);
v___x_1240_ = l_Lake_proc(v___x_1239_, v___x_1238_, v___x_1236_, v_log_1221_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1252_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_a_1242_ = lean_ctor_get(v___x_1240_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1244_ = v___x_1240_;
v_isShared_1245_ = v_isSharedCheck_1252_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1252_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v_a_1242_);
v___x_1247_ = v___x_1228_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1242_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_trace_1225_);
lean_ctor_set(v_reuseFailAlloc_1251_, 2, v_buildTime_1226_);
lean_ctor_set_uint8(v_reuseFailAlloc_1251_, sizeof(void*)*3, v_action_1222_);
lean_ctor_set_uint8(v_reuseFailAlloc_1251_, sizeof(void*)*3 + 1, v_wantsRebuild_1223_);
lean_ctor_set_uint8(v_reuseFailAlloc_1251_, sizeof(void*)*3 + 2, v_canceled_1224_);
v___x_1247_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1249_; 
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1247_);
v___x_1249_ = v___x_1244_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1241_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
else
{
lean_object* v_a_1253_; lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1264_; 
v_a_1253_ = lean_ctor_get(v___x_1240_, 0);
v_a_1254_ = lean_ctor_get(v___x_1240_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1256_ = v___x_1240_;
v_isShared_1257_ = v_isSharedCheck_1264_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_inc(v_a_1253_);
lean_dec(v___x_1240_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1264_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v_a_1254_);
v___x_1259_ = v___x_1228_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1254_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_trace_1225_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_buildTime_1226_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*3, v_action_1222_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*3 + 1, v_wantsRebuild_1223_);
lean_ctor_set_uint8(v_reuseFailAlloc_1263_, sizeof(void*)*3 + 2, v_canceled_1224_);
v___x_1259_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1261_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v___x_1259_);
v___x_1261_ = v___x_1256_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1253_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1308_; 
lean_inc(v_buildTime_1214_);
lean_inc_ref(v_trace_1213_);
lean_inc_ref(v_log_1209_);
lean_dec_ref(v___y_1083_);
lean_dec_ref(v___x_1081_);
lean_dec_ref(v_oFiles_1078_);
lean_dec_ref(v___y_1077_);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___y_1088_);
if (v_isSharedCheck_1308_ == 0)
{
lean_object* v_unused_1309_; lean_object* v_unused_1310_; lean_object* v_unused_1311_; 
v_unused_1309_ = lean_ctor_get(v___y_1088_, 2);
lean_dec(v_unused_1309_);
v_unused_1310_ = lean_ctor_get(v___y_1088_, 1);
lean_dec(v_unused_1310_);
v_unused_1311_ = lean_ctor_get(v___y_1088_, 0);
lean_dec(v_unused_1311_);
v___x_1296_ = v___y_1088_;
v_isShared_1297_ = v_isSharedCheck_1308_;
goto v_resetjp_1295_;
}
else
{
lean_dec(v___y_1088_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1308_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_a_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v_a_1298_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1215_, 1);
v___x_1299_ = lean_io_error_to_string(v_a_1298_);
v___x_1300_ = 3;
v___x_1301_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set_uint8(v___x_1301_, sizeof(void*)*1, v___x_1300_);
v___x_1302_ = lean_array_get_size(v_log_1209_);
v___x_1303_ = lean_array_push(v_log_1209_, v___x_1301_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1303_);
v___x_1305_ = v___x_1296_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_trace_1213_);
lean_ctor_set(v_reuseFailAlloc_1307_, 2, v_buildTime_1214_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, sizeof(void*)*3, v_action_1210_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, sizeof(void*)*3 + 1, v_wantsRebuild_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1307_, sizeof(void*)*3 + 2, v_canceled_1212_);
v___x_1305_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1302_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
return v___x_1306_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object* v_bootstrap_1312_, lean_object* v___y_1313_, lean_object* v_oFiles_1314_, lean_object* v_shouldExport_1315_, lean_object* v___x_1316_, lean_object* v___x_1317_, lean_object* v___x_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
uint8_t v_bootstrap_boxed_1326_; uint8_t v_shouldExport_boxed_1327_; uint8_t v___x_195640__boxed_1328_; size_t v___x_195642__boxed_1329_; lean_object* v_res_1330_; 
v_bootstrap_boxed_1326_ = lean_unbox(v_bootstrap_1312_);
v_shouldExport_boxed_1327_ = lean_unbox(v_shouldExport_1315_);
v___x_195640__boxed_1328_ = lean_unbox(v___x_1316_);
v___x_195642__boxed_1329_ = lean_unbox_usize(v___x_1318_);
lean_dec(v___x_1318_);
v_res_1330_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(v_bootstrap_boxed_1326_, v___y_1313_, v_oFiles_1314_, v_shouldExport_boxed_1327_, v___x_195640__boxed_1328_, v___x_1317_, v___x_195642__boxed_1329_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec(v___y_1320_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(uint8_t v_bootstrap_1332_, lean_object* v___y_1333_, uint8_t v_shouldExport_1334_, uint8_t v___x_1335_, lean_object* v___x_1336_, size_t v___x_1337_, lean_object* v_oFiles_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___y_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1346_ = lean_box(v_bootstrap_1332_);
v___x_1347_ = lean_box(v_shouldExport_1334_);
v___x_1348_ = lean_box(v___x_1335_);
v___x_1349_ = lean_box_usize(v___x_1337_);
lean_inc_ref(v___y_1333_);
v___y_1350_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed), 14, 7);
lean_closure_set(v___y_1350_, 0, v___x_1346_);
lean_closure_set(v___y_1350_, 1, v___y_1333_);
lean_closure_set(v___y_1350_, 2, v_oFiles_1338_);
lean_closure_set(v___y_1350_, 3, v___x_1347_);
lean_closure_set(v___y_1350_, 4, v___x_1348_);
lean_closure_set(v___y_1350_, 5, v___x_1336_);
lean_closure_set(v___y_1350_, 6, v___x_1349_);
v___x_1351_ = 0;
v___x_1352_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1353_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1333_, v___y_1350_, v___x_1351_, v___x_1352_, v___x_1335_, v___x_1351_, v___x_1351_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1363_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
v_a_1355_ = lean_ctor_get(v___x_1353_, 1);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1357_ = v___x_1353_;
v_isShared_1358_ = v_isSharedCheck_1363_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_inc(v_a_1354_);
lean_dec(v___x_1353_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1363_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v_path_1359_; lean_object* v___x_1361_; 
v_path_1359_ = lean_ctor_get(v_a_1354_, 1);
lean_inc_ref(v_path_1359_);
lean_dec(v_a_1354_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v_path_1359_);
v___x_1361_ = v___x_1357_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_path_1359_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_a_1355_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
v_a_1364_ = lean_ctor_get(v___x_1353_, 0);
v_a_1365_ = lean_ctor_get(v___x_1353_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1353_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_inc(v_a_1364_);
lean_dec(v___x_1353_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1364_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object* v_bootstrap_1373_, lean_object* v___y_1374_, lean_object* v_shouldExport_1375_, lean_object* v___x_1376_, lean_object* v___x_1377_, lean_object* v___x_1378_, lean_object* v_oFiles_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
uint8_t v_bootstrap_boxed_1387_; uint8_t v_shouldExport_boxed_1388_; uint8_t v___x_196053__boxed_1389_; size_t v___x_196055__boxed_1390_; lean_object* v_res_1391_; 
v_bootstrap_boxed_1387_ = lean_unbox(v_bootstrap_1373_);
v_shouldExport_boxed_1388_ = lean_unbox(v_shouldExport_1375_);
v___x_196053__boxed_1389_ = lean_unbox(v___x_1376_);
v___x_196055__boxed_1390_ = lean_unbox_usize(v___x_1378_);
lean_dec(v___x_1378_);
v_res_1391_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(v_bootstrap_boxed_1387_, v___y_1374_, v_shouldExport_boxed_1388_, v___x_196053__boxed_1389_, v___x_1377_, v___x_196055__boxed_1390_, v_oFiles_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec(v___y_1381_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object* v_config_1396_, lean_object* v_config_1397_, uint8_t v_shouldExport_1398_, uint8_t v___x_1399_, lean_object* v___x_1400_, lean_object* v___x_1401_, lean_object* v___x_1402_, lean_object* v___x_1403_, lean_object* v___f_1404_, lean_object* v_dir_1405_, lean_object* v_self_1406_, lean_object* v___x_1407_, lean_object* v___f_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
uint8_t v___y_1417_; size_t v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v_a_1437_; lean_object* v_a_1438_; lean_object* v___x_1481_; 
lean_inc_ref(v___y_1409_);
lean_inc_ref(v___y_1413_);
lean_inc_ref(v___y_1412_);
lean_inc(v___y_1411_);
lean_inc(v___x_1402_);
v___x_1481_ = lean_apply_7(v___y_1409_, v___x_1407_, v___x_1402_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, lean_box(0));
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v_a_1483_; lean_object* v___x_1484_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
v_a_1483_ = lean_ctor_get(v___x_1481_, 1);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___x_1481_, 2);
v___x_1484_ = l_Lake_Job_await___redArg(v_a_1482_, v_a_1483_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v_a_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_a_1485_);
v_a_1486_ = lean_ctor_get(v___x_1484_, 1);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1484_, 2);
v___x_1487_ = lean_unsigned_to_nat(0u);
v___x_1488_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_1489_ = lean_array_get_size(v_a_1485_);
v___x_1490_ = lean_nat_dec_lt(v___x_1487_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_dec(v_a_1485_);
lean_dec_ref(v___f_1408_);
v_a_1437_ = v___x_1488_;
v_a_1438_ = v_a_1486_;
goto v___jp_1436_;
}
else
{
size_t v___x_1491_; size_t v___x_1492_; lean_object* v___x_195400__overap_1493_; lean_object* v___x_1494_; 
v___x_1491_ = ((size_t)0ULL);
v___x_1492_ = lean_usize_of_nat(v___x_1489_);
lean_inc_ref(v___x_1403_);
v___x_195400__overap_1493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1403_, v___f_1408_, v_a_1485_, v___x_1491_, v___x_1492_, v___x_1488_);
lean_inc_ref(v___y_1413_);
lean_inc_ref(v___y_1412_);
lean_inc(v___y_1411_);
lean_inc(v___x_1402_);
lean_inc_ref(v___y_1409_);
v___x_1494_ = lean_apply_7(v___x_195400__overap_1493_, v___y_1409_, v___x_1402_, v___y_1411_, v___y_1412_, v___y_1413_, v_a_1486_, lean_box(0));
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v_a_1496_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
v_a_1496_ = lean_ctor_get(v___x_1494_, 1);
lean_inc(v_a_1496_);
lean_dec_ref_known(v___x_1494_, 2);
v_a_1437_ = v_a_1495_;
v_a_1438_ = v_a_1496_;
goto v___jp_1436_;
}
else
{
lean_object* v_a_1497_; lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec_ref(v___y_1409_);
lean_dec_ref(v_self_1406_);
lean_dec_ref(v_dir_1405_);
lean_dec_ref(v___f_1404_);
lean_dec_ref(v___x_1403_);
lean_dec(v___x_1402_);
lean_dec(v___x_1401_);
lean_dec_ref(v___x_1400_);
lean_dec_ref(v_config_1396_);
v_a_1497_ = lean_ctor_get(v___x_1494_, 0);
v_a_1498_ = lean_ctor_get(v___x_1494_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1494_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_inc(v_a_1497_);
lean_dec(v___x_1494_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1497_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec_ref(v___y_1409_);
lean_dec_ref(v___f_1408_);
lean_dec_ref(v_self_1406_);
lean_dec_ref(v_dir_1405_);
lean_dec_ref(v___f_1404_);
lean_dec_ref(v___x_1403_);
lean_dec(v___x_1402_);
lean_dec(v___x_1401_);
lean_dec_ref(v___x_1400_);
lean_dec_ref(v_config_1396_);
v_a_1506_ = lean_ctor_get(v___x_1484_, 0);
v_a_1507_ = lean_ctor_get(v___x_1484_, 1);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1484_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_inc(v_a_1506_);
lean_dec(v___x_1484_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1506_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec_ref(v___y_1409_);
lean_dec_ref(v___f_1408_);
lean_dec_ref(v_self_1406_);
lean_dec_ref(v_dir_1405_);
lean_dec_ref(v___f_1404_);
lean_dec_ref(v___x_1403_);
lean_dec(v___x_1402_);
lean_dec(v___x_1401_);
lean_dec_ref(v___x_1400_);
lean_dec_ref(v_config_1396_);
v_a_1515_ = lean_ctor_get(v___x_1481_, 0);
v_a_1516_ = lean_ctor_get(v___x_1481_, 1);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1481_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_inc(v_a_1515_);
lean_dec(v___x_1481_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1515_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
v___jp_1416_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___f_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1423_ = lean_box(v___y_1417_);
v___x_1424_ = lean_box(v_shouldExport_1398_);
v___x_1425_ = lean_box(v___x_1399_);
v___x_1426_ = lean_box_usize(v___y_1418_);
v___f_1427_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed), 14, 6);
lean_closure_set(v___f_1427_, 0, v___x_1423_);
lean_closure_set(v___f_1427_, 1, v___y_1422_);
lean_closure_set(v___f_1427_, 2, v___x_1424_);
lean_closure_set(v___f_1427_, 3, v___x_1425_);
lean_closure_set(v___f_1427_, 4, v___x_1400_);
lean_closure_set(v___f_1427_, 5, v___x_1426_);
v___x_1428_ = l_Array_append___redArg(v___y_1420_, v___y_1421_);
lean_dec_ref(v___y_1421_);
v___x_1429_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_1430_ = l_Lake_Job_collectArray___redArg(v___x_1428_, v___x_1429_);
lean_dec_ref(v___x_1428_);
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = 0;
v___x_1433_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_1434_ = l_Lake_Job_mapM___redArg(v___x_1401_, v___x_1430_, v___f_1427_, v___x_1431_, v___x_1432_, v___y_1409_, v___x_1402_, v___y_1411_, v___y_1412_, v___y_1413_, v___x_1433_);
lean_dec(v___x_1402_);
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
lean_ctor_set(v___x_1435_, 1, v___y_1419_);
return v___x_1435_;
}
v___jp_1436_:
{
lean_object* v_toLeanConfig_1439_; lean_object* v_toLeanConfig_1440_; uint8_t v_bootstrap_1441_; lean_object* v_buildDir_1442_; lean_object* v_nativeLibDir_1443_; lean_object* v_moreLinkObjs_1444_; lean_object* v_moreLinkObjs_1445_; lean_object* v___x_1446_; size_t v_sz_1447_; size_t v___x_1448_; lean_object* v___x_195358__overap_1449_; lean_object* v___x_1450_; 
v_toLeanConfig_1439_ = lean_ctor_get(v_config_1396_, 1);
lean_inc_ref(v_toLeanConfig_1439_);
v_toLeanConfig_1440_ = lean_ctor_get(v_config_1397_, 0);
v_bootstrap_1441_ = lean_ctor_get_uint8(v_config_1396_, sizeof(void*)*29);
v_buildDir_1442_ = lean_ctor_get(v_config_1396_, 5);
lean_inc_ref(v_buildDir_1442_);
v_nativeLibDir_1443_ = lean_ctor_get(v_config_1396_, 7);
lean_inc_ref(v_nativeLibDir_1443_);
lean_dec_ref(v_config_1396_);
v_moreLinkObjs_1444_ = lean_ctor_get(v_toLeanConfig_1439_, 6);
lean_inc_ref(v_moreLinkObjs_1444_);
lean_dec_ref(v_toLeanConfig_1439_);
v_moreLinkObjs_1445_ = lean_ctor_get(v_toLeanConfig_1440_, 6);
v___x_1446_ = l_Array_append___redArg(v_moreLinkObjs_1444_, v_moreLinkObjs_1445_);
v_sz_1447_ = lean_array_size(v___x_1446_);
v___x_1448_ = ((size_t)0ULL);
v___x_195358__overap_1449_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1403_, v___f_1404_, v_sz_1447_, v___x_1448_, v___x_1446_);
lean_inc_ref(v___y_1413_);
lean_inc_ref(v___y_1412_);
lean_inc(v___y_1411_);
lean_inc(v___x_1402_);
lean_inc_ref(v___y_1409_);
v___x_1450_ = lean_apply_7(v___x_195358__overap_1449_, v___y_1409_, v___x_1402_, v___y_1411_, v___y_1412_, v___y_1413_, v_a_1438_, lean_box(0));
if (lean_obj_tag(v___x_1450_) == 0)
{
if (v_shouldExport_1398_ == 0)
{
lean_object* v_a_1451_; lean_object* v_a_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
v_a_1452_ = lean_ctor_get(v___x_1450_, 1);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1450_, 2);
v___x_1453_ = l_System_FilePath_normalize(v_buildDir_1442_);
v___x_1454_ = l_Lake_joinRelative(v_dir_1405_, v___x_1453_);
v___x_1455_ = l_System_FilePath_normalize(v_nativeLibDir_1443_);
v___x_1456_ = l_Lake_joinRelative(v___x_1454_, v___x_1455_);
v___x_1457_ = l_Lake_LeanLib_libName(v_self_1406_);
v___x_1458_ = l_Lake_nameToStaticLib(v___x_1457_, v_shouldExport_1398_);
v___x_1459_ = l_Lake_joinRelative(v___x_1456_, v___x_1458_);
v___y_1417_ = v_bootstrap_1441_;
v___y_1418_ = v___x_1448_;
v___y_1419_ = v_a_1452_;
v___y_1420_ = v_a_1437_;
v___y_1421_ = v_a_1451_;
v___y_1422_ = v___x_1459_;
goto v___jp_1416_;
}
else
{
lean_object* v_a_1460_; lean_object* v_a_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_a_1460_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1460_);
v_a_1461_ = lean_ctor_get(v___x_1450_, 1);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1450_, 2);
v___x_1462_ = l_System_FilePath_normalize(v_buildDir_1442_);
v___x_1463_ = l_Lake_joinRelative(v_dir_1405_, v___x_1462_);
v___x_1464_ = l_System_FilePath_normalize(v_nativeLibDir_1443_);
v___x_1465_ = l_Lake_joinRelative(v___x_1463_, v___x_1464_);
v___x_1466_ = l_Lake_LeanLib_libName(v_self_1406_);
v___x_1467_ = 0;
v___x_1468_ = l_Lake_nameToStaticLib(v___x_1466_, v___x_1467_);
v___x_1469_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_1470_ = l_System_FilePath_addExtension(v___x_1468_, v___x_1469_);
v___x_1471_ = l_Lake_joinRelative(v___x_1465_, v___x_1470_);
v___y_1417_ = v_bootstrap_1441_;
v___y_1418_ = v___x_1448_;
v___y_1419_ = v_a_1461_;
v___y_1420_ = v_a_1437_;
v___y_1421_ = v_a_1460_;
v___y_1422_ = v___x_1471_;
goto v___jp_1416_;
}
}
else
{
lean_object* v_a_1472_; lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec_ref(v_nativeLibDir_1443_);
lean_dec_ref(v_buildDir_1442_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v___y_1409_);
lean_dec_ref(v_self_1406_);
lean_dec_ref(v_dir_1405_);
lean_dec(v___x_1402_);
lean_dec(v___x_1401_);
lean_dec_ref(v___x_1400_);
v_a_1472_ = lean_ctor_get(v___x_1450_, 0);
v_a_1473_ = lean_ctor_get(v___x_1450_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1450_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_inc(v_a_1472_);
lean_dec(v___x_1450_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1472_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed(lean_object** _args){
lean_object* v_config_1524_ = _args[0];
lean_object* v_config_1525_ = _args[1];
lean_object* v_shouldExport_1526_ = _args[2];
lean_object* v___x_1527_ = _args[3];
lean_object* v___x_1528_ = _args[4];
lean_object* v___x_1529_ = _args[5];
lean_object* v___x_1530_ = _args[6];
lean_object* v___x_1531_ = _args[7];
lean_object* v___f_1532_ = _args[8];
lean_object* v_dir_1533_ = _args[9];
lean_object* v_self_1534_ = _args[10];
lean_object* v___x_1535_ = _args[11];
lean_object* v___f_1536_ = _args[12];
lean_object* v___y_1537_ = _args[13];
lean_object* v___y_1538_ = _args[14];
lean_object* v___y_1539_ = _args[15];
lean_object* v___y_1540_ = _args[16];
lean_object* v___y_1541_ = _args[17];
lean_object* v___y_1542_ = _args[18];
lean_object* v___y_1543_ = _args[19];
_start:
{
uint8_t v_shouldExport_boxed_1544_; uint8_t v___x_196151__boxed_1545_; lean_object* v_res_1546_; 
v_shouldExport_boxed_1544_ = lean_unbox(v_shouldExport_1526_);
v___x_196151__boxed_1545_ = lean_unbox(v___x_1527_);
v_res_1546_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(v_config_1524_, v_config_1525_, v_shouldExport_boxed_1544_, v___x_196151__boxed_1545_, v___x_1528_, v___x_1529_, v___x_1530_, v___x_1531_, v___f_1532_, v_dir_1533_, v_self_1534_, v___x_1535_, v___f_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec(v_config_1525_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object* v_self_1550_, uint8_t v_shouldExport_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_){
_start:
{
lean_object* v___x_1559_; lean_object* v_toApplicative_1560_; lean_object* v_toBind_1561_; lean_object* v_toFunctor_1562_; lean_object* v_toPure_1563_; lean_object* v___f_1564_; lean_object* v___f_1565_; lean_object* v___f_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v_toBuildConfig_1577_; lean_object* v_registeredJobs_1578_; uint8_t v_verbosity_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___f_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; uint8_t v___x_1587_; lean_object* v___y_1589_; 
v___x_1559_ = l_instMonadBaseIO;
v_toApplicative_1560_ = lean_ctor_get(v___x_1559_, 0);
v_toBind_1561_ = lean_ctor_get(v___x_1559_, 1);
v_toFunctor_1562_ = lean_ctor_get(v_toApplicative_1560_, 0);
v_toPure_1563_ = lean_ctor_get(v_toApplicative_1560_, 1);
lean_inc_n(v_toBind_1561_, 3);
lean_inc_n(v_toPure_1563_, 5);
v___f_1564_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1564_, 0, v_toPure_1563_);
lean_closure_set(v___f_1564_, 1, v_toBind_1561_);
v___f_1565_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1565_, 0, v_toPure_1563_);
lean_closure_set(v___f_1565_, 1, v_toBind_1561_);
lean_inc_ref(v___f_1564_);
v___f_1566_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1566_, 0, v_toPure_1563_);
lean_closure_set(v___f_1566_, 1, v___f_1564_);
lean_inc_ref_n(v_toFunctor_1562_, 2);
v___f_1567_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1567_, 0, v_toFunctor_1562_);
lean_closure_set(v___f_1567_, 1, v_toPure_1563_);
lean_closure_set(v___f_1567_, 2, v_toBind_1561_);
v___x_1568_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1562_);
v___f_1569_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1569_, 0, v_toPure_1563_);
v___x_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set(v___x_1570_, 1, v___f_1569_);
lean_ctor_set(v___x_1570_, 2, v___f_1567_);
lean_ctor_set(v___x_1570_, 3, v___f_1566_);
lean_ctor_set(v___x_1570_, 4, v___f_1565_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___f_1564_);
v___x_1572_ = l_ReaderT_instMonad___redArg(v___x_1571_);
v___x_1573_ = l_ReaderT_instMonad___redArg(v___x_1572_);
v___x_1574_ = l_ReaderT_instMonad___redArg(v___x_1573_);
v___x_1575_ = l_ReaderT_instMonad___redArg(v___x_1574_);
v___x_1576_ = l_Lake_EquipT_instMonad___redArg(v___x_1575_);
v_toBuildConfig_1577_ = lean_ctor_get(v_a_1556_, 0);
v_registeredJobs_1578_ = lean_ctor_get(v_a_1556_, 4);
v_verbosity_1579_ = lean_ctor_get_uint8(v_toBuildConfig_1577_, sizeof(void*)*6 + 4);
v___x_1580_ = l_Lake_instDataKindFilePath;
v___x_1581_ = lean_box(v_shouldExport_1551_);
lean_inc_ref(v___x_1576_);
v___f_1582_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1582_, 0, v___x_1581_);
lean_closure_set(v___f_1582_, 1, v___x_1576_);
v___x_1583_ = lean_box(v_verbosity_1579_);
v___x_1584_ = lean_obj_tag_nat(v___x_1583_);
lean_dec(v___x_1583_);
v___x_1585_ = lean_unsigned_to_nat(2u);
v___x_1586_ = lean_nat_dec_eq(v___x_1584_, v___x_1585_);
v___x_1587_ = 1;
if (v___x_1586_ == 0)
{
lean_object* v___x_1635_; 
v___x_1635_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_1589_ = v___x_1635_;
goto v___jp_1588_;
}
else
{
if (v_shouldExport_1551_ == 0)
{
lean_object* v___x_1636_; 
v___x_1636_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___y_1589_ = v___x_1636_;
goto v___jp_1588_;
}
else
{
lean_object* v___x_1637_; 
v___x_1637_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_1589_ = v___x_1637_;
goto v___jp_1588_;
}
}
v___jp_1588_:
{
lean_object* v_pkg_1590_; lean_object* v_name_1591_; lean_object* v_config_1592_; lean_object* v_keyName_1593_; lean_object* v_dir_1594_; lean_object* v_config_1595_; lean_object* v___f_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___f_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; 
v_pkg_1590_ = lean_ctor_get(v_self_1550_, 0);
v_name_1591_ = lean_ctor_get(v_self_1550_, 1);
v_config_1592_ = lean_ctor_get(v_self_1550_, 2);
lean_inc(v_config_1592_);
v_keyName_1593_ = lean_ctor_get(v_pkg_1590_, 2);
v_dir_1594_ = lean_ctor_get(v_pkg_1590_, 4);
lean_inc_ref(v_dir_1594_);
v_config_1595_ = lean_ctor_get(v_pkg_1590_, 6);
lean_inc_ref(v_config_1595_);
lean_inc_ref_n(v_pkg_1590_, 2);
v___f_1596_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(v___f_1596_, 0, v___x_1580_);
lean_closure_set(v___f_1596_, 1, v_pkg_1590_);
lean_inc_n(v_name_1591_, 2);
v___x_1597_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1591_, v___x_1587_);
v___x_1598_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0));
v___x_1599_ = lean_string_append(v___x_1597_, v___x_1598_);
v___x_1600_ = lean_string_append(v___x_1599_, v___y_1589_);
v___x_1601_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_1593_);
v___x_1602_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1602_, 0, v_keyName_1593_);
lean_ctor_set(v___x_1602_, 1, v_name_1591_);
v___x_1603_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_1550_);
v___x_1604_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
lean_ctor_set(v___x_1604_, 2, v_self_1550_);
lean_ctor_set(v___x_1604_, 3, v___x_1601_);
v___x_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1605_, 0, v_pkg_1590_);
v___x_1606_ = lean_box(v_shouldExport_1551_);
v___x_1607_ = lean_box(v___x_1587_);
lean_inc_ref(v___x_1576_);
v___f_1608_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed), 20, 13);
lean_closure_set(v___f_1608_, 0, v_config_1595_);
lean_closure_set(v___f_1608_, 1, v_config_1592_);
lean_closure_set(v___f_1608_, 2, v___x_1606_);
lean_closure_set(v___f_1608_, 3, v___x_1607_);
lean_closure_set(v___f_1608_, 4, v___x_1576_);
lean_closure_set(v___f_1608_, 5, v___x_1580_);
lean_closure_set(v___f_1608_, 6, v___x_1605_);
lean_closure_set(v___f_1608_, 7, v___x_1576_);
lean_closure_set(v___f_1608_, 8, v___f_1596_);
lean_closure_set(v___f_1608_, 9, v_dir_1594_);
lean_closure_set(v___f_1608_, 10, v_self_1550_);
lean_closure_set(v___f_1608_, 11, v___x_1604_);
lean_closure_set(v___f_1608_, 12, v___f_1582_);
v___x_1609_ = 0;
v___x_1610_ = l_Lake_ensureJob___redArg(v___x_1580_, v___f_1608_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1634_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_a_1612_ = lean_ctor_get(v___x_1610_, 1);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1614_ = v___x_1610_;
v_isShared_1615_ = v_isSharedCheck_1634_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1634_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v_task_1616_; lean_object* v_kind_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1632_; 
v_task_1616_ = lean_ctor_get(v_a_1611_, 0);
v_kind_1617_ = lean_ctor_get(v_a_1611_, 1);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_a_1611_);
if (v_isSharedCheck_1632_ == 0)
{
lean_object* v_unused_1633_; 
v_unused_1633_ = lean_ctor_get(v_a_1611_, 2);
lean_dec(v_unused_1633_);
v___x_1619_ = v_a_1611_;
v_isShared_1620_ = v_isSharedCheck_1632_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_kind_1617_);
lean_inc(v_task_1616_);
lean_dec(v_a_1611_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1632_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v_job_1622_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 2, v___x_1600_);
v_job_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_task_1616_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_kind_1617_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v___x_1600_);
v_job_1622_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_ctor_set_uint8(v_job_1622_, sizeof(void*)*3, v___x_1609_);
v___x_1623_ = lean_st_ref_take(v_registeredJobs_1578_);
lean_inc_ref(v_job_1622_);
v___x_1624_ = l_Lake_Job_toOpaque___redArg(v_job_1622_);
v___x_1625_ = lean_array_push(v___x_1623_, v___x_1624_);
v___x_1626_ = lean_st_ref_put(v_registeredJobs_1578_, v___x_1625_);
v___x_1627_ = l_Lake_Job_renew___redArg(v_job_1622_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1627_);
v___x_1629_ = v___x_1614_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_a_1612_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1600_);
return v___x_1610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object* v_self_1638_, lean_object* v_shouldExport_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
uint8_t v_shouldExport_boxed_1647_; lean_object* v_res_1648_; 
v_shouldExport_boxed_1647_ = lean_unbox(v_shouldExport_1639_);
v_res_1648_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1638_, v_shouldExport_boxed_1647_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec(v_a_1641_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t v_fmt_1649_, lean_object* v_a_1650_){
_start:
{
if (v_fmt_1649_ == 0)
{
return v_a_1650_;
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1651_ = l_Lake_mkRelPathString(v_a_1650_);
v___x_1652_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
v___x_1653_ = l_Lean_Json_compress(v___x_1652_);
return v___x_1653_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object* v_fmt_1654_, lean_object* v_a_1655_){
_start:
{
uint8_t v_fmt_boxed_1656_; lean_object* v_res_1657_; 
v_fmt_boxed_1656_ = lean_unbox(v_fmt_1654_);
v_res_1657_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_boxed_1656_, v_a_1655_);
return v_res_1657_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2(void){
_start:
{
uint8_t v___x_1660_; lean_object* v_name_1661_; lean_object* v___x_1662_; 
v___x_1660_ = 1;
v_name_1661_ = l_Lake_instDataKindFilePath;
v___x_1662_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1661_, v___x_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* v_defaultPkg_1666_, lean_object* v_self_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_name_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; 
v_name_1675_ = l_Lake_instDataKindFilePath;
v___x_1676_ = 1;
lean_inc_ref_n(v_self_1667_, 2);
v___x_1677_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1666_, v_self_1667_, v_self_1667_, v___x_1676_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1719_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_a_1679_ = lean_ctor_get(v___x_1677_, 1);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1681_ = v___x_1677_;
v_isShared_1682_ = v_isSharedCheck_1719_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1719_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___y_1684_; lean_object* v_snd_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1717_; 
v_snd_1702_ = lean_ctor_get(v_a_1678_, 1);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_a_1678_);
if (v_isSharedCheck_1717_ == 0)
{
lean_object* v_unused_1718_; 
v_unused_1718_ = lean_ctor_get(v_a_1678_, 0);
lean_dec(v_unused_1718_);
v___x_1704_ = v_a_1678_;
v_isShared_1705_ = v_isSharedCheck_1717_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_snd_1702_);
lean_dec(v_a_1678_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1717_;
goto v_resetjp_1703_;
}
v___jp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1685_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1686_ = l_Lake_PartialBuildKey_toString(v_self_1667_);
v___x_1687_ = lean_string_append(v___x_1685_, v___x_1686_);
lean_dec_ref(v___x_1686_);
v___x_1688_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1689_ = lean_string_append(v___x_1687_, v___x_1688_);
v___x_1690_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
v___x_1691_ = lean_string_append(v___x_1689_, v___x_1690_);
v___x_1692_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1693_ = lean_string_append(v___x_1691_, v___x_1692_);
v___x_1694_ = lean_string_append(v___x_1693_, v___y_1684_);
lean_dec_ref(v___y_1684_);
v___x_1695_ = 3;
v___x_1696_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set_uint8(v___x_1696_, sizeof(void*)*1, v___x_1695_);
v___x_1697_ = lean_array_get_size(v_a_1679_);
v___x_1698_ = lean_array_push(v_a_1679_, v___x_1696_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set_tag(v___x_1681_, 1);
lean_ctor_set(v___x_1681_, 1, v___x_1698_);
lean_ctor_set(v___x_1681_, 0, v___x_1697_);
v___x_1700_ = v___x_1681_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
v_resetjp_1703_:
{
lean_object* v_kind_1706_; uint8_t v___x_1707_; 
v_kind_1706_ = lean_ctor_get(v_snd_1702_, 1);
v___x_1707_ = lean_name_eq(v_kind_1706_, v_name_1675_);
if (v___x_1707_ == 0)
{
uint8_t v___x_1708_; 
lean_inc(v_kind_1706_);
lean_del_object(v___x_1704_);
lean_dec(v_snd_1702_);
v___x_1708_ = l_Lean_Name_isAnonymous(v_kind_1706_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1709_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1710_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1706_, v___x_1676_);
v___x_1711_ = lean_string_append(v___x_1709_, v___x_1710_);
lean_dec_ref(v___x_1710_);
v___x_1712_ = lean_string_append(v___x_1711_, v___x_1709_);
v___y_1684_ = v___x_1712_;
goto v___jp_1683_;
}
else
{
lean_object* v___x_1713_; 
lean_dec(v_kind_1706_);
v___x_1713_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1684_ = v___x_1713_;
goto v___jp_1683_;
}
}
else
{
lean_object* v___x_1715_; 
lean_del_object(v___x_1681_);
lean_dec_ref(v_self_1667_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v_a_1679_);
lean_ctor_set(v___x_1704_, 0, v_snd_1702_);
v___x_1715_ = v___x_1704_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_snd_1702_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_a_1679_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec_ref(v_self_1667_);
v_a_1720_ = lean_ctor_get(v___x_1677_, 0);
v_a_1721_ = lean_ctor_get(v___x_1677_, 1);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1677_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_inc(v_a_1720_);
lean_dec(v___x_1677_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1720_);
lean_ctor_set(v_reuseFailAlloc_1727_, 1, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* v_defaultPkg_1729_, lean_object* v_self_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1729_, v_self_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec_ref(v_a_1734_);
lean_dec(v_a_1733_);
lean_dec(v_a_1732_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* v___x_1739_, size_t v_sz_1740_, size_t v_i_1741_, lean_object* v_bs_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
uint8_t v___x_1750_; 
v___x_1750_ = lean_usize_dec_lt(v_i_1741_, v_sz_1740_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; 
lean_dec_ref(v___y_1743_);
lean_dec_ref(v___x_1739_);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v_bs_1742_);
lean_ctor_set(v___x_1751_, 1, v___y_1748_);
return v___x_1751_;
}
else
{
lean_object* v_v_1752_; lean_object* v___x_1753_; lean_object* v_bs_x27_1754_; lean_object* v___x_1755_; 
v_v_1752_ = lean_array_uget(v_bs_1742_, v_i_1741_);
v___x_1753_ = lean_unsigned_to_nat(0u);
v_bs_x27_1754_ = lean_array_uset(v_bs_1742_, v_i_1741_, v___x_1753_);
lean_inc_ref(v___y_1743_);
lean_inc_ref(v___x_1739_);
v___x_1755_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1739_, v_v_1752_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v_a_1757_; size_t v___x_1758_; size_t v___x_1759_; lean_object* v___x_1760_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
v_a_1757_ = lean_ctor_get(v___x_1755_, 1);
lean_inc(v_a_1757_);
lean_dec_ref_known(v___x_1755_, 2);
v___x_1758_ = ((size_t)1ULL);
v___x_1759_ = lean_usize_add(v_i_1741_, v___x_1758_);
v___x_1760_ = lean_array_uset(v_bs_x27_1754_, v_i_1741_, v_a_1756_);
v_i_1741_ = v___x_1759_;
v_bs_1742_ = v___x_1760_;
v___y_1748_ = v_a_1757_;
goto _start;
}
else
{
lean_object* v_a_1762_; lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec_ref(v_bs_x27_1754_);
lean_dec_ref(v___y_1743_);
lean_dec_ref(v___x_1739_);
v_a_1762_ = lean_ctor_get(v___x_1755_, 0);
v_a_1763_ = lean_ctor_get(v___x_1755_, 1);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1755_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_inc(v_a_1762_);
lean_dec(v___x_1755_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1762_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_a_1763_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* v___x_1771_, lean_object* v_sz_1772_, lean_object* v_i_1773_, lean_object* v_bs_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
size_t v_sz_boxed_1782_; size_t v_i_boxed_1783_; lean_object* v_res_1784_; 
v_sz_boxed_1782_ = lean_unbox_usize(v_sz_1772_);
lean_dec(v_sz_1772_);
v_i_boxed_1783_ = lean_unbox_usize(v_i_1773_);
lean_dec(v_i_1773_);
v_res_1784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1771_, v_sz_boxed_1782_, v_i_boxed_1783_, v_bs_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec(v___y_1776_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(lean_object* v_a_1785_, lean_object* v_as_1786_, size_t v_i_1787_, size_t v_stop_1788_, lean_object* v_b_1789_, lean_object* v___y_1790_){
_start:
{
uint8_t v___x_1792_; 
v___x_1792_ = lean_usize_dec_eq(v_i_1787_, v_stop_1788_);
if (v___x_1792_ == 0)
{
lean_object* v_log_1793_; uint8_t v_action_1794_; uint8_t v_wantsRebuild_1795_; uint8_t v_canceled_1796_; lean_object* v_trace_1797_; lean_object* v_buildTime_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_log_1793_ = lean_ctor_get(v___y_1790_, 0);
v_action_1794_ = lean_ctor_get_uint8(v___y_1790_, sizeof(void*)*3);
v_wantsRebuild_1795_ = lean_ctor_get_uint8(v___y_1790_, sizeof(void*)*3 + 1);
v_canceled_1796_ = lean_ctor_get_uint8(v___y_1790_, sizeof(void*)*3 + 2);
v_trace_1797_ = lean_ctor_get(v___y_1790_, 1);
v_buildTime_1798_ = lean_ctor_get(v___y_1790_, 2);
v___x_1799_ = lean_array_uget_borrowed(v_as_1786_, v_i_1787_);
v___x_1800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
lean_inc(v___x_1799_);
v___x_1801_ = lean_string_append(v___x_1799_, v___x_1800_);
v___x_1802_ = lean_io_prim_handle_put_str(v_a_1785_, v___x_1801_);
lean_dec_ref(v___x_1801_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; size_t v___x_1804_; size_t v___x_1805_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1802_, 1);
v___x_1804_ = ((size_t)1ULL);
v___x_1805_ = lean_usize_add(v_i_1787_, v___x_1804_);
v_i_1787_ = v___x_1805_;
v_b_1789_ = v_a_1803_;
goto _start;
}
else
{
lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1820_; 
lean_inc(v_buildTime_1798_);
lean_inc_ref(v_trace_1797_);
lean_inc_ref(v_log_1793_);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___y_1790_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; lean_object* v_unused_1822_; lean_object* v_unused_1823_; 
v_unused_1821_ = lean_ctor_get(v___y_1790_, 2);
lean_dec(v_unused_1821_);
v_unused_1822_ = lean_ctor_get(v___y_1790_, 1);
lean_dec(v_unused_1822_);
v_unused_1823_ = lean_ctor_get(v___y_1790_, 0);
lean_dec(v_unused_1823_);
v___x_1808_ = v___y_1790_;
v_isShared_1809_ = v_isSharedCheck_1820_;
goto v_resetjp_1807_;
}
else
{
lean_dec(v___y_1790_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1820_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v_a_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1817_; 
v_a_1810_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1802_, 1);
v___x_1811_ = lean_io_error_to_string(v_a_1810_);
v___x_1812_ = 3;
v___x_1813_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1813_, 0, v___x_1811_);
lean_ctor_set_uint8(v___x_1813_, sizeof(void*)*1, v___x_1812_);
v___x_1814_ = lean_array_get_size(v_log_1793_);
v___x_1815_ = lean_array_push(v_log_1793_, v___x_1813_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1815_);
v___x_1817_ = v___x_1808_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_trace_1797_);
lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_buildTime_1798_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*3, v_action_1794_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*3 + 1, v_wantsRebuild_1795_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*3 + 2, v_canceled_1796_);
v___x_1817_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1814_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
return v___x_1818_;
}
}
}
}
else
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1824_, 0, v_b_1789_);
lean_ctor_set(v___x_1824_, 1, v___y_1790_);
return v___x_1824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(lean_object* v_a_1825_, lean_object* v_as_1826_, lean_object* v_i_1827_, lean_object* v_stop_1828_, lean_object* v_b_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
size_t v_i_boxed_1832_; size_t v_stop_boxed_1833_; lean_object* v_res_1834_; 
v_i_boxed_1832_ = lean_unbox_usize(v_i_1827_);
lean_dec(v_i_1827_);
v_stop_boxed_1833_ = lean_unbox_usize(v_stop_1828_);
lean_dec(v_stop_1828_);
v_res_1834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1825_, v_as_1826_, v_i_boxed_1832_, v_stop_boxed_1833_, v_b_1829_, v___y_1830_);
lean_dec_ref(v_as_1826_);
lean_dec(v_a_1825_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(uint8_t v_bootstrap_1835_, lean_object* v___y_1836_, lean_object* v_oFiles_1837_, uint8_t v_shouldExport_1838_, uint8_t v___x_1839_, size_t v___x_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
if (v_bootstrap_1835_ == 0)
{
lean_object* v_toContext_1848_; lean_object* v_lakeEnv_1849_; lean_object* v_lean_1850_; lean_object* v_log_1851_; uint8_t v_action_1852_; uint8_t v_wantsRebuild_1853_; uint8_t v_canceled_1854_; lean_object* v_trace_1855_; lean_object* v_buildTime_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1886_; 
v_toContext_1848_ = lean_ctor_get(v___y_1845_, 1);
v_lakeEnv_1849_ = lean_ctor_get(v_toContext_1848_, 0);
v_lean_1850_ = lean_ctor_get(v_lakeEnv_1849_, 1);
v_log_1851_ = lean_ctor_get(v___y_1846_, 0);
v_action_1852_ = lean_ctor_get_uint8(v___y_1846_, sizeof(void*)*3);
v_wantsRebuild_1853_ = lean_ctor_get_uint8(v___y_1846_, sizeof(void*)*3 + 1);
v_canceled_1854_ = lean_ctor_get_uint8(v___y_1846_, sizeof(void*)*3 + 2);
v_trace_1855_ = lean_ctor_get(v___y_1846_, 1);
v_buildTime_1856_ = lean_ctor_get(v___y_1846_, 2);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___y_1846_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1858_ = v___y_1846_;
v_isShared_1859_ = v_isSharedCheck_1886_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_buildTime_1856_);
lean_inc(v_trace_1855_);
lean_inc(v_log_1851_);
lean_dec(v___y_1846_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1886_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v_ar_1860_; lean_object* v___x_1861_; 
v_ar_1860_ = lean_ctor_get(v_lean_1850_, 13);
lean_inc_ref(v_ar_1860_);
v___x_1861_ = l_Lake_compileStaticLib(v___y_1836_, v_oFiles_1837_, v_ar_1860_, v_bootstrap_1835_, v_log_1851_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1873_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
v_a_1863_ = lean_ctor_get(v___x_1861_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1865_ = v___x_1861_;
v_isShared_1866_ = v_isSharedCheck_1873_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_inc(v_a_1862_);
lean_dec(v___x_1861_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1873_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v_a_1863_);
v___x_1868_ = v___x_1858_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1863_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_trace_1855_);
lean_ctor_set(v_reuseFailAlloc_1872_, 2, v_buildTime_1856_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, sizeof(void*)*3, v_action_1852_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, sizeof(void*)*3 + 1, v_wantsRebuild_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1872_, sizeof(void*)*3 + 2, v_canceled_1854_);
v___x_1868_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1870_; 
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 1, v___x_1868_);
v___x_1870_ = v___x_1865_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1862_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1885_; 
v_a_1874_ = lean_ctor_get(v___x_1861_, 0);
v_a_1875_ = lean_ctor_get(v___x_1861_, 1);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1877_ = v___x_1861_;
v_isShared_1878_ = v_isSharedCheck_1885_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_inc(v_a_1874_);
lean_dec(v___x_1861_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1885_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v_a_1875_);
v___x_1880_ = v___x_1858_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1875_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_trace_1855_);
lean_ctor_set(v_reuseFailAlloc_1884_, 2, v_buildTime_1856_);
lean_ctor_set_uint8(v_reuseFailAlloc_1884_, sizeof(void*)*3, v_action_1852_);
lean_ctor_set_uint8(v_reuseFailAlloc_1884_, sizeof(void*)*3 + 1, v_wantsRebuild_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1884_, sizeof(void*)*3 + 2, v_canceled_1854_);
v___x_1880_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1882_; 
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 1, v___x_1880_);
v___x_1882_ = v___x_1877_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1874_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
}
else
{
uint8_t v___x_1887_; 
v___x_1887_ = l_System_Platform_isOSX;
if (v___x_1887_ == 0)
{
uint8_t v___x_1888_; 
v___x_1888_ = l_System_Platform_isWindows;
if (v___x_1888_ == 0)
{
lean_object* v_toContext_1889_; lean_object* v_lakeEnv_1890_; lean_object* v_lean_1891_; lean_object* v_log_1892_; uint8_t v_action_1893_; uint8_t v_wantsRebuild_1894_; uint8_t v_canceled_1895_; lean_object* v_trace_1896_; lean_object* v_buildTime_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1927_; 
v_toContext_1889_ = lean_ctor_get(v___y_1845_, 1);
v_lakeEnv_1890_ = lean_ctor_get(v_toContext_1889_, 0);
v_lean_1891_ = lean_ctor_get(v_lakeEnv_1890_, 1);
v_log_1892_ = lean_ctor_get(v___y_1846_, 0);
v_action_1893_ = lean_ctor_get_uint8(v___y_1846_, sizeof(void*)*3);
v_wantsRebuild_1894_ = lean_ctor_get_uint8(v___y_1846_, sizeof(void*)*3 + 1);
v_canceled_1895_ = lean_ctor_get_uint8(v___y_1846_, sizeof(void*)*3 + 2);
v_trace_1896_ = lean_ctor_get(v___y_1846_, 1);
v_buildTime_1897_ = lean_ctor_get(v___y_1846_, 2);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___y_1846_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1899_ = v___y_1846_;
v_isShared_1900_ = v_isSharedCheck_1927_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_buildTime_1897_);
lean_inc(v_trace_1896_);
lean_inc(v_log_1892_);
lean_dec(v___y_1846_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1927_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v_ar_1901_; lean_object* v___x_1902_; 
v_ar_1901_ = lean_ctor_get(v_lean_1891_, 13);
lean_inc_ref(v_ar_1901_);
v___x_1902_ = l_Lake_compileStaticLib(v___y_1836_, v_oFiles_1837_, v_ar_1901_, v___x_1888_, v_log_1892_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1914_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_a_1904_ = lean_ctor_get(v___x_1902_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1906_ = v___x_1902_;
v_isShared_1907_ = v_isSharedCheck_1914_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1914_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v_a_1904_);
v___x_1909_ = v___x_1899_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1904_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_trace_1896_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_buildTime_1897_);
lean_ctor_set_uint8(v_reuseFailAlloc_1913_, sizeof(void*)*3, v_action_1893_);
lean_ctor_set_uint8(v_reuseFailAlloc_1913_, sizeof(void*)*3 + 1, v_wantsRebuild_1894_);
lean_ctor_set_uint8(v_reuseFailAlloc_1913_, sizeof(void*)*3 + 2, v_canceled_1895_);
v___x_1909_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1911_; 
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 1, v___x_1909_);
v___x_1911_ = v___x_1906_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1903_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v___x_1909_);
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
else
{
lean_object* v_a_1915_; lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1926_; 
v_a_1915_ = lean_ctor_get(v___x_1902_, 0);
v_a_1916_ = lean_ctor_get(v___x_1902_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1918_ = v___x_1902_;
v_isShared_1919_ = v_isSharedCheck_1926_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_inc(v_a_1915_);
lean_dec(v___x_1902_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1926_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v_a_1916_);
v___x_1921_ = v___x_1899_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1916_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_trace_1896_);
lean_ctor_set(v_reuseFailAlloc_1925_, 2, v_buildTime_1897_);
lean_ctor_set_uint8(v_reuseFailAlloc_1925_, sizeof(void*)*3, v_action_1893_);
lean_ctor_set_uint8(v_reuseFailAlloc_1925_, sizeof(void*)*3 + 1, v_wantsRebuild_1894_);
lean_ctor_set_uint8(v_reuseFailAlloc_1925_, sizeof(void*)*3 + 2, v_canceled_1895_);
v___x_1921_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1923_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___x_1921_);
v___x_1923_ = v___x_1918_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1915_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1928_; lean_object* v_lakeEnv_1929_; lean_object* v_lean_1930_; lean_object* v_log_1931_; uint8_t v_action_1932_; uint8_t v_wantsRebuild_1933_; uint8_t v_canceled_1934_; lean_object* v_trace_1935_; lean_object* v_buildTime_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1966_; 
v_toContext_1928_ = lean_ctor_get(v___y_1845_, 1);
v_lakeEnv_1929_ = lean_ctor_get(v_toContext_1928_, 0);
v_lean_1930_ = lean_ctor_get(v_lakeEnv_1929_, 1);
v_log_1931_ = lean_ctor_get(v___y_1846_, 0);
v_action_1932_ = lean_ctor_get_uint8(v___y_1846_, sizeof(void*)*3);
v_wantsRebuild_1933_ = lean_ctor_get_uint8(v___y_1846_, sizeof(void*)*3 + 1);
v_canceled_1934_ = lean_ctor_get_uint8(v___y_1846_, sizeof(void*)*3 + 2);
v_trace_1935_ = lean_ctor_get(v___y_1846_, 1);
v_buildTime_1936_ = lean_ctor_get(v___y_1846_, 2);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___y_1846_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1938_ = v___y_1846_;
v_isShared_1939_ = v_isSharedCheck_1966_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_buildTime_1936_);
lean_inc(v_trace_1935_);
lean_inc(v_log_1931_);
lean_dec(v___y_1846_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1966_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v_ar_1940_; lean_object* v___x_1941_; 
v_ar_1940_ = lean_ctor_get(v_lean_1930_, 13);
lean_inc_ref(v_ar_1940_);
v___x_1941_ = l_Lake_compileStaticLib(v___y_1836_, v_oFiles_1837_, v_ar_1940_, v_shouldExport_1838_, v_log_1931_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1953_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
v_a_1943_ = lean_ctor_get(v___x_1941_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1945_ = v___x_1941_;
v_isShared_1946_ = v_isSharedCheck_1953_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_inc(v_a_1942_);
lean_dec(v___x_1941_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1953_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v_a_1943_);
v___x_1948_ = v___x_1938_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1943_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_trace_1935_);
lean_ctor_set(v_reuseFailAlloc_1952_, 2, v_buildTime_1936_);
lean_ctor_set_uint8(v_reuseFailAlloc_1952_, sizeof(void*)*3, v_action_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_1952_, sizeof(void*)*3 + 1, v_wantsRebuild_1933_);
lean_ctor_set_uint8(v_reuseFailAlloc_1952_, sizeof(void*)*3 + 2, v_canceled_1934_);
v___x_1948_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1950_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v___x_1948_);
v___x_1950_ = v___x_1945_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1942_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1965_; 
v_a_1954_ = lean_ctor_get(v___x_1941_, 0);
v_a_1955_ = lean_ctor_get(v___x_1941_, 1);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1957_ = v___x_1941_;
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_inc(v_a_1954_);
lean_dec(v___x_1941_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v_a_1955_);
v___x_1960_ = v___x_1938_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1955_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_trace_1935_);
lean_ctor_set(v_reuseFailAlloc_1964_, 2, v_buildTime_1936_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*3, v_action_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*3 + 1, v_wantsRebuild_1933_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*3 + 2, v_canceled_1934_);
v___x_1960_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v___x_1960_);
v___x_1962_ = v___x_1957_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1954_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1967_; uint8_t v_action_1968_; uint8_t v_wantsRebuild_1969_; uint8_t v_canceled_1970_; lean_object* v_trace_1971_; lean_object* v_buildTime_1972_; lean_object* v___x_1973_; 
v_log_1967_ = lean_ctor_get(v___y_1846_, 0);
v_action_1968_ = lean_ctor_get_uint8(v___y_1846_, sizeof(void*)*3);
v_wantsRebuild_1969_ = lean_ctor_get_uint8(v___y_1846_, sizeof(void*)*3 + 1);
v_canceled_1970_ = lean_ctor_get_uint8(v___y_1846_, sizeof(void*)*3 + 2);
v_trace_1971_ = lean_ctor_get(v___y_1846_, 1);
v_buildTime_1972_ = lean_ctor_get(v___y_1846_, 2);
lean_inc_ref(v___y_1836_);
v___x_1973_ = l_Lake_createParentDirs(v___y_1836_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v_a_1977_; uint8_t v___x_2026_; lean_object* v___x_2027_; 
lean_dec_ref_known(v___x_1973_, 1);
v___x_1974_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1836_);
v___x_1975_ = l_System_FilePath_addExtension(v___y_1836_, v___x_1974_);
v___x_2026_ = 1;
v___x_2027_ = lean_io_prim_handle_mk(v___x_1975_, v___x_2026_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
v___x_2029_ = lean_unsigned_to_nat(0u);
v___x_2030_ = lean_array_get_size(v_oFiles_1837_);
v___x_2031_ = lean_nat_dec_lt(v___x_2029_, v___x_2030_);
if (v___x_2031_ == 0)
{
lean_dec(v_a_2028_);
lean_dec_ref(v_oFiles_1837_);
v_a_1977_ = v___y_1846_;
goto v___jp_1976_;
}
else
{
lean_object* v___x_2032_; size_t v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = lean_box(0);
v___x_2033_ = lean_usize_of_nat(v___x_2030_);
v___x_2034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2028_, v_oFiles_1837_, v___x_1840_, v___x_2033_, v___x_2032_, v___y_1846_);
lean_dec_ref(v_oFiles_1837_);
lean_dec(v_a_2028_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 1);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 2);
v_a_1977_ = v_a_2035_;
goto v___jp_1976_;
}
else
{
lean_dec_ref(v___x_1975_);
lean_dec_ref(v___y_1836_);
return v___x_2034_;
}
}
}
else
{
lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2049_; 
lean_inc(v_buildTime_1972_);
lean_inc_ref(v_trace_1971_);
lean_inc_ref(v_log_1967_);
lean_dec_ref(v___x_1975_);
lean_dec_ref(v_oFiles_1837_);
lean_dec_ref(v___y_1836_);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___y_1846_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; lean_object* v_unused_2051_; lean_object* v_unused_2052_; 
v_unused_2050_ = lean_ctor_get(v___y_1846_, 2);
lean_dec(v_unused_2050_);
v_unused_2051_ = lean_ctor_get(v___y_1846_, 1);
lean_dec(v_unused_2051_);
v_unused_2052_ = lean_ctor_get(v___y_1846_, 0);
lean_dec(v_unused_2052_);
v___x_2037_ = v___y_1846_;
v_isShared_2038_ = v_isSharedCheck_2049_;
goto v_resetjp_2036_;
}
else
{
lean_dec(v___y_1846_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2049_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v_a_2039_; lean_object* v___x_2040_; uint8_t v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v_a_2039_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2027_, 1);
v___x_2040_ = lean_io_error_to_string(v_a_2039_);
v___x_2041_ = 3;
v___x_2042_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2042_, 0, v___x_2040_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*1, v___x_2041_);
v___x_2043_ = lean_array_get_size(v_log_1967_);
v___x_2044_ = lean_array_push(v_log_1967_, v___x_2042_);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2044_);
v___x_2046_ = v___x_2037_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_trace_1971_);
lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_buildTime_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_2048_, sizeof(void*)*3, v_action_1968_);
lean_ctor_set_uint8(v_reuseFailAlloc_2048_, sizeof(void*)*3 + 1, v_wantsRebuild_1969_);
lean_ctor_set_uint8(v_reuseFailAlloc_2048_, sizeof(void*)*3 + 2, v_canceled_1970_);
v___x_2046_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2043_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
return v___x_2047_;
}
}
}
v___jp_1976_:
{
lean_object* v___x_1978_; lean_object* v_log_1979_; uint8_t v_action_1980_; uint8_t v_wantsRebuild_1981_; uint8_t v_canceled_1982_; lean_object* v_trace_1983_; lean_object* v_buildTime_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2025_; 
v___x_1978_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1979_ = lean_ctor_get(v_a_1977_, 0);
v_action_1980_ = lean_ctor_get_uint8(v_a_1977_, sizeof(void*)*3);
v_wantsRebuild_1981_ = lean_ctor_get_uint8(v_a_1977_, sizeof(void*)*3 + 1);
v_canceled_1982_ = lean_ctor_get_uint8(v_a_1977_, sizeof(void*)*3 + 2);
v_trace_1983_ = lean_ctor_get(v_a_1977_, 1);
v_buildTime_1984_ = lean_ctor_get(v_a_1977_, 2);
v_isSharedCheck_2025_ = !lean_is_exclusive(v_a_1977_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_1986_ = v_a_1977_;
v_isShared_1987_ = v_isSharedCheck_2025_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_buildTime_1984_);
lean_inc(v_trace_1983_);
lean_inc(v_log_1979_);
lean_dec(v_a_1977_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2025_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1988_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1989_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1990_ = lean_unsigned_to_nat(5u);
v___x_1991_ = lean_mk_empty_array_with_capacity(v___x_1990_);
lean_dec_ref(v___x_1991_);
v___x_1992_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1993_ = lean_array_push(v___x_1992_, v___y_1836_);
v___x_1994_ = lean_array_push(v___x_1993_, v___x_1989_);
v___x_1995_ = lean_array_push(v___x_1994_, v___x_1975_);
v___x_1996_ = lean_box(0);
v___x_1997_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1998_ = 0;
v___x_1999_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1999_, 0, v___x_1978_);
lean_ctor_set(v___x_1999_, 1, v___x_1988_);
lean_ctor_set(v___x_1999_, 2, v___x_1995_);
lean_ctor_set(v___x_1999_, 3, v___x_1996_);
lean_ctor_set(v___x_1999_, 4, v___x_1997_);
lean_ctor_set_uint8(v___x_1999_, sizeof(void*)*5, v___x_1839_);
lean_ctor_set_uint8(v___x_1999_, sizeof(void*)*5 + 1, v___x_1998_);
v___x_2000_ = l_Lake_proc(v___x_1999_, v___x_1998_, v___x_1996_, v_log_1979_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2012_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_a_2002_ = lean_ctor_get(v___x_2000_, 1);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2004_ = v___x_2000_;
v_isShared_2005_ = v_isSharedCheck_2012_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2012_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v_a_2002_);
v___x_2007_ = v___x_1986_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2002_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_trace_1983_);
lean_ctor_set(v_reuseFailAlloc_2011_, 2, v_buildTime_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2011_, sizeof(void*)*3, v_action_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_2011_, sizeof(void*)*3 + 1, v_wantsRebuild_1981_);
lean_ctor_set_uint8(v_reuseFailAlloc_2011_, sizeof(void*)*3 + 2, v_canceled_1982_);
v___x_2007_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
lean_object* v___x_2009_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 1, v___x_2007_);
v___x_2009_ = v___x_2004_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2001_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2024_; 
v_a_2013_ = lean_ctor_get(v___x_2000_, 0);
v_a_2014_ = lean_ctor_get(v___x_2000_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2016_ = v___x_2000_;
v_isShared_2017_ = v_isSharedCheck_2024_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_inc(v_a_2013_);
lean_dec(v___x_2000_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2024_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v_a_2014_);
v___x_2019_ = v___x_1986_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2014_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_trace_1983_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_buildTime_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2023_, sizeof(void*)*3, v_action_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_2023_, sizeof(void*)*3 + 1, v_wantsRebuild_1981_);
lean_ctor_set_uint8(v_reuseFailAlloc_2023_, sizeof(void*)*3 + 2, v_canceled_1982_);
v___x_2019_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2021_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 1, v___x_2019_);
v___x_2021_ = v___x_2016_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2013_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2066_; 
lean_inc(v_buildTime_1972_);
lean_inc_ref(v_trace_1971_);
lean_inc_ref(v_log_1967_);
lean_dec_ref(v_oFiles_1837_);
lean_dec_ref(v___y_1836_);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___y_1846_);
if (v_isSharedCheck_2066_ == 0)
{
lean_object* v_unused_2067_; lean_object* v_unused_2068_; lean_object* v_unused_2069_; 
v_unused_2067_ = lean_ctor_get(v___y_1846_, 2);
lean_dec(v_unused_2067_);
v_unused_2068_ = lean_ctor_get(v___y_1846_, 1);
lean_dec(v_unused_2068_);
v_unused_2069_ = lean_ctor_get(v___y_1846_, 0);
lean_dec(v_unused_2069_);
v___x_2054_ = v___y_1846_;
v_isShared_2055_ = v_isSharedCheck_2066_;
goto v_resetjp_2053_;
}
else
{
lean_dec(v___y_1846_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2066_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_a_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
v_a_2056_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_1973_, 1);
v___x_2057_ = lean_io_error_to_string(v_a_2056_);
v___x_2058_ = 3;
v___x_2059_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2059_, 0, v___x_2057_);
lean_ctor_set_uint8(v___x_2059_, sizeof(void*)*1, v___x_2058_);
v___x_2060_ = lean_array_get_size(v_log_1967_);
v___x_2061_ = lean_array_push(v_log_1967_, v___x_2059_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2061_);
v___x_2063_ = v___x_2054_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2065_, 1, v_trace_1971_);
lean_ctor_set(v_reuseFailAlloc_2065_, 2, v_buildTime_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_2065_, sizeof(void*)*3, v_action_1968_);
lean_ctor_set_uint8(v_reuseFailAlloc_2065_, sizeof(void*)*3 + 1, v_wantsRebuild_1969_);
lean_ctor_set_uint8(v_reuseFailAlloc_2065_, sizeof(void*)*3 + 2, v_canceled_1970_);
v___x_2063_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2060_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
return v___x_2064_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object* v_bootstrap_2070_, lean_object* v___y_2071_, lean_object* v_oFiles_2072_, lean_object* v_shouldExport_2073_, lean_object* v___x_2074_, lean_object* v___x_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
uint8_t v_bootstrap_boxed_2083_; uint8_t v_shouldExport_boxed_2084_; uint8_t v___x_5907__boxed_2085_; size_t v___x_5908__boxed_2086_; lean_object* v_res_2087_; 
v_bootstrap_boxed_2083_ = lean_unbox(v_bootstrap_2070_);
v_shouldExport_boxed_2084_ = lean_unbox(v_shouldExport_2073_);
v___x_5907__boxed_2085_ = lean_unbox(v___x_2074_);
v___x_5908__boxed_2086_ = lean_unbox_usize(v___x_2075_);
lean_dec(v___x_2075_);
v_res_2087_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_boxed_2083_, v___y_2071_, v_oFiles_2072_, v_shouldExport_boxed_2084_, v___x_5907__boxed_2085_, v___x_5908__boxed_2086_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t v_bootstrap_2088_, lean_object* v___y_2089_, uint8_t v_shouldExport_2090_, uint8_t v___x_2091_, size_t v___x_2092_, lean_object* v_oFiles_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___y_2105_; uint8_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2101_ = lean_box(v_bootstrap_2088_);
v___x_2102_ = lean_box(v_shouldExport_2090_);
v___x_2103_ = lean_box(v___x_2091_);
v___x_2104_ = lean_box_usize(v___x_2092_);
lean_inc_ref(v___y_2089_);
v___y_2105_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed), 13, 6);
lean_closure_set(v___y_2105_, 0, v___x_2101_);
lean_closure_set(v___y_2105_, 1, v___y_2089_);
lean_closure_set(v___y_2105_, 2, v_oFiles_2093_);
lean_closure_set(v___y_2105_, 3, v___x_2102_);
lean_closure_set(v___y_2105_, 4, v___x_2103_);
lean_closure_set(v___y_2105_, 5, v___x_2104_);
v___x_2106_ = 0;
v___x_2107_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_2108_ = l_Lake_buildArtifactUnlessUpToDate(v___y_2089_, v___y_2105_, v___x_2106_, v___x_2107_, v___x_2091_, v___x_2106_, v___x_2106_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2118_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
v_a_2110_ = lean_ctor_get(v___x_2108_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2112_ = v___x_2108_;
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_inc(v_a_2109_);
lean_dec(v___x_2108_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v_path_2114_; lean_object* v___x_2116_; 
v_path_2114_ = lean_ctor_get(v_a_2109_, 1);
lean_inc_ref(v_path_2114_);
lean_dec(v_a_2109_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v_path_2114_);
v___x_2116_ = v___x_2112_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_path_2114_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_a_2110_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
v_a_2119_ = lean_ctor_get(v___x_2108_, 0);
v_a_2120_ = lean_ctor_get(v___x_2108_, 1);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2108_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_inc(v_a_2119_);
lean_dec(v___x_2108_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* v_bootstrap_2128_, lean_object* v___y_2129_, lean_object* v_shouldExport_2130_, lean_object* v___x_2131_, lean_object* v___x_2132_, lean_object* v_oFiles_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
uint8_t v_bootstrap_boxed_2141_; uint8_t v_shouldExport_boxed_2142_; uint8_t v___x_6307__boxed_2143_; size_t v___x_6308__boxed_2144_; lean_object* v_res_2145_; 
v_bootstrap_boxed_2141_ = lean_unbox(v_bootstrap_2128_);
v_shouldExport_boxed_2142_ = lean_unbox(v_shouldExport_2130_);
v___x_6307__boxed_2143_ = lean_unbox(v___x_2131_);
v___x_6308__boxed_2144_ = lean_unbox_usize(v___x_2132_);
lean_dec(v___x_2132_);
v_res_2145_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_boxed_2141_, v___y_2129_, v_shouldExport_boxed_2142_, v___x_6307__boxed_2143_, v___x_6308__boxed_2144_, v_oFiles_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec(v___y_2135_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* v_a_2146_, size_t v_sz_2147_, size_t v_i_2148_, lean_object* v_bs_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
uint8_t v___x_2157_; 
v___x_2157_ = lean_usize_dec_lt(v_i_2148_, v_sz_2147_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; 
lean_dec_ref(v___y_2150_);
lean_dec_ref(v_a_2146_);
v___x_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2158_, 0, v_bs_2149_);
lean_ctor_set(v___x_2158_, 1, v___y_2155_);
return v___x_2158_;
}
else
{
lean_object* v_v_2159_; lean_object* v___x_2160_; lean_object* v_bs_x27_2161_; lean_object* v___x_2162_; 
v_v_2159_ = lean_array_uget(v_bs_2149_, v_i_2148_);
v___x_2160_ = lean_unsigned_to_nat(0u);
v_bs_x27_2161_ = lean_array_uset(v_bs_2149_, v_i_2148_, v___x_2160_);
lean_inc_ref(v___y_2150_);
lean_inc_ref(v_a_2146_);
v___x_2162_ = l_Lake_ModuleFacet_fetch___redArg(v_v_2159_, v_a_2146_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v_a_2164_; size_t v___x_2165_; size_t v___x_2166_; lean_object* v___x_2167_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
v_a_2164_ = lean_ctor_get(v___x_2162_, 1);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2162_, 2);
v___x_2165_ = ((size_t)1ULL);
v___x_2166_ = lean_usize_add(v_i_2148_, v___x_2165_);
v___x_2167_ = lean_array_uset(v_bs_x27_2161_, v_i_2148_, v_a_2163_);
v_i_2148_ = v___x_2166_;
v_bs_2149_ = v___x_2167_;
v___y_2155_ = v_a_2164_;
goto _start;
}
else
{
lean_object* v_a_2169_; lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec_ref(v_bs_x27_2161_);
lean_dec_ref(v___y_2150_);
lean_dec_ref(v_a_2146_);
v_a_2169_ = lean_ctor_get(v___x_2162_, 0);
v_a_2170_ = lean_ctor_get(v___x_2162_, 1);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2162_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_inc(v_a_2169_);
lean_dec(v___x_2162_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object* v_a_2178_, lean_object* v_sz_2179_, lean_object* v_i_2180_, lean_object* v_bs_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
size_t v_sz_boxed_2189_; size_t v_i_boxed_2190_; lean_object* v_res_2191_; 
v_sz_boxed_2189_ = lean_unbox_usize(v_sz_2179_);
lean_dec(v_sz_2179_);
v_i_boxed_2190_ = lean_unbox_usize(v_i_2180_);
lean_dec(v_i_2180_);
v_res_2191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_2178_, v_sz_boxed_2189_, v_i_boxed_2190_, v_bs_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec(v___y_2183_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(uint8_t v_shouldExport_2192_, lean_object* v_as_2193_, size_t v_i_2194_, size_t v_stop_2195_, lean_object* v_b_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
uint8_t v___x_2204_; 
v___x_2204_ = lean_usize_dec_eq(v_i_2194_, v_stop_2195_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; lean_object* v_lib_2206_; lean_object* v_config_2207_; lean_object* v_nativeFacets_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; size_t v_sz_2211_; size_t v___x_2212_; lean_object* v___x_2213_; 
v___x_2205_ = lean_array_uget_borrowed(v_as_2193_, v_i_2194_);
v_lib_2206_ = lean_ctor_get(v___x_2205_, 0);
v_config_2207_ = lean_ctor_get(v_lib_2206_, 2);
v_nativeFacets_2208_ = lean_ctor_get(v_config_2207_, 8);
v___x_2209_ = lean_box(v_shouldExport_2192_);
lean_inc_ref(v_nativeFacets_2208_);
v___x_2210_ = lean_apply_1(v_nativeFacets_2208_, v___x_2209_);
v_sz_2211_ = lean_array_size(v___x_2210_);
v___x_2212_ = ((size_t)0ULL);
lean_inc_ref(v___y_2197_);
lean_inc(v___x_2205_);
v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2205_, v_sz_2211_, v___x_2212_, v___x_2210_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v_a_2215_; lean_object* v___x_2216_; size_t v___x_2217_; size_t v___x_2218_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
v_a_2215_ = lean_ctor_get(v___x_2213_, 1);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2213_, 2);
v___x_2216_ = l_Array_append___redArg(v_b_2196_, v_a_2214_);
lean_dec(v_a_2214_);
v___x_2217_ = ((size_t)1ULL);
v___x_2218_ = lean_usize_add(v_i_2194_, v___x_2217_);
v_i_2194_ = v___x_2218_;
v_b_2196_ = v___x_2216_;
v___y_2202_ = v_a_2215_;
goto _start;
}
else
{
lean_dec_ref(v___y_2197_);
lean_dec_ref(v_b_2196_);
return v___x_2213_;
}
}
else
{
lean_object* v___x_2220_; 
lean_dec_ref(v___y_2197_);
v___x_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2220_, 0, v_b_2196_);
lean_ctor_set(v___x_2220_, 1, v___y_2202_);
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(lean_object* v_shouldExport_2221_, lean_object* v_as_2222_, lean_object* v_i_2223_, lean_object* v_stop_2224_, lean_object* v_b_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
uint8_t v_shouldExport_boxed_2233_; size_t v_i_boxed_2234_; size_t v_stop_boxed_2235_; lean_object* v_res_2236_; 
v_shouldExport_boxed_2233_ = lean_unbox(v_shouldExport_2221_);
v_i_boxed_2234_ = lean_unbox_usize(v_i_2223_);
lean_dec(v_i_2223_);
v_stop_boxed_2235_ = lean_unbox_usize(v_stop_2224_);
lean_dec(v_stop_2224_);
v_res_2236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_boxed_2233_, v_as_2222_, v_i_boxed_2234_, v_stop_boxed_2235_, v_b_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v_as_2222_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object* v_config_2237_, lean_object* v_config_2238_, uint8_t v_shouldExport_2239_, uint8_t v___x_2240_, lean_object* v___x_2241_, lean_object* v___x_2242_, lean_object* v_pkg_2243_, lean_object* v_dir_2244_, lean_object* v_self_2245_, lean_object* v___x_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
uint8_t v___y_2255_; size_t v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v_a_2275_; lean_object* v_a_2276_; lean_object* v___x_2318_; 
lean_inc_ref(v___y_2247_);
lean_inc_ref(v___y_2251_);
lean_inc_ref(v___y_2250_);
lean_inc(v___y_2249_);
lean_inc(v___x_2242_);
v___x_2318_ = lean_apply_7(v___y_2247_, v___x_2246_, v___x_2242_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, lean_box(0));
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v_a_2320_; lean_object* v___x_2321_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
v_a_2320_ = lean_ctor_get(v___x_2318_, 1);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2318_, 2);
v___x_2321_ = l_Lake_Job_await___redArg(v_a_2319_, v_a_2320_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v_a_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
v_a_2323_ = lean_ctor_get(v___x_2321_, 1);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2321_, 2);
v___x_2324_ = lean_unsigned_to_nat(0u);
v___x_2325_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_2326_ = lean_array_get_size(v_a_2322_);
v___x_2327_ = lean_nat_dec_lt(v___x_2324_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_dec(v_a_2322_);
v_a_2275_ = v___x_2325_;
v_a_2276_ = v_a_2323_;
goto v___jp_2274_;
}
else
{
size_t v___x_2328_; size_t v___x_2329_; lean_object* v___x_2330_; 
v___x_2328_ = ((size_t)0ULL);
v___x_2329_ = lean_usize_of_nat(v___x_2326_);
lean_inc_ref(v___y_2247_);
v___x_2330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2239_, v_a_2322_, v___x_2328_, v___x_2329_, v___x_2325_, v___y_2247_, v___x_2242_, v___y_2249_, v___y_2250_, v___y_2251_, v_a_2323_);
lean_dec(v_a_2322_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v_a_2332_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
v_a_2332_ = lean_ctor_get(v___x_2330_, 1);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2330_, 2);
v_a_2275_ = v_a_2331_;
v_a_2276_ = v_a_2332_;
goto v___jp_2274_;
}
else
{
lean_object* v_a_2333_; lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec_ref(v___y_2247_);
lean_dec_ref(v_self_2245_);
lean_dec_ref(v_dir_2244_);
lean_dec_ref(v_pkg_2243_);
lean_dec(v___x_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v_config_2237_);
v_a_2333_ = lean_ctor_get(v___x_2330_, 0);
v_a_2334_ = lean_ctor_get(v___x_2330_, 1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2330_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_inc(v_a_2333_);
lean_dec(v___x_2330_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2333_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v___y_2247_);
lean_dec_ref(v_self_2245_);
lean_dec_ref(v_dir_2244_);
lean_dec_ref(v_pkg_2243_);
lean_dec(v___x_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v_config_2237_);
v_a_2342_ = lean_ctor_get(v___x_2321_, 0);
v_a_2343_ = lean_ctor_get(v___x_2321_, 1);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2321_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_inc(v_a_2342_);
lean_dec(v___x_2321_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2342_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v___y_2247_);
lean_dec_ref(v_self_2245_);
lean_dec_ref(v_dir_2244_);
lean_dec_ref(v_pkg_2243_);
lean_dec(v___x_2242_);
lean_dec(v___x_2241_);
lean_dec_ref(v_config_2237_);
v_a_2351_ = lean_ctor_get(v___x_2318_, 0);
v_a_2352_ = lean_ctor_get(v___x_2318_, 1);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2318_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_inc(v_a_2351_);
lean_dec(v___x_2318_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2351_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
v___jp_2254_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___f_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2261_ = lean_box(v___y_2255_);
v___x_2262_ = lean_box(v_shouldExport_2239_);
v___x_2263_ = lean_box(v___x_2240_);
v___x_2264_ = lean_box_usize(v___y_2256_);
v___f_2265_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2265_, 0, v___x_2261_);
lean_closure_set(v___f_2265_, 1, v___y_2260_);
lean_closure_set(v___f_2265_, 2, v___x_2262_);
lean_closure_set(v___f_2265_, 3, v___x_2263_);
lean_closure_set(v___f_2265_, 4, v___x_2264_);
v___x_2266_ = l_Array_append___redArg(v___y_2259_, v___y_2257_);
lean_dec_ref(v___y_2257_);
v___x_2267_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_2268_ = l_Lake_Job_collectArray___redArg(v___x_2266_, v___x_2267_);
lean_dec_ref(v___x_2266_);
v___x_2269_ = lean_unsigned_to_nat(0u);
v___x_2270_ = 0;
v___x_2271_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_2272_ = l_Lake_Job_mapM___redArg(v___x_2241_, v___x_2268_, v___f_2265_, v___x_2269_, v___x_2270_, v___y_2247_, v___x_2242_, v___y_2249_, v___y_2250_, v___y_2251_, v___x_2271_);
lean_dec(v___x_2242_);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v___y_2258_);
return v___x_2273_;
}
v___jp_2274_:
{
lean_object* v_toLeanConfig_2277_; lean_object* v_toLeanConfig_2278_; uint8_t v_bootstrap_2279_; lean_object* v_buildDir_2280_; lean_object* v_nativeLibDir_2281_; lean_object* v_moreLinkObjs_2282_; lean_object* v_moreLinkObjs_2283_; lean_object* v___x_2284_; size_t v_sz_2285_; size_t v___x_2286_; lean_object* v___x_2287_; 
v_toLeanConfig_2277_ = lean_ctor_get(v_config_2237_, 1);
lean_inc_ref(v_toLeanConfig_2277_);
v_toLeanConfig_2278_ = lean_ctor_get(v_config_2238_, 0);
v_bootstrap_2279_ = lean_ctor_get_uint8(v_config_2237_, sizeof(void*)*29);
v_buildDir_2280_ = lean_ctor_get(v_config_2237_, 5);
lean_inc_ref(v_buildDir_2280_);
v_nativeLibDir_2281_ = lean_ctor_get(v_config_2237_, 7);
lean_inc_ref(v_nativeLibDir_2281_);
lean_dec_ref(v_config_2237_);
v_moreLinkObjs_2282_ = lean_ctor_get(v_toLeanConfig_2277_, 6);
lean_inc_ref(v_moreLinkObjs_2282_);
lean_dec_ref(v_toLeanConfig_2277_);
v_moreLinkObjs_2283_ = lean_ctor_get(v_toLeanConfig_2278_, 6);
v___x_2284_ = l_Array_append___redArg(v_moreLinkObjs_2282_, v_moreLinkObjs_2283_);
v_sz_2285_ = lean_array_size(v___x_2284_);
v___x_2286_ = ((size_t)0ULL);
lean_inc_ref(v___y_2247_);
v___x_2287_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_2243_, v_sz_2285_, v___x_2286_, v___x_2284_, v___y_2247_, v___x_2242_, v___y_2249_, v___y_2250_, v___y_2251_, v_a_2276_);
if (lean_obj_tag(v___x_2287_) == 0)
{
if (v_shouldExport_2239_ == 0)
{
lean_object* v_a_2288_; lean_object* v_a_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
v_a_2289_ = lean_ctor_get(v___x_2287_, 1);
lean_inc(v_a_2289_);
lean_dec_ref_known(v___x_2287_, 2);
v___x_2290_ = l_System_FilePath_normalize(v_buildDir_2280_);
v___x_2291_ = l_Lake_joinRelative(v_dir_2244_, v___x_2290_);
v___x_2292_ = l_System_FilePath_normalize(v_nativeLibDir_2281_);
v___x_2293_ = l_Lake_joinRelative(v___x_2291_, v___x_2292_);
v___x_2294_ = l_Lake_LeanLib_libName(v_self_2245_);
v___x_2295_ = l_Lake_nameToStaticLib(v___x_2294_, v_shouldExport_2239_);
v___x_2296_ = l_Lake_joinRelative(v___x_2293_, v___x_2295_);
v___y_2255_ = v_bootstrap_2279_;
v___y_2256_ = v___x_2286_;
v___y_2257_ = v_a_2288_;
v___y_2258_ = v_a_2289_;
v___y_2259_ = v_a_2275_;
v___y_2260_ = v___x_2296_;
goto v___jp_2254_;
}
else
{
lean_object* v_a_2297_; lean_object* v_a_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v_a_2297_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2297_);
v_a_2298_ = lean_ctor_get(v___x_2287_, 1);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2287_, 2);
v___x_2299_ = l_System_FilePath_normalize(v_buildDir_2280_);
v___x_2300_ = l_Lake_joinRelative(v_dir_2244_, v___x_2299_);
v___x_2301_ = l_System_FilePath_normalize(v_nativeLibDir_2281_);
v___x_2302_ = l_Lake_joinRelative(v___x_2300_, v___x_2301_);
v___x_2303_ = l_Lake_LeanLib_libName(v_self_2245_);
v___x_2304_ = 0;
v___x_2305_ = l_Lake_nameToStaticLib(v___x_2303_, v___x_2304_);
v___x_2306_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_2307_ = l_System_FilePath_addExtension(v___x_2305_, v___x_2306_);
v___x_2308_ = l_Lake_joinRelative(v___x_2302_, v___x_2307_);
v___y_2255_ = v_bootstrap_2279_;
v___y_2256_ = v___x_2286_;
v___y_2257_ = v_a_2297_;
v___y_2258_ = v_a_2298_;
v___y_2259_ = v_a_2275_;
v___y_2260_ = v___x_2308_;
goto v___jp_2254_;
}
}
else
{
lean_object* v_a_2309_; lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec_ref(v_nativeLibDir_2281_);
lean_dec_ref(v_buildDir_2280_);
lean_dec_ref(v_a_2275_);
lean_dec_ref(v___y_2247_);
lean_dec_ref(v_self_2245_);
lean_dec_ref(v_dir_2244_);
lean_dec(v___x_2242_);
lean_dec(v___x_2241_);
v_a_2309_ = lean_ctor_get(v___x_2287_, 0);
v_a_2310_ = lean_ctor_get(v___x_2287_, 1);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2287_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_inc(v_a_2309_);
lean_dec(v___x_2287_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2309_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(lean_object** _args){
lean_object* v_config_2360_ = _args[0];
lean_object* v_config_2361_ = _args[1];
lean_object* v_shouldExport_2362_ = _args[2];
lean_object* v___x_2363_ = _args[3];
lean_object* v___x_2364_ = _args[4];
lean_object* v___x_2365_ = _args[5];
lean_object* v_pkg_2366_ = _args[6];
lean_object* v_dir_2367_ = _args[7];
lean_object* v_self_2368_ = _args[8];
lean_object* v___x_2369_ = _args[9];
lean_object* v___y_2370_ = _args[10];
lean_object* v___y_2371_ = _args[11];
lean_object* v___y_2372_ = _args[12];
lean_object* v___y_2373_ = _args[13];
lean_object* v___y_2374_ = _args[14];
lean_object* v___y_2375_ = _args[15];
lean_object* v___y_2376_ = _args[16];
_start:
{
uint8_t v_shouldExport_boxed_2377_; uint8_t v___x_6505__boxed_2378_; lean_object* v_res_2379_; 
v_shouldExport_boxed_2377_ = lean_unbox(v_shouldExport_2362_);
v___x_6505__boxed_2378_ = lean_unbox(v___x_2363_);
v_res_2379_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v_config_2360_, v_config_2361_, v_shouldExport_boxed_2377_, v___x_6505__boxed_2378_, v___x_2364_, v___x_2365_, v_pkg_2366_, v_dir_2367_, v_self_2368_, v___x_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec(v_config_2361_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object* v___y_2380_, lean_object* v_self_2381_, uint8_t v_shouldExport_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_toBuildConfig_2389_; lean_object* v_registeredJobs_2390_; uint8_t v_verbosity_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; uint8_t v___x_2397_; lean_object* v___y_2399_; 
v_toBuildConfig_2389_ = lean_ctor_get(v_a_2386_, 0);
v_registeredJobs_2390_ = lean_ctor_get(v_a_2386_, 4);
v_verbosity_2391_ = lean_ctor_get_uint8(v_toBuildConfig_2389_, sizeof(void*)*6 + 4);
v___x_2392_ = l_Lake_instDataKindFilePath;
v___x_2393_ = lean_box(v_verbosity_2391_);
v___x_2394_ = lean_obj_tag_nat(v___x_2393_);
lean_dec(v___x_2393_);
v___x_2395_ = lean_unsigned_to_nat(2u);
v___x_2396_ = lean_nat_dec_eq(v___x_2394_, v___x_2395_);
v___x_2397_ = 1;
if (v___x_2396_ == 0)
{
lean_object* v___x_2444_; 
v___x_2444_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_2399_ = v___x_2444_;
goto v___jp_2398_;
}
else
{
if (v_shouldExport_2382_ == 0)
{
lean_object* v___x_2445_; 
v___x_2445_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___y_2399_ = v___x_2445_;
goto v___jp_2398_;
}
else
{
lean_object* v___x_2446_; 
v___x_2446_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_2399_ = v___x_2446_;
goto v___jp_2398_;
}
}
v___jp_2398_:
{
lean_object* v_pkg_2400_; lean_object* v_name_2401_; lean_object* v_config_2402_; lean_object* v_keyName_2403_; lean_object* v_dir_2404_; lean_object* v_config_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___f_2417_; uint8_t v___x_2418_; lean_object* v___x_2419_; 
v_pkg_2400_ = lean_ctor_get(v_self_2381_, 0);
lean_inc_ref_n(v_pkg_2400_, 2);
v_name_2401_ = lean_ctor_get(v_self_2381_, 1);
v_config_2402_ = lean_ctor_get(v_self_2381_, 2);
lean_inc(v_config_2402_);
v_keyName_2403_ = lean_ctor_get(v_pkg_2400_, 2);
v_dir_2404_ = lean_ctor_get(v_pkg_2400_, 4);
lean_inc_ref(v_dir_2404_);
v_config_2405_ = lean_ctor_get(v_pkg_2400_, 6);
lean_inc_ref(v_config_2405_);
lean_inc_n(v_name_2401_, 2);
v___x_2406_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2401_, v___x_2397_);
v___x_2407_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0));
v___x_2408_ = lean_string_append(v___x_2406_, v___x_2407_);
v___x_2409_ = lean_string_append(v___x_2408_, v___y_2399_);
v___x_2410_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_2403_);
v___x_2411_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2411_, 0, v_keyName_2403_);
lean_ctor_set(v___x_2411_, 1, v_name_2401_);
v___x_2412_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_2381_);
v___x_2413_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
lean_ctor_set(v___x_2413_, 2, v_self_2381_);
lean_ctor_set(v___x_2413_, 3, v___x_2410_);
v___x_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2414_, 0, v_pkg_2400_);
v___x_2415_ = lean_box(v_shouldExport_2382_);
v___x_2416_ = lean_box(v___x_2397_);
v___f_2417_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed), 17, 10);
lean_closure_set(v___f_2417_, 0, v_config_2405_);
lean_closure_set(v___f_2417_, 1, v_config_2402_);
lean_closure_set(v___f_2417_, 2, v___x_2415_);
lean_closure_set(v___f_2417_, 3, v___x_2416_);
lean_closure_set(v___f_2417_, 4, v___x_2392_);
lean_closure_set(v___f_2417_, 5, v___x_2414_);
lean_closure_set(v___f_2417_, 6, v_pkg_2400_);
lean_closure_set(v___f_2417_, 7, v_dir_2404_);
lean_closure_set(v___f_2417_, 8, v_self_2381_);
lean_closure_set(v___f_2417_, 9, v___x_2413_);
v___x_2418_ = 0;
v___x_2419_ = l_Lake_ensureJob___redArg(v___x_2392_, v___f_2417_, v___y_2380_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2443_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_a_2421_ = lean_ctor_get(v___x_2419_, 1);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2423_ = v___x_2419_;
v_isShared_2424_ = v_isSharedCheck_2443_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2443_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v_task_2425_; lean_object* v_kind_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2441_; 
v_task_2425_ = lean_ctor_get(v_a_2420_, 0);
v_kind_2426_ = lean_ctor_get(v_a_2420_, 1);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_a_2420_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; 
v_unused_2442_ = lean_ctor_get(v_a_2420_, 2);
lean_dec(v_unused_2442_);
v___x_2428_ = v_a_2420_;
v_isShared_2429_ = v_isSharedCheck_2441_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_kind_2426_);
lean_inc(v_task_2425_);
lean_dec(v_a_2420_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2441_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v_job_2431_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 2, v___x_2409_);
v_job_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_task_2425_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_kind_2426_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v___x_2409_);
v_job_2431_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2438_; 
lean_ctor_set_uint8(v_job_2431_, sizeof(void*)*3, v___x_2418_);
v___x_2432_ = lean_st_ref_take(v_registeredJobs_2390_);
lean_inc_ref(v_job_2431_);
v___x_2433_ = l_Lake_Job_toOpaque___redArg(v_job_2431_);
v___x_2434_ = lean_array_push(v___x_2432_, v___x_2433_);
v___x_2435_ = lean_st_ref_put(v_registeredJobs_2390_, v___x_2434_);
v___x_2436_ = l_Lake_Job_renew___redArg(v_job_2431_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2436_);
v___x_2438_ = v___x_2423_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v_a_2421_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2409_);
return v___x_2419_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* v___y_2447_, lean_object* v_self_2448_, lean_object* v_shouldExport_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
uint8_t v_shouldExport_boxed_2456_; lean_object* v_res_2457_; 
v_shouldExport_boxed_2456_ = lean_unbox(v_shouldExport_2449_);
v_res_2457_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2447_, v_self_2448_, v_shouldExport_boxed_2456_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec(v_a_2450_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* v_x_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
uint8_t v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = 0;
v___x_2467_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2459_, v_x_2458_, v___x_2466_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object* v_x_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec(v___y_2470_);
return v_res_2476_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2479_; uint8_t v___x_2480_; lean_object* v___x_2481_; lean_object* v___f_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___f_2479_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2480_ = 1;
v___x_2481_ = l_Lake_instDataKindFilePath;
v___f_2482_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__0));
v___x_2483_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2484_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2484_, 0, v___x_2483_);
lean_ctor_set(v___x_2484_, 1, v___f_2482_);
lean_ctor_set(v___x_2484_, 2, v___x_2481_);
lean_ctor_set(v___x_2484_, 3, v___f_2479_);
lean_ctor_set_uint8(v___x_2484_, sizeof(void*)*4, v___x_2480_);
lean_ctor_set_uint8(v___x_2484_, sizeof(void*)*4 + 1, v___x_2480_);
return v___x_2484_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_obj_once(&l_Lake_LeanLib_staticFacetConfig___closed__2, &l_Lake_LeanLib_staticFacetConfig___closed__2_once, _init_l_Lake_LeanLib_staticFacetConfig___closed__2);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(lean_object* v_a_2486_, lean_object* v_as_2487_, size_t v_i_2488_, size_t v_stop_2489_, lean_object* v_b_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2486_, v_as_2487_, v_i_2488_, v_stop_2489_, v_b_2490_, v___y_2496_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* v_a_2499_, lean_object* v_as_2500_, lean_object* v_i_2501_, lean_object* v_stop_2502_, lean_object* v_b_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
size_t v_i_boxed_2511_; size_t v_stop_boxed_2512_; lean_object* v_res_2513_; 
v_i_boxed_2511_ = lean_unbox_usize(v_i_2501_);
lean_dec(v_i_2501_);
v_stop_boxed_2512_ = lean_unbox_usize(v_stop_2502_);
lean_dec(v_stop_2502_);
v_res_2513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_2499_, v_as_2500_, v_i_boxed_2511_, v_stop_boxed_2512_, v_b_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec_ref(v_as_2500_);
lean_dec(v_a_2499_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* v_x_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
uint8_t v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = 1;
v___x_2523_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2515_, v_x_2514_, v___x_2522_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object* v_x_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec(v___y_2526_);
return v_res_2532_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2534_; uint8_t v___x_2535_; lean_object* v___x_2536_; lean_object* v___f_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___f_2534_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2535_ = 1;
v___x_2536_ = l_Lake_instDataKindFilePath;
v___f_2537_ = ((lean_object*)(l_Lake_LeanLib_staticExportFacetConfig___closed__0));
v___x_2538_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2539_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
lean_ctor_set(v___x_2539_, 1, v___f_2537_);
lean_ctor_set(v___x_2539_, 2, v___x_2536_);
lean_ctor_set(v___x_2539_, 3, v___f_2534_);
lean_ctor_set_uint8(v___x_2539_, sizeof(void*)*4, v___x_2535_);
lean_ctor_set_uint8(v___x_2539_, sizeof(void*)*4 + 1, v___x_2535_);
return v___x_2539_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig(void){
_start:
{
lean_object* v___x_2540_; 
v___x_2540_ = lean_obj_once(&l_Lake_LeanLib_staticExportFacetConfig___closed__1, &l_Lake_LeanLib_staticExportFacetConfig___closed__1_once, _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1);
return v___x_2540_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0(void){
_start:
{
uint8_t v___x_2541_; lean_object* v_name_2542_; lean_object* v___x_2543_; 
v___x_2541_ = 1;
v_name_2542_ = l_Lake_instDataKindDynlib;
v___x_2543_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2542_, v___x_2541_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object* v_defaultPkg_2544_, lean_object* v_self_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_name_2553_; uint8_t v___x_2554_; lean_object* v___x_2555_; 
v_name_2553_ = l_Lake_instDataKindDynlib;
v___x_2554_ = 1;
lean_inc_ref_n(v_self_2545_, 2);
v___x_2555_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_2544_, v_self_2545_, v_self_2545_, v___x_2554_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2597_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_a_2557_ = lean_ctor_get(v___x_2555_, 1);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2559_ = v___x_2555_;
v_isShared_2560_ = v_isSharedCheck_2597_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2597_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___y_2562_; lean_object* v_snd_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2595_; 
v_snd_2580_ = lean_ctor_get(v_a_2556_, 1);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_a_2556_);
if (v_isSharedCheck_2595_ == 0)
{
lean_object* v_unused_2596_; 
v_unused_2596_ = lean_ctor_get(v_a_2556_, 0);
lean_dec(v_unused_2596_);
v___x_2582_ = v_a_2556_;
v_isShared_2583_ = v_isSharedCheck_2595_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_snd_2580_);
lean_dec(v_a_2556_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2595_;
goto v_resetjp_2581_;
}
v___jp_2561_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2563_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_2564_ = l_Lake_PartialBuildKey_toString(v_self_2545_);
v___x_2565_ = lean_string_append(v___x_2563_, v___x_2564_);
lean_dec_ref(v___x_2564_);
v___x_2566_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_2567_ = lean_string_append(v___x_2565_, v___x_2566_);
v___x_2568_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0);
v___x_2569_ = lean_string_append(v___x_2567_, v___x_2568_);
v___x_2570_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_2571_ = lean_string_append(v___x_2569_, v___x_2570_);
v___x_2572_ = lean_string_append(v___x_2571_, v___y_2562_);
lean_dec_ref(v___y_2562_);
v___x_2573_ = 3;
v___x_2574_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set_uint8(v___x_2574_, sizeof(void*)*1, v___x_2573_);
v___x_2575_ = lean_array_get_size(v_a_2557_);
v___x_2576_ = lean_array_push(v_a_2557_, v___x_2574_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set_tag(v___x_2559_, 1);
lean_ctor_set(v___x_2559_, 1, v___x_2576_);
lean_ctor_set(v___x_2559_, 0, v___x_2575_);
v___x_2578_ = v___x_2559_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
v_resetjp_2581_:
{
lean_object* v_kind_2584_; uint8_t v___x_2585_; 
v_kind_2584_ = lean_ctor_get(v_snd_2580_, 1);
v___x_2585_ = lean_name_eq(v_kind_2584_, v_name_2553_);
if (v___x_2585_ == 0)
{
uint8_t v___x_2586_; 
lean_inc(v_kind_2584_);
lean_del_object(v___x_2582_);
lean_dec(v_snd_2580_);
v___x_2586_ = l_Lean_Name_isAnonymous(v_kind_2584_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2587_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_2588_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2584_, v___x_2554_);
v___x_2589_ = lean_string_append(v___x_2587_, v___x_2588_);
lean_dec_ref(v___x_2588_);
v___x_2590_ = lean_string_append(v___x_2589_, v___x_2587_);
v___y_2562_ = v___x_2590_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2591_; 
lean_dec(v_kind_2584_);
v___x_2591_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_2562_ = v___x_2591_;
goto v___jp_2561_;
}
}
else
{
lean_object* v___x_2593_; 
lean_del_object(v___x_2559_);
lean_dec_ref(v_self_2545_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set(v___x_2582_, 1, v_a_2557_);
lean_ctor_set(v___x_2582_, 0, v_snd_2580_);
v___x_2593_ = v___x_2582_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_snd_2580_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v_a_2557_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec_ref(v_self_2545_);
v_a_2598_ = lean_ctor_get(v___x_2555_, 0);
v_a_2599_ = lean_ctor_get(v___x_2555_, 1);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2555_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_inc(v_a_2598_);
lean_dec(v___x_2555_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2598_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* v_defaultPkg_2607_, lean_object* v_self_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_2607_, v_self_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_);
lean_dec_ref(v_a_2613_);
lean_dec_ref(v_a_2612_);
lean_dec(v_a_2611_);
lean_dec(v_a_2610_);
return v_res_2616_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2619_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0));
v___x_2620_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
lean_ctor_set(v___x_2621_, 1, v___x_2619_);
return v___x_2621_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5(void){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object* v___x_2623_, lean_object* v_as_2624_, size_t v_i_2625_, size_t v_stop_2626_, lean_object* v_b_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
uint8_t v___x_2635_; 
v___x_2635_ = lean_usize_dec_eq(v_i_2625_, v_stop_2626_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = lean_array_uget_borrowed(v_as_2624_, v_i_2625_);
lean_inc_ref(v___y_2628_);
lean_inc(v___x_2636_);
lean_inc_ref(v___x_2623_);
v___x_2637_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_2623_, v___x_2636_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v_a_2639_; lean_object* v___x_2640_; size_t v___x_2641_; size_t v___x_2642_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
v_a_2639_ = lean_ctor_get(v___x_2637_, 1);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2637_, 2);
v___x_2640_ = lean_array_push(v_b_2627_, v_a_2638_);
v___x_2641_ = ((size_t)1ULL);
v___x_2642_ = lean_usize_add(v_i_2625_, v___x_2641_);
v_i_2625_ = v___x_2642_;
v_b_2627_ = v___x_2640_;
v___y_2633_ = v_a_2639_;
goto _start;
}
else
{
lean_object* v_a_2644_; lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec_ref(v___y_2628_);
lean_dec_ref(v_b_2627_);
lean_dec_ref(v___x_2623_);
v_a_2644_ = lean_ctor_get(v___x_2637_, 0);
v_a_2645_ = lean_ctor_get(v___x_2637_, 1);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2637_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_inc(v_a_2644_);
lean_dec(v___x_2637_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2644_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
else
{
lean_object* v___x_2653_; 
lean_dec_ref(v___y_2628_);
lean_dec_ref(v___x_2623_);
v___x_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2653_, 0, v_b_2627_);
lean_ctor_set(v___x_2653_, 1, v___y_2633_);
return v___x_2653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* v___x_2654_, lean_object* v_as_2655_, lean_object* v_i_2656_, lean_object* v_stop_2657_, lean_object* v_b_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
size_t v_i_boxed_2666_; size_t v_stop_boxed_2667_; lean_object* v_res_2668_; 
v_i_boxed_2666_ = lean_unbox_usize(v_i_2656_);
lean_dec(v_i_2656_);
v_stop_boxed_2667_ = lean_unbox_usize(v_stop_2657_);
lean_dec(v_stop_2657_);
v_res_2668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_2654_, v_as_2655_, v_i_boxed_2666_, v_stop_boxed_2667_, v_b_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v_as_2655_);
return v_res_2668_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object* v_self_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_toHashSet_2671_; lean_object* v_toArray_2672_; uint8_t v___x_2673_; 
v_toHashSet_2671_ = lean_ctor_get(v_self_2669_, 0);
v_toArray_2672_ = lean_ctor_get(v_self_2669_, 1);
v___x_2673_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_2671_, v_a_2670_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2683_; 
lean_inc_ref(v_toArray_2672_);
lean_inc_ref(v_toHashSet_2671_);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_self_2669_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; lean_object* v_unused_2685_; 
v_unused_2684_ = lean_ctor_get(v_self_2669_, 1);
lean_dec(v_unused_2684_);
v_unused_2685_ = lean_ctor_get(v_self_2669_, 0);
lean_dec(v_unused_2685_);
v___x_2675_ = v_self_2669_;
v_isShared_2676_ = v_isSharedCheck_2683_;
goto v_resetjp_2674_;
}
else
{
lean_dec(v_self_2669_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2683_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2681_; 
v___x_2677_ = lean_box(0);
lean_inc_ref(v_a_2670_);
v___x_2678_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_toHashSet_2671_, v_a_2670_, v___x_2677_);
v___x_2679_ = lean_array_push(v_toArray_2672_, v_a_2670_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 1, v___x_2679_);
lean_ctor_set(v___x_2675_, 0, v___x_2678_);
v___x_2681_ = v___x_2675_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2678_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
else
{
lean_dec_ref(v_a_2670_);
return v_self_2669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object* v_as_2686_, size_t v_i_2687_, size_t v_stop_2688_, lean_object* v_b_2689_){
_start:
{
uint8_t v___x_2690_; 
v___x_2690_ = lean_usize_dec_eq(v_i_2687_, v_stop_2688_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; lean_object* v___x_2692_; size_t v___x_2693_; size_t v___x_2694_; 
v___x_2691_ = lean_array_uget_borrowed(v_as_2686_, v_i_2687_);
lean_inc(v___x_2691_);
v___x_2692_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_2689_, v___x_2691_);
v___x_2693_ = ((size_t)1ULL);
v___x_2694_ = lean_usize_add(v_i_2687_, v___x_2693_);
v_i_2687_ = v___x_2694_;
v_b_2689_ = v___x_2692_;
goto _start;
}
else
{
return v_b_2689_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object* v_as_2696_, lean_object* v_i_2697_, lean_object* v_stop_2698_, lean_object* v_b_2699_){
_start:
{
size_t v_i_boxed_2700_; size_t v_stop_boxed_2701_; lean_object* v_res_2702_; 
v_i_boxed_2700_ = lean_unbox_usize(v_i_2697_);
lean_dec(v_i_2697_);
v_stop_boxed_2701_ = lean_unbox_usize(v_stop_2698_);
lean_dec(v_stop_2698_);
v_res_2702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_2696_, v_i_boxed_2700_, v_stop_boxed_2701_, v_b_2699_);
lean_dec_ref(v_as_2696_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object* v_self_2703_, lean_object* v_arr_2704_){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v___x_2705_ = lean_unsigned_to_nat(0u);
v___x_2706_ = lean_array_get_size(v_arr_2704_);
v___x_2707_ = lean_nat_dec_lt(v___x_2705_, v___x_2706_);
if (v___x_2707_ == 0)
{
return v_self_2703_;
}
else
{
size_t v___x_2708_; size_t v___x_2709_; lean_object* v___x_2710_; 
v___x_2708_ = ((size_t)0ULL);
v___x_2709_ = lean_usize_of_nat(v___x_2706_);
v___x_2710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2704_, v___x_2708_, v___x_2709_, v_self_2703_);
return v___x_2710_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(lean_object* v_self_2711_, lean_object* v_arr_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_self_2711_, v_arr_2712_);
lean_dec_ref(v_arr_2712_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(lean_object* v_as_2714_, size_t v_i_2715_, size_t v_stop_2716_, lean_object* v_b_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
uint8_t v___x_2725_; 
v___x_2725_ = lean_usize_dec_eq(v_i_2715_, v_stop_2716_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v_lib_2727_; lean_object* v_pkg_2728_; lean_object* v_name_2729_; lean_object* v_keyName_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2726_ = lean_array_uget_borrowed(v_as_2714_, v_i_2715_);
v_lib_2727_ = lean_ctor_get(v___x_2726_, 0);
v_pkg_2728_ = lean_ctor_get(v_lib_2727_, 0);
v_name_2729_ = lean_ctor_get(v___x_2726_, 1);
v_keyName_2730_ = lean_ctor_get(v_pkg_2728_, 2);
v___x_2731_ = l_Lake_Module_transImportsFacet;
lean_inc(v_name_2729_);
lean_inc(v_keyName_2730_);
v___x_2732_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2732_, 0, v_keyName_2730_);
lean_ctor_set(v___x_2732_, 1, v_name_2729_);
v___x_2733_ = l_Lake_Module_keyword;
lean_inc(v___x_2726_);
v___x_2734_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2732_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
lean_ctor_set(v___x_2734_, 2, v___x_2726_);
lean_ctor_set(v___x_2734_, 3, v___x_2731_);
lean_inc_ref(v___y_2718_);
lean_inc_ref(v___y_2722_);
lean_inc_ref(v___y_2721_);
lean_inc(v___y_2720_);
lean_inc(v___y_2719_);
v___x_2735_ = lean_apply_7(v___y_2718_, v___x_2734_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, lean_box(0));
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v_a_2737_; lean_object* v___x_2738_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
v_a_2737_ = lean_ctor_get(v___x_2735_, 1);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2735_, 2);
v___x_2738_ = l_Lake_Job_await___redArg(v_a_2736_, v_a_2737_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v_a_2740_; lean_object* v___x_2741_; size_t v___x_2742_; size_t v___x_2743_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
v_a_2740_ = lean_ctor_get(v___x_2738_, 1);
lean_inc(v_a_2740_);
lean_dec_ref_known(v___x_2738_, 2);
v___x_2741_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_b_2717_, v_a_2739_);
lean_dec(v_a_2739_);
v___x_2742_ = ((size_t)1ULL);
v___x_2743_ = lean_usize_add(v_i_2715_, v___x_2742_);
v_i_2715_ = v___x_2743_;
v_b_2717_ = v___x_2741_;
v___y_2723_ = v_a_2740_;
goto _start;
}
else
{
lean_object* v_a_2745_; lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec_ref(v___y_2718_);
lean_dec_ref(v_b_2717_);
v_a_2745_ = lean_ctor_get(v___x_2738_, 0);
v_a_2746_ = lean_ctor_get(v___x_2738_, 1);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2738_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_inc(v_a_2745_);
lean_dec(v___x_2738_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2745_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
else
{
lean_object* v_a_2754_; lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec_ref(v___y_2718_);
lean_dec_ref(v_b_2717_);
v_a_2754_ = lean_ctor_get(v___x_2735_, 0);
v_a_2755_ = lean_ctor_get(v___x_2735_, 1);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2735_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_inc(v_a_2754_);
lean_dec(v___x_2735_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2754_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_a_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
else
{
lean_object* v___x_2763_; 
lean_dec_ref(v___y_2718_);
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v_b_2717_);
lean_ctor_set(v___x_2763_, 1, v___y_2723_);
return v___x_2763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object* v_as_2764_, lean_object* v_i_2765_, lean_object* v_stop_2766_, lean_object* v_b_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
size_t v_i_boxed_2775_; size_t v_stop_boxed_2776_; lean_object* v_res_2777_; 
v_i_boxed_2775_ = lean_unbox_usize(v_i_2765_);
lean_dec(v_i_2765_);
v_stop_boxed_2776_ = lean_unbox_usize(v_stop_2766_);
lean_dec(v_stop_2766_);
v_res_2777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_as_2764_, v_i_boxed_2775_, v_stop_boxed_2776_, v_b_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v_as_2764_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(lean_object* v_as_2778_, size_t v_i_2779_, size_t v_stop_2780_, lean_object* v_b_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
uint8_t v___x_2789_; 
v___x_2789_ = lean_usize_dec_eq(v_i_2779_, v_stop_2780_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2790_; lean_object* v_pkg_2791_; lean_object* v_name_2792_; lean_object* v_keyName_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2790_ = lean_array_uget_borrowed(v_as_2778_, v_i_2779_);
v_pkg_2791_ = lean_ctor_get(v___x_2790_, 0);
v_name_2792_ = lean_ctor_get(v___x_2790_, 1);
v_keyName_2793_ = lean_ctor_get(v_pkg_2791_, 2);
v___x_2794_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_2792_);
lean_inc(v_keyName_2793_);
v___x_2795_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2795_, 0, v_keyName_2793_);
lean_ctor_set(v___x_2795_, 1, v_name_2792_);
v___x_2796_ = l_Lake_ExternLib_keyword;
lean_inc(v___x_2790_);
v___x_2797_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2795_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
lean_ctor_set(v___x_2797_, 2, v___x_2790_);
lean_ctor_set(v___x_2797_, 3, v___x_2794_);
lean_inc_ref(v___y_2782_);
lean_inc_ref(v___y_2786_);
lean_inc_ref(v___y_2785_);
lean_inc(v___y_2784_);
lean_inc(v___y_2783_);
v___x_2798_ = lean_apply_7(v___y_2782_, v___x_2797_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, lean_box(0));
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v_a_2800_; lean_object* v___x_2801_; size_t v___x_2802_; size_t v___x_2803_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
v_a_2800_ = lean_ctor_get(v___x_2798_, 1);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2798_, 2);
v___x_2801_ = lean_array_push(v_b_2781_, v_a_2799_);
v___x_2802_ = ((size_t)1ULL);
v___x_2803_ = lean_usize_add(v_i_2779_, v___x_2802_);
v_i_2779_ = v___x_2803_;
v_b_2781_ = v___x_2801_;
v___y_2787_ = v_a_2800_;
goto _start;
}
else
{
lean_object* v_a_2805_; lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec_ref(v___y_2782_);
lean_dec_ref(v_b_2781_);
v_a_2805_ = lean_ctor_get(v___x_2798_, 0);
v_a_2806_ = lean_ctor_get(v___x_2798_, 1);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2798_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_inc(v_a_2805_);
lean_dec(v___x_2798_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2805_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
else
{
lean_object* v___x_2814_; 
lean_dec_ref(v___y_2782_);
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v_b_2781_);
lean_ctor_set(v___x_2814_, 1, v___y_2787_);
return v___x_2814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(lean_object* v_as_2815_, lean_object* v_i_2816_, lean_object* v_stop_2817_, lean_object* v_b_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
size_t v_i_boxed_2826_; size_t v_stop_boxed_2827_; lean_object* v_res_2828_; 
v_i_boxed_2826_ = lean_unbox_usize(v_i_2816_);
lean_dec(v_i_2816_);
v_stop_boxed_2827_ = lean_unbox_usize(v_stop_2817_);
lean_dec(v_stop_2817_);
v_res_2828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v_as_2815_, v_i_boxed_2826_, v_stop_boxed_2827_, v_b_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v_as_2815_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(lean_object* v_as_2829_, size_t v_i_2830_, size_t v_stop_2831_, lean_object* v_b_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_a_2841_; lean_object* v_a_2842_; uint8_t v___x_2846_; 
v___x_2846_ = lean_usize_dec_eq(v_i_2830_, v_stop_2831_);
if (v___x_2846_ == 0)
{
lean_object* v_fst_2847_; lean_object* v_snd_2848_; lean_object* v___x_2849_; lean_object* v_lib_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2887_; 
v_fst_2847_ = lean_ctor_get(v_b_2832_, 0);
v_snd_2848_ = lean_ctor_get(v_b_2832_, 1);
v___x_2849_ = lean_array_uget(v_as_2829_, v_i_2830_);
v_lib_2850_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v___x_2849_, 1);
lean_dec(v_unused_2888_);
v___x_2852_ = v___x_2849_;
v_isShared_2853_ = v_isSharedCheck_2887_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_lib_2850_);
lean_dec(v___x_2849_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2887_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v_pkg_2854_; lean_object* v_name_2855_; uint8_t v___x_2856_; 
v_pkg_2854_ = lean_ctor_get(v_lib_2850_, 0);
v_name_2855_ = lean_ctor_get(v_lib_2850_, 1);
lean_inc(v_name_2855_);
v___x_2856_ = l_Lean_NameSet_contains(v_fst_2847_, v_name_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2884_; 
lean_inc(v_snd_2848_);
lean_inc(v_fst_2847_);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_b_2832_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; lean_object* v_unused_2886_; 
v_unused_2885_ = lean_ctor_get(v_b_2832_, 1);
lean_dec(v_unused_2885_);
v_unused_2886_ = lean_ctor_get(v_b_2832_, 0);
lean_dec(v_unused_2886_);
v___x_2858_ = v_b_2832_;
v_isShared_2859_ = v_isSharedCheck_2884_;
goto v_resetjp_2857_;
}
else
{
lean_dec(v_b_2832_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2884_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v_keyName_2860_; lean_object* v___x_2861_; lean_object* v___x_2863_; 
v_keyName_2860_ = lean_ctor_get(v_pkg_2854_, 2);
v___x_2861_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_2855_);
lean_inc(v_keyName_2860_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set_tag(v___x_2852_, 3);
lean_ctor_set(v___x_2852_, 1, v_name_2855_);
lean_ctor_set(v___x_2852_, 0, v_keyName_2860_);
v___x_2863_ = v___x_2852_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_keyName_2860_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v_name_2855_);
v___x_2863_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2864_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2865_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
lean_ctor_set(v___x_2865_, 2, v_lib_2850_);
lean_ctor_set(v___x_2865_, 3, v___x_2861_);
lean_inc_ref(v___y_2833_);
lean_inc_ref(v___y_2837_);
lean_inc_ref(v___y_2836_);
lean_inc(v___y_2835_);
lean_inc(v___y_2834_);
v___x_2866_ = lean_apply_7(v___y_2833_, v___x_2865_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, lean_box(0));
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v_a_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2872_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
v_a_2868_ = lean_ctor_get(v___x_2866_, 1);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2866_, 2);
v___x_2869_ = lean_array_push(v_snd_2848_, v_a_2867_);
v___x_2870_ = l_Lean_NameSet_insert(v_fst_2847_, v_name_2855_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 1, v___x_2869_);
lean_ctor_set(v___x_2858_, 0, v___x_2870_);
v___x_2872_ = v___x_2858_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v___x_2869_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
v_a_2841_ = v___x_2872_;
v_a_2842_ = v_a_2868_;
goto v___jp_2840_;
}
}
else
{
lean_object* v_a_2874_; lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_del_object(v___x_2858_);
lean_dec(v_name_2855_);
lean_dec(v_snd_2848_);
lean_dec(v_fst_2847_);
lean_dec_ref(v___y_2833_);
v_a_2874_ = lean_ctor_get(v___x_2866_, 0);
v_a_2875_ = lean_ctor_get(v___x_2866_, 1);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2866_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_inc(v_a_2874_);
lean_dec(v___x_2866_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2874_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
}
else
{
lean_dec(v_name_2855_);
lean_del_object(v___x_2852_);
lean_dec_ref(v_lib_2850_);
v_a_2841_ = v_b_2832_;
v_a_2842_ = v___y_2838_;
goto v___jp_2840_;
}
}
}
else
{
lean_object* v___x_2889_; 
lean_dec_ref(v___y_2833_);
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v_b_2832_);
lean_ctor_set(v___x_2889_, 1, v___y_2838_);
return v___x_2889_;
}
v___jp_2840_:
{
size_t v___x_2843_; size_t v___x_2844_; 
v___x_2843_ = ((size_t)1ULL);
v___x_2844_ = lean_usize_add(v_i_2830_, v___x_2843_);
v_i_2830_ = v___x_2844_;
v_b_2832_ = v_a_2841_;
v___y_2838_ = v_a_2842_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object* v_as_2890_, lean_object* v_i_2891_, lean_object* v_stop_2892_, lean_object* v_b_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
size_t v_i_boxed_2901_; size_t v_stop_boxed_2902_; lean_object* v_res_2903_; 
v_i_boxed_2901_ = lean_unbox_usize(v_i_2891_);
lean_dec(v_i_2891_);
v_stop_boxed_2902_ = lean_unbox_usize(v_stop_2892_);
lean_dec(v_stop_2892_);
v_res_2903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_as_2890_, v_i_boxed_2901_, v_stop_boxed_2902_, v_b_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v_as_2890_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(lean_object* v___x_2904_, lean_object* v_as_2905_, size_t v_i_2906_, size_t v_stop_2907_, lean_object* v_b_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
uint8_t v___x_2916_; 
v___x_2916_ = lean_usize_dec_eq(v_i_2906_, v_stop_2907_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = lean_array_uget_borrowed(v_as_2905_, v_i_2906_);
lean_inc_ref(v___y_2909_);
lean_inc(v___x_2917_);
lean_inc_ref(v___x_2904_);
v___x_2918_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v___x_2904_, v___x_2917_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v_a_2920_; lean_object* v___x_2921_; size_t v___x_2922_; size_t v___x_2923_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
v_a_2920_ = lean_ctor_get(v___x_2918_, 1);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2918_, 2);
v___x_2921_ = lean_array_push(v_b_2908_, v_a_2919_);
v___x_2922_ = ((size_t)1ULL);
v___x_2923_ = lean_usize_add(v_i_2906_, v___x_2922_);
v_i_2906_ = v___x_2923_;
v_b_2908_ = v___x_2921_;
v___y_2914_ = v_a_2920_;
goto _start;
}
else
{
lean_object* v_a_2925_; lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec_ref(v___y_2909_);
lean_dec_ref(v_b_2908_);
lean_dec_ref(v___x_2904_);
v_a_2925_ = lean_ctor_get(v___x_2918_, 0);
v_a_2926_ = lean_ctor_get(v___x_2918_, 1);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2918_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_inc(v_a_2925_);
lean_dec(v___x_2918_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2925_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_object* v___x_2934_; 
lean_dec_ref(v___y_2909_);
lean_dec_ref(v___x_2904_);
v___x_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2934_, 0, v_b_2908_);
lean_ctor_set(v___x_2934_, 1, v___y_2914_);
return v___x_2934_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object* v___x_2935_, lean_object* v_as_2936_, lean_object* v_i_2937_, lean_object* v_stop_2938_, lean_object* v_b_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
size_t v_i_boxed_2947_; size_t v_stop_boxed_2948_; lean_object* v_res_2949_; 
v_i_boxed_2947_ = lean_unbox_usize(v_i_2937_);
lean_dec(v_i_2937_);
v_stop_boxed_2948_ = lean_unbox_usize(v_stop_2938_);
lean_dec(v_stop_2938_);
v_res_2949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v___x_2935_, v_as_2936_, v_i_boxed_2947_, v_stop_boxed_2948_, v_b_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v_as_2936_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(lean_object* v___x_2950_, lean_object* v_as_2951_, size_t v_i_2952_, size_t v_stop_2953_, lean_object* v_b_2954_){
_start:
{
lean_object* v___y_2956_; uint8_t v___x_2960_; 
v___x_2960_ = lean_usize_dec_eq(v_i_2952_, v_stop_2953_);
if (v___x_2960_ == 0)
{
lean_object* v_toConfigDecl_2961_; lean_object* v_name_2962_; lean_object* v_kind_2963_; lean_object* v_config_2964_; lean_object* v___x_2965_; uint8_t v___x_2966_; 
v_toConfigDecl_2961_ = lean_array_uget_borrowed(v_as_2951_, v_i_2952_);
v_name_2962_ = lean_ctor_get(v_toConfigDecl_2961_, 1);
v_kind_2963_ = lean_ctor_get(v_toConfigDecl_2961_, 2);
v_config_2964_ = lean_ctor_get(v_toConfigDecl_2961_, 3);
v___x_2965_ = l_Lake_ExternLib_keyword;
v___x_2966_ = lean_name_eq(v_kind_2963_, v___x_2965_);
if (v___x_2966_ == 0)
{
v___y_2956_ = v_b_2954_;
goto v___jp_2955_;
}
else
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
lean_inc(v_config_2964_);
lean_inc(v_name_2962_);
lean_inc_ref(v___x_2950_);
v___x_2967_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2950_);
lean_ctor_set(v___x_2967_, 1, v_name_2962_);
lean_ctor_set(v___x_2967_, 2, v_config_2964_);
v___x_2968_ = lean_array_push(v_b_2954_, v___x_2967_);
v___y_2956_ = v___x_2968_;
goto v___jp_2955_;
}
}
else
{
lean_dec_ref(v___x_2950_);
return v_b_2954_;
}
v___jp_2955_:
{
size_t v___x_2957_; size_t v___x_2958_; 
v___x_2957_ = ((size_t)1ULL);
v___x_2958_ = lean_usize_add(v_i_2952_, v___x_2957_);
v_i_2952_ = v___x_2958_;
v_b_2954_ = v___y_2956_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(lean_object* v___x_2969_, lean_object* v_as_2970_, lean_object* v_i_2971_, lean_object* v_stop_2972_, lean_object* v_b_2973_){
_start:
{
size_t v_i_boxed_2974_; size_t v_stop_boxed_2975_; lean_object* v_res_2976_; 
v_i_boxed_2974_ = lean_unbox_usize(v_i_2971_);
lean_dec(v_i_2971_);
v_stop_boxed_2975_ = lean_unbox_usize(v_stop_2972_);
lean_dec(v_stop_2972_);
v_res_2976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v___x_2969_, v_as_2970_, v_i_boxed_2974_, v_stop_boxed_2975_, v_b_2973_);
lean_dec_ref(v_as_2970_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(lean_object* v_as_2977_, size_t v_i_2978_, size_t v_stop_2979_, lean_object* v_b_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
uint8_t v___x_2988_; 
v___x_2988_ = lean_usize_dec_eq(v_i_2978_, v_stop_2979_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; lean_object* v_lib_2990_; lean_object* v_config_2991_; lean_object* v_nativeFacets_2992_; uint8_t v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; size_t v_sz_2996_; size_t v___x_2997_; lean_object* v___x_2998_; 
v___x_2989_ = lean_array_uget_borrowed(v_as_2977_, v_i_2978_);
v_lib_2990_ = lean_ctor_get(v___x_2989_, 0);
v_config_2991_ = lean_ctor_get(v_lib_2990_, 2);
v_nativeFacets_2992_ = lean_ctor_get(v_config_2991_, 8);
v___x_2993_ = 1;
v___x_2994_ = lean_box(v___x_2993_);
lean_inc_ref(v_nativeFacets_2992_);
v___x_2995_ = lean_apply_1(v_nativeFacets_2992_, v___x_2994_);
v_sz_2996_ = lean_array_size(v___x_2995_);
v___x_2997_ = ((size_t)0ULL);
lean_inc_ref(v___y_2981_);
lean_inc(v___x_2989_);
v___x_2998_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2989_, v_sz_2996_, v___x_2997_, v___x_2995_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v_a_3000_; lean_object* v___x_3001_; size_t v___x_3002_; size_t v___x_3003_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
v_a_3000_ = lean_ctor_get(v___x_2998_, 1);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2998_, 2);
v___x_3001_ = l_Array_append___redArg(v_b_2980_, v_a_2999_);
lean_dec(v_a_2999_);
v___x_3002_ = ((size_t)1ULL);
v___x_3003_ = lean_usize_add(v_i_2978_, v___x_3002_);
v_i_2978_ = v___x_3003_;
v_b_2980_ = v___x_3001_;
v___y_2986_ = v_a_3000_;
goto _start;
}
else
{
lean_dec_ref(v___y_2981_);
lean_dec_ref(v_b_2980_);
return v___x_2998_;
}
}
else
{
lean_object* v___x_3005_; 
lean_dec_ref(v___y_2981_);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v_b_2980_);
lean_ctor_set(v___x_3005_, 1, v___y_2986_);
return v___x_3005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object* v_as_3006_, lean_object* v_i_3007_, lean_object* v_stop_3008_, lean_object* v_b_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
size_t v_i_boxed_3017_; size_t v_stop_boxed_3018_; lean_object* v_res_3019_; 
v_i_boxed_3017_ = lean_unbox_usize(v_i_3007_);
lean_dec(v_i_3007_);
v_stop_boxed_3018_ = lean_unbox_usize(v_stop_3008_);
lean_dec(v_stop_3008_);
v_res_3019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_as_3006_, v_i_boxed_3017_, v_stop_boxed_3018_, v_b_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec(v___y_3012_);
lean_dec(v___y_3011_);
lean_dec_ref(v_as_3006_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(lean_object* v_self_3020_, lean_object* v_dir_3021_, lean_object* v___x_3022_, lean_object* v_targetDecls_3023_, lean_object* v_pkg_3024_, lean_object* v_name_3025_, lean_object* v___x_3026_, lean_object* v_config_3027_, lean_object* v_config_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v_a_3037_; lean_object* v_a_3038_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v_a_3048_; lean_object* v_a_3049_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v_a_3096_; lean_object* v_a_3097_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v_snd_3115_; lean_object* v_a_3116_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v_a_3138_; lean_object* v_a_3139_; lean_object* v___x_3162_; 
lean_inc_ref(v___y_3029_);
lean_inc_ref(v___y_3033_);
lean_inc_ref(v___y_3032_);
lean_inc(v___y_3031_);
lean_inc(v___x_3022_);
v___x_3162_ = lean_apply_7(v___y_3029_, v___x_3026_, v___x_3022_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, lean_box(0));
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v_a_3164_; lean_object* v___x_3165_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
v_a_3164_ = lean_ctor_get(v___x_3162_, 1);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3162_, 2);
v___x_3165_ = l_Lake_Job_await___redArg(v_a_3163_, v_a_3164_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v_a_3167_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v_a_3178_; lean_object* v_a_3179_; lean_object* v_a_3191_; lean_object* v_a_3192_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; uint8_t v___x_3226_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
v_a_3167_ = lean_ctor_get(v___x_3165_, 1);
lean_inc(v_a_3167_);
lean_dec_ref_known(v___x_3165_, 2);
v___x_3223_ = lean_unsigned_to_nat(0u);
v___x_3224_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_3225_ = lean_array_get_size(v_a_3166_);
v___x_3226_ = lean_nat_dec_lt(v___x_3223_, v___x_3225_);
if (v___x_3226_ == 0)
{
v_a_3191_ = v___x_3224_;
v_a_3192_ = v_a_3167_;
goto v___jp_3190_;
}
else
{
size_t v___x_3227_; size_t v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = ((size_t)0ULL);
v___x_3228_ = lean_usize_of_nat(v___x_3225_);
lean_inc_ref(v___y_3029_);
v___x_3229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3166_, v___x_3227_, v___x_3228_, v___x_3224_, v___y_3029_, v___x_3022_, v___y_3031_, v___y_3032_, v___y_3033_, v_a_3167_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v_a_3231_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
v_a_3231_ = lean_ctor_get(v___x_3229_, 1);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3229_, 2);
v_a_3191_ = v_a_3230_;
v_a_3192_ = v_a_3231_;
goto v___jp_3190_;
}
else
{
lean_object* v_a_3232_; lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3240_; 
lean_dec(v_a_3166_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v_config_3027_);
lean_dec(v_name_3025_);
lean_dec_ref(v_pkg_3024_);
lean_dec(v___x_3022_);
lean_dec_ref(v_dir_3021_);
lean_dec_ref(v_self_3020_);
v_a_3232_ = lean_ctor_get(v___x_3229_, 0);
v_a_3233_ = lean_ctor_get(v___x_3229_, 1);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3235_ = v___x_3229_;
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_inc(v_a_3232_);
lean_dec(v___x_3229_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3232_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_a_3233_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
v___jp_3168_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; uint8_t v___x_3182_; 
v___x_3180_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
v___x_3181_ = lean_array_get_size(v_a_3166_);
v___x_3182_ = lean_nat_dec_lt(v___y_3171_, v___x_3181_);
if (v___x_3182_ == 0)
{
lean_dec(v_a_3166_);
v___y_3128_ = v___y_3169_;
v___y_3129_ = v___y_3170_;
v___y_3130_ = v___y_3171_;
v___y_3131_ = v___y_3172_;
v___y_3132_ = v___y_3173_;
v___y_3133_ = v_a_3178_;
v___y_3134_ = v___y_3174_;
v___y_3135_ = v___y_3175_;
v___y_3136_ = v___y_3176_;
v___y_3137_ = v___y_3177_;
v_a_3138_ = v___x_3180_;
v_a_3139_ = v_a_3179_;
goto v___jp_3127_;
}
else
{
size_t v___x_3183_; size_t v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = ((size_t)0ULL);
v___x_3184_ = lean_usize_of_nat(v___x_3181_);
lean_inc_ref(v___y_3029_);
v___x_3185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3166_, v___x_3183_, v___x_3184_, v___x_3180_, v___y_3029_, v___x_3022_, v___y_3031_, v___y_3032_, v___y_3033_, v_a_3179_);
lean_dec(v_a_3166_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v_a_3187_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
v_a_3187_ = lean_ctor_get(v___x_3185_, 1);
lean_inc(v_a_3187_);
lean_dec_ref_known(v___x_3185_, 2);
v___y_3128_ = v___y_3169_;
v___y_3129_ = v___y_3170_;
v___y_3130_ = v___y_3171_;
v___y_3131_ = v___y_3172_;
v___y_3132_ = v___y_3173_;
v___y_3133_ = v_a_3178_;
v___y_3134_ = v___y_3174_;
v___y_3135_ = v___y_3175_;
v___y_3136_ = v___y_3176_;
v___y_3137_ = v___y_3177_;
v_a_3138_ = v_a_3186_;
v_a_3139_ = v_a_3187_;
goto v___jp_3127_;
}
else
{
lean_object* v_a_3188_; lean_object* v_a_3189_; 
lean_dec_ref(v_a_3178_);
lean_dec_ref(v___y_3177_);
lean_dec_ref(v___y_3175_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec_ref(v___y_3170_);
lean_dec_ref(v___y_3029_);
lean_dec(v_name_3025_);
lean_dec_ref(v_pkg_3024_);
lean_dec(v___x_3022_);
lean_dec_ref(v_dir_3021_);
lean_dec_ref(v_self_3020_);
v_a_3188_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3188_);
v_a_3189_ = lean_ctor_get(v___x_3185_, 1);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3185_, 2);
v_a_3037_ = v_a_3188_;
v_a_3038_ = v_a_3189_;
goto v___jp_3036_;
}
}
}
v___jp_3190_:
{
lean_object* v_toLeanConfig_3193_; lean_object* v_toLeanConfig_3194_; lean_object* v_buildDir_3195_; lean_object* v_nativeLibDir_3196_; lean_object* v_moreLinkObjs_3197_; lean_object* v_moreLinkLibs_3198_; lean_object* v_moreLinkArgs_3199_; lean_object* v_weakLinkArgs_3200_; lean_object* v_moreLinkObjs_3201_; lean_object* v_moreLinkLibs_3202_; lean_object* v_moreLinkArgs_3203_; lean_object* v_weakLinkArgs_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; uint8_t v___x_3208_; 
v_toLeanConfig_3193_ = lean_ctor_get(v_config_3027_, 1);
lean_inc_ref(v_toLeanConfig_3193_);
v_toLeanConfig_3194_ = lean_ctor_get(v_config_3028_, 0);
v_buildDir_3195_ = lean_ctor_get(v_config_3027_, 5);
lean_inc_ref(v_buildDir_3195_);
v_nativeLibDir_3196_ = lean_ctor_get(v_config_3027_, 7);
lean_inc_ref(v_nativeLibDir_3196_);
lean_dec_ref(v_config_3027_);
v_moreLinkObjs_3197_ = lean_ctor_get(v_toLeanConfig_3193_, 6);
lean_inc_ref(v_moreLinkObjs_3197_);
v_moreLinkLibs_3198_ = lean_ctor_get(v_toLeanConfig_3193_, 7);
lean_inc_ref(v_moreLinkLibs_3198_);
v_moreLinkArgs_3199_ = lean_ctor_get(v_toLeanConfig_3193_, 8);
lean_inc_ref(v_moreLinkArgs_3199_);
v_weakLinkArgs_3200_ = lean_ctor_get(v_toLeanConfig_3193_, 9);
lean_inc_ref(v_weakLinkArgs_3200_);
lean_dec_ref(v_toLeanConfig_3193_);
v_moreLinkObjs_3201_ = lean_ctor_get(v_toLeanConfig_3194_, 6);
v_moreLinkLibs_3202_ = lean_ctor_get(v_toLeanConfig_3194_, 7);
v_moreLinkArgs_3203_ = lean_ctor_get(v_toLeanConfig_3194_, 8);
v_weakLinkArgs_3204_ = lean_ctor_get(v_toLeanConfig_3194_, 9);
v___x_3205_ = l_Array_append___redArg(v_moreLinkObjs_3197_, v_moreLinkObjs_3201_);
v___x_3206_ = lean_unsigned_to_nat(0u);
v___x_3207_ = lean_array_get_size(v___x_3205_);
v___x_3208_ = lean_nat_dec_lt(v___x_3206_, v___x_3207_);
if (v___x_3208_ == 0)
{
lean_dec_ref(v___x_3205_);
v___y_3169_ = v_moreLinkArgs_3203_;
v___y_3170_ = v_weakLinkArgs_3200_;
v___y_3171_ = v___x_3206_;
v___y_3172_ = v_moreLinkArgs_3199_;
v___y_3173_ = v_moreLinkLibs_3198_;
v___y_3174_ = v_weakLinkArgs_3204_;
v___y_3175_ = v_buildDir_3195_;
v___y_3176_ = v_moreLinkLibs_3202_;
v___y_3177_ = v_nativeLibDir_3196_;
v_a_3178_ = v_a_3191_;
v_a_3179_ = v_a_3192_;
goto v___jp_3168_;
}
else
{
size_t v___x_3209_; size_t v___x_3210_; lean_object* v___x_3211_; 
v___x_3209_ = ((size_t)0ULL);
v___x_3210_ = lean_usize_of_nat(v___x_3207_);
lean_inc_ref(v___y_3029_);
lean_inc_ref(v_pkg_3024_);
v___x_3211_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_3024_, v___x_3205_, v___x_3209_, v___x_3210_, v_a_3191_, v___y_3029_, v___x_3022_, v___y_3031_, v___y_3032_, v___y_3033_, v_a_3192_);
lean_dec_ref(v___x_3205_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v_a_3213_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
v_a_3213_ = lean_ctor_get(v___x_3211_, 1);
lean_inc(v_a_3213_);
lean_dec_ref_known(v___x_3211_, 2);
v___y_3169_ = v_moreLinkArgs_3203_;
v___y_3170_ = v_weakLinkArgs_3200_;
v___y_3171_ = v___x_3206_;
v___y_3172_ = v_moreLinkArgs_3199_;
v___y_3173_ = v_moreLinkLibs_3198_;
v___y_3174_ = v_weakLinkArgs_3204_;
v___y_3175_ = v_buildDir_3195_;
v___y_3176_ = v_moreLinkLibs_3202_;
v___y_3177_ = v_nativeLibDir_3196_;
v_a_3178_ = v_a_3212_;
v_a_3179_ = v_a_3213_;
goto v___jp_3168_;
}
else
{
lean_object* v_a_3214_; lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_dec_ref(v_weakLinkArgs_3200_);
lean_dec_ref(v_moreLinkArgs_3199_);
lean_dec_ref(v_moreLinkLibs_3198_);
lean_dec_ref(v_nativeLibDir_3196_);
lean_dec_ref(v_buildDir_3195_);
lean_dec(v_a_3166_);
lean_dec_ref(v___y_3029_);
lean_dec(v_name_3025_);
lean_dec_ref(v_pkg_3024_);
lean_dec(v___x_3022_);
lean_dec_ref(v_dir_3021_);
lean_dec_ref(v_self_3020_);
v_a_3214_ = lean_ctor_get(v___x_3211_, 0);
v_a_3215_ = lean_ctor_get(v___x_3211_, 1);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3211_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_inc(v_a_3214_);
lean_dec(v___x_3211_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3214_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
}
}
else
{
lean_object* v_a_3241_; lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec_ref(v___y_3029_);
lean_dec_ref(v_config_3027_);
lean_dec(v_name_3025_);
lean_dec_ref(v_pkg_3024_);
lean_dec(v___x_3022_);
lean_dec_ref(v_dir_3021_);
lean_dec_ref(v_self_3020_);
v_a_3241_ = lean_ctor_get(v___x_3165_, 0);
v_a_3242_ = lean_ctor_get(v___x_3165_, 1);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3165_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_inc(v_a_3241_);
lean_dec(v___x_3165_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3241_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
else
{
lean_object* v_a_3250_; lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec_ref(v___y_3029_);
lean_dec_ref(v_config_3027_);
lean_dec(v_name_3025_);
lean_dec_ref(v_pkg_3024_);
lean_dec(v___x_3022_);
lean_dec_ref(v_dir_3021_);
lean_dec_ref(v_self_3020_);
v_a_3250_ = lean_ctor_get(v___x_3162_, 0);
v_a_3251_ = lean_ctor_get(v___x_3162_, 1);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3162_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_inc(v_a_3250_);
lean_dec(v___x_3162_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3250_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
v___jp_3036_:
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3039_, 0, v_a_3037_);
lean_ctor_set(v___x_3039_, 1, v_a_3038_);
return v___x_3039_;
}
v___jp_3040_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; uint8_t v___x_3060_; uint8_t v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_inc_ref(v_self_3020_);
v___x_3050_ = l_Lake_LeanLib_libName(v_self_3020_);
v___x_3051_ = l_System_FilePath_normalize(v___y_3046_);
v___x_3052_ = l_Lake_joinRelative(v_dir_3021_, v___x_3051_);
v___x_3053_ = l_System_FilePath_normalize(v___y_3047_);
v___x_3054_ = l_Lake_joinRelative(v___x_3052_, v___x_3053_);
v___x_3055_ = 0;
v___x_3056_ = l_Lake_nameToSharedLib(v___x_3050_, v___x_3055_);
v___x_3057_ = l_Lake_joinRelative(v___x_3054_, v___x_3056_);
v___x_3058_ = l_Array_append___redArg(v___y_3042_, v___y_3045_);
v___x_3059_ = l_Array_append___redArg(v___y_3043_, v___y_3041_);
v___x_3060_ = l_Lake_LeanLib_isPlugin(v_self_3020_);
v___x_3061_ = l_System_Platform_isWindows;
v___x_3062_ = lean_box(0);
v___x_3063_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_3064_ = l_Lake_buildLeanSharedLib(v___x_3050_, v___x_3057_, v___y_3044_, v_a_3048_, v___x_3058_, v___x_3059_, v___x_3060_, v___x_3061_, v___x_3062_, v___y_3029_, v___x_3022_, v___y_3031_, v___y_3032_, v___y_3033_, v___x_3063_);
lean_dec(v___x_3022_);
lean_dec_ref(v___y_3044_);
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
lean_ctor_set(v___x_3065_, 1, v_a_3049_);
return v___x_3065_;
}
v___jp_3066_:
{
lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3078_ = lean_array_get_size(v___y_3077_);
v___x_3079_ = lean_nat_dec_lt(v___y_3069_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_dec_ref(v___y_3077_);
v___y_3041_ = v___y_3067_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___y_3070_;
v___y_3044_ = v___y_3073_;
v___y_3045_ = v___y_3072_;
v___y_3046_ = v___y_3075_;
v___y_3047_ = v___y_3076_;
v_a_3048_ = v___y_3071_;
v_a_3049_ = v___y_3074_;
goto v___jp_3040_;
}
else
{
size_t v___x_3080_; size_t v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = ((size_t)0ULL);
v___x_3081_ = lean_usize_of_nat(v___x_3078_);
lean_inc_ref(v___y_3029_);
v___x_3082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_3077_, v___x_3080_, v___x_3081_, v___y_3071_, v___y_3029_, v___x_3022_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3074_);
lean_dec_ref(v___y_3077_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v_a_3084_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
v_a_3084_ = lean_ctor_get(v___x_3082_, 1);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3082_, 2);
v___y_3041_ = v___y_3067_;
v___y_3042_ = v___y_3068_;
v___y_3043_ = v___y_3070_;
v___y_3044_ = v___y_3073_;
v___y_3045_ = v___y_3072_;
v___y_3046_ = v___y_3075_;
v___y_3047_ = v___y_3076_;
v_a_3048_ = v_a_3083_;
v_a_3049_ = v_a_3084_;
goto v___jp_3040_;
}
else
{
lean_object* v_a_3085_; lean_object* v_a_3086_; 
lean_dec_ref(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec_ref(v___y_3073_);
lean_dec_ref(v___y_3070_);
lean_dec_ref(v___y_3068_);
lean_dec_ref(v___y_3029_);
lean_dec(v___x_3022_);
lean_dec_ref(v_dir_3021_);
lean_dec_ref(v_self_3020_);
v_a_3085_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3085_);
v_a_3086_ = lean_ctor_get(v___x_3082_, 1);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3082_, 2);
v_a_3037_ = v_a_3085_;
v_a_3038_ = v_a_3086_;
goto v___jp_3036_;
}
}
}
v___jp_3087_:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3098_ = lean_mk_empty_array_with_capacity(v___y_3090_);
v___x_3099_ = lean_array_get_size(v_targetDecls_3023_);
v___x_3100_ = lean_nat_dec_lt(v___y_3090_, v___x_3099_);
if (v___x_3100_ == 0)
{
lean_dec_ref(v_pkg_3024_);
v___y_3067_ = v___y_3088_;
v___y_3068_ = v___y_3089_;
v___y_3069_ = v___y_3090_;
v___y_3070_ = v___y_3091_;
v___y_3071_ = v_a_3096_;
v___y_3072_ = v___y_3093_;
v___y_3073_ = v___y_3092_;
v___y_3074_ = v_a_3097_;
v___y_3075_ = v___y_3094_;
v___y_3076_ = v___y_3095_;
v___y_3077_ = v___x_3098_;
goto v___jp_3066_;
}
else
{
size_t v___x_3101_; size_t v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = ((size_t)0ULL);
v___x_3102_ = lean_usize_of_nat(v___x_3099_);
v___x_3103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_3024_, v_targetDecls_3023_, v___x_3101_, v___x_3102_, v___x_3098_);
v___y_3067_ = v___y_3088_;
v___y_3068_ = v___y_3089_;
v___y_3069_ = v___y_3090_;
v___y_3070_ = v___y_3091_;
v___y_3071_ = v_a_3096_;
v___y_3072_ = v___y_3093_;
v___y_3073_ = v___y_3092_;
v___y_3074_ = v_a_3097_;
v___y_3075_ = v___y_3094_;
v___y_3076_ = v___y_3095_;
v___y_3077_ = v___x_3103_;
goto v___jp_3066_;
}
}
v___jp_3104_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; 
v___x_3117_ = l_Array_append___redArg(v___y_3109_, v___y_3114_);
v___x_3118_ = lean_array_get_size(v___x_3117_);
v___x_3119_ = lean_nat_dec_lt(v___y_3107_, v___x_3118_);
if (v___x_3119_ == 0)
{
lean_dec_ref(v___x_3117_);
v___y_3088_ = v___y_3105_;
v___y_3089_ = v___y_3106_;
v___y_3090_ = v___y_3107_;
v___y_3091_ = v___y_3108_;
v___y_3092_ = v___y_3111_;
v___y_3093_ = v___y_3110_;
v___y_3094_ = v___y_3112_;
v___y_3095_ = v___y_3113_;
v_a_3096_ = v_snd_3115_;
v_a_3097_ = v_a_3116_;
goto v___jp_3087_;
}
else
{
size_t v___x_3120_; size_t v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = ((size_t)0ULL);
v___x_3121_ = lean_usize_of_nat(v___x_3118_);
lean_inc_ref(v___y_3029_);
lean_inc_ref(v_pkg_3024_);
v___x_3122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_3024_, v___x_3117_, v___x_3120_, v___x_3121_, v_snd_3115_, v___y_3029_, v___x_3022_, v___y_3031_, v___y_3032_, v___y_3033_, v_a_3116_);
lean_dec_ref(v___x_3117_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v_a_3124_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
v_a_3124_ = lean_ctor_get(v___x_3122_, 1);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3122_, 2);
v___y_3088_ = v___y_3105_;
v___y_3089_ = v___y_3106_;
v___y_3090_ = v___y_3107_;
v___y_3091_ = v___y_3108_;
v___y_3092_ = v___y_3111_;
v___y_3093_ = v___y_3110_;
v___y_3094_ = v___y_3112_;
v___y_3095_ = v___y_3113_;
v_a_3096_ = v_a_3123_;
v_a_3097_ = v_a_3124_;
goto v___jp_3087_;
}
else
{
lean_object* v_a_3125_; lean_object* v_a_3126_; 
lean_dec_ref(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v___y_3106_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v_pkg_3024_);
lean_dec(v___x_3022_);
lean_dec_ref(v_dir_3021_);
lean_dec_ref(v_self_3020_);
v_a_3125_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3125_);
v_a_3126_ = lean_ctor_get(v___x_3122_, 1);
lean_inc(v_a_3126_);
lean_dec_ref_known(v___x_3122_, 2);
v_a_3037_ = v_a_3125_;
v_a_3038_ = v_a_3126_;
goto v___jp_3036_;
}
}
}
v___jp_3127_:
{
lean_object* v_toArray_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3160_; 
v_toArray_3140_ = lean_ctor_get(v_a_3138_, 1);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_a_3138_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; 
v_unused_3161_ = lean_ctor_get(v_a_3138_, 0);
lean_dec(v_unused_3161_);
v___x_3142_ = v_a_3138_;
v_isShared_3143_ = v_isSharedCheck_3160_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_toArray_3140_);
lean_dec(v_a_3138_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3160_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; uint8_t v___x_3146_; 
v___x_3144_ = lean_mk_empty_array_with_capacity(v___y_3130_);
v___x_3145_ = lean_array_get_size(v_toArray_3140_);
v___x_3146_ = lean_nat_dec_lt(v___y_3130_, v___x_3145_);
if (v___x_3146_ == 0)
{
lean_del_object(v___x_3142_);
lean_dec_ref(v_toArray_3140_);
lean_dec(v_name_3025_);
v___y_3105_ = v___y_3128_;
v___y_3106_ = v___y_3129_;
v___y_3107_ = v___y_3130_;
v___y_3108_ = v___y_3131_;
v___y_3109_ = v___y_3132_;
v___y_3110_ = v___y_3134_;
v___y_3111_ = v___y_3133_;
v___y_3112_ = v___y_3135_;
v___y_3113_ = v___y_3137_;
v___y_3114_ = v___y_3136_;
v_snd_3115_ = v___x_3144_;
v_a_3116_ = v_a_3139_;
goto v___jp_3104_;
}
else
{
lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3150_; 
v___x_3147_ = l_Lean_NameSet_empty;
v___x_3148_ = l_Lean_NameSet_insert(v___x_3147_, v_name_3025_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 1, v___x_3144_);
lean_ctor_set(v___x_3142_, 0, v___x_3148_);
v___x_3150_ = v___x_3142_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3148_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___x_3144_);
v___x_3150_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
size_t v___x_3151_; size_t v___x_3152_; lean_object* v___x_3153_; 
v___x_3151_ = ((size_t)0ULL);
v___x_3152_ = lean_usize_of_nat(v___x_3145_);
lean_inc_ref(v___y_3029_);
v___x_3153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_3140_, v___x_3151_, v___x_3152_, v___x_3150_, v___y_3029_, v___x_3022_, v___y_3031_, v___y_3032_, v___y_3033_, v_a_3139_);
lean_dec_ref(v_toArray_3140_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v_a_3155_; lean_object* v_snd_3156_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
v_a_3155_ = lean_ctor_get(v___x_3153_, 1);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3153_, 2);
v_snd_3156_ = lean_ctor_get(v_a_3154_, 1);
lean_inc(v_snd_3156_);
lean_dec(v_a_3154_);
v___y_3105_ = v___y_3128_;
v___y_3106_ = v___y_3129_;
v___y_3107_ = v___y_3130_;
v___y_3108_ = v___y_3131_;
v___y_3109_ = v___y_3132_;
v___y_3110_ = v___y_3134_;
v___y_3111_ = v___y_3133_;
v___y_3112_ = v___y_3135_;
v___y_3113_ = v___y_3137_;
v___y_3114_ = v___y_3136_;
v_snd_3115_ = v_snd_3156_;
v_a_3116_ = v_a_3155_;
goto v___jp_3104_;
}
else
{
lean_object* v_a_3157_; lean_object* v_a_3158_; 
lean_dec_ref(v___y_3137_);
lean_dec_ref(v___y_3135_);
lean_dec_ref(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v_pkg_3024_);
lean_dec(v___x_3022_);
lean_dec_ref(v_dir_3021_);
lean_dec_ref(v_self_3020_);
v_a_3157_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3157_);
v_a_3158_ = lean_ctor_get(v___x_3153_, 1);
lean_inc(v_a_3158_);
lean_dec_ref_known(v___x_3153_, 2);
v_a_3037_ = v_a_3157_;
v_a_3038_ = v_a_3158_;
goto v___jp_3036_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* v_self_3259_, lean_object* v_dir_3260_, lean_object* v___x_3261_, lean_object* v_targetDecls_3262_, lean_object* v_pkg_3263_, lean_object* v_name_3264_, lean_object* v___x_3265_, lean_object* v_config_3266_, lean_object* v_config_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v_self_3259_, v_dir_3260_, v___x_3261_, v_targetDecls_3262_, v_pkg_3263_, v_name_3264_, v___x_3265_, v_config_3266_, v_config_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec(v_config_3267_);
lean_dec_ref(v_targetDecls_3262_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object* v_self_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_){
_start:
{
lean_object* v_pkg_3285_; lean_object* v_name_3286_; lean_object* v_config_3287_; lean_object* v_keyName_3288_; lean_object* v_dir_3289_; lean_object* v_config_3290_; lean_object* v_targetDecls_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___f_3302_; uint8_t v___x_3303_; lean_object* v___x_3304_; 
v_pkg_3285_ = lean_ctor_get(v_self_3277_, 0);
lean_inc_ref_n(v_pkg_3285_, 2);
v_name_3286_ = lean_ctor_get(v_self_3277_, 1);
lean_inc_n(v_name_3286_, 3);
v_config_3287_ = lean_ctor_get(v_self_3277_, 2);
lean_inc(v_config_3287_);
v_keyName_3288_ = lean_ctor_get(v_pkg_3285_, 2);
v_dir_3289_ = lean_ctor_get(v_pkg_3285_, 4);
lean_inc_ref(v_dir_3289_);
v_config_3290_ = lean_ctor_get(v_pkg_3285_, 6);
lean_inc_ref(v_config_3290_);
v_targetDecls_3291_ = lean_ctor_get(v_pkg_3285_, 15);
lean_inc_ref(v_targetDecls_3291_);
v___x_3292_ = l_Lake_instDataKindDynlib;
v___x_3293_ = 1;
v___x_3294_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3286_, v___x_3293_);
v___x_3295_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0));
v___x_3296_ = lean_string_append(v___x_3294_, v___x_3295_);
v___x_3297_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_3288_);
v___x_3298_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3298_, 0, v_keyName_3288_);
lean_ctor_set(v___x_3298_, 1, v_name_3286_);
v___x_3299_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3277_);
v___x_3300_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
lean_ctor_set(v___x_3300_, 2, v_self_3277_);
lean_ctor_set(v___x_3300_, 3, v___x_3297_);
v___x_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3301_, 0, v_pkg_3285_);
v___f_3302_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3302_, 0, v_self_3277_);
lean_closure_set(v___f_3302_, 1, v_dir_3289_);
lean_closure_set(v___f_3302_, 2, v___x_3301_);
lean_closure_set(v___f_3302_, 3, v_targetDecls_3291_);
lean_closure_set(v___f_3302_, 4, v_pkg_3285_);
lean_closure_set(v___f_3302_, 5, v_name_3286_);
lean_closure_set(v___f_3302_, 6, v___x_3300_);
lean_closure_set(v___f_3302_, 7, v_config_3290_);
lean_closure_set(v___f_3302_, 8, v_config_3287_);
v___x_3303_ = 0;
v___x_3304_ = l_Lake_ensureJob___redArg(v___x_3292_, v___f_3302_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3329_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
v_a_3306_ = lean_ctor_get(v___x_3304_, 1);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3308_ = v___x_3304_;
v_isShared_3309_ = v_isSharedCheck_3329_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_inc(v_a_3305_);
lean_dec(v___x_3304_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3329_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v_task_3310_; lean_object* v_kind_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3327_; 
v_task_3310_ = lean_ctor_get(v_a_3305_, 0);
v_kind_3311_ = lean_ctor_get(v_a_3305_, 1);
v_isSharedCheck_3327_ = !lean_is_exclusive(v_a_3305_);
if (v_isSharedCheck_3327_ == 0)
{
lean_object* v_unused_3328_; 
v_unused_3328_ = lean_ctor_get(v_a_3305_, 2);
lean_dec(v_unused_3328_);
v___x_3313_ = v_a_3305_;
v_isShared_3314_ = v_isSharedCheck_3327_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_kind_3311_);
lean_inc(v_task_3310_);
lean_dec(v_a_3305_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3327_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v_registeredJobs_3315_; lean_object* v_job_3317_; 
v_registeredJobs_3315_ = lean_ctor_get(v_a_3282_, 4);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 2, v___x_3296_);
v_job_3317_ = v___x_3313_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_task_3310_);
lean_ctor_set(v_reuseFailAlloc_3326_, 1, v_kind_3311_);
lean_ctor_set(v_reuseFailAlloc_3326_, 2, v___x_3296_);
v_job_3317_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
lean_ctor_set_uint8(v_job_3317_, sizeof(void*)*3, v___x_3303_);
v___x_3318_ = lean_st_ref_take(v_registeredJobs_3315_);
lean_inc_ref(v_job_3317_);
v___x_3319_ = l_Lake_Job_toOpaque___redArg(v_job_3317_);
v___x_3320_ = lean_array_push(v___x_3318_, v___x_3319_);
v___x_3321_ = lean_st_ref_put(v_registeredJobs_3315_, v___x_3320_);
v___x_3322_ = l_Lake_Job_renew___redArg(v_job_3317_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3322_);
v___x_3324_ = v___x_3308_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_a_3306_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3296_);
return v___x_3304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object* v_self_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_);
lean_dec_ref(v_a_3335_);
lean_dec_ref(v_a_3334_);
lean_dec(v_a_3333_);
lean_dec(v_a_3332_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t v_fmt_3339_, lean_object* v_a_3340_){
_start:
{
if (v_fmt_3339_ == 0)
{
lean_object* v_path_3341_; 
v_path_3341_ = lean_ctor_get(v_a_3340_, 0);
lean_inc_ref(v_path_3341_);
return v_path_3341_;
}
else
{
lean_object* v_path_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_path_3342_ = lean_ctor_get(v_a_3340_, 0);
lean_inc_ref(v_path_3342_);
v___x_3343_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3343_, 0, v_path_3342_);
v___x_3344_ = l_Lean_Json_compress(v___x_3343_);
return v___x_3344_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* v_fmt_3345_, lean_object* v_a_3346_){
_start:
{
uint8_t v_fmt_boxed_3347_; lean_object* v_res_3348_; 
v_fmt_boxed_3347_ = lean_unbox(v_fmt_3345_);
v_res_3348_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_boxed_3347_, v_a_3346_);
lean_dec_ref(v_a_3346_);
return v_res_3348_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3351_; uint8_t v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___f_3351_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__0));
v___x_3352_ = 1;
v___x_3353_ = l_Lake_instDataKindDynlib;
v___x_3354_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__1));
v___x_3355_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3356_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
lean_ctor_set(v___x_3356_, 1, v___x_3354_);
lean_ctor_set(v___x_3356_, 2, v___x_3353_);
lean_ctor_set(v___x_3356_, 3, v___f_3351_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*4, v___x_3352_);
lean_ctor_set_uint8(v___x_3356_, sizeof(void*)*4 + 1, v___x_3352_);
return v___x_3356_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_obj_once(&l_Lake_LeanLib_sharedFacetConfig___closed__2, &l_Lake_LeanLib_sharedFacetConfig___closed__2_once, _init_l_Lake_LeanLib_sharedFacetConfig___closed__2);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* v___x_3358_, lean_object* v_as_3359_, size_t v_sz_3360_, size_t v_i_3361_, lean_object* v_b_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
uint8_t v___x_3370_; 
v___x_3370_ = lean_usize_dec_lt(v_i_3361_, v_sz_3360_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; 
lean_dec_ref(v___y_3363_);
lean_dec_ref(v___x_3358_);
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v_b_3362_);
lean_ctor_set(v___x_3371_, 1, v___y_3368_);
return v___x_3371_;
}
else
{
lean_object* v_a_3372_; lean_object* v___x_3373_; 
v_a_3372_ = lean_array_uget_borrowed(v_as_3359_, v_i_3361_);
lean_inc_ref(v___y_3363_);
lean_inc_n(v_a_3372_, 2);
lean_inc_ref(v___x_3358_);
v___x_3373_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v___x_3358_, v_a_3372_, v_a_3372_, v___x_3370_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
if (lean_obj_tag(v___x_3373_) == 0)
{
lean_object* v_a_3374_; lean_object* v_a_3375_; lean_object* v_snd_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; size_t v___x_3379_; size_t v___x_3380_; 
v_a_3374_ = lean_ctor_get(v___x_3373_, 0);
lean_inc(v_a_3374_);
v_a_3375_ = lean_ctor_get(v___x_3373_, 1);
lean_inc(v_a_3375_);
lean_dec_ref_known(v___x_3373_, 2);
v_snd_3376_ = lean_ctor_get(v_a_3374_, 1);
lean_inc(v_snd_3376_);
lean_dec(v_a_3374_);
v___x_3377_ = l_Lake_Job_toOpaque___redArg(v_snd_3376_);
v___x_3378_ = l_Lake_Job_mix___redArg(v_b_3362_, v___x_3377_);
v___x_3379_ = ((size_t)1ULL);
v___x_3380_ = lean_usize_add(v_i_3361_, v___x_3379_);
v_i_3361_ = v___x_3380_;
v_b_3362_ = v___x_3378_;
v___y_3368_ = v_a_3375_;
goto _start;
}
else
{
lean_object* v_a_3382_; lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec_ref(v___y_3363_);
lean_dec_ref(v_b_3362_);
lean_dec_ref(v___x_3358_);
v_a_3382_ = lean_ctor_get(v___x_3373_, 0);
v_a_3383_ = lean_ctor_get(v___x_3373_, 1);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3373_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_inc(v_a_3382_);
lean_dec(v___x_3373_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3382_);
lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* v___x_3391_, lean_object* v_as_3392_, lean_object* v_sz_3393_, lean_object* v_i_3394_, lean_object* v_b_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
size_t v_sz_boxed_3403_; size_t v_i_boxed_3404_; lean_object* v_res_3405_; 
v_sz_boxed_3403_ = lean_unbox_usize(v_sz_3393_);
lean_dec(v_sz_3393_);
v_i_boxed_3404_ = lean_unbox_usize(v_i_3394_);
lean_dec(v_i_3394_);
v_res_3405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_3391_, v_as_3392_, v_sz_boxed_3403_, v_i_boxed_3404_, v_b_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v_as_3392_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* v___x_3406_, lean_object* v_as_3407_, size_t v_sz_3408_, size_t v_i_3409_, lean_object* v_b_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
uint8_t v___x_3418_; 
v___x_3418_ = lean_usize_dec_lt(v_i_3409_, v_sz_3408_);
if (v___x_3418_ == 0)
{
lean_object* v___x_3419_; 
lean_dec_ref(v___y_3411_);
lean_dec_ref(v___x_3406_);
v___x_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3419_, 0, v_b_3410_);
lean_ctor_set(v___x_3419_, 1, v___y_3416_);
return v___x_3419_;
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3421_; 
v_a_3420_ = lean_array_uget_borrowed(v_as_3407_, v_i_3409_);
lean_inc_ref(v___y_3411_);
lean_inc(v_a_3420_);
lean_inc_ref(v___x_3406_);
v___x_3421_ = l_Lake_Package_fetchTargetJob(v___x_3406_, v_a_3420_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v_a_3423_; lean_object* v___x_3424_; size_t v___x_3425_; size_t v___x_3426_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
v_a_3423_ = lean_ctor_get(v___x_3421_, 1);
lean_inc(v_a_3423_);
lean_dec_ref_known(v___x_3421_, 2);
v___x_3424_ = l_Lake_Job_mix___redArg(v_b_3410_, v_a_3422_);
v___x_3425_ = ((size_t)1ULL);
v___x_3426_ = lean_usize_add(v_i_3409_, v___x_3425_);
v_i_3409_ = v___x_3426_;
v_b_3410_ = v___x_3424_;
v___y_3416_ = v_a_3423_;
goto _start;
}
else
{
lean_object* v_a_3428_; lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec_ref(v___y_3411_);
lean_dec_ref(v_b_3410_);
lean_dec_ref(v___x_3406_);
v_a_3428_ = lean_ctor_get(v___x_3421_, 0);
v_a_3429_ = lean_ctor_get(v___x_3421_, 1);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3421_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_inc(v_a_3428_);
lean_dec(v___x_3421_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3428_);
lean_ctor_set(v_reuseFailAlloc_3435_, 1, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* v___x_3437_, lean_object* v_as_3438_, lean_object* v_sz_3439_, lean_object* v_i_3440_, lean_object* v_b_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
size_t v_sz_boxed_3449_; size_t v_i_boxed_3450_; lean_object* v_res_3451_; 
v_sz_boxed_3449_ = lean_unbox_usize(v_sz_3439_);
lean_dec(v_sz_3439_);
v_i_boxed_3450_ = lean_unbox_usize(v_i_3440_);
lean_dec(v_i_3440_);
v_res_3451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_3437_, v_as_3438_, v_sz_boxed_3449_, v_i_boxed_3450_, v_b_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v_as_3438_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___lam__0(lean_object* v___x_3452_, lean_object* v_config_3453_, lean_object* v_job_3454_, lean_object* v_pkg_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v___x_3463_; 
lean_inc_ref(v___y_3456_);
lean_inc_ref(v___y_3460_);
lean_inc_ref(v___y_3459_);
lean_inc(v___y_3458_);
lean_inc(v___y_3457_);
v___x_3463_ = lean_apply_7(v___y_3456_, v___x_3452_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, lean_box(0));
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v_a_3465_; lean_object* v_needs_3466_; lean_object* v_extraDepTargets_3467_; lean_object* v___x_3468_; size_t v_sz_3469_; size_t v___x_3470_; lean_object* v___x_3471_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
lean_inc(v_a_3464_);
v_a_3465_ = lean_ctor_get(v___x_3463_, 1);
lean_inc(v_a_3465_);
lean_dec_ref_known(v___x_3463_, 2);
v_needs_3466_ = lean_ctor_get(v_config_3453_, 5);
v_extraDepTargets_3467_ = lean_ctor_get(v_config_3453_, 6);
v___x_3468_ = l_Lake_Job_mix___redArg(v_job_3454_, v_a_3464_);
v_sz_3469_ = lean_array_size(v_extraDepTargets_3467_);
v___x_3470_ = ((size_t)0ULL);
lean_inc_ref(v___y_3456_);
lean_inc_ref(v_pkg_3455_);
v___x_3471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_3455_, v_extraDepTargets_3467_, v_sz_3469_, v___x_3470_, v___x_3468_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v_a_3465_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v_a_3473_; size_t v_sz_3474_; lean_object* v___x_3475_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
v_a_3473_ = lean_ctor_get(v___x_3471_, 1);
lean_inc(v_a_3473_);
lean_dec_ref_known(v___x_3471_, 2);
v_sz_3474_ = lean_array_size(v_needs_3466_);
v___x_3475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_3455_, v_needs_3466_, v_sz_3474_, v___x_3470_, v_a_3472_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v_a_3473_);
return v___x_3475_;
}
else
{
lean_dec_ref(v___y_3456_);
lean_dec_ref(v_pkg_3455_);
return v___x_3471_;
}
}
else
{
lean_dec_ref(v___y_3456_);
lean_dec_ref(v_pkg_3455_);
lean_dec_ref(v_job_3454_);
return v___x_3463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___lam__0___boxed(lean_object* v___x_3476_, lean_object* v_config_3477_, lean_object* v_job_3478_, lean_object* v_pkg_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___lam__0(v___x_3476_, v_config_3477_, v_job_3478_, v_pkg_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec(v_config_3477_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object* v_self_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v_pkg_3498_; lean_object* v_name_3499_; lean_object* v_config_3500_; lean_object* v_baseName_3501_; lean_object* v_keyName_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; uint8_t v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v_job_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___f_3528_; lean_object* v___x_3529_; 
v_pkg_3498_ = lean_ctor_get(v_self_3490_, 0);
lean_inc_ref_n(v_pkg_3498_, 2);
v_name_3499_ = lean_ctor_get(v_self_3490_, 1);
lean_inc(v_name_3499_);
v_config_3500_ = lean_ctor_get(v_self_3490_, 2);
lean_inc(v_config_3500_);
lean_dec_ref(v_self_3490_);
v_baseName_3501_ = lean_ctor_get(v_pkg_3498_, 1);
v_keyName_3502_ = lean_ctor_get(v_pkg_3498_, 2);
v___x_3503_ = l_Lake_instDataKindUnit;
v___x_3504_ = 1;
lean_inc(v_baseName_3501_);
v___x_3505_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3501_, v___x_3504_);
v___x_3506_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0));
v___x_3507_ = lean_string_append(v___x_3505_, v___x_3506_);
v___x_3508_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3499_, v___x_3504_);
v___x_3509_ = lean_string_append(v___x_3507_, v___x_3508_);
lean_dec_ref(v___x_3508_);
v___x_3510_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1));
v___x_3511_ = lean_string_append(v___x_3509_, v___x_3510_);
v___x_3512_ = lean_box(0);
v___x_3513_ = lean_box(0);
v___x_3514_ = lean_unsigned_to_nat(0u);
v___x_3515_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___lam__0___closed__0));
v___x_3516_ = 0;
v___x_3517_ = 0;
lean_inc_ref(v___x_3511_);
v___x_3518_ = l_Lake_BuildTrace_nil(v___x_3511_);
v___x_3519_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3519_, 0, v___x_3515_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
lean_ctor_set(v___x_3519_, 2, v___x_3514_);
lean_ctor_set_uint8(v___x_3519_, sizeof(void*)*3, v___x_3516_);
lean_ctor_set_uint8(v___x_3519_, sizeof(void*)*3 + 1, v___x_3517_);
lean_ctor_set_uint8(v___x_3519_, sizeof(void*)*3 + 2, v___x_3517_);
v___x_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3512_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = lean_task_pure(v___x_3520_);
v___x_3522_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v_job_3523_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_3523_, 0, v___x_3521_);
lean_ctor_set(v_job_3523_, 1, v___x_3513_);
lean_ctor_set(v_job_3523_, 2, v___x_3522_);
lean_ctor_set_uint8(v_job_3523_, sizeof(void*)*3, v___x_3517_);
v___x_3524_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_3502_);
v___x_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3525_, 0, v_keyName_3502_);
v___x_3526_ = l_Lake_Package_keyword;
v___x_3527_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3525_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
lean_ctor_set(v___x_3527_, 2, v_pkg_3498_);
lean_ctor_set(v___x_3527_, 3, v___x_3524_);
v___f_3528_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3528_, 0, v___x_3527_);
lean_closure_set(v___f_3528_, 1, v_config_3500_);
lean_closure_set(v___f_3528_, 2, v_job_3523_);
lean_closure_set(v___f_3528_, 3, v_pkg_3498_);
v___x_3529_ = l_Lake_ensureJob___redArg(v___x_3503_, v___f_3528_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3554_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
v_a_3531_ = lean_ctor_get(v___x_3529_, 1);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3533_ = v___x_3529_;
v_isShared_3534_ = v_isSharedCheck_3554_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_inc(v_a_3530_);
lean_dec(v___x_3529_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3554_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v_task_3535_; lean_object* v_kind_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3552_; 
v_task_3535_ = lean_ctor_get(v_a_3530_, 0);
v_kind_3536_ = lean_ctor_get(v_a_3530_, 1);
v_isSharedCheck_3552_ = !lean_is_exclusive(v_a_3530_);
if (v_isSharedCheck_3552_ == 0)
{
lean_object* v_unused_3553_; 
v_unused_3553_ = lean_ctor_get(v_a_3530_, 2);
lean_dec(v_unused_3553_);
v___x_3538_ = v_a_3530_;
v_isShared_3539_ = v_isSharedCheck_3552_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_kind_3536_);
lean_inc(v_task_3535_);
lean_dec(v_a_3530_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3552_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v_registeredJobs_3540_; lean_object* v_job_3542_; 
v_registeredJobs_3540_ = lean_ctor_get(v_a_3495_, 4);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 2, v___x_3511_);
v_job_3542_ = v___x_3538_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_task_3535_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v_kind_3536_);
lean_ctor_set(v_reuseFailAlloc_3551_, 2, v___x_3511_);
v_job_3542_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3549_; 
lean_ctor_set_uint8(v_job_3542_, sizeof(void*)*3, v___x_3517_);
v___x_3543_ = lean_st_ref_take(v_registeredJobs_3540_);
lean_inc_ref(v_job_3542_);
v___x_3544_ = l_Lake_Job_toOpaque___redArg(v_job_3542_);
v___x_3545_ = lean_array_push(v___x_3543_, v___x_3544_);
v___x_3546_ = lean_st_ref_put(v_registeredJobs_3540_, v___x_3545_);
v___x_3547_ = l_Lake_Job_renew___redArg(v_job_3542_);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v___x_3547_);
v___x_3549_ = v___x_3533_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3547_);
lean_ctor_set(v_reuseFailAlloc_3550_, 1, v_a_3531_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3511_);
return v___x_3529_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object* v_self_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec_ref(v_a_3559_);
lean_dec(v_a_3558_);
lean_dec(v_a_3557_);
return v_res_3563_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3565_; uint8_t v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___f_3565_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_3566_ = 1;
v___x_3567_ = l_Lake_instDataKindUnit;
v___x_3568_ = ((lean_object*)(l_Lake_LeanLib_extraDepFacetConfig___closed__0));
v___x_3569_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3570_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3570_, 0, v___x_3569_);
lean_ctor_set(v___x_3570_, 1, v___x_3568_);
lean_ctor_set(v___x_3570_, 2, v___x_3567_);
lean_ctor_set(v___x_3570_, 3, v___f_3565_);
lean_ctor_set_uint8(v___x_3570_, sizeof(void*)*4, v___x_3566_);
lean_ctor_set_uint8(v___x_3570_, sizeof(void*)*4 + 1, v___x_3566_);
return v___x_3570_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = lean_obj_once(&l_Lake_LeanLib_extraDepFacetConfig___closed__1, &l_Lake_LeanLib_extraDepFacetConfig___closed__1_once, _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* v_self_3572_, size_t v_sz_3573_, size_t v_i_3574_, lean_object* v_bs_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
uint8_t v___x_3583_; 
v___x_3583_ = lean_usize_dec_lt(v_i_3574_, v_sz_3573_);
if (v___x_3583_ == 0)
{
lean_object* v___x_3584_; 
lean_dec_ref(v___y_3576_);
lean_dec_ref(v_self_3572_);
v___x_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3584_, 0, v_bs_3575_);
lean_ctor_set(v___x_3584_, 1, v___y_3581_);
return v___x_3584_;
}
else
{
lean_object* v_pkg_3585_; lean_object* v_name_3586_; lean_object* v_keyName_3587_; lean_object* v_v_3588_; lean_object* v___x_3589_; lean_object* v_bs_x27_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v_pkg_3585_ = lean_ctor_get(v_self_3572_, 0);
v_name_3586_ = lean_ctor_get(v_self_3572_, 1);
v_keyName_3587_ = lean_ctor_get(v_pkg_3585_, 2);
v_v_3588_ = lean_array_uget(v_bs_3575_, v_i_3574_);
v___x_3589_ = lean_unsigned_to_nat(0u);
v_bs_x27_3590_ = lean_array_uset(v_bs_3575_, v_i_3574_, v___x_3589_);
lean_inc(v_name_3586_);
lean_inc(v_keyName_3587_);
v___x_3591_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3591_, 0, v_keyName_3587_);
lean_ctor_set(v___x_3591_, 1, v_name_3586_);
v___x_3592_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3572_);
v___x_3593_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3591_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
lean_ctor_set(v___x_3593_, 2, v_self_3572_);
lean_ctor_set(v___x_3593_, 3, v_v_3588_);
lean_inc_ref(v___y_3576_);
lean_inc_ref(v___y_3580_);
lean_inc_ref(v___y_3579_);
lean_inc(v___y_3578_);
lean_inc(v___y_3577_);
v___x_3594_ = lean_apply_7(v___y_3576_, v___x_3593_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, lean_box(0));
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v_a_3596_; lean_object* v___x_3597_; size_t v___x_3598_; size_t v___x_3599_; lean_object* v___x_3600_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
v_a_3596_ = lean_ctor_get(v___x_3594_, 1);
lean_inc(v_a_3596_);
lean_dec_ref_known(v___x_3594_, 2);
v___x_3597_ = l_Lake_Job_toOpaque___redArg(v_a_3595_);
v___x_3598_ = ((size_t)1ULL);
v___x_3599_ = lean_usize_add(v_i_3574_, v___x_3598_);
v___x_3600_ = lean_array_uset(v_bs_x27_3590_, v_i_3574_, v___x_3597_);
v_i_3574_ = v___x_3599_;
v_bs_3575_ = v___x_3600_;
v___y_3581_ = v_a_3596_;
goto _start;
}
else
{
lean_object* v_a_3602_; lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec_ref(v_bs_x27_3590_);
lean_dec_ref(v___y_3576_);
lean_dec_ref(v_self_3572_);
v_a_3602_ = lean_ctor_get(v___x_3594_, 0);
v_a_3603_ = lean_ctor_get(v___x_3594_, 1);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3594_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_inc(v_a_3602_);
lean_dec(v___x_3594_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3602_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* v_self_3611_, lean_object* v_sz_3612_, lean_object* v_i_3613_, lean_object* v_bs_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
size_t v_sz_boxed_3622_; size_t v_i_boxed_3623_; lean_object* v_res_3624_; 
v_sz_boxed_3622_ = lean_unbox_usize(v_sz_3612_);
lean_dec(v_sz_3612_);
v_i_boxed_3623_ = lean_unbox_usize(v_i_3613_);
lean_dec(v_i_3613_);
v_res_3624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3611_, v_sz_boxed_3622_, v_i_boxed_3623_, v_bs_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec(v___y_3616_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object* v_self_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_){
_start:
{
lean_object* v_config_3634_; lean_object* v_defaultFacets_3635_; size_t v_sz_3636_; size_t v___x_3637_; lean_object* v___x_3638_; 
v_config_3634_ = lean_ctor_get(v_self_3626_, 2);
v_defaultFacets_3635_ = lean_ctor_get(v_config_3634_, 7);
lean_inc_ref(v_defaultFacets_3635_);
v_sz_3636_ = lean_array_size(v_defaultFacets_3635_);
v___x_3637_ = ((size_t)0ULL);
v___x_3638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3626_, v_sz_3636_, v___x_3637_, v_defaultFacets_3635_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3649_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
v_a_3640_ = lean_ctor_get(v___x_3638_, 1);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3642_ = v___x_3638_;
v_isShared_3643_ = v_isSharedCheck_3649_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_inc(v_a_3639_);
lean_dec(v___x_3638_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3649_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; 
v___x_3644_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0));
v___x_3645_ = l_Lake_Job_mixArray___redArg(v_a_3639_, v___x_3644_);
lean_dec(v_a_3639_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v___x_3645_);
v___x_3647_ = v___x_3642_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_a_3640_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
else
{
lean_object* v_a_3650_; lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3658_; 
v_a_3650_ = lean_ctor_get(v___x_3638_, 0);
v_a_3651_ = lean_ctor_get(v___x_3638_, 1);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3653_ = v___x_3638_;
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_inc(v_a_3650_);
lean_dec(v___x_3638_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3656_; 
if (v_isShared_3654_ == 0)
{
v___x_3656_ = v___x_3653_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3650_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_a_3651_);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object* v_self_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
lean_dec_ref(v_a_3664_);
lean_dec_ref(v_a_3663_);
lean_dec(v_a_3662_);
lean_dec(v_a_3661_);
return v_res_3667_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3669_; uint8_t v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___f_3669_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_3670_ = 1;
v___x_3671_ = l_Lake_instDataKindUnit;
v___x_3672_ = ((lean_object*)(l_Lake_LeanLib_defaultFacetConfig___closed__0));
v___x_3673_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3674_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
lean_ctor_set(v___x_3674_, 1, v___x_3672_);
lean_ctor_set(v___x_3674_, 2, v___x_3671_);
lean_ctor_set(v___x_3674_, 3, v___f_3669_);
lean_ctor_set_uint8(v___x_3674_, sizeof(void*)*4, v___x_3670_);
lean_ctor_set_uint8(v___x_3674_, sizeof(void*)*4 + 1, v___x_3670_);
return v___x_3674_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = lean_obj_once(&l_Lake_LeanLib_defaultFacetConfig___closed__1, &l_Lake_LeanLib_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanLib_defaultFacetConfig___closed__1);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_3676_, lean_object* v_v_3677_, lean_object* v_t_3678_){
_start:
{
if (lean_obj_tag(v_t_3678_) == 0)
{
lean_object* v_size_3679_; lean_object* v_k_3680_; lean_object* v_v_3681_; lean_object* v_l_3682_; lean_object* v_r_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3963_; 
v_size_3679_ = lean_ctor_get(v_t_3678_, 0);
v_k_3680_ = lean_ctor_get(v_t_3678_, 1);
v_v_3681_ = lean_ctor_get(v_t_3678_, 2);
v_l_3682_ = lean_ctor_get(v_t_3678_, 3);
v_r_3683_ = lean_ctor_get(v_t_3678_, 4);
v_isSharedCheck_3963_ = !lean_is_exclusive(v_t_3678_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3685_ = v_t_3678_;
v_isShared_3686_ = v_isSharedCheck_3963_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_r_3683_);
lean_inc(v_l_3682_);
lean_inc(v_v_3681_);
lean_inc(v_k_3680_);
lean_inc(v_size_3679_);
lean_dec(v_t_3678_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3963_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
uint8_t v___x_3687_; 
v___x_3687_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3676_, v_k_3680_);
switch(v___x_3687_)
{
case 0:
{
lean_object* v_impl_3688_; lean_object* v___x_3689_; 
lean_dec(v_size_3679_);
v_impl_3688_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3676_, v_v_3677_, v_l_3682_);
v___x_3689_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3683_) == 0)
{
lean_object* v_size_3690_; lean_object* v_size_3691_; lean_object* v_k_3692_; lean_object* v_v_3693_; lean_object* v_l_3694_; lean_object* v_r_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; uint8_t v___x_3698_; 
v_size_3690_ = lean_ctor_get(v_r_3683_, 0);
v_size_3691_ = lean_ctor_get(v_impl_3688_, 0);
v_k_3692_ = lean_ctor_get(v_impl_3688_, 1);
v_v_3693_ = lean_ctor_get(v_impl_3688_, 2);
v_l_3694_ = lean_ctor_get(v_impl_3688_, 3);
v_r_3695_ = lean_ctor_get(v_impl_3688_, 4);
lean_inc(v_r_3695_);
v___x_3696_ = lean_unsigned_to_nat(3u);
v___x_3697_ = lean_nat_mul(v___x_3696_, v_size_3690_);
v___x_3698_ = lean_nat_dec_lt(v___x_3697_, v_size_3691_);
lean_dec(v___x_3697_);
if (v___x_3698_ == 0)
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
lean_dec(v_r_3695_);
v___x_3699_ = lean_nat_add(v___x_3689_, v_size_3691_);
v___x_3700_ = lean_nat_add(v___x_3699_, v_size_3690_);
lean_dec(v___x_3699_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 3, v_impl_3688_);
lean_ctor_set(v___x_3685_, 0, v___x_3700_);
v___x_3702_ = v___x_3685_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3700_);
lean_ctor_set(v_reuseFailAlloc_3703_, 1, v_k_3680_);
lean_ctor_set(v_reuseFailAlloc_3703_, 2, v_v_3681_);
lean_ctor_set(v_reuseFailAlloc_3703_, 3, v_impl_3688_);
lean_ctor_set(v_reuseFailAlloc_3703_, 4, v_r_3683_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
else
{
lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3769_; 
lean_inc(v_l_3694_);
lean_inc(v_v_3693_);
lean_inc(v_k_3692_);
lean_inc(v_size_3691_);
v_isSharedCheck_3769_ = !lean_is_exclusive(v_impl_3688_);
if (v_isSharedCheck_3769_ == 0)
{
lean_object* v_unused_3770_; lean_object* v_unused_3771_; lean_object* v_unused_3772_; lean_object* v_unused_3773_; lean_object* v_unused_3774_; 
v_unused_3770_ = lean_ctor_get(v_impl_3688_, 4);
lean_dec(v_unused_3770_);
v_unused_3771_ = lean_ctor_get(v_impl_3688_, 3);
lean_dec(v_unused_3771_);
v_unused_3772_ = lean_ctor_get(v_impl_3688_, 2);
lean_dec(v_unused_3772_);
v_unused_3773_ = lean_ctor_get(v_impl_3688_, 1);
lean_dec(v_unused_3773_);
v_unused_3774_ = lean_ctor_get(v_impl_3688_, 0);
lean_dec(v_unused_3774_);
v___x_3705_ = v_impl_3688_;
v_isShared_3706_ = v_isSharedCheck_3769_;
goto v_resetjp_3704_;
}
else
{
lean_dec(v_impl_3688_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3769_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v_size_3707_; lean_object* v_size_3708_; lean_object* v_k_3709_; lean_object* v_v_3710_; lean_object* v_l_3711_; lean_object* v_r_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; 
v_size_3707_ = lean_ctor_get(v_l_3694_, 0);
v_size_3708_ = lean_ctor_get(v_r_3695_, 0);
v_k_3709_ = lean_ctor_get(v_r_3695_, 1);
v_v_3710_ = lean_ctor_get(v_r_3695_, 2);
v_l_3711_ = lean_ctor_get(v_r_3695_, 3);
v_r_3712_ = lean_ctor_get(v_r_3695_, 4);
v___x_3713_ = lean_unsigned_to_nat(2u);
v___x_3714_ = lean_nat_mul(v___x_3713_, v_size_3707_);
v___x_3715_ = lean_nat_dec_lt(v_size_3708_, v___x_3714_);
lean_dec(v___x_3714_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3744_; 
lean_inc(v_r_3712_);
lean_inc(v_l_3711_);
lean_inc(v_v_3710_);
lean_inc(v_k_3709_);
v_isSharedCheck_3744_ = !lean_is_exclusive(v_r_3695_);
if (v_isSharedCheck_3744_ == 0)
{
lean_object* v_unused_3745_; lean_object* v_unused_3746_; lean_object* v_unused_3747_; lean_object* v_unused_3748_; lean_object* v_unused_3749_; 
v_unused_3745_ = lean_ctor_get(v_r_3695_, 4);
lean_dec(v_unused_3745_);
v_unused_3746_ = lean_ctor_get(v_r_3695_, 3);
lean_dec(v_unused_3746_);
v_unused_3747_ = lean_ctor_get(v_r_3695_, 2);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_r_3695_, 1);
lean_dec(v_unused_3748_);
v_unused_3749_ = lean_ctor_get(v_r_3695_, 0);
lean_dec(v_unused_3749_);
v___x_3717_ = v_r_3695_;
v_isShared_3718_ = v_isSharedCheck_3744_;
goto v_resetjp_3716_;
}
else
{
lean_dec(v_r_3695_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3744_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___x_3732_; lean_object* v___y_3734_; 
v___x_3719_ = lean_nat_add(v___x_3689_, v_size_3691_);
lean_dec(v_size_3691_);
v___x_3720_ = lean_nat_add(v___x_3719_, v_size_3690_);
lean_dec(v___x_3719_);
v___x_3732_ = lean_nat_add(v___x_3689_, v_size_3707_);
if (lean_obj_tag(v_l_3711_) == 0)
{
lean_object* v_size_3742_; 
v_size_3742_ = lean_ctor_get(v_l_3711_, 0);
lean_inc(v_size_3742_);
v___y_3734_ = v_size_3742_;
goto v___jp_3733_;
}
else
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_unsigned_to_nat(0u);
v___y_3734_ = v___x_3743_;
goto v___jp_3733_;
}
v___jp_3721_:
{
lean_object* v___x_3725_; lean_object* v___x_3727_; 
v___x_3725_ = lean_nat_add(v___y_3723_, v___y_3724_);
lean_dec(v___y_3724_);
lean_dec(v___y_3723_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 4, v_r_3683_);
lean_ctor_set(v___x_3717_, 3, v_r_3712_);
lean_ctor_set(v___x_3717_, 2, v_v_3681_);
lean_ctor_set(v___x_3717_, 1, v_k_3680_);
lean_ctor_set(v___x_3717_, 0, v___x_3725_);
v___x_3727_ = v___x_3717_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3725_);
lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_k_3680_);
lean_ctor_set(v_reuseFailAlloc_3731_, 2, v_v_3681_);
lean_ctor_set(v_reuseFailAlloc_3731_, 3, v_r_3712_);
lean_ctor_set(v_reuseFailAlloc_3731_, 4, v_r_3683_);
v___x_3727_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3729_; 
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 4, v___x_3727_);
lean_ctor_set(v___x_3705_, 3, v___y_3722_);
lean_ctor_set(v___x_3705_, 2, v_v_3710_);
lean_ctor_set(v___x_3705_, 1, v_k_3709_);
lean_ctor_set(v___x_3705_, 0, v___x_3720_);
v___x_3729_ = v___x_3705_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_k_3709_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v_v_3710_);
lean_ctor_set(v_reuseFailAlloc_3730_, 3, v___y_3722_);
lean_ctor_set(v_reuseFailAlloc_3730_, 4, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
v___jp_3733_:
{
lean_object* v___x_3735_; lean_object* v___x_3737_; 
v___x_3735_ = lean_nat_add(v___x_3732_, v___y_3734_);
lean_dec(v___y_3734_);
lean_dec(v___x_3732_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 4, v_l_3711_);
lean_ctor_set(v___x_3685_, 3, v_l_3694_);
lean_ctor_set(v___x_3685_, 2, v_v_3693_);
lean_ctor_set(v___x_3685_, 1, v_k_3692_);
lean_ctor_set(v___x_3685_, 0, v___x_3735_);
v___x_3737_ = v___x_3685_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3735_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_k_3692_);
lean_ctor_set(v_reuseFailAlloc_3741_, 2, v_v_3693_);
lean_ctor_set(v_reuseFailAlloc_3741_, 3, v_l_3694_);
lean_ctor_set(v_reuseFailAlloc_3741_, 4, v_l_3711_);
v___x_3737_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3738_; 
v___x_3738_ = lean_nat_add(v___x_3689_, v_size_3690_);
if (lean_obj_tag(v_r_3712_) == 0)
{
lean_object* v_size_3739_; 
v_size_3739_ = lean_ctor_get(v_r_3712_, 0);
lean_inc(v_size_3739_);
v___y_3722_ = v___x_3737_;
v___y_3723_ = v___x_3738_;
v___y_3724_ = v_size_3739_;
goto v___jp_3721_;
}
else
{
lean_object* v___x_3740_; 
v___x_3740_ = lean_unsigned_to_nat(0u);
v___y_3722_ = v___x_3737_;
v___y_3723_ = v___x_3738_;
v___y_3724_ = v___x_3740_;
goto v___jp_3721_;
}
}
}
}
}
else
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3755_; 
lean_del_object(v___x_3685_);
v___x_3750_ = lean_nat_add(v___x_3689_, v_size_3691_);
lean_dec(v_size_3691_);
v___x_3751_ = lean_nat_add(v___x_3750_, v_size_3690_);
lean_dec(v___x_3750_);
v___x_3752_ = lean_nat_add(v___x_3689_, v_size_3690_);
v___x_3753_ = lean_nat_add(v___x_3752_, v_size_3708_);
lean_dec(v___x_3752_);
lean_inc_ref(v_r_3683_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 4, v_r_3683_);
lean_ctor_set(v___x_3705_, 3, v_r_3695_);
lean_ctor_set(v___x_3705_, 2, v_v_3681_);
lean_ctor_set(v___x_3705_, 1, v_k_3680_);
lean_ctor_set(v___x_3705_, 0, v___x_3753_);
v___x_3755_ = v___x_3705_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3768_, 1, v_k_3680_);
lean_ctor_set(v_reuseFailAlloc_3768_, 2, v_v_3681_);
lean_ctor_set(v_reuseFailAlloc_3768_, 3, v_r_3695_);
lean_ctor_set(v_reuseFailAlloc_3768_, 4, v_r_3683_);
v___x_3755_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
v_isSharedCheck_3762_ = !lean_is_exclusive(v_r_3683_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; lean_object* v_unused_3764_; lean_object* v_unused_3765_; lean_object* v_unused_3766_; lean_object* v_unused_3767_; 
v_unused_3763_ = lean_ctor_get(v_r_3683_, 4);
lean_dec(v_unused_3763_);
v_unused_3764_ = lean_ctor_get(v_r_3683_, 3);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_r_3683_, 2);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_r_3683_, 1);
lean_dec(v_unused_3766_);
v_unused_3767_ = lean_ctor_get(v_r_3683_, 0);
lean_dec(v_unused_3767_);
v___x_3757_ = v_r_3683_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_dec(v_r_3683_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 4, v___x_3755_);
lean_ctor_set(v___x_3757_, 3, v_l_3694_);
lean_ctor_set(v___x_3757_, 2, v_v_3693_);
lean_ctor_set(v___x_3757_, 1, v_k_3692_);
lean_ctor_set(v___x_3757_, 0, v___x_3751_);
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3751_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_k_3692_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v_v_3693_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v_l_3694_);
lean_ctor_set(v_reuseFailAlloc_3761_, 4, v___x_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3775_; 
v_l_3775_ = lean_ctor_get(v_impl_3688_, 3);
if (lean_obj_tag(v_l_3775_) == 0)
{
lean_object* v_r_3776_; lean_object* v_k_3777_; lean_object* v_v_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3789_; 
lean_inc_ref(v_l_3775_);
v_r_3776_ = lean_ctor_get(v_impl_3688_, 4);
v_k_3777_ = lean_ctor_get(v_impl_3688_, 1);
v_v_3778_ = lean_ctor_get(v_impl_3688_, 2);
v_isSharedCheck_3789_ = !lean_is_exclusive(v_impl_3688_);
if (v_isSharedCheck_3789_ == 0)
{
lean_object* v_unused_3790_; lean_object* v_unused_3791_; 
v_unused_3790_ = lean_ctor_get(v_impl_3688_, 3);
lean_dec(v_unused_3790_);
v_unused_3791_ = lean_ctor_get(v_impl_3688_, 0);
lean_dec(v_unused_3791_);
v___x_3780_ = v_impl_3688_;
v_isShared_3781_ = v_isSharedCheck_3789_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_r_3776_);
lean_inc(v_v_3778_);
lean_inc(v_k_3777_);
lean_dec(v_impl_3688_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3789_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3782_; lean_object* v___x_3784_; 
v___x_3782_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3776_);
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 3, v_r_3776_);
lean_ctor_set(v___x_3780_, 2, v_v_3681_);
lean_ctor_set(v___x_3780_, 1, v_k_3680_);
lean_ctor_set(v___x_3780_, 0, v___x_3689_);
v___x_3784_ = v___x_3780_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3788_, 1, v_k_3680_);
lean_ctor_set(v_reuseFailAlloc_3788_, 2, v_v_3681_);
lean_ctor_set(v_reuseFailAlloc_3788_, 3, v_r_3776_);
lean_ctor_set(v_reuseFailAlloc_3788_, 4, v_r_3776_);
v___x_3784_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
lean_object* v___x_3786_; 
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 4, v___x_3784_);
lean_ctor_set(v___x_3685_, 3, v_l_3775_);
lean_ctor_set(v___x_3685_, 2, v_v_3778_);
lean_ctor_set(v___x_3685_, 1, v_k_3777_);
lean_ctor_set(v___x_3685_, 0, v___x_3782_);
v___x_3786_ = v___x_3685_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3787_, 1, v_k_3777_);
lean_ctor_set(v_reuseFailAlloc_3787_, 2, v_v_3778_);
lean_ctor_set(v_reuseFailAlloc_3787_, 3, v_l_3775_);
lean_ctor_set(v_reuseFailAlloc_3787_, 4, v___x_3784_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
else
{
lean_object* v_r_3792_; 
v_r_3792_ = lean_ctor_get(v_impl_3688_, 4);
lean_inc(v_r_3792_);
if (lean_obj_tag(v_r_3792_) == 0)
{
lean_object* v_k_3793_; lean_object* v_v_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3817_; 
lean_inc(v_l_3775_);
v_k_3793_ = lean_ctor_get(v_impl_3688_, 1);
v_v_3794_ = lean_ctor_get(v_impl_3688_, 2);
v_isSharedCheck_3817_ = !lean_is_exclusive(v_impl_3688_);
if (v_isSharedCheck_3817_ == 0)
{
lean_object* v_unused_3818_; lean_object* v_unused_3819_; lean_object* v_unused_3820_; 
v_unused_3818_ = lean_ctor_get(v_impl_3688_, 4);
lean_dec(v_unused_3818_);
v_unused_3819_ = lean_ctor_get(v_impl_3688_, 3);
lean_dec(v_unused_3819_);
v_unused_3820_ = lean_ctor_get(v_impl_3688_, 0);
lean_dec(v_unused_3820_);
v___x_3796_ = v_impl_3688_;
v_isShared_3797_ = v_isSharedCheck_3817_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_v_3794_);
lean_inc(v_k_3793_);
lean_dec(v_impl_3688_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3817_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v_k_3798_; lean_object* v_v_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3813_; 
v_k_3798_ = lean_ctor_get(v_r_3792_, 1);
v_v_3799_ = lean_ctor_get(v_r_3792_, 2);
v_isSharedCheck_3813_ = !lean_is_exclusive(v_r_3792_);
if (v_isSharedCheck_3813_ == 0)
{
lean_object* v_unused_3814_; lean_object* v_unused_3815_; lean_object* v_unused_3816_; 
v_unused_3814_ = lean_ctor_get(v_r_3792_, 4);
lean_dec(v_unused_3814_);
v_unused_3815_ = lean_ctor_get(v_r_3792_, 3);
lean_dec(v_unused_3815_);
v_unused_3816_ = lean_ctor_get(v_r_3792_, 0);
lean_dec(v_unused_3816_);
v___x_3801_ = v_r_3792_;
v_isShared_3802_ = v_isSharedCheck_3813_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_v_3799_);
lean_inc(v_k_3798_);
lean_dec(v_r_3792_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3813_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3803_ = lean_unsigned_to_nat(3u);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 4, v_l_3775_);
lean_ctor_set(v___x_3801_, 3, v_l_3775_);
lean_ctor_set(v___x_3801_, 2, v_v_3794_);
lean_ctor_set(v___x_3801_, 1, v_k_3793_);
lean_ctor_set(v___x_3801_, 0, v___x_3689_);
v___x_3805_ = v___x_3801_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_k_3793_);
lean_ctor_set(v_reuseFailAlloc_3812_, 2, v_v_3794_);
lean_ctor_set(v_reuseFailAlloc_3812_, 3, v_l_3775_);
lean_ctor_set(v_reuseFailAlloc_3812_, 4, v_l_3775_);
v___x_3805_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
lean_object* v___x_3807_; 
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 4, v_l_3775_);
lean_ctor_set(v___x_3796_, 2, v_v_3681_);
lean_ctor_set(v___x_3796_, 1, v_k_3680_);
lean_ctor_set(v___x_3796_, 0, v___x_3689_);
v___x_3807_ = v___x_3796_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v_k_3680_);
lean_ctor_set(v_reuseFailAlloc_3811_, 2, v_v_3681_);
lean_ctor_set(v_reuseFailAlloc_3811_, 3, v_l_3775_);
lean_ctor_set(v_reuseFailAlloc_3811_, 4, v_l_3775_);
v___x_3807_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
lean_object* v___x_3809_; 
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 4, v___x_3807_);
lean_ctor_set(v___x_3685_, 3, v___x_3805_);
lean_ctor_set(v___x_3685_, 2, v_v_3799_);
lean_ctor_set(v___x_3685_, 1, v_k_3798_);
lean_ctor_set(v___x_3685_, 0, v___x_3803_);
v___x_3809_ = v___x_3685_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v_k_3798_);
lean_ctor_set(v_reuseFailAlloc_3810_, 2, v_v_3799_);
lean_ctor_set(v_reuseFailAlloc_3810_, 3, v___x_3805_);
lean_ctor_set(v_reuseFailAlloc_3810_, 4, v___x_3807_);
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
}
}
else
{
lean_object* v___x_3821_; lean_object* v___x_3823_; 
v___x_3821_ = lean_unsigned_to_nat(2u);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 4, v_r_3792_);
lean_ctor_set(v___x_3685_, 3, v_impl_3688_);
lean_ctor_set(v___x_3685_, 0, v___x_3821_);
v___x_3823_ = v___x_3685_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v_k_3680_);
lean_ctor_set(v_reuseFailAlloc_3824_, 2, v_v_3681_);
lean_ctor_set(v_reuseFailAlloc_3824_, 3, v_impl_3688_);
lean_ctor_set(v_reuseFailAlloc_3824_, 4, v_r_3792_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3826_; 
lean_dec(v_v_3681_);
lean_dec(v_k_3680_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 2, v_v_3677_);
lean_ctor_set(v___x_3685_, 1, v_k_3676_);
v___x_3826_ = v___x_3685_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_size_3679_);
lean_ctor_set(v_reuseFailAlloc_3827_, 1, v_k_3676_);
lean_ctor_set(v_reuseFailAlloc_3827_, 2, v_v_3677_);
lean_ctor_set(v_reuseFailAlloc_3827_, 3, v_l_3682_);
lean_ctor_set(v_reuseFailAlloc_3827_, 4, v_r_3683_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
default: 
{
lean_object* v_impl_3828_; lean_object* v___x_3829_; 
lean_dec(v_size_3679_);
v_impl_3828_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3676_, v_v_3677_, v_r_3683_);
v___x_3829_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3682_) == 0)
{
lean_object* v_size_3830_; lean_object* v_size_3831_; lean_object* v_k_3832_; lean_object* v_v_3833_; lean_object* v_l_3834_; lean_object* v_r_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v_size_3830_ = lean_ctor_get(v_l_3682_, 0);
v_size_3831_ = lean_ctor_get(v_impl_3828_, 0);
v_k_3832_ = lean_ctor_get(v_impl_3828_, 1);
v_v_3833_ = lean_ctor_get(v_impl_3828_, 2);
v_l_3834_ = lean_ctor_get(v_impl_3828_, 3);
lean_inc(v_l_3834_);
v_r_3835_ = lean_ctor_get(v_impl_3828_, 4);
v___x_3836_ = lean_unsigned_to_nat(3u);
v___x_3837_ = lean_nat_mul(v___x_3836_, v_size_3830_);
v___x_3838_ = lean_nat_dec_lt(v___x_3837_, v_size_3831_);
lean_dec(v___x_3837_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3842_; 
lean_dec(v_l_3834_);
v___x_3839_ = lean_nat_add(v___x_3829_, v_size_3830_);
v___x_3840_ = lean_nat_add(v___x_3839_, v_size_3831_);
lean_dec(v___x_3839_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 4, v_impl_3828_);
lean_ctor_set(v___x_3685_, 0, v___x_3840_);
v___x_3842_ = v___x_3685_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3840_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_k_3680_);
lean_ctor_set(v_reuseFailAlloc_3843_, 2, v_v_3681_);
lean_ctor_set(v_reuseFailAlloc_3843_, 3, v_l_3682_);
lean_ctor_set(v_reuseFailAlloc_3843_, 4, v_impl_3828_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
else
{
lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3907_; 
lean_inc(v_r_3835_);
lean_inc(v_v_3833_);
lean_inc(v_k_3832_);
lean_inc(v_size_3831_);
v_isSharedCheck_3907_ = !lean_is_exclusive(v_impl_3828_);
if (v_isSharedCheck_3907_ == 0)
{
lean_object* v_unused_3908_; lean_object* v_unused_3909_; lean_object* v_unused_3910_; lean_object* v_unused_3911_; lean_object* v_unused_3912_; 
v_unused_3908_ = lean_ctor_get(v_impl_3828_, 4);
lean_dec(v_unused_3908_);
v_unused_3909_ = lean_ctor_get(v_impl_3828_, 3);
lean_dec(v_unused_3909_);
v_unused_3910_ = lean_ctor_get(v_impl_3828_, 2);
lean_dec(v_unused_3910_);
v_unused_3911_ = lean_ctor_get(v_impl_3828_, 1);
lean_dec(v_unused_3911_);
v_unused_3912_ = lean_ctor_get(v_impl_3828_, 0);
lean_dec(v_unused_3912_);
v___x_3845_ = v_impl_3828_;
v_isShared_3846_ = v_isSharedCheck_3907_;
goto v_resetjp_3844_;
}
else
{
lean_dec(v_impl_3828_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3907_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v_size_3847_; lean_object* v_k_3848_; lean_object* v_v_3849_; lean_object* v_l_3850_; lean_object* v_r_3851_; lean_object* v_size_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; uint8_t v___x_3855_; 
v_size_3847_ = lean_ctor_get(v_l_3834_, 0);
v_k_3848_ = lean_ctor_get(v_l_3834_, 1);
v_v_3849_ = lean_ctor_get(v_l_3834_, 2);
v_l_3850_ = lean_ctor_get(v_l_3834_, 3);
v_r_3851_ = lean_ctor_get(v_l_3834_, 4);
v_size_3852_ = lean_ctor_get(v_r_3835_, 0);
v___x_3853_ = lean_unsigned_to_nat(2u);
v___x_3854_ = lean_nat_mul(v___x_3853_, v_size_3852_);
v___x_3855_ = lean_nat_dec_lt(v_size_3847_, v___x_3854_);
lean_dec(v___x_3854_);
if (v___x_3855_ == 0)
{
lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3883_; 
lean_inc(v_r_3851_);
lean_inc(v_l_3850_);
lean_inc(v_v_3849_);
lean_inc(v_k_3848_);
v_isSharedCheck_3883_ = !lean_is_exclusive(v_l_3834_);
if (v_isSharedCheck_3883_ == 0)
{
lean_object* v_unused_3884_; lean_object* v_unused_3885_; lean_object* v_unused_3886_; lean_object* v_unused_3887_; lean_object* v_unused_3888_; 
v_unused_3884_ = lean_ctor_get(v_l_3834_, 4);
lean_dec(v_unused_3884_);
v_unused_3885_ = lean_ctor_get(v_l_3834_, 3);
lean_dec(v_unused_3885_);
v_unused_3886_ = lean_ctor_get(v_l_3834_, 2);
lean_dec(v_unused_3886_);
v_unused_3887_ = lean_ctor_get(v_l_3834_, 1);
lean_dec(v_unused_3887_);
v_unused_3888_ = lean_ctor_get(v_l_3834_, 0);
lean_dec(v_unused_3888_);
v___x_3857_ = v_l_3834_;
v_isShared_3858_ = v_isSharedCheck_3883_;
goto v_resetjp_3856_;
}
else
{
lean_dec(v_l_3834_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3883_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3873_; 
v___x_3859_ = lean_nat_add(v___x_3829_, v_size_3830_);
v___x_3860_ = lean_nat_add(v___x_3859_, v_size_3831_);
lean_dec(v_size_3831_);
if (lean_obj_tag(v_l_3850_) == 0)
{
lean_object* v_size_3881_; 
v_size_3881_ = lean_ctor_get(v_l_3850_, 0);
lean_inc(v_size_3881_);
v___y_3873_ = v_size_3881_;
goto v___jp_3872_;
}
else
{
lean_object* v___x_3882_; 
v___x_3882_ = lean_unsigned_to_nat(0u);
v___y_3873_ = v___x_3882_;
goto v___jp_3872_;
}
v___jp_3861_:
{
lean_object* v___x_3865_; lean_object* v___x_3867_; 
v___x_3865_ = lean_nat_add(v___y_3863_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec(v___y_3863_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 4, v_r_3835_);
lean_ctor_set(v___x_3857_, 3, v_r_3851_);
lean_ctor_set(v___x_3857_, 2, v_v_3833_);
lean_ctor_set(v___x_3857_, 1, v_k_3832_);
lean_ctor_set(v___x_3857_, 0, v___x_3865_);
v___x_3867_ = v___x_3857_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3865_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v_k_3832_);
lean_ctor_set(v_reuseFailAlloc_3871_, 2, v_v_3833_);
lean_ctor_set(v_reuseFailAlloc_3871_, 3, v_r_3851_);
lean_ctor_set(v_reuseFailAlloc_3871_, 4, v_r_3835_);
v___x_3867_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
lean_object* v___x_3869_; 
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 4, v___x_3867_);
lean_ctor_set(v___x_3845_, 3, v___y_3862_);
lean_ctor_set(v___x_3845_, 2, v_v_3849_);
lean_ctor_set(v___x_3845_, 1, v_k_3848_);
lean_ctor_set(v___x_3845_, 0, v___x_3860_);
v___x_3869_ = v___x_3845_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3860_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_k_3848_);
lean_ctor_set(v_reuseFailAlloc_3870_, 2, v_v_3849_);
lean_ctor_set(v_reuseFailAlloc_3870_, 3, v___y_3862_);
lean_ctor_set(v_reuseFailAlloc_3870_, 4, v___x_3867_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
v___jp_3872_:
{
lean_object* v___x_3874_; lean_object* v___x_3876_; 
v___x_3874_ = lean_nat_add(v___x_3859_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec(v___x_3859_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 4, v_l_3850_);
lean_ctor_set(v___x_3685_, 0, v___x_3874_);
v___x_3876_ = v___x_3685_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3874_);
lean_ctor_set(v_reuseFailAlloc_3880_, 1, v_k_3680_);
lean_ctor_set(v_reuseFailAlloc_3880_, 2, v_v_3681_);
lean_ctor_set(v_reuseFailAlloc_3880_, 3, v_l_3682_);
lean_ctor_set(v_reuseFailAlloc_3880_, 4, v_l_3850_);
v___x_3876_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
lean_object* v___x_3877_; 
v___x_3877_ = lean_nat_add(v___x_3829_, v_size_3852_);
if (lean_obj_tag(v_r_3851_) == 0)
{
lean_object* v_size_3878_; 
v_size_3878_ = lean_ctor_get(v_r_3851_, 0);
lean_inc(v_size_3878_);
v___y_3862_ = v___x_3876_;
v___y_3863_ = v___x_3877_;
v___y_3864_ = v_size_3878_;
goto v___jp_3861_;
}
else
{
lean_object* v___x_3879_; 
v___x_3879_ = lean_unsigned_to_nat(0u);
v___y_3862_ = v___x_3876_;
v___y_3863_ = v___x_3877_;
v___y_3864_ = v___x_3879_;
goto v___jp_3861_;
}
}
}
}
}
else
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3893_; 
lean_del_object(v___x_3685_);
v___x_3889_ = lean_nat_add(v___x_3829_, v_size_3830_);
v___x_3890_ = lean_nat_add(v___x_3889_, v_size_3831_);
lean_dec(v_size_3831_);
v___x_3891_ = lean_nat_add(v___x_3889_, v_size_3847_);
lean_dec(v___x_3889_);
lean_inc_ref(v_l_3682_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 4, v_l_3834_);
lean_ctor_set(v___x_3845_, 3, v_l_3682_);
lean_ctor_set(v___x_3845_, 2, v_v_3681_);
lean_ctor_set(v___x_3845_, 1, v_k_3680_);
lean_ctor_set(v___x_3845_, 0, v___x_3891_);
v___x_3893_ = v___x_3845_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v_k_3680_);
lean_ctor_set(v_reuseFailAlloc_3906_, 2, v_v_3681_);
lean_ctor_set(v_reuseFailAlloc_3906_, 3, v_l_3682_);
lean_ctor_set(v_reuseFailAlloc_3906_, 4, v_l_3834_);
v___x_3893_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
v_isSharedCheck_3900_ = !lean_is_exclusive(v_l_3682_);
if (v_isSharedCheck_3900_ == 0)
{
lean_object* v_unused_3901_; lean_object* v_unused_3902_; lean_object* v_unused_3903_; lean_object* v_unused_3904_; lean_object* v_unused_3905_; 
v_unused_3901_ = lean_ctor_get(v_l_3682_, 4);
lean_dec(v_unused_3901_);
v_unused_3902_ = lean_ctor_get(v_l_3682_, 3);
lean_dec(v_unused_3902_);
v_unused_3903_ = lean_ctor_get(v_l_3682_, 2);
lean_dec(v_unused_3903_);
v_unused_3904_ = lean_ctor_get(v_l_3682_, 1);
lean_dec(v_unused_3904_);
v_unused_3905_ = lean_ctor_get(v_l_3682_, 0);
lean_dec(v_unused_3905_);
v___x_3895_ = v_l_3682_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_dec(v_l_3682_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 4, v_r_3835_);
lean_ctor_set(v___x_3895_, 3, v___x_3893_);
lean_ctor_set(v___x_3895_, 2, v_v_3833_);
lean_ctor_set(v___x_3895_, 1, v_k_3832_);
lean_ctor_set(v___x_3895_, 0, v___x_3890_);
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3890_);
lean_ctor_set(v_reuseFailAlloc_3899_, 1, v_k_3832_);
lean_ctor_set(v_reuseFailAlloc_3899_, 2, v_v_3833_);
lean_ctor_set(v_reuseFailAlloc_3899_, 3, v___x_3893_);
lean_ctor_set(v_reuseFailAlloc_3899_, 4, v_r_3835_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3913_; 
v_l_3913_ = lean_ctor_get(v_impl_3828_, 3);
lean_inc(v_l_3913_);
if (lean_obj_tag(v_l_3913_) == 0)
{
lean_object* v_r_3914_; lean_object* v_k_3915_; lean_object* v_v_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3939_; 
v_r_3914_ = lean_ctor_get(v_impl_3828_, 4);
v_k_3915_ = lean_ctor_get(v_impl_3828_, 1);
v_v_3916_ = lean_ctor_get(v_impl_3828_, 2);
v_isSharedCheck_3939_ = !lean_is_exclusive(v_impl_3828_);
if (v_isSharedCheck_3939_ == 0)
{
lean_object* v_unused_3940_; lean_object* v_unused_3941_; 
v_unused_3940_ = lean_ctor_get(v_impl_3828_, 3);
lean_dec(v_unused_3940_);
v_unused_3941_ = lean_ctor_get(v_impl_3828_, 0);
lean_dec(v_unused_3941_);
v___x_3918_ = v_impl_3828_;
v_isShared_3919_ = v_isSharedCheck_3939_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_r_3914_);
lean_inc(v_v_3916_);
lean_inc(v_k_3915_);
lean_dec(v_impl_3828_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3939_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v_k_3920_; lean_object* v_v_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3935_; 
v_k_3920_ = lean_ctor_get(v_l_3913_, 1);
v_v_3921_ = lean_ctor_get(v_l_3913_, 2);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_l_3913_);
if (v_isSharedCheck_3935_ == 0)
{
lean_object* v_unused_3936_; lean_object* v_unused_3937_; lean_object* v_unused_3938_; 
v_unused_3936_ = lean_ctor_get(v_l_3913_, 4);
lean_dec(v_unused_3936_);
v_unused_3937_ = lean_ctor_get(v_l_3913_, 3);
lean_dec(v_unused_3937_);
v_unused_3938_ = lean_ctor_get(v_l_3913_, 0);
lean_dec(v_unused_3938_);
v___x_3923_ = v_l_3913_;
v_isShared_3924_ = v_isSharedCheck_3935_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_v_3921_);
lean_inc(v_k_3920_);
lean_dec(v_l_3913_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3935_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3925_; lean_object* v___x_3927_; 
v___x_3925_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3914_, 2);
if (v_isShared_3924_ == 0)
{
lean_ctor_set(v___x_3923_, 4, v_r_3914_);
lean_ctor_set(v___x_3923_, 3, v_r_3914_);
lean_ctor_set(v___x_3923_, 2, v_v_3681_);
lean_ctor_set(v___x_3923_, 1, v_k_3680_);
lean_ctor_set(v___x_3923_, 0, v___x_3829_);
v___x_3927_ = v___x_3923_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3829_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_k_3680_);
lean_ctor_set(v_reuseFailAlloc_3934_, 2, v_v_3681_);
lean_ctor_set(v_reuseFailAlloc_3934_, 3, v_r_3914_);
lean_ctor_set(v_reuseFailAlloc_3934_, 4, v_r_3914_);
v___x_3927_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
lean_object* v___x_3929_; 
lean_inc(v_r_3914_);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 3, v_r_3914_);
lean_ctor_set(v___x_3918_, 0, v___x_3829_);
v___x_3929_ = v___x_3918_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v___x_3829_);
lean_ctor_set(v_reuseFailAlloc_3933_, 1, v_k_3915_);
lean_ctor_set(v_reuseFailAlloc_3933_, 2, v_v_3916_);
lean_ctor_set(v_reuseFailAlloc_3933_, 3, v_r_3914_);
lean_ctor_set(v_reuseFailAlloc_3933_, 4, v_r_3914_);
v___x_3929_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
lean_object* v___x_3931_; 
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 4, v___x_3929_);
lean_ctor_set(v___x_3685_, 3, v___x_3927_);
lean_ctor_set(v___x_3685_, 2, v_v_3921_);
lean_ctor_set(v___x_3685_, 1, v_k_3920_);
lean_ctor_set(v___x_3685_, 0, v___x_3925_);
v___x_3931_ = v___x_3685_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3925_);
lean_ctor_set(v_reuseFailAlloc_3932_, 1, v_k_3920_);
lean_ctor_set(v_reuseFailAlloc_3932_, 2, v_v_3921_);
lean_ctor_set(v_reuseFailAlloc_3932_, 3, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3932_, 4, v___x_3929_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
}
}
else
{
lean_object* v_r_3942_; 
v_r_3942_ = lean_ctor_get(v_impl_3828_, 4);
lean_inc(v_r_3942_);
if (lean_obj_tag(v_r_3942_) == 0)
{
lean_object* v_k_3943_; lean_object* v_v_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3955_; 
v_k_3943_ = lean_ctor_get(v_impl_3828_, 1);
v_v_3944_ = lean_ctor_get(v_impl_3828_, 2);
v_isSharedCheck_3955_ = !lean_is_exclusive(v_impl_3828_);
if (v_isSharedCheck_3955_ == 0)
{
lean_object* v_unused_3956_; lean_object* v_unused_3957_; lean_object* v_unused_3958_; 
v_unused_3956_ = lean_ctor_get(v_impl_3828_, 4);
lean_dec(v_unused_3956_);
v_unused_3957_ = lean_ctor_get(v_impl_3828_, 3);
lean_dec(v_unused_3957_);
v_unused_3958_ = lean_ctor_get(v_impl_3828_, 0);
lean_dec(v_unused_3958_);
v___x_3946_ = v_impl_3828_;
v_isShared_3947_ = v_isSharedCheck_3955_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_v_3944_);
lean_inc(v_k_3943_);
lean_dec(v_impl_3828_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3955_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v___x_3948_; lean_object* v___x_3950_; 
v___x_3948_ = lean_unsigned_to_nat(3u);
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 4, v_l_3913_);
lean_ctor_set(v___x_3946_, 2, v_v_3681_);
lean_ctor_set(v___x_3946_, 1, v_k_3680_);
lean_ctor_set(v___x_3946_, 0, v___x_3829_);
v___x_3950_ = v___x_3946_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3829_);
lean_ctor_set(v_reuseFailAlloc_3954_, 1, v_k_3680_);
lean_ctor_set(v_reuseFailAlloc_3954_, 2, v_v_3681_);
lean_ctor_set(v_reuseFailAlloc_3954_, 3, v_l_3913_);
lean_ctor_set(v_reuseFailAlloc_3954_, 4, v_l_3913_);
v___x_3950_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
lean_object* v___x_3952_; 
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 4, v_r_3942_);
lean_ctor_set(v___x_3685_, 3, v___x_3950_);
lean_ctor_set(v___x_3685_, 2, v_v_3944_);
lean_ctor_set(v___x_3685_, 1, v_k_3943_);
lean_ctor_set(v___x_3685_, 0, v___x_3948_);
v___x_3952_ = v___x_3685_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3948_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v_k_3943_);
lean_ctor_set(v_reuseFailAlloc_3953_, 2, v_v_3944_);
lean_ctor_set(v_reuseFailAlloc_3953_, 3, v___x_3950_);
lean_ctor_set(v_reuseFailAlloc_3953_, 4, v_r_3942_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
else
{
lean_object* v___x_3959_; lean_object* v___x_3961_; 
v___x_3959_ = lean_unsigned_to_nat(2u);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 4, v_impl_3828_);
lean_ctor_set(v___x_3685_, 3, v_r_3942_);
lean_ctor_set(v___x_3685_, 0, v___x_3959_);
v___x_3961_ = v___x_3685_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3959_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v_k_3680_);
lean_ctor_set(v_reuseFailAlloc_3962_, 2, v_v_3681_);
lean_ctor_set(v_reuseFailAlloc_3962_, 3, v_r_3942_);
lean_ctor_set(v_reuseFailAlloc_3962_, 4, v_impl_3828_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
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
lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3964_ = lean_unsigned_to_nat(1u);
v___x_3965_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
lean_ctor_set(v___x_3965_, 1, v_k_3676_);
lean_ctor_set(v___x_3965_, 2, v_v_3677_);
lean_ctor_set(v___x_3965_, 3, v_t_3678_);
lean_ctor_set(v___x_3965_, 4, v_t_3678_);
return v___x_3965_;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3966_ = lean_box(1);
v___x_3967_ = l_Lake_LeanLib_defaultFacetConfig;
v___x_3968_ = l_Lake_LeanLib_defaultFacet;
v___x_3969_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3968_, v___x_3967_, v___x_3966_);
return v___x_3969_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3970_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__0, &l_Lake_LeanLib_initFacetConfigs___closed__0_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__0);
v___x_3971_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig));
v___x_3972_ = l_Lake_LeanLib_modulesFacet;
v___x_3973_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3972_, v___x_3971_, v___x_3970_);
return v___x_3973_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3974_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__1, &l_Lake_LeanLib_initFacetConfigs___closed__1_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__1);
v___x_3975_ = l_Lake_LeanLib_elabArtsFacetConfig;
v___x_3976_ = l_Lake_LeanLib_elabArtsFacet;
v___x_3977_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3976_, v___x_3975_, v___x_3974_);
return v___x_3977_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3978_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__2, &l_Lake_LeanLib_initFacetConfigs___closed__2_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__2);
v___x_3979_ = l_Lake_LeanLib_irArtsFacetConfig;
v___x_3980_ = l_Lake_LeanLib_irArtsFacet;
v___x_3981_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3980_, v___x_3979_, v___x_3978_);
return v___x_3981_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3982_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__3, &l_Lake_LeanLib_initFacetConfigs___closed__3_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__3);
v___x_3983_ = l_Lake_LeanLib_leanArtsFacetConfig;
v___x_3984_ = l_Lake_LeanLib_leanArtsFacet;
v___x_3985_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3984_, v___x_3983_, v___x_3982_);
return v___x_3985_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3986_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__4, &l_Lake_LeanLib_initFacetConfigs___closed__4_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__4);
v___x_3987_ = l_Lake_LeanLib_staticFacetConfig;
v___x_3988_ = l_Lake_LeanLib_staticFacet;
v___x_3989_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3988_, v___x_3987_, v___x_3986_);
return v___x_3989_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3990_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__5, &l_Lake_LeanLib_initFacetConfigs___closed__5_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__5);
v___x_3991_ = l_Lake_LeanLib_staticExportFacetConfig;
v___x_3992_ = l_Lake_LeanLib_staticExportFacet;
v___x_3993_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3992_, v___x_3991_, v___x_3990_);
return v___x_3993_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3994_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__6, &l_Lake_LeanLib_initFacetConfigs___closed__6_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__6);
v___x_3995_ = l_Lake_LeanLib_sharedFacetConfig;
v___x_3996_ = l_Lake_LeanLib_sharedFacet;
v___x_3997_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3996_, v___x_3995_, v___x_3994_);
return v___x_3997_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3998_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__7, &l_Lake_LeanLib_initFacetConfigs___closed__7_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__7);
v___x_3999_ = l_Lake_LeanLib_extraDepFacetConfig;
v___x_4000_ = l_Lake_LeanLib_extraDepFacet;
v___x_4001_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4000_, v___x_3999_, v___x_3998_);
return v___x_4001_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_4002_; 
v___x_4002_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__8, &l_Lake_LeanLib_initFacetConfigs___closed__8_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__8);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_4003_, lean_object* v_k_4004_, lean_object* v_v_4005_, lean_object* v_t_4006_, lean_object* v_hl_4007_){
_start:
{
lean_object* v___x_4008_; 
v___x_4008_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_4004_, v_v_4005_, v_t_4006_);
return v___x_4008_;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs(void){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Lake_LeanLib_initFacetConfigs;
return v___x_4009_;
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
