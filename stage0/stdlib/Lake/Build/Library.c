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
lean_object* v_a_655_; lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_670_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v_a_656_ = lean_ctor_get(v___x_654_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_670_ == 0)
{
v___x_658_ = v___x_654_;
v_isShared_659_ = v_isSharedCheck_670_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_inc(v_a_655_);
lean_dec(v___x_654_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_670_;
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
size_t v___x_667_; size_t v___x_668_; lean_object* v___x_669_; 
lean_del_object(v___x_658_);
v___x_667_ = ((size_t)0ULL);
v___x_668_ = lean_usize_of_nat(v___x_662_);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0(v_a_655_, v___x_667_, v___x_668_, v___x_661_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_656_);
lean_dec(v_a_655_);
return v___x_669_;
}
}
}
else
{
lean_object* v_a_671_; lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec_ref(v_a_637_);
v_a_671_ = lean_ctor_get(v___x_654_, 0);
v_a_672_ = lean_ctor_get(v___x_654_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_654_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_inc(v_a_671_);
lean_dec(v___x_654_);
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
lean_dec_ref(v_a_637_);
v_a_680_ = lean_ctor_get(v___x_651_, 0);
v_a_681_ = lean_ctor_get(v___x_651_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_651_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_inc(v_a_680_);
lean_dec(v___x_651_);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___boxed(lean_object* v_self_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts(v_self_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec(v_a_692_);
lean_dec(v_a_691_);
return v_res_697_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_box(0);
v___x_699_ = l_Lean_Json_compress(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(uint8_t v_fmt_700_){
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
v___x_702_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_703_){
_start:
{
uint8_t v_fmt_boxed_704_; lean_object* v_res_705_; 
v_fmt_boxed_704_ = lean_unbox(v_fmt_703_);
v_res_705_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(v_fmt_boxed_704_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0(uint8_t v_fmt_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(v_fmt_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___boxed(lean_object* v_fmt_709_, lean_object* v_a_710_){
_start:
{
uint8_t v_fmt_boxed_711_; lean_object* v_res_712_; 
v_fmt_boxed_711_ = lean_unbox(v_fmt_709_);
v_res_712_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0(v_fmt_boxed_711_, v_a_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_elabArtsFacetConfig___lam__0(uint8_t v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(v___y_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_elabArtsFacetConfig___lam__0___boxed(lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
uint8_t v___y_68__boxed_718_; lean_object* v_res_719_; 
v___y_68__boxed_718_ = lean_unbox(v___y_716_);
v_res_719_ = l_Lake_LeanLib_elabArtsFacetConfig___lam__0(v___y_68__boxed_718_, v___y_717_);
return v_res_719_;
}
}
static lean_object* _init_l_Lake_LeanLib_elabArtsFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_722_; uint8_t v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___f_722_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_723_ = 1;
v___x_724_ = l_Lake_instDataKindUnit;
v___x_725_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__1));
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
static lean_object* _init_l_Lake_LeanLib_elabArtsFacetConfig(void){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = lean_obj_once(&l_Lake_LeanLib_elabArtsFacetConfig___closed__2, &l_Lake_LeanLib_elabArtsFacetConfig___closed__2_once, _init_l_Lake_LeanLib_elabArtsFacetConfig___closed__2);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(lean_object* v_as_729_, size_t v_i_730_, size_t v_stop_731_, lean_object* v_b_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = lean_usize_dec_eq(v_i_730_, v_stop_731_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v_lib_742_; lean_object* v_pkg_743_; lean_object* v_name_744_; lean_object* v_keyName_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_741_ = lean_array_uget_borrowed(v_as_729_, v_i_730_);
v_lib_742_ = lean_ctor_get(v___x_741_, 0);
v_pkg_743_ = lean_ctor_get(v_lib_742_, 0);
v_name_744_ = lean_ctor_get(v___x_741_, 1);
v_keyName_745_ = lean_ctor_get(v_pkg_743_, 2);
v___x_746_ = l_Lake_Module_irArtsFacet;
lean_inc(v_name_744_);
lean_inc(v_keyName_745_);
v___x_747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_747_, 0, v_keyName_745_);
lean_ctor_set(v___x_747_, 1, v_name_744_);
v___x_748_ = l_Lake_Module_keyword;
lean_inc(v___x_741_);
v___x_749_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
lean_ctor_set(v___x_749_, 2, v___x_741_);
lean_ctor_set(v___x_749_, 3, v___x_746_);
lean_inc_ref(v___y_733_);
lean_inc_ref(v___y_737_);
lean_inc(v___y_736_);
lean_inc(v___y_735_);
lean_inc(v___y_734_);
v___x_750_ = lean_apply_7(v___y_733_, v___x_749_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, lean_box(0));
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v_a_752_; lean_object* v___x_753_; size_t v___x_754_; size_t v___x_755_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
v_a_752_ = lean_ctor_get(v___x_750_, 1);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_750_, 2);
v___x_753_ = l_Lake_Job_mix___redArg(v_b_732_, v_a_751_);
v___x_754_ = ((size_t)1ULL);
v___x_755_ = lean_usize_add(v_i_730_, v___x_754_);
v_i_730_ = v___x_755_;
v_b_732_ = v___x_753_;
v___y_738_ = v_a_752_;
goto _start;
}
else
{
lean_object* v_a_757_; lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v___y_733_);
lean_dec_ref(v_b_732_);
v_a_757_ = lean_ctor_get(v___x_750_, 0);
v_a_758_ = lean_ctor_get(v___x_750_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_750_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_inc(v_a_757_);
lean_dec(v___x_750_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_757_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v___x_766_; 
lean_dec_ref(v___y_733_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v_b_732_);
lean_ctor_set(v___x_766_, 1, v___y_738_);
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0___boxed(lean_object* v_as_767_, lean_object* v_i_768_, lean_object* v_stop_769_, lean_object* v_b_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
size_t v_i_boxed_778_; size_t v_stop_boxed_779_; lean_object* v_res_780_; 
v_i_boxed_778_ = lean_unbox_usize(v_i_768_);
lean_dec(v_i_768_);
v_stop_boxed_779_ = lean_unbox_usize(v_stop_769_);
lean_dec(v_stop_769_);
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(v_as_767_, v_i_boxed_778_, v_stop_boxed_779_, v_b_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v_as_767_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts(lean_object* v_self_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_pkg_789_; lean_object* v_name_790_; lean_object* v_keyName_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_pkg_789_ = lean_ctor_get(v_self_781_, 0);
v_name_790_ = lean_ctor_get(v_self_781_, 1);
v_keyName_791_ = lean_ctor_get(v_pkg_789_, 2);
v___x_792_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_790_);
lean_inc(v_keyName_791_);
v___x_793_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_793_, 0, v_keyName_791_);
lean_ctor_set(v___x_793_, 1, v_name_790_);
v___x_794_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_795_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
lean_ctor_set(v___x_795_, 2, v_self_781_);
lean_ctor_set(v___x_795_, 3, v___x_792_);
lean_inc_ref(v_a_782_);
lean_inc_ref(v_a_786_);
lean_inc(v_a_785_);
lean_inc(v_a_784_);
lean_inc(v_a_783_);
v___x_796_ = lean_apply_7(v_a_782_, v___x_795_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, lean_box(0));
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v_a_798_; lean_object* v___x_799_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
v_a_798_ = lean_ctor_get(v___x_796_, 1);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_796_, 2);
v___x_799_ = l_Lake_Job_await___redArg(v_a_797_, v_a_798_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_815_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
v_a_801_ = lean_ctor_get(v___x_799_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_815_ == 0)
{
v___x_803_ = v___x_799_;
v_isShared_804_ = v_isSharedCheck_815_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_inc(v_a_800_);
lean_dec(v___x_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_815_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_805_ = lean_unsigned_to_nat(0u);
v___x_806_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4);
v___x_807_ = lean_array_get_size(v_a_800_);
v___x_808_ = lean_nat_dec_lt(v___x_805_, v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_810_; 
lean_dec(v_a_800_);
lean_dec_ref(v_a_782_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_806_);
v___x_810_ = v___x_803_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_a_801_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
else
{
size_t v___x_812_; size_t v___x_813_; lean_object* v___x_814_; 
lean_del_object(v___x_803_);
v___x_812_ = ((size_t)0ULL);
v___x_813_ = lean_usize_of_nat(v___x_807_);
v___x_814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(v_a_800_, v___x_812_, v___x_813_, v___x_806_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_801_);
lean_dec(v_a_800_);
return v___x_814_;
}
}
}
else
{
lean_object* v_a_816_; lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v_a_782_);
v_a_816_ = lean_ctor_get(v___x_799_, 0);
v_a_817_ = lean_ctor_get(v___x_799_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_799_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_inc(v_a_816_);
lean_dec(v___x_799_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_816_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
else
{
lean_object* v_a_825_; lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec_ref(v_a_782_);
v_a_825_ = lean_ctor_get(v___x_796_, 0);
v_a_826_ = lean_ctor_get(v___x_796_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_796_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_inc(v_a_825_);
lean_dec(v___x_796_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_825_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts___boxed(lean_object* v_self_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts(v_self_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec(v_a_837_);
lean_dec(v_a_836_);
return v_res_842_;
}
}
static lean_object* _init_l_Lake_LeanLib_irArtsFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_844_; uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___f_844_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_845_ = 1;
v___x_846_ = l_Lake_instDataKindUnit;
v___x_847_ = ((lean_object*)(l_Lake_LeanLib_irArtsFacetConfig___closed__0));
v___x_848_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_849_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v___x_847_);
lean_ctor_set(v___x_849_, 2, v___x_846_);
lean_ctor_set(v___x_849_, 3, v___f_844_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*4, v___x_845_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*4 + 1, v___x_845_);
return v___x_849_;
}
}
static lean_object* _init_l_Lake_LeanLib_irArtsFacetConfig(void){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = lean_obj_once(&l_Lake_LeanLib_irArtsFacetConfig___closed__1, &l_Lake_LeanLib_irArtsFacetConfig___closed__1_once, _init_l_Lake_LeanLib_irArtsFacetConfig___closed__1);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0(lean_object* v_x_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_pkg_859_; lean_object* v_name_860_; lean_object* v_keyName_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v_pkg_859_ = lean_ctor_get(v_x_851_, 0);
v_name_860_ = lean_ctor_get(v_x_851_, 1);
v_keyName_861_ = lean_ctor_get(v_pkg_859_, 2);
v___x_862_ = l_Lake_LeanLib_irArtsFacet;
lean_inc(v_name_860_);
lean_inc(v_keyName_861_);
v___x_863_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_863_, 0, v_keyName_861_);
lean_ctor_set(v___x_863_, 1, v_name_860_);
v___x_864_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_865_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_865_, 0, v___x_863_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
lean_ctor_set(v___x_865_, 2, v_x_851_);
lean_ctor_set(v___x_865_, 3, v___x_862_);
lean_inc_ref(v___y_856_);
lean_inc(v___y_855_);
lean_inc(v___y_854_);
lean_inc(v___y_853_);
v___x_866_ = lean_apply_7(v___y_852_, v___x_865_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, lean_box(0));
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(lean_object* v_x_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lake_LeanLib_leanArtsFacetConfig___lam__0(v_x_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec(v___y_870_);
lean_dec(v___y_869_);
return v_res_875_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_877_; lean_object* v___f_878_; uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___f_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_877_ = 0;
v___f_878_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_879_ = 1;
v___x_880_ = l_Lake_instDataKindUnit;
v___f_881_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_882_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_883_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v___f_881_);
lean_ctor_set(v___x_883_, 2, v___x_880_);
lean_ctor_set(v___x_883_, 3, v___f_878_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*4, v___x_879_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*4 + 1, v___x_877_);
return v___x_883_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig(void){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = lean_obj_once(&l_Lake_LeanLib_leanArtsFacetConfig___closed__1, &l_Lake_LeanLib_leanArtsFacetConfig___closed__1_once, _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__1);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(lean_object* v_a_885_, lean_object* v_x_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lake_ModuleFacet_fetch___redArg(v_x_886_, v_a_885_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object* v_a_895_, lean_object* v_x_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(v_a_895_, v_x_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec(v___y_899_);
lean_dec(v___y_898_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(uint8_t v_shouldExport_905_, lean_object* v___x_906_, lean_object* v_bs_907_, lean_object* v_a_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_lib_916_; lean_object* v_config_917_; lean_object* v_nativeFacets_918_; lean_object* v___f_919_; lean_object* v___x_920_; lean_object* v___x_921_; size_t v_sz_922_; size_t v___x_923_; lean_object* v___x_189769__overap_924_; lean_object* v___x_925_; 
v_lib_916_ = lean_ctor_get(v_a_908_, 0);
v_config_917_ = lean_ctor_get(v_lib_916_, 2);
v_nativeFacets_918_ = lean_ctor_get(v_config_917_, 8);
lean_inc_ref(v_nativeFacets_918_);
v___f_919_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed), 9, 1);
lean_closure_set(v___f_919_, 0, v_a_908_);
v___x_920_ = lean_box(v_shouldExport_905_);
v___x_921_ = lean_apply_1(v_nativeFacets_918_, v___x_920_);
v_sz_922_ = lean_array_size(v___x_921_);
v___x_923_ = ((size_t)0ULL);
v___x_189769__overap_924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_906_, v___f_919_, v_sz_922_, v___x_923_, v___x_921_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_912_);
lean_inc(v___y_911_);
lean_inc(v___y_910_);
v___x_925_ = lean_apply_7(v___x_189769__overap_924_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, lean_box(0));
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_935_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_a_927_ = lean_ctor_get(v___x_925_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_935_ == 0)
{
v___x_929_ = v___x_925_;
v_isShared_930_ = v_isSharedCheck_935_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_inc(v_a_926_);
lean_dec(v___x_925_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_935_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = l_Array_append___redArg(v_bs_907_, v_a_926_);
lean_dec(v_a_926_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_931_);
v___x_933_ = v___x_929_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_a_927_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
else
{
lean_dec_ref(v_bs_907_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed(lean_object* v_shouldExport_936_, lean_object* v___x_937_, lean_object* v_bs_938_, lean_object* v_a_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
uint8_t v_shouldExport_boxed_947_; lean_object* v_res_948_; 
v_shouldExport_boxed_947_ = lean_unbox(v_shouldExport_936_);
v_res_948_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(v_shouldExport_boxed_947_, v___x_937_, v_bs_938_, v_a_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec(v___y_942_);
lean_dec(v___y_941_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(lean_object* v___x_949_, lean_object* v_pkg_950_, lean_object* v_x_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lake_Target_fetchIn___redArg(v___x_949_, v_pkg_950_, v_x_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object* v___x_960_, lean_object* v_pkg_961_, lean_object* v_x_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(v___x_960_, v_pkg_961_, v_x_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v___y_965_);
lean_dec(v___y_964_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object* v_a_971_, lean_object* v_x_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_log_981_; uint8_t v_action_982_; uint8_t v_wantsRebuild_983_; uint8_t v_canceled_984_; lean_object* v_trace_985_; lean_object* v_buildTime_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_log_981_ = lean_ctor_get(v___y_979_, 0);
v_action_982_ = lean_ctor_get_uint8(v___y_979_, sizeof(void*)*3);
v_wantsRebuild_983_ = lean_ctor_get_uint8(v___y_979_, sizeof(void*)*3 + 1);
v_canceled_984_ = lean_ctor_get_uint8(v___y_979_, sizeof(void*)*3 + 2);
v_trace_985_ = lean_ctor_get(v___y_979_, 1);
v_buildTime_986_ = lean_ctor_get(v___y_979_, 2);
v___x_987_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_988_ = lean_string_append(v___y_973_, v___x_987_);
v___x_989_ = lean_io_prim_handle_put_str(v_a_971_, v___x_988_);
lean_dec_ref(v___x_988_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_991_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_a_990_);
lean_ctor_set(v___x_991_, 1, v___y_979_);
return v___x_991_;
}
else
{
lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1005_; 
lean_inc(v_buildTime_986_);
lean_inc_ref(v_trace_985_);
lean_inc_ref(v_log_981_);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___y_979_);
if (v_isSharedCheck_1005_ == 0)
{
lean_object* v_unused_1006_; lean_object* v_unused_1007_; lean_object* v_unused_1008_; 
v_unused_1006_ = lean_ctor_get(v___y_979_, 2);
lean_dec(v_unused_1006_);
v_unused_1007_ = lean_ctor_get(v___y_979_, 1);
lean_dec(v_unused_1007_);
v_unused_1008_ = lean_ctor_get(v___y_979_, 0);
lean_dec(v_unused_1008_);
v___x_993_ = v___y_979_;
v_isShared_994_ = v_isSharedCheck_1005_;
goto v_resetjp_992_;
}
else
{
lean_dec(v___y_979_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1005_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_a_995_; lean_object* v___x_996_; uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v_a_995_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_989_, 1);
v___x_996_ = lean_io_error_to_string(v_a_995_);
v___x_997_ = 3;
v___x_998_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*1, v___x_997_);
v___x_999_ = lean_array_get_size(v_log_981_);
v___x_1000_ = lean_array_push(v_log_981_, v___x_998_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_1000_);
v___x_1002_ = v___x_993_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_trace_985_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_buildTime_986_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*3, v_action_982_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*3 + 1, v_wantsRebuild_983_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*3 + 2, v_canceled_984_);
v___x_1002_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_999_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
return v___x_1003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object* v_a_1009_, lean_object* v_x_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(v_a_1009_, v_x_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v_a_1009_);
return v_res_1019_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1027_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3));
v___x_1028_ = lean_unsigned_to_nat(5u);
v___x_1029_ = lean_mk_empty_array_with_capacity(v___x_1028_);
v___x_1030_ = lean_array_push(v___x_1029_, v___x_1027_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4));
v___x_1032_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6);
v___x_1033_ = lean_array_push(v___x_1032_, v___x_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(uint8_t v_bootstrap_1036_, lean_object* v___y_1037_, lean_object* v_oFiles_1038_, uint8_t v_shouldExport_1039_, uint8_t v___x_1040_, lean_object* v___x_1041_, size_t v___x_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
if (v_bootstrap_1036_ == 0)
{
lean_object* v_toContext_1050_; lean_object* v_lakeEnv_1051_; lean_object* v_lean_1052_; lean_object* v_log_1053_; uint8_t v_action_1054_; uint8_t v_wantsRebuild_1055_; uint8_t v_canceled_1056_; lean_object* v_trace_1057_; lean_object* v_buildTime_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1088_; 
lean_dec_ref(v___y_1043_);
lean_dec_ref(v___x_1041_);
v_toContext_1050_ = lean_ctor_get(v___y_1047_, 1);
v_lakeEnv_1051_ = lean_ctor_get(v_toContext_1050_, 0);
v_lean_1052_ = lean_ctor_get(v_lakeEnv_1051_, 1);
v_log_1053_ = lean_ctor_get(v___y_1048_, 0);
v_action_1054_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3);
v_wantsRebuild_1055_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3 + 1);
v_canceled_1056_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3 + 2);
v_trace_1057_ = lean_ctor_get(v___y_1048_, 1);
v_buildTime_1058_ = lean_ctor_get(v___y_1048_, 2);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___y_1048_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1060_ = v___y_1048_;
v_isShared_1061_ = v_isSharedCheck_1088_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_buildTime_1058_);
lean_inc(v_trace_1057_);
lean_inc(v_log_1053_);
lean_dec(v___y_1048_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1088_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v_ar_1062_; lean_object* v___x_1063_; 
v_ar_1062_ = lean_ctor_get(v_lean_1052_, 13);
lean_inc_ref(v_ar_1062_);
v___x_1063_ = l_Lake_compileStaticLib(v___y_1037_, v_oFiles_1038_, v_ar_1062_, v_bootstrap_1036_, v_log_1053_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1075_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_a_1065_ = lean_ctor_get(v___x_1063_, 1);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1067_ = v___x_1063_;
v_isShared_1068_ = v_isSharedCheck_1075_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1075_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v_a_1065_);
v___x_1070_ = v___x_1060_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1065_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_trace_1057_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_buildTime_1058_);
lean_ctor_set_uint8(v_reuseFailAlloc_1074_, sizeof(void*)*3, v_action_1054_);
lean_ctor_set_uint8(v_reuseFailAlloc_1074_, sizeof(void*)*3 + 1, v_wantsRebuild_1055_);
lean_ctor_set_uint8(v_reuseFailAlloc_1074_, sizeof(void*)*3 + 2, v_canceled_1056_);
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
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_1076_; lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1087_; 
v_a_1076_ = lean_ctor_get(v___x_1063_, 0);
v_a_1077_ = lean_ctor_get(v___x_1063_, 1);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1079_ = v___x_1063_;
v_isShared_1080_ = v_isSharedCheck_1087_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_inc(v_a_1076_);
lean_dec(v___x_1063_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1087_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v_a_1077_);
v___x_1082_ = v___x_1060_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1077_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_trace_1057_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_buildTime_1058_);
lean_ctor_set_uint8(v_reuseFailAlloc_1086_, sizeof(void*)*3, v_action_1054_);
lean_ctor_set_uint8(v_reuseFailAlloc_1086_, sizeof(void*)*3 + 1, v_wantsRebuild_1055_);
lean_ctor_set_uint8(v_reuseFailAlloc_1086_, sizeof(void*)*3 + 2, v_canceled_1056_);
v___x_1082_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1084_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v___x_1082_);
v___x_1084_ = v___x_1079_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1076_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
}
else
{
uint8_t v___x_1089_; 
v___x_1089_ = l_System_Platform_isOSX;
if (v___x_1089_ == 0)
{
uint8_t v___x_1090_; 
lean_dec_ref(v___y_1043_);
lean_dec_ref(v___x_1041_);
v___x_1090_ = l_System_Platform_isWindows;
if (v___x_1090_ == 0)
{
lean_object* v_toContext_1091_; lean_object* v_lakeEnv_1092_; lean_object* v_lean_1093_; lean_object* v_log_1094_; uint8_t v_action_1095_; uint8_t v_wantsRebuild_1096_; uint8_t v_canceled_1097_; lean_object* v_trace_1098_; lean_object* v_buildTime_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1129_; 
v_toContext_1091_ = lean_ctor_get(v___y_1047_, 1);
v_lakeEnv_1092_ = lean_ctor_get(v_toContext_1091_, 0);
v_lean_1093_ = lean_ctor_get(v_lakeEnv_1092_, 1);
v_log_1094_ = lean_ctor_get(v___y_1048_, 0);
v_action_1095_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3);
v_wantsRebuild_1096_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3 + 1);
v_canceled_1097_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3 + 2);
v_trace_1098_ = lean_ctor_get(v___y_1048_, 1);
v_buildTime_1099_ = lean_ctor_get(v___y_1048_, 2);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___y_1048_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1101_ = v___y_1048_;
v_isShared_1102_ = v_isSharedCheck_1129_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_buildTime_1099_);
lean_inc(v_trace_1098_);
lean_inc(v_log_1094_);
lean_dec(v___y_1048_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1129_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_ar_1103_; lean_object* v___x_1104_; 
v_ar_1103_ = lean_ctor_get(v_lean_1093_, 13);
lean_inc_ref(v_ar_1103_);
v___x_1104_ = l_Lake_compileStaticLib(v___y_1037_, v_oFiles_1038_, v_ar_1103_, v___x_1090_, v_log_1094_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1116_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_a_1106_ = lean_ctor_get(v___x_1104_, 1);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1108_ = v___x_1104_;
v_isShared_1109_ = v_isSharedCheck_1116_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1116_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v_a_1106_);
v___x_1111_ = v___x_1101_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1106_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_trace_1098_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_buildTime_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, sizeof(void*)*3, v_action_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, sizeof(void*)*3 + 1, v_wantsRebuild_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1115_, sizeof(void*)*3 + 2, v_canceled_1097_);
v___x_1111_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1113_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 1, v___x_1111_);
v___x_1113_ = v___x_1108_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1105_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1128_; 
v_a_1117_ = lean_ctor_get(v___x_1104_, 0);
v_a_1118_ = lean_ctor_get(v___x_1104_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1120_ = v___x_1104_;
v_isShared_1121_ = v_isSharedCheck_1128_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_inc(v_a_1117_);
lean_dec(v___x_1104_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1128_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v_a_1118_);
v___x_1123_ = v___x_1101_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1118_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_trace_1098_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v_buildTime_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1127_, sizeof(void*)*3, v_action_1095_);
lean_ctor_set_uint8(v_reuseFailAlloc_1127_, sizeof(void*)*3 + 1, v_wantsRebuild_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1127_, sizeof(void*)*3 + 2, v_canceled_1097_);
v___x_1123_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1125_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 1, v___x_1123_);
v___x_1125_ = v___x_1120_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1117_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1130_; lean_object* v_lakeEnv_1131_; lean_object* v_lean_1132_; lean_object* v_log_1133_; uint8_t v_action_1134_; uint8_t v_wantsRebuild_1135_; uint8_t v_canceled_1136_; lean_object* v_trace_1137_; lean_object* v_buildTime_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1168_; 
v_toContext_1130_ = lean_ctor_get(v___y_1047_, 1);
v_lakeEnv_1131_ = lean_ctor_get(v_toContext_1130_, 0);
v_lean_1132_ = lean_ctor_get(v_lakeEnv_1131_, 1);
v_log_1133_ = lean_ctor_get(v___y_1048_, 0);
v_action_1134_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3);
v_wantsRebuild_1135_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3 + 1);
v_canceled_1136_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3 + 2);
v_trace_1137_ = lean_ctor_get(v___y_1048_, 1);
v_buildTime_1138_ = lean_ctor_get(v___y_1048_, 2);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___y_1048_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1140_ = v___y_1048_;
v_isShared_1141_ = v_isSharedCheck_1168_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_buildTime_1138_);
lean_inc(v_trace_1137_);
lean_inc(v_log_1133_);
lean_dec(v___y_1048_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1168_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_ar_1142_; lean_object* v___x_1143_; 
v_ar_1142_ = lean_ctor_get(v_lean_1132_, 13);
lean_inc_ref(v_ar_1142_);
v___x_1143_ = l_Lake_compileStaticLib(v___y_1037_, v_oFiles_1038_, v_ar_1142_, v_shouldExport_1039_, v_log_1133_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1155_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_a_1145_ = lean_ctor_get(v___x_1143_, 1);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1147_ = v___x_1143_;
v_isShared_1148_ = v_isSharedCheck_1155_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1155_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v_a_1145_);
v___x_1150_ = v___x_1140_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1145_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_trace_1137_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_buildTime_1138_);
lean_ctor_set_uint8(v_reuseFailAlloc_1154_, sizeof(void*)*3, v_action_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1154_, sizeof(void*)*3 + 1, v_wantsRebuild_1135_);
lean_ctor_set_uint8(v_reuseFailAlloc_1154_, sizeof(void*)*3 + 2, v_canceled_1136_);
v___x_1150_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1152_; 
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v___x_1150_);
v___x_1152_ = v___x_1147_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1144_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1167_; 
v_a_1156_ = lean_ctor_get(v___x_1143_, 0);
v_a_1157_ = lean_ctor_get(v___x_1143_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1159_ = v___x_1143_;
v_isShared_1160_ = v_isSharedCheck_1167_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_inc(v_a_1156_);
lean_dec(v___x_1143_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1167_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v_a_1157_);
v___x_1162_ = v___x_1140_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1157_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_trace_1137_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_buildTime_1138_);
lean_ctor_set_uint8(v_reuseFailAlloc_1166_, sizeof(void*)*3, v_action_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1166_, sizeof(void*)*3 + 1, v_wantsRebuild_1135_);
lean_ctor_set_uint8(v_reuseFailAlloc_1166_, sizeof(void*)*3 + 2, v_canceled_1136_);
v___x_1162_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1164_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v___x_1162_);
v___x_1164_ = v___x_1159_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1156_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1169_; uint8_t v_action_1170_; uint8_t v_wantsRebuild_1171_; uint8_t v_canceled_1172_; lean_object* v_trace_1173_; lean_object* v_buildTime_1174_; lean_object* v___x_1175_; 
v_log_1169_ = lean_ctor_get(v___y_1048_, 0);
v_action_1170_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3);
v_wantsRebuild_1171_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3 + 1);
v_canceled_1172_ = lean_ctor_get_uint8(v___y_1048_, sizeof(void*)*3 + 2);
v_trace_1173_ = lean_ctor_get(v___y_1048_, 1);
v_buildTime_1174_ = lean_ctor_get(v___y_1048_, 2);
lean_inc_ref(v___y_1037_);
v___x_1175_ = l_Lake_createParentDirs(v___y_1037_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v_a_1179_; uint8_t v___x_1226_; lean_object* v___x_1227_; 
lean_dec_ref_known(v___x_1175_, 1);
v___x_1176_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1037_);
v___x_1177_ = l_System_FilePath_addExtension(v___y_1037_, v___x_1176_);
v___x_1226_ = 1;
v___x_1227_ = lean_io_prim_handle_mk(v___x_1177_, v___x_1226_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_array_get_size(v_oFiles_1038_);
v___x_1231_ = lean_nat_dec_lt(v___x_1229_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_dec(v_a_1228_);
lean_dec_ref(v___y_1043_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v_oFiles_1038_);
v_a_1179_ = v___y_1048_;
goto v___jp_1178_;
}
else
{
lean_object* v___f_1232_; lean_object* v___x_1233_; size_t v___x_1234_; lean_object* v___x_189918__overap_1235_; lean_object* v___x_1236_; 
v___f_1232_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1232_, 0, v_a_1228_);
v___x_1233_ = lean_box(0);
v___x_1234_ = lean_usize_of_nat(v___x_1230_);
v___x_189918__overap_1235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1041_, v___f_1232_, v_oFiles_1038_, v___x_1042_, v___x_1234_, v___x_1233_);
lean_inc_ref(v___y_1047_);
lean_inc(v___y_1046_);
lean_inc(v___y_1045_);
lean_inc(v___y_1044_);
v___x_1236_ = lean_apply_7(v___x_189918__overap_1235_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, lean_box(0));
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 1);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 2);
v_a_1179_ = v_a_1237_;
goto v___jp_1178_;
}
else
{
lean_dec_ref(v___x_1177_);
lean_dec_ref(v___y_1037_);
return v___x_1236_;
}
}
}
else
{
lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1251_; 
lean_inc(v_buildTime_1174_);
lean_inc_ref(v_trace_1173_);
lean_inc_ref(v_log_1169_);
lean_dec_ref(v___x_1177_);
lean_dec_ref(v___y_1043_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v_oFiles_1038_);
lean_dec_ref(v___y_1037_);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___y_1048_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; lean_object* v_unused_1253_; lean_object* v_unused_1254_; 
v_unused_1252_ = lean_ctor_get(v___y_1048_, 2);
lean_dec(v_unused_1252_);
v_unused_1253_ = lean_ctor_get(v___y_1048_, 1);
lean_dec(v_unused_1253_);
v_unused_1254_ = lean_ctor_get(v___y_1048_, 0);
lean_dec(v_unused_1254_);
v___x_1239_ = v___y_1048_;
v_isShared_1240_ = v_isSharedCheck_1251_;
goto v_resetjp_1238_;
}
else
{
lean_dec(v___y_1048_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1251_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_a_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
v_a_1241_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1242_ = lean_io_error_to_string(v_a_1241_);
v___x_1243_ = 3;
v___x_1244_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set_uint8(v___x_1244_, sizeof(void*)*1, v___x_1243_);
v___x_1245_ = lean_array_get_size(v_log_1169_);
v___x_1246_ = lean_array_push(v_log_1169_, v___x_1244_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1246_);
v___x_1248_ = v___x_1239_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_trace_1173_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_buildTime_1174_);
lean_ctor_set_uint8(v_reuseFailAlloc_1250_, sizeof(void*)*3, v_action_1170_);
lean_ctor_set_uint8(v_reuseFailAlloc_1250_, sizeof(void*)*3 + 1, v_wantsRebuild_1171_);
lean_ctor_set_uint8(v_reuseFailAlloc_1250_, sizeof(void*)*3 + 2, v_canceled_1172_);
v___x_1248_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1245_);
lean_ctor_set(v___x_1249_, 1, v___x_1248_);
return v___x_1249_;
}
}
}
v___jp_1178_:
{
lean_object* v___x_1180_; lean_object* v_log_1181_; uint8_t v_action_1182_; uint8_t v_wantsRebuild_1183_; uint8_t v_canceled_1184_; lean_object* v_trace_1185_; lean_object* v_buildTime_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1225_; 
v___x_1180_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1181_ = lean_ctor_get(v_a_1179_, 0);
v_action_1182_ = lean_ctor_get_uint8(v_a_1179_, sizeof(void*)*3);
v_wantsRebuild_1183_ = lean_ctor_get_uint8(v_a_1179_, sizeof(void*)*3 + 1);
v_canceled_1184_ = lean_ctor_get_uint8(v_a_1179_, sizeof(void*)*3 + 2);
v_trace_1185_ = lean_ctor_get(v_a_1179_, 1);
v_buildTime_1186_ = lean_ctor_get(v_a_1179_, 2);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_a_1179_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1188_ = v_a_1179_;
v_isShared_1189_ = v_isSharedCheck_1225_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_buildTime_1186_);
lean_inc(v_trace_1185_);
lean_inc(v_log_1181_);
lean_dec(v_a_1179_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1225_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1190_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1191_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1192_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1193_ = lean_array_push(v___x_1192_, v___y_1037_);
v___x_1194_ = lean_array_push(v___x_1193_, v___x_1191_);
v___x_1195_ = lean_array_push(v___x_1194_, v___x_1177_);
v___x_1196_ = lean_box(0);
v___x_1197_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1198_ = 0;
v___x_1199_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1199_, 0, v___x_1180_);
lean_ctor_set(v___x_1199_, 1, v___x_1190_);
lean_ctor_set(v___x_1199_, 2, v___x_1195_);
lean_ctor_set(v___x_1199_, 3, v___x_1196_);
lean_ctor_set(v___x_1199_, 4, v___x_1197_);
lean_ctor_set_uint8(v___x_1199_, sizeof(void*)*5, v___x_1040_);
lean_ctor_set_uint8(v___x_1199_, sizeof(void*)*5 + 1, v___x_1198_);
v___x_1200_ = l_Lake_proc(v___x_1199_, v___x_1198_, v___x_1196_, v_log_1181_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1212_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_a_1202_ = lean_ctor_get(v___x_1200_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1204_ = v___x_1200_;
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1212_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v_a_1202_);
v___x_1207_ = v___x_1188_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1202_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_trace_1185_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_buildTime_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*3, v_action_1182_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*3 + 1, v_wantsRebuild_1183_);
lean_ctor_set_uint8(v_reuseFailAlloc_1211_, sizeof(void*)*3 + 2, v_canceled_1184_);
v___x_1207_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1209_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v___x_1207_);
v___x_1209_ = v___x_1204_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1201_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1224_; 
v_a_1213_ = lean_ctor_get(v___x_1200_, 0);
v_a_1214_ = lean_ctor_get(v___x_1200_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1216_ = v___x_1200_;
v_isShared_1217_ = v_isSharedCheck_1224_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_inc(v_a_1213_);
lean_dec(v___x_1200_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1224_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v_a_1214_);
v___x_1219_ = v___x_1188_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1214_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_trace_1185_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_buildTime_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, sizeof(void*)*3, v_action_1182_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, sizeof(void*)*3 + 1, v_wantsRebuild_1183_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, sizeof(void*)*3 + 2, v_canceled_1184_);
v___x_1219_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1221_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v___x_1219_);
v___x_1221_ = v___x_1216_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1213_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1268_; 
lean_inc(v_buildTime_1174_);
lean_inc_ref(v_trace_1173_);
lean_inc_ref(v_log_1169_);
lean_dec_ref(v___y_1043_);
lean_dec_ref(v___x_1041_);
lean_dec_ref(v_oFiles_1038_);
lean_dec_ref(v___y_1037_);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___y_1048_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; lean_object* v_unused_1270_; lean_object* v_unused_1271_; 
v_unused_1269_ = lean_ctor_get(v___y_1048_, 2);
lean_dec(v_unused_1269_);
v_unused_1270_ = lean_ctor_get(v___y_1048_, 1);
lean_dec(v_unused_1270_);
v_unused_1271_ = lean_ctor_get(v___y_1048_, 0);
lean_dec(v_unused_1271_);
v___x_1256_ = v___y_1048_;
v_isShared_1257_ = v_isSharedCheck_1268_;
goto v_resetjp_1255_;
}
else
{
lean_dec(v___y_1048_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1268_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_a_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
v_a_1258_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1258_);
lean_dec_ref_known(v___x_1175_, 1);
v___x_1259_ = lean_io_error_to_string(v_a_1258_);
v___x_1260_ = 3;
v___x_1261_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1261_, 0, v___x_1259_);
lean_ctor_set_uint8(v___x_1261_, sizeof(void*)*1, v___x_1260_);
v___x_1262_ = lean_array_get_size(v_log_1169_);
v___x_1263_ = lean_array_push(v_log_1169_, v___x_1261_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 0, v___x_1263_);
v___x_1265_ = v___x_1256_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_trace_1173_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_buildTime_1174_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3, v_action_1170_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3 + 1, v_wantsRebuild_1171_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3 + 2, v_canceled_1172_);
v___x_1265_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1262_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
return v___x_1266_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object* v_bootstrap_1272_, lean_object* v___y_1273_, lean_object* v_oFiles_1274_, lean_object* v_shouldExport_1275_, lean_object* v___x_1276_, lean_object* v___x_1277_, lean_object* v___x_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
uint8_t v_bootstrap_boxed_1286_; uint8_t v_shouldExport_boxed_1287_; uint8_t v___x_190292__boxed_1288_; size_t v___x_190294__boxed_1289_; lean_object* v_res_1290_; 
v_bootstrap_boxed_1286_ = lean_unbox(v_bootstrap_1272_);
v_shouldExport_boxed_1287_ = lean_unbox(v_shouldExport_1275_);
v___x_190292__boxed_1288_ = lean_unbox(v___x_1276_);
v___x_190294__boxed_1289_ = lean_unbox_usize(v___x_1278_);
lean_dec(v___x_1278_);
v_res_1290_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(v_bootstrap_boxed_1286_, v___y_1273_, v_oFiles_1274_, v_shouldExport_boxed_1287_, v___x_190292__boxed_1288_, v___x_1277_, v___x_190294__boxed_1289_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec(v___y_1280_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(uint8_t v_bootstrap_1292_, lean_object* v___y_1293_, uint8_t v_shouldExport_1294_, uint8_t v___x_1295_, lean_object* v___x_1296_, size_t v___x_1297_, lean_object* v_oFiles_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___y_1310_; uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1306_ = lean_box(v_bootstrap_1292_);
v___x_1307_ = lean_box(v_shouldExport_1294_);
v___x_1308_ = lean_box(v___x_1295_);
v___x_1309_ = lean_box_usize(v___x_1297_);
lean_inc_ref(v___y_1293_);
v___y_1310_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed), 14, 7);
lean_closure_set(v___y_1310_, 0, v___x_1306_);
lean_closure_set(v___y_1310_, 1, v___y_1293_);
lean_closure_set(v___y_1310_, 2, v_oFiles_1298_);
lean_closure_set(v___y_1310_, 3, v___x_1307_);
lean_closure_set(v___y_1310_, 4, v___x_1308_);
lean_closure_set(v___y_1310_, 5, v___x_1296_);
lean_closure_set(v___y_1310_, 6, v___x_1309_);
v___x_1311_ = 0;
v___x_1312_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1313_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1293_, v___y_1310_, v___x_1311_, v___x_1312_, v___x_1295_, v___x_1311_, v___x_1311_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1323_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_a_1315_ = lean_ctor_get(v___x_1313_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1317_ = v___x_1313_;
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1323_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v_path_1319_; lean_object* v___x_1321_; 
v_path_1319_ = lean_ctor_get(v_a_1314_, 1);
lean_inc_ref(v_path_1319_);
lean_dec(v_a_1314_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v_path_1319_);
v___x_1321_ = v___x_1317_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_path_1319_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_a_1315_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
v_a_1324_ = lean_ctor_get(v___x_1313_, 0);
v_a_1325_ = lean_ctor_get(v___x_1313_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1313_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_inc(v_a_1324_);
lean_dec(v___x_1313_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1324_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object* v_bootstrap_1333_, lean_object* v___y_1334_, lean_object* v_shouldExport_1335_, lean_object* v___x_1336_, lean_object* v___x_1337_, lean_object* v___x_1338_, lean_object* v_oFiles_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
uint8_t v_bootstrap_boxed_1347_; uint8_t v_shouldExport_boxed_1348_; uint8_t v___x_190705__boxed_1349_; size_t v___x_190707__boxed_1350_; lean_object* v_res_1351_; 
v_bootstrap_boxed_1347_ = lean_unbox(v_bootstrap_1333_);
v_shouldExport_boxed_1348_ = lean_unbox(v_shouldExport_1335_);
v___x_190705__boxed_1349_ = lean_unbox(v___x_1336_);
v___x_190707__boxed_1350_ = lean_unbox_usize(v___x_1338_);
lean_dec(v___x_1338_);
v_res_1351_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(v_bootstrap_boxed_1347_, v___y_1334_, v_shouldExport_boxed_1348_, v___x_190705__boxed_1349_, v___x_1337_, v___x_190707__boxed_1350_, v_oFiles_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec(v___y_1341_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object* v_config_1356_, lean_object* v_config_1357_, uint8_t v_shouldExport_1358_, uint8_t v___x_1359_, lean_object* v___x_1360_, lean_object* v___x_1361_, lean_object* v___x_1362_, lean_object* v___x_1363_, lean_object* v___f_1364_, lean_object* v_dir_1365_, lean_object* v_self_1366_, lean_object* v___x_1367_, lean_object* v___f_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
size_t v___y_1377_; uint8_t v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v_a_1397_; lean_object* v_a_1398_; lean_object* v___x_1441_; 
lean_inc_ref(v___y_1369_);
lean_inc_ref(v___y_1373_);
lean_inc(v___y_1372_);
lean_inc(v___y_1371_);
lean_inc(v___x_1362_);
v___x_1441_ = lean_apply_7(v___y_1369_, v___x_1367_, v___x_1362_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, lean_box(0));
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v_a_1443_; lean_object* v___x_1444_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
v_a_1443_ = lean_ctor_get(v___x_1441_, 1);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1441_, 2);
v___x_1444_ = l_Lake_Job_await___redArg(v_a_1442_, v_a_1443_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v_a_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
v_a_1446_ = lean_ctor_get(v___x_1444_, 1);
lean_inc(v_a_1446_);
lean_dec_ref_known(v___x_1444_, 2);
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_1449_ = lean_array_get_size(v_a_1445_);
v___x_1450_ = lean_nat_dec_lt(v___x_1447_, v___x_1449_);
if (v___x_1450_ == 0)
{
lean_dec(v_a_1445_);
lean_dec_ref(v___f_1368_);
v_a_1397_ = v___x_1448_;
v_a_1398_ = v_a_1446_;
goto v___jp_1396_;
}
else
{
size_t v___x_1451_; size_t v___x_1452_; lean_object* v___x_190052__overap_1453_; lean_object* v___x_1454_; 
v___x_1451_ = ((size_t)0ULL);
v___x_1452_ = lean_usize_of_nat(v___x_1449_);
lean_inc_ref(v___x_1363_);
v___x_190052__overap_1453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1363_, v___f_1368_, v_a_1445_, v___x_1451_, v___x_1452_, v___x_1448_);
lean_inc_ref(v___y_1373_);
lean_inc(v___y_1372_);
lean_inc(v___y_1371_);
lean_inc(v___x_1362_);
lean_inc_ref(v___y_1369_);
v___x_1454_ = lean_apply_7(v___x_190052__overap_1453_, v___y_1369_, v___x_1362_, v___y_1371_, v___y_1372_, v___y_1373_, v_a_1446_, lean_box(0));
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v_a_1456_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
v_a_1456_ = lean_ctor_get(v___x_1454_, 1);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1454_, 2);
v_a_1397_ = v_a_1455_;
v_a_1398_ = v_a_1456_;
goto v___jp_1396_;
}
else
{
lean_object* v_a_1457_; lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v___y_1369_);
lean_dec_ref(v_self_1366_);
lean_dec_ref(v_dir_1365_);
lean_dec_ref(v___f_1364_);
lean_dec_ref(v___x_1363_);
lean_dec(v___x_1362_);
lean_dec(v___x_1361_);
lean_dec_ref(v___x_1360_);
lean_dec_ref(v_config_1356_);
v_a_1457_ = lean_ctor_get(v___x_1454_, 0);
v_a_1458_ = lean_ctor_get(v___x_1454_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1454_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_inc(v_a_1457_);
lean_dec(v___x_1454_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1457_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref(v___y_1369_);
lean_dec_ref(v___f_1368_);
lean_dec_ref(v_self_1366_);
lean_dec_ref(v_dir_1365_);
lean_dec_ref(v___f_1364_);
lean_dec_ref(v___x_1363_);
lean_dec(v___x_1362_);
lean_dec(v___x_1361_);
lean_dec_ref(v___x_1360_);
lean_dec_ref(v_config_1356_);
v_a_1466_ = lean_ctor_get(v___x_1444_, 0);
v_a_1467_ = lean_ctor_get(v___x_1444_, 1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1444_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_inc(v_a_1466_);
lean_dec(v___x_1444_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1466_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec_ref(v___y_1369_);
lean_dec_ref(v___f_1368_);
lean_dec_ref(v_self_1366_);
lean_dec_ref(v_dir_1365_);
lean_dec_ref(v___f_1364_);
lean_dec_ref(v___x_1363_);
lean_dec(v___x_1362_);
lean_dec(v___x_1361_);
lean_dec_ref(v___x_1360_);
lean_dec_ref(v_config_1356_);
v_a_1475_ = lean_ctor_get(v___x_1441_, 0);
v_a_1476_ = lean_ctor_get(v___x_1441_, 1);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1441_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_inc(v_a_1475_);
lean_dec(v___x_1441_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1475_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
v___jp_1376_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___f_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1383_ = lean_box(v___y_1378_);
v___x_1384_ = lean_box(v_shouldExport_1358_);
v___x_1385_ = lean_box(v___x_1359_);
v___x_1386_ = lean_box_usize(v___y_1377_);
v___f_1387_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed), 14, 6);
lean_closure_set(v___f_1387_, 0, v___x_1383_);
lean_closure_set(v___f_1387_, 1, v___y_1382_);
lean_closure_set(v___f_1387_, 2, v___x_1384_);
lean_closure_set(v___f_1387_, 3, v___x_1385_);
lean_closure_set(v___f_1387_, 4, v___x_1360_);
lean_closure_set(v___f_1387_, 5, v___x_1386_);
v___x_1388_ = l_Array_append___redArg(v___y_1379_, v___y_1380_);
lean_dec_ref(v___y_1380_);
v___x_1389_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_1390_ = l_Lake_Job_collectArray___redArg(v___x_1388_, v___x_1389_);
lean_dec_ref(v___x_1388_);
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = 0;
v___x_1393_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_1394_ = l_Lake_Job_mapM___redArg(v___x_1361_, v___x_1390_, v___f_1387_, v___x_1391_, v___x_1392_, v___y_1369_, v___x_1362_, v___y_1371_, v___y_1372_, v___y_1373_, v___x_1393_);
lean_dec(v___x_1362_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v___y_1381_);
return v___x_1395_;
}
v___jp_1396_:
{
lean_object* v_toLeanConfig_1399_; lean_object* v_toLeanConfig_1400_; uint8_t v_bootstrap_1401_; lean_object* v_buildDir_1402_; lean_object* v_nativeLibDir_1403_; lean_object* v_moreLinkObjs_1404_; lean_object* v_moreLinkObjs_1405_; lean_object* v___x_1406_; size_t v_sz_1407_; size_t v___x_1408_; lean_object* v___x_190010__overap_1409_; lean_object* v___x_1410_; 
v_toLeanConfig_1399_ = lean_ctor_get(v_config_1356_, 1);
lean_inc_ref(v_toLeanConfig_1399_);
v_toLeanConfig_1400_ = lean_ctor_get(v_config_1357_, 0);
v_bootstrap_1401_ = lean_ctor_get_uint8(v_config_1356_, sizeof(void*)*28);
v_buildDir_1402_ = lean_ctor_get(v_config_1356_, 5);
lean_inc_ref(v_buildDir_1402_);
v_nativeLibDir_1403_ = lean_ctor_get(v_config_1356_, 7);
lean_inc_ref(v_nativeLibDir_1403_);
lean_dec_ref(v_config_1356_);
v_moreLinkObjs_1404_ = lean_ctor_get(v_toLeanConfig_1399_, 6);
lean_inc_ref(v_moreLinkObjs_1404_);
lean_dec_ref(v_toLeanConfig_1399_);
v_moreLinkObjs_1405_ = lean_ctor_get(v_toLeanConfig_1400_, 6);
v___x_1406_ = l_Array_append___redArg(v_moreLinkObjs_1404_, v_moreLinkObjs_1405_);
v_sz_1407_ = lean_array_size(v___x_1406_);
v___x_1408_ = ((size_t)0ULL);
v___x_190010__overap_1409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1363_, v___f_1364_, v_sz_1407_, v___x_1408_, v___x_1406_);
lean_inc_ref(v___y_1373_);
lean_inc(v___y_1372_);
lean_inc(v___y_1371_);
lean_inc(v___x_1362_);
lean_inc_ref(v___y_1369_);
v___x_1410_ = lean_apply_7(v___x_190010__overap_1409_, v___y_1369_, v___x_1362_, v___y_1371_, v___y_1372_, v___y_1373_, v_a_1398_, lean_box(0));
if (lean_obj_tag(v___x_1410_) == 0)
{
if (v_shouldExport_1358_ == 0)
{
lean_object* v_a_1411_; lean_object* v_a_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
v_a_1412_ = lean_ctor_get(v___x_1410_, 1);
lean_inc(v_a_1412_);
lean_dec_ref_known(v___x_1410_, 2);
v___x_1413_ = l_System_FilePath_normalize(v_buildDir_1402_);
v___x_1414_ = l_Lake_joinRelative(v_dir_1365_, v___x_1413_);
v___x_1415_ = l_System_FilePath_normalize(v_nativeLibDir_1403_);
v___x_1416_ = l_Lake_joinRelative(v___x_1414_, v___x_1415_);
v___x_1417_ = l_Lake_LeanLib_libName(v_self_1366_);
v___x_1418_ = l_Lake_nameToStaticLib(v___x_1417_, v_shouldExport_1358_);
v___x_1419_ = l_Lake_joinRelative(v___x_1416_, v___x_1418_);
v___y_1377_ = v___x_1408_;
v___y_1378_ = v_bootstrap_1401_;
v___y_1379_ = v_a_1397_;
v___y_1380_ = v_a_1411_;
v___y_1381_ = v_a_1412_;
v___y_1382_ = v___x_1419_;
goto v___jp_1376_;
}
else
{
lean_object* v_a_1420_; lean_object* v_a_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v_a_1420_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1420_);
v_a_1421_ = lean_ctor_get(v___x_1410_, 1);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1410_, 2);
v___x_1422_ = l_System_FilePath_normalize(v_buildDir_1402_);
v___x_1423_ = l_Lake_joinRelative(v_dir_1365_, v___x_1422_);
v___x_1424_ = l_System_FilePath_normalize(v_nativeLibDir_1403_);
v___x_1425_ = l_Lake_joinRelative(v___x_1423_, v___x_1424_);
v___x_1426_ = l_Lake_LeanLib_libName(v_self_1366_);
v___x_1427_ = 0;
v___x_1428_ = l_Lake_nameToStaticLib(v___x_1426_, v___x_1427_);
v___x_1429_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_1430_ = l_System_FilePath_addExtension(v___x_1428_, v___x_1429_);
v___x_1431_ = l_Lake_joinRelative(v___x_1425_, v___x_1430_);
v___y_1377_ = v___x_1408_;
v___y_1378_ = v_bootstrap_1401_;
v___y_1379_ = v_a_1397_;
v___y_1380_ = v_a_1420_;
v___y_1381_ = v_a_1421_;
v___y_1382_ = v___x_1431_;
goto v___jp_1376_;
}
}
else
{
lean_object* v_a_1432_; lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref(v_nativeLibDir_1403_);
lean_dec_ref(v_buildDir_1402_);
lean_dec_ref(v_a_1397_);
lean_dec_ref(v___y_1369_);
lean_dec_ref(v_self_1366_);
lean_dec_ref(v_dir_1365_);
lean_dec(v___x_1362_);
lean_dec(v___x_1361_);
lean_dec_ref(v___x_1360_);
v_a_1432_ = lean_ctor_get(v___x_1410_, 0);
v_a_1433_ = lean_ctor_get(v___x_1410_, 1);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1410_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_inc(v_a_1432_);
lean_dec(v___x_1410_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1432_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed(lean_object** _args){
lean_object* v_config_1484_ = _args[0];
lean_object* v_config_1485_ = _args[1];
lean_object* v_shouldExport_1486_ = _args[2];
lean_object* v___x_1487_ = _args[3];
lean_object* v___x_1488_ = _args[4];
lean_object* v___x_1489_ = _args[5];
lean_object* v___x_1490_ = _args[6];
lean_object* v___x_1491_ = _args[7];
lean_object* v___f_1492_ = _args[8];
lean_object* v_dir_1493_ = _args[9];
lean_object* v_self_1494_ = _args[10];
lean_object* v___x_1495_ = _args[11];
lean_object* v___f_1496_ = _args[12];
lean_object* v___y_1497_ = _args[13];
lean_object* v___y_1498_ = _args[14];
lean_object* v___y_1499_ = _args[15];
lean_object* v___y_1500_ = _args[16];
lean_object* v___y_1501_ = _args[17];
lean_object* v___y_1502_ = _args[18];
lean_object* v___y_1503_ = _args[19];
_start:
{
uint8_t v_shouldExport_boxed_1504_; uint8_t v___x_190803__boxed_1505_; lean_object* v_res_1506_; 
v_shouldExport_boxed_1504_ = lean_unbox(v_shouldExport_1486_);
v___x_190803__boxed_1505_ = lean_unbox(v___x_1487_);
v_res_1506_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(v_config_1484_, v_config_1485_, v_shouldExport_boxed_1504_, v___x_190803__boxed_1505_, v___x_1488_, v___x_1489_, v___x_1490_, v___x_1491_, v___f_1492_, v_dir_1493_, v_self_1494_, v___x_1495_, v___f_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec(v_config_1485_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object* v_self_1510_, uint8_t v_shouldExport_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v___x_1519_; lean_object* v_toApplicative_1520_; lean_object* v_toBind_1521_; lean_object* v_toFunctor_1522_; lean_object* v_toPure_1523_; lean_object* v___f_1524_; lean_object* v___f_1525_; lean_object* v___f_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; lean_object* v___f_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_toBuildConfig_1537_; lean_object* v_registeredJobs_1538_; uint8_t v_verbosity_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___f_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; uint8_t v___x_1547_; lean_object* v___y_1549_; 
v___x_1519_ = l_instMonadBaseIO;
v_toApplicative_1520_ = lean_ctor_get(v___x_1519_, 0);
v_toBind_1521_ = lean_ctor_get(v___x_1519_, 1);
v_toFunctor_1522_ = lean_ctor_get(v_toApplicative_1520_, 0);
v_toPure_1523_ = lean_ctor_get(v_toApplicative_1520_, 1);
lean_inc_n(v_toBind_1521_, 3);
lean_inc_n(v_toPure_1523_, 5);
v___f_1524_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1524_, 0, v_toPure_1523_);
lean_closure_set(v___f_1524_, 1, v_toBind_1521_);
v___f_1525_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1525_, 0, v_toPure_1523_);
lean_closure_set(v___f_1525_, 1, v_toBind_1521_);
lean_inc_ref(v___f_1524_);
v___f_1526_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1526_, 0, v_toPure_1523_);
lean_closure_set(v___f_1526_, 1, v___f_1524_);
lean_inc_ref_n(v_toFunctor_1522_, 2);
v___f_1527_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1527_, 0, v_toFunctor_1522_);
lean_closure_set(v___f_1527_, 1, v_toPure_1523_);
lean_closure_set(v___f_1527_, 2, v_toBind_1521_);
v___x_1528_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1522_);
v___f_1529_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1529_, 0, v_toPure_1523_);
v___x_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___f_1529_);
lean_ctor_set(v___x_1530_, 2, v___f_1527_);
lean_ctor_set(v___x_1530_, 3, v___f_1526_);
lean_ctor_set(v___x_1530_, 4, v___f_1525_);
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
lean_ctor_set(v___x_1531_, 1, v___f_1524_);
v___x_1532_ = l_ReaderT_instMonad___redArg(v___x_1531_);
v___x_1533_ = l_StateRefT_x27_instMonad___redArg(v___x_1532_);
v___x_1534_ = l_ReaderT_instMonad___redArg(v___x_1533_);
v___x_1535_ = l_ReaderT_instMonad___redArg(v___x_1534_);
v___x_1536_ = l_Lake_EquipT_instMonad___redArg(v___x_1535_);
v_toBuildConfig_1537_ = lean_ctor_get(v_a_1516_, 0);
v_registeredJobs_1538_ = lean_ctor_get(v_a_1516_, 4);
v_verbosity_1539_ = lean_ctor_get_uint8(v_toBuildConfig_1537_, sizeof(void*)*5 + 4);
v___x_1540_ = l_Lake_instDataKindFilePath;
v___x_1541_ = lean_box(v_shouldExport_1511_);
lean_inc_ref(v___x_1536_);
v___f_1542_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1542_, 0, v___x_1541_);
lean_closure_set(v___f_1542_, 1, v___x_1536_);
v___x_1543_ = lean_box(v_verbosity_1539_);
v___x_1544_ = lean_obj_tag_nat(v___x_1543_);
lean_dec(v___x_1543_);
v___x_1545_ = lean_unsigned_to_nat(2u);
v___x_1546_ = lean_nat_dec_eq(v___x_1544_, v___x_1545_);
v___x_1547_ = 1;
if (v___x_1546_ == 0)
{
lean_object* v___x_1595_; 
v___x_1595_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_1549_ = v___x_1595_;
goto v___jp_1548_;
}
else
{
if (v_shouldExport_1511_ == 0)
{
lean_object* v___x_1596_; 
v___x_1596_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___y_1549_ = v___x_1596_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1597_; 
v___x_1597_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_1549_ = v___x_1597_;
goto v___jp_1548_;
}
}
v___jp_1548_:
{
lean_object* v_pkg_1550_; lean_object* v_name_1551_; lean_object* v_config_1552_; lean_object* v_keyName_1553_; lean_object* v_dir_1554_; lean_object* v_config_1555_; lean_object* v___f_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___f_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; 
v_pkg_1550_ = lean_ctor_get(v_self_1510_, 0);
v_name_1551_ = lean_ctor_get(v_self_1510_, 1);
v_config_1552_ = lean_ctor_get(v_self_1510_, 2);
lean_inc(v_config_1552_);
v_keyName_1553_ = lean_ctor_get(v_pkg_1550_, 2);
v_dir_1554_ = lean_ctor_get(v_pkg_1550_, 4);
lean_inc_ref(v_dir_1554_);
v_config_1555_ = lean_ctor_get(v_pkg_1550_, 6);
lean_inc_ref(v_config_1555_);
lean_inc_ref_n(v_pkg_1550_, 2);
v___f_1556_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(v___f_1556_, 0, v___x_1540_);
lean_closure_set(v___f_1556_, 1, v_pkg_1550_);
lean_inc_n(v_name_1551_, 2);
v___x_1557_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1551_, v___x_1547_);
v___x_1558_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0));
v___x_1559_ = lean_string_append(v___x_1557_, v___x_1558_);
v___x_1560_ = lean_string_append(v___x_1559_, v___y_1549_);
v___x_1561_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_1553_);
v___x_1562_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_keyName_1553_);
lean_ctor_set(v___x_1562_, 1, v_name_1551_);
v___x_1563_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_1510_);
v___x_1564_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1562_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
lean_ctor_set(v___x_1564_, 2, v_self_1510_);
lean_ctor_set(v___x_1564_, 3, v___x_1561_);
v___x_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1565_, 0, v_pkg_1550_);
v___x_1566_ = lean_box(v_shouldExport_1511_);
v___x_1567_ = lean_box(v___x_1547_);
lean_inc_ref(v___x_1536_);
v___f_1568_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed), 20, 13);
lean_closure_set(v___f_1568_, 0, v_config_1555_);
lean_closure_set(v___f_1568_, 1, v_config_1552_);
lean_closure_set(v___f_1568_, 2, v___x_1566_);
lean_closure_set(v___f_1568_, 3, v___x_1567_);
lean_closure_set(v___f_1568_, 4, v___x_1536_);
lean_closure_set(v___f_1568_, 5, v___x_1540_);
lean_closure_set(v___f_1568_, 6, v___x_1565_);
lean_closure_set(v___f_1568_, 7, v___x_1536_);
lean_closure_set(v___f_1568_, 8, v___f_1556_);
lean_closure_set(v___f_1568_, 9, v_dir_1554_);
lean_closure_set(v___f_1568_, 10, v_self_1510_);
lean_closure_set(v___f_1568_, 11, v___x_1564_);
lean_closure_set(v___f_1568_, 12, v___f_1542_);
v___x_1569_ = 0;
v___x_1570_ = l_Lake_ensureJob___redArg(v___x_1540_, v___f_1568_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1594_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_a_1572_ = lean_ctor_get(v___x_1570_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1574_ = v___x_1570_;
v_isShared_1575_ = v_isSharedCheck_1594_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1594_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v_task_1576_; lean_object* v_kind_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1592_; 
v_task_1576_ = lean_ctor_get(v_a_1571_, 0);
v_kind_1577_ = lean_ctor_get(v_a_1571_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_a_1571_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v_a_1571_, 2);
lean_dec(v_unused_1593_);
v___x_1579_ = v_a_1571_;
v_isShared_1580_ = v_isSharedCheck_1592_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_kind_1577_);
lean_inc(v_task_1576_);
lean_dec(v_a_1571_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1592_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_job_1582_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 2, v___x_1560_);
v_job_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_task_1576_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_kind_1577_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v___x_1560_);
v_job_1582_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_ctor_set_uint8(v_job_1582_, sizeof(void*)*3, v___x_1569_);
v___x_1583_ = lean_st_ref_take(v_registeredJobs_1538_);
lean_inc_ref(v_job_1582_);
v___x_1584_ = l_Lake_Job_toOpaque___redArg(v_job_1582_);
v___x_1585_ = lean_array_push(v___x_1583_, v___x_1584_);
v___x_1586_ = lean_st_ref_put(v_registeredJobs_1538_, v___x_1585_);
v___x_1587_ = l_Lake_Job_renew___redArg(v_job_1582_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1587_);
v___x_1589_ = v___x_1574_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_a_1572_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1560_);
return v___x_1570_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object* v_self_1598_, lean_object* v_shouldExport_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
uint8_t v_shouldExport_boxed_1607_; lean_object* v_res_1608_; 
v_shouldExport_boxed_1607_ = lean_unbox(v_shouldExport_1599_);
v_res_1608_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1598_, v_shouldExport_boxed_1607_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec(v_a_1601_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t v_fmt_1609_, lean_object* v_a_1610_){
_start:
{
if (v_fmt_1609_ == 0)
{
return v_a_1610_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1611_ = l_Lake_mkRelPathString(v_a_1610_);
v___x_1612_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
v___x_1613_ = l_Lean_Json_compress(v___x_1612_);
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object* v_fmt_1614_, lean_object* v_a_1615_){
_start:
{
uint8_t v_fmt_boxed_1616_; lean_object* v_res_1617_; 
v_fmt_boxed_1616_ = lean_unbox(v_fmt_1614_);
v_res_1617_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_boxed_1616_, v_a_1615_);
return v_res_1617_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2(void){
_start:
{
uint8_t v___x_1620_; lean_object* v_name_1621_; lean_object* v___x_1622_; 
v___x_1620_ = 1;
v_name_1621_ = l_Lake_instDataKindFilePath;
v___x_1622_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1621_, v___x_1620_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* v_defaultPkg_1626_, lean_object* v_self_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_name_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; 
v_name_1635_ = l_Lake_instDataKindFilePath;
v___x_1636_ = 1;
lean_inc_ref_n(v_self_1627_, 2);
v___x_1637_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1626_, v_self_1627_, v_self_1627_, v___x_1636_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1679_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_a_1639_ = lean_ctor_get(v___x_1637_, 1);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1641_ = v___x_1637_;
v_isShared_1642_ = v_isSharedCheck_1679_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1679_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___y_1644_; lean_object* v_snd_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1677_; 
v_snd_1662_ = lean_ctor_get(v_a_1638_, 1);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_a_1638_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; 
v_unused_1678_ = lean_ctor_get(v_a_1638_, 0);
lean_dec(v_unused_1678_);
v___x_1664_ = v_a_1638_;
v_isShared_1665_ = v_isSharedCheck_1677_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_snd_1662_);
lean_dec(v_a_1638_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1677_;
goto v_resetjp_1663_;
}
v___jp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1645_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1646_ = l_Lake_PartialBuildKey_toString(v_self_1627_);
v___x_1647_ = lean_string_append(v___x_1645_, v___x_1646_);
lean_dec_ref(v___x_1646_);
v___x_1648_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1649_ = lean_string_append(v___x_1647_, v___x_1648_);
v___x_1650_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
v___x_1651_ = lean_string_append(v___x_1649_, v___x_1650_);
v___x_1652_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1653_ = lean_string_append(v___x_1651_, v___x_1652_);
v___x_1654_ = lean_string_append(v___x_1653_, v___y_1644_);
lean_dec_ref(v___y_1644_);
v___x_1655_ = 3;
v___x_1656_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set_uint8(v___x_1656_, sizeof(void*)*1, v___x_1655_);
v___x_1657_ = lean_array_get_size(v_a_1639_);
v___x_1658_ = lean_array_push(v_a_1639_, v___x_1656_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 1);
lean_ctor_set(v___x_1641_, 1, v___x_1658_);
lean_ctor_set(v___x_1641_, 0, v___x_1657_);
v___x_1660_ = v___x_1641_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
v_resetjp_1663_:
{
lean_object* v_kind_1666_; uint8_t v___x_1667_; 
v_kind_1666_ = lean_ctor_get(v_snd_1662_, 1);
v___x_1667_ = lean_name_eq(v_kind_1666_, v_name_1635_);
if (v___x_1667_ == 0)
{
uint8_t v___x_1668_; 
lean_inc(v_kind_1666_);
lean_del_object(v___x_1664_);
lean_dec(v_snd_1662_);
v___x_1668_ = l_Lean_Name_isAnonymous(v_kind_1666_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1669_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1670_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1666_, v___x_1636_);
v___x_1671_ = lean_string_append(v___x_1669_, v___x_1670_);
lean_dec_ref(v___x_1670_);
v___x_1672_ = lean_string_append(v___x_1671_, v___x_1669_);
v___y_1644_ = v___x_1672_;
goto v___jp_1643_;
}
else
{
lean_object* v___x_1673_; 
lean_dec(v_kind_1666_);
v___x_1673_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1644_ = v___x_1673_;
goto v___jp_1643_;
}
}
else
{
lean_object* v___x_1675_; 
lean_del_object(v___x_1641_);
lean_dec_ref(v_self_1627_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 1, v_a_1639_);
lean_ctor_set(v___x_1664_, 0, v_snd_1662_);
v___x_1675_ = v___x_1664_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_snd_1662_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_a_1639_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec_ref(v_self_1627_);
v_a_1680_ = lean_ctor_get(v___x_1637_, 0);
v_a_1681_ = lean_ctor_get(v___x_1637_, 1);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1637_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_inc(v_a_1680_);
lean_dec(v___x_1637_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1680_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* v_defaultPkg_1689_, lean_object* v_self_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1689_, v_self_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec(v_a_1693_);
lean_dec(v_a_1692_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* v___x_1699_, size_t v_sz_1700_, size_t v_i_1701_, lean_object* v_bs_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_usize_dec_lt(v_i_1701_, v_sz_1700_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_dec_ref(v___y_1703_);
lean_dec_ref(v___x_1699_);
v___x_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1711_, 0, v_bs_1702_);
lean_ctor_set(v___x_1711_, 1, v___y_1708_);
return v___x_1711_;
}
else
{
lean_object* v_v_1712_; lean_object* v___x_1713_; lean_object* v_bs_x27_1714_; lean_object* v___x_1715_; 
v_v_1712_ = lean_array_uget(v_bs_1702_, v_i_1701_);
v___x_1713_ = lean_unsigned_to_nat(0u);
v_bs_x27_1714_ = lean_array_uset(v_bs_1702_, v_i_1701_, v___x_1713_);
lean_inc_ref(v___y_1703_);
lean_inc_ref(v___x_1699_);
v___x_1715_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1699_, v_v_1712_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v_a_1717_; size_t v___x_1718_; size_t v___x_1719_; lean_object* v___x_1720_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
v_a_1717_ = lean_ctor_get(v___x_1715_, 1);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1715_, 2);
v___x_1718_ = ((size_t)1ULL);
v___x_1719_ = lean_usize_add(v_i_1701_, v___x_1718_);
v___x_1720_ = lean_array_uset(v_bs_x27_1714_, v_i_1701_, v_a_1716_);
v_i_1701_ = v___x_1719_;
v_bs_1702_ = v___x_1720_;
v___y_1708_ = v_a_1717_;
goto _start;
}
else
{
lean_object* v_a_1722_; lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref(v_bs_x27_1714_);
lean_dec_ref(v___y_1703_);
lean_dec_ref(v___x_1699_);
v_a_1722_ = lean_ctor_get(v___x_1715_, 0);
v_a_1723_ = lean_ctor_get(v___x_1715_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1715_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_inc(v_a_1722_);
lean_dec(v___x_1715_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1722_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* v___x_1731_, lean_object* v_sz_1732_, lean_object* v_i_1733_, lean_object* v_bs_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
size_t v_sz_boxed_1742_; size_t v_i_boxed_1743_; lean_object* v_res_1744_; 
v_sz_boxed_1742_ = lean_unbox_usize(v_sz_1732_);
lean_dec(v_sz_1732_);
v_i_boxed_1743_ = lean_unbox_usize(v_i_1733_);
lean_dec(v_i_1733_);
v_res_1744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1731_, v_sz_boxed_1742_, v_i_boxed_1743_, v_bs_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec(v___y_1736_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(lean_object* v_a_1745_, lean_object* v_as_1746_, size_t v_i_1747_, size_t v_stop_1748_, lean_object* v_b_1749_, lean_object* v___y_1750_){
_start:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_usize_dec_eq(v_i_1747_, v_stop_1748_);
if (v___x_1752_ == 0)
{
lean_object* v_log_1753_; uint8_t v_action_1754_; uint8_t v_wantsRebuild_1755_; uint8_t v_canceled_1756_; lean_object* v_trace_1757_; lean_object* v_buildTime_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_log_1753_ = lean_ctor_get(v___y_1750_, 0);
v_action_1754_ = lean_ctor_get_uint8(v___y_1750_, sizeof(void*)*3);
v_wantsRebuild_1755_ = lean_ctor_get_uint8(v___y_1750_, sizeof(void*)*3 + 1);
v_canceled_1756_ = lean_ctor_get_uint8(v___y_1750_, sizeof(void*)*3 + 2);
v_trace_1757_ = lean_ctor_get(v___y_1750_, 1);
v_buildTime_1758_ = lean_ctor_get(v___y_1750_, 2);
v___x_1759_ = lean_array_uget_borrowed(v_as_1746_, v_i_1747_);
v___x_1760_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
lean_inc(v___x_1759_);
v___x_1761_ = lean_string_append(v___x_1759_, v___x_1760_);
v___x_1762_ = lean_io_prim_handle_put_str(v_a_1745_, v___x_1761_);
lean_dec_ref(v___x_1761_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; size_t v___x_1764_; size_t v___x_1765_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = ((size_t)1ULL);
v___x_1765_ = lean_usize_add(v_i_1747_, v___x_1764_);
v_i_1747_ = v___x_1765_;
v_b_1749_ = v_a_1763_;
goto _start;
}
else
{
lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1780_; 
lean_inc(v_buildTime_1758_);
lean_inc_ref(v_trace_1757_);
lean_inc_ref(v_log_1753_);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___y_1750_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; lean_object* v_unused_1782_; lean_object* v_unused_1783_; 
v_unused_1781_ = lean_ctor_get(v___y_1750_, 2);
lean_dec(v_unused_1781_);
v_unused_1782_ = lean_ctor_get(v___y_1750_, 1);
lean_dec(v_unused_1782_);
v_unused_1783_ = lean_ctor_get(v___y_1750_, 0);
lean_dec(v_unused_1783_);
v___x_1768_ = v___y_1750_;
v_isShared_1769_ = v_isSharedCheck_1780_;
goto v_resetjp_1767_;
}
else
{
lean_dec(v___y_1750_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1780_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_a_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1777_; 
v_a_1770_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1771_ = lean_io_error_to_string(v_a_1770_);
v___x_1772_ = 3;
v___x_1773_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1773_, 0, v___x_1771_);
lean_ctor_set_uint8(v___x_1773_, sizeof(void*)*1, v___x_1772_);
v___x_1774_ = lean_array_get_size(v_log_1753_);
v___x_1775_ = lean_array_push(v_log_1753_, v___x_1773_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1775_);
v___x_1777_ = v___x_1768_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_trace_1757_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_buildTime_1758_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*3, v_action_1754_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*3 + 1, v_wantsRebuild_1755_);
lean_ctor_set_uint8(v_reuseFailAlloc_1779_, sizeof(void*)*3 + 2, v_canceled_1756_);
v___x_1777_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1774_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
return v___x_1778_;
}
}
}
}
else
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v_b_1749_);
lean_ctor_set(v___x_1784_, 1, v___y_1750_);
return v___x_1784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(lean_object* v_a_1785_, lean_object* v_as_1786_, lean_object* v_i_1787_, lean_object* v_stop_1788_, lean_object* v_b_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
size_t v_i_boxed_1792_; size_t v_stop_boxed_1793_; lean_object* v_res_1794_; 
v_i_boxed_1792_ = lean_unbox_usize(v_i_1787_);
lean_dec(v_i_1787_);
v_stop_boxed_1793_ = lean_unbox_usize(v_stop_1788_);
lean_dec(v_stop_1788_);
v_res_1794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1785_, v_as_1786_, v_i_boxed_1792_, v_stop_boxed_1793_, v_b_1789_, v___y_1790_);
lean_dec_ref(v_as_1786_);
lean_dec(v_a_1785_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(uint8_t v_bootstrap_1795_, lean_object* v___y_1796_, lean_object* v_oFiles_1797_, uint8_t v_shouldExport_1798_, uint8_t v___x_1799_, size_t v___x_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
if (v_bootstrap_1795_ == 0)
{
lean_object* v_toContext_1808_; lean_object* v_lakeEnv_1809_; lean_object* v_lean_1810_; lean_object* v_log_1811_; uint8_t v_action_1812_; uint8_t v_wantsRebuild_1813_; uint8_t v_canceled_1814_; lean_object* v_trace_1815_; lean_object* v_buildTime_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1846_; 
v_toContext_1808_ = lean_ctor_get(v___y_1805_, 1);
v_lakeEnv_1809_ = lean_ctor_get(v_toContext_1808_, 0);
v_lean_1810_ = lean_ctor_get(v_lakeEnv_1809_, 1);
v_log_1811_ = lean_ctor_get(v___y_1806_, 0);
v_action_1812_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3);
v_wantsRebuild_1813_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3 + 1);
v_canceled_1814_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3 + 2);
v_trace_1815_ = lean_ctor_get(v___y_1806_, 1);
v_buildTime_1816_ = lean_ctor_get(v___y_1806_, 2);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___y_1806_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1818_ = v___y_1806_;
v_isShared_1819_ = v_isSharedCheck_1846_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_buildTime_1816_);
lean_inc(v_trace_1815_);
lean_inc(v_log_1811_);
lean_dec(v___y_1806_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1846_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v_ar_1820_; lean_object* v___x_1821_; 
v_ar_1820_ = lean_ctor_get(v_lean_1810_, 13);
lean_inc_ref(v_ar_1820_);
v___x_1821_ = l_Lake_compileStaticLib(v___y_1796_, v_oFiles_1797_, v_ar_1820_, v_bootstrap_1795_, v_log_1811_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1833_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_a_1823_ = lean_ctor_get(v___x_1821_, 1);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1825_ = v___x_1821_;
v_isShared_1826_ = v_isSharedCheck_1833_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1833_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v_a_1823_);
v___x_1828_ = v___x_1818_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1823_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_trace_1815_);
lean_ctor_set(v_reuseFailAlloc_1832_, 2, v_buildTime_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1832_, sizeof(void*)*3, v_action_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1832_, sizeof(void*)*3 + 1, v_wantsRebuild_1813_);
lean_ctor_set_uint8(v_reuseFailAlloc_1832_, sizeof(void*)*3 + 2, v_canceled_1814_);
v___x_1828_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1830_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 1, v___x_1828_);
v___x_1830_ = v___x_1825_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1822_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1845_; 
v_a_1834_ = lean_ctor_get(v___x_1821_, 0);
v_a_1835_ = lean_ctor_get(v___x_1821_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1837_ = v___x_1821_;
v_isShared_1838_ = v_isSharedCheck_1845_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_inc(v_a_1834_);
lean_dec(v___x_1821_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1845_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v_a_1835_);
v___x_1840_ = v___x_1818_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1835_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_trace_1815_);
lean_ctor_set(v_reuseFailAlloc_1844_, 2, v_buildTime_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, sizeof(void*)*3, v_action_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, sizeof(void*)*3 + 1, v_wantsRebuild_1813_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, sizeof(void*)*3 + 2, v_canceled_1814_);
v___x_1840_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1842_; 
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 1, v___x_1840_);
v___x_1842_ = v___x_1837_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1834_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
}
else
{
uint8_t v___x_1847_; 
v___x_1847_ = l_System_Platform_isOSX;
if (v___x_1847_ == 0)
{
uint8_t v___x_1848_; 
v___x_1848_ = l_System_Platform_isWindows;
if (v___x_1848_ == 0)
{
lean_object* v_toContext_1849_; lean_object* v_lakeEnv_1850_; lean_object* v_lean_1851_; lean_object* v_log_1852_; uint8_t v_action_1853_; uint8_t v_wantsRebuild_1854_; uint8_t v_canceled_1855_; lean_object* v_trace_1856_; lean_object* v_buildTime_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1887_; 
v_toContext_1849_ = lean_ctor_get(v___y_1805_, 1);
v_lakeEnv_1850_ = lean_ctor_get(v_toContext_1849_, 0);
v_lean_1851_ = lean_ctor_get(v_lakeEnv_1850_, 1);
v_log_1852_ = lean_ctor_get(v___y_1806_, 0);
v_action_1853_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3);
v_wantsRebuild_1854_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3 + 1);
v_canceled_1855_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3 + 2);
v_trace_1856_ = lean_ctor_get(v___y_1806_, 1);
v_buildTime_1857_ = lean_ctor_get(v___y_1806_, 2);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___y_1806_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1859_ = v___y_1806_;
v_isShared_1860_ = v_isSharedCheck_1887_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_buildTime_1857_);
lean_inc(v_trace_1856_);
lean_inc(v_log_1852_);
lean_dec(v___y_1806_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1887_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v_ar_1861_; lean_object* v___x_1862_; 
v_ar_1861_ = lean_ctor_get(v_lean_1851_, 13);
lean_inc_ref(v_ar_1861_);
v___x_1862_ = l_Lake_compileStaticLib(v___y_1796_, v_oFiles_1797_, v_ar_1861_, v___x_1848_, v_log_1852_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1874_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
v_a_1864_ = lean_ctor_get(v___x_1862_, 1);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1866_ = v___x_1862_;
v_isShared_1867_ = v_isSharedCheck_1874_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_inc(v_a_1863_);
lean_dec(v___x_1862_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1874_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v_a_1864_);
v___x_1869_ = v___x_1859_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1864_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_trace_1856_);
lean_ctor_set(v_reuseFailAlloc_1873_, 2, v_buildTime_1857_);
lean_ctor_set_uint8(v_reuseFailAlloc_1873_, sizeof(void*)*3, v_action_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1873_, sizeof(void*)*3 + 1, v_wantsRebuild_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1873_, sizeof(void*)*3 + 2, v_canceled_1855_);
v___x_1869_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1871_; 
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 1, v___x_1869_);
v___x_1871_ = v___x_1866_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1863_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1886_; 
v_a_1875_ = lean_ctor_get(v___x_1862_, 0);
v_a_1876_ = lean_ctor_get(v___x_1862_, 1);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1878_ = v___x_1862_;
v_isShared_1879_ = v_isSharedCheck_1886_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_inc(v_a_1875_);
lean_dec(v___x_1862_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1886_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v_a_1876_);
v___x_1881_ = v___x_1859_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1876_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_trace_1856_);
lean_ctor_set(v_reuseFailAlloc_1885_, 2, v_buildTime_1857_);
lean_ctor_set_uint8(v_reuseFailAlloc_1885_, sizeof(void*)*3, v_action_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1885_, sizeof(void*)*3 + 1, v_wantsRebuild_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1885_, sizeof(void*)*3 + 2, v_canceled_1855_);
v___x_1881_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
lean_object* v___x_1883_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v___x_1881_);
v___x_1883_ = v___x_1878_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1875_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1888_; lean_object* v_lakeEnv_1889_; lean_object* v_lean_1890_; lean_object* v_log_1891_; uint8_t v_action_1892_; uint8_t v_wantsRebuild_1893_; uint8_t v_canceled_1894_; lean_object* v_trace_1895_; lean_object* v_buildTime_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1926_; 
v_toContext_1888_ = lean_ctor_get(v___y_1805_, 1);
v_lakeEnv_1889_ = lean_ctor_get(v_toContext_1888_, 0);
v_lean_1890_ = lean_ctor_get(v_lakeEnv_1889_, 1);
v_log_1891_ = lean_ctor_get(v___y_1806_, 0);
v_action_1892_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3);
v_wantsRebuild_1893_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3 + 1);
v_canceled_1894_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3 + 2);
v_trace_1895_ = lean_ctor_get(v___y_1806_, 1);
v_buildTime_1896_ = lean_ctor_get(v___y_1806_, 2);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___y_1806_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1898_ = v___y_1806_;
v_isShared_1899_ = v_isSharedCheck_1926_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_buildTime_1896_);
lean_inc(v_trace_1895_);
lean_inc(v_log_1891_);
lean_dec(v___y_1806_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1926_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v_ar_1900_; lean_object* v___x_1901_; 
v_ar_1900_ = lean_ctor_get(v_lean_1890_, 13);
lean_inc_ref(v_ar_1900_);
v___x_1901_ = l_Lake_compileStaticLib(v___y_1796_, v_oFiles_1797_, v_ar_1900_, v_shouldExport_1798_, v_log_1891_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1913_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_a_1903_ = lean_ctor_get(v___x_1901_, 1);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1905_ = v___x_1901_;
v_isShared_1906_ = v_isSharedCheck_1913_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1913_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v_a_1903_);
v___x_1908_ = v___x_1898_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1903_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_trace_1895_);
lean_ctor_set(v_reuseFailAlloc_1912_, 2, v_buildTime_1896_);
lean_ctor_set_uint8(v_reuseFailAlloc_1912_, sizeof(void*)*3, v_action_1892_);
lean_ctor_set_uint8(v_reuseFailAlloc_1912_, sizeof(void*)*3 + 1, v_wantsRebuild_1893_);
lean_ctor_set_uint8(v_reuseFailAlloc_1912_, sizeof(void*)*3 + 2, v_canceled_1894_);
v___x_1908_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1910_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 1, v___x_1908_);
v___x_1910_ = v___x_1905_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1902_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1925_; 
v_a_1914_ = lean_ctor_get(v___x_1901_, 0);
v_a_1915_ = lean_ctor_get(v___x_1901_, 1);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1917_ = v___x_1901_;
v_isShared_1918_ = v_isSharedCheck_1925_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_inc(v_a_1914_);
lean_dec(v___x_1901_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1925_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v_a_1915_);
v___x_1920_ = v___x_1898_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1915_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_trace_1895_);
lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_buildTime_1896_);
lean_ctor_set_uint8(v_reuseFailAlloc_1924_, sizeof(void*)*3, v_action_1892_);
lean_ctor_set_uint8(v_reuseFailAlloc_1924_, sizeof(void*)*3 + 1, v_wantsRebuild_1893_);
lean_ctor_set_uint8(v_reuseFailAlloc_1924_, sizeof(void*)*3 + 2, v_canceled_1894_);
v___x_1920_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1922_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 1, v___x_1920_);
v___x_1922_ = v___x_1917_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1914_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1927_; uint8_t v_action_1928_; uint8_t v_wantsRebuild_1929_; uint8_t v_canceled_1930_; lean_object* v_trace_1931_; lean_object* v_buildTime_1932_; lean_object* v___x_1933_; 
v_log_1927_ = lean_ctor_get(v___y_1806_, 0);
v_action_1928_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3);
v_wantsRebuild_1929_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3 + 1);
v_canceled_1930_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3 + 2);
v_trace_1931_ = lean_ctor_get(v___y_1806_, 1);
v_buildTime_1932_ = lean_ctor_get(v___y_1806_, 2);
lean_inc_ref(v___y_1796_);
v___x_1933_ = l_Lake_createParentDirs(v___y_1796_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v_a_1937_; uint8_t v___x_1986_; lean_object* v___x_1987_; 
lean_dec_ref_known(v___x_1933_, 1);
v___x_1934_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1796_);
v___x_1935_ = l_System_FilePath_addExtension(v___y_1796_, v___x_1934_);
v___x_1986_ = 1;
v___x_1987_ = lean_io_prim_handle_mk(v___x_1935_, v___x_1986_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = lean_array_get_size(v_oFiles_1797_);
v___x_1991_ = lean_nat_dec_lt(v___x_1989_, v___x_1990_);
if (v___x_1991_ == 0)
{
lean_dec(v_a_1988_);
lean_dec_ref(v_oFiles_1797_);
v_a_1937_ = v___y_1806_;
goto v___jp_1936_;
}
else
{
lean_object* v___x_1992_; size_t v___x_1993_; lean_object* v___x_1994_; 
v___x_1992_ = lean_box(0);
v___x_1993_ = lean_usize_of_nat(v___x_1990_);
v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1988_, v_oFiles_1797_, v___x_1800_, v___x_1993_, v___x_1992_, v___y_1806_);
lean_dec_ref(v_oFiles_1797_);
lean_dec(v_a_1988_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 1);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1994_, 2);
v_a_1937_ = v_a_1995_;
goto v___jp_1936_;
}
else
{
lean_dec_ref(v___x_1935_);
lean_dec_ref(v___y_1796_);
return v___x_1994_;
}
}
}
else
{
lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2009_; 
lean_inc(v_buildTime_1932_);
lean_inc_ref(v_trace_1931_);
lean_inc_ref(v_log_1927_);
lean_dec_ref(v___x_1935_);
lean_dec_ref(v_oFiles_1797_);
lean_dec_ref(v___y_1796_);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___y_1806_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; lean_object* v_unused_2011_; lean_object* v_unused_2012_; 
v_unused_2010_ = lean_ctor_get(v___y_1806_, 2);
lean_dec(v_unused_2010_);
v_unused_2011_ = lean_ctor_get(v___y_1806_, 1);
lean_dec(v_unused_2011_);
v_unused_2012_ = lean_ctor_get(v___y_1806_, 0);
lean_dec(v_unused_2012_);
v___x_1997_ = v___y_1806_;
v_isShared_1998_ = v_isSharedCheck_2009_;
goto v_resetjp_1996_;
}
else
{
lean_dec(v___y_1806_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2009_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_a_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v_a_1999_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1987_, 1);
v___x_2000_ = lean_io_error_to_string(v_a_1999_);
v___x_2001_ = 3;
v___x_2002_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2002_, 0, v___x_2000_);
lean_ctor_set_uint8(v___x_2002_, sizeof(void*)*1, v___x_2001_);
v___x_2003_ = lean_array_get_size(v_log_1927_);
v___x_2004_ = lean_array_push(v_log_1927_, v___x_2002_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2004_);
v___x_2006_ = v___x_1997_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_trace_1931_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_buildTime_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*3, v_action_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*3 + 1, v_wantsRebuild_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*3 + 2, v_canceled_1930_);
v___x_2006_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2003_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
return v___x_2007_;
}
}
}
v___jp_1936_:
{
lean_object* v___x_1938_; lean_object* v_log_1939_; uint8_t v_action_1940_; uint8_t v_wantsRebuild_1941_; uint8_t v_canceled_1942_; lean_object* v_trace_1943_; lean_object* v_buildTime_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1985_; 
v___x_1938_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1939_ = lean_ctor_get(v_a_1937_, 0);
v_action_1940_ = lean_ctor_get_uint8(v_a_1937_, sizeof(void*)*3);
v_wantsRebuild_1941_ = lean_ctor_get_uint8(v_a_1937_, sizeof(void*)*3 + 1);
v_canceled_1942_ = lean_ctor_get_uint8(v_a_1937_, sizeof(void*)*3 + 2);
v_trace_1943_ = lean_ctor_get(v_a_1937_, 1);
v_buildTime_1944_ = lean_ctor_get(v_a_1937_, 2);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_a_1937_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1946_ = v_a_1937_;
v_isShared_1947_ = v_isSharedCheck_1985_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_buildTime_1944_);
lean_inc(v_trace_1943_);
lean_inc(v_log_1939_);
lean_dec(v_a_1937_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1985_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1948_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1949_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1950_ = lean_unsigned_to_nat(5u);
v___x_1951_ = lean_mk_empty_array_with_capacity(v___x_1950_);
lean_dec_ref(v___x_1951_);
v___x_1952_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1953_ = lean_array_push(v___x_1952_, v___y_1796_);
v___x_1954_ = lean_array_push(v___x_1953_, v___x_1949_);
v___x_1955_ = lean_array_push(v___x_1954_, v___x_1935_);
v___x_1956_ = lean_box(0);
v___x_1957_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1958_ = 0;
v___x_1959_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1959_, 0, v___x_1938_);
lean_ctor_set(v___x_1959_, 1, v___x_1948_);
lean_ctor_set(v___x_1959_, 2, v___x_1955_);
lean_ctor_set(v___x_1959_, 3, v___x_1956_);
lean_ctor_set(v___x_1959_, 4, v___x_1957_);
lean_ctor_set_uint8(v___x_1959_, sizeof(void*)*5, v___x_1799_);
lean_ctor_set_uint8(v___x_1959_, sizeof(void*)*5 + 1, v___x_1958_);
v___x_1960_ = l_Lake_proc(v___x_1959_, v___x_1958_, v___x_1956_, v_log_1939_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1972_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_a_1962_ = lean_ctor_get(v___x_1960_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1964_ = v___x_1960_;
v_isShared_1965_ = v_isSharedCheck_1972_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1972_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v_a_1962_);
v___x_1967_ = v___x_1946_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1962_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_trace_1943_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_buildTime_1944_);
lean_ctor_set_uint8(v_reuseFailAlloc_1971_, sizeof(void*)*3, v_action_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1971_, sizeof(void*)*3 + 1, v_wantsRebuild_1941_);
lean_ctor_set_uint8(v_reuseFailAlloc_1971_, sizeof(void*)*3 + 2, v_canceled_1942_);
v___x_1967_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1969_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 1, v___x_1967_);
v___x_1969_ = v___x_1964_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1961_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1984_; 
v_a_1973_ = lean_ctor_get(v___x_1960_, 0);
v_a_1974_ = lean_ctor_get(v___x_1960_, 1);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1976_ = v___x_1960_;
v_isShared_1977_ = v_isSharedCheck_1984_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_inc(v_a_1973_);
lean_dec(v___x_1960_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1984_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v_a_1974_);
v___x_1979_ = v___x_1946_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1974_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_trace_1943_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_buildTime_1944_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*3, v_action_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*3 + 1, v_wantsRebuild_1941_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*3 + 2, v_canceled_1942_);
v___x_1979_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v___x_1979_);
v___x_1981_ = v___x_1976_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1973_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2026_; 
lean_inc(v_buildTime_1932_);
lean_inc_ref(v_trace_1931_);
lean_inc_ref(v_log_1927_);
lean_dec_ref(v_oFiles_1797_);
lean_dec_ref(v___y_1796_);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___y_1806_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; lean_object* v_unused_2028_; lean_object* v_unused_2029_; 
v_unused_2027_ = lean_ctor_get(v___y_1806_, 2);
lean_dec(v_unused_2027_);
v_unused_2028_ = lean_ctor_get(v___y_1806_, 1);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v___y_1806_, 0);
lean_dec(v_unused_2029_);
v___x_2014_ = v___y_1806_;
v_isShared_2015_ = v_isSharedCheck_2026_;
goto v_resetjp_2013_;
}
else
{
lean_dec(v___y_1806_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2026_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v_a_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
v_a_2016_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_1933_, 1);
v___x_2017_ = lean_io_error_to_string(v_a_2016_);
v___x_2018_ = 3;
v___x_2019_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2019_, 0, v___x_2017_);
lean_ctor_set_uint8(v___x_2019_, sizeof(void*)*1, v___x_2018_);
v___x_2020_ = lean_array_get_size(v_log_1927_);
v___x_2021_ = lean_array_push(v_log_1927_, v___x_2019_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2021_);
v___x_2023_ = v___x_2014_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2021_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_trace_1931_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_buildTime_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*3, v_action_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*3 + 1, v_wantsRebuild_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*3 + 2, v_canceled_1930_);
v___x_2023_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2020_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
return v___x_2024_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object* v_bootstrap_2030_, lean_object* v___y_2031_, lean_object* v_oFiles_2032_, lean_object* v_shouldExport_2033_, lean_object* v___x_2034_, lean_object* v___x_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
uint8_t v_bootstrap_boxed_2043_; uint8_t v_shouldExport_boxed_2044_; uint8_t v___x_5831__boxed_2045_; size_t v___x_5832__boxed_2046_; lean_object* v_res_2047_; 
v_bootstrap_boxed_2043_ = lean_unbox(v_bootstrap_2030_);
v_shouldExport_boxed_2044_ = lean_unbox(v_shouldExport_2033_);
v___x_5831__boxed_2045_ = lean_unbox(v___x_2034_);
v___x_5832__boxed_2046_ = lean_unbox_usize(v___x_2035_);
lean_dec(v___x_2035_);
v_res_2047_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_boxed_2043_, v___y_2031_, v_oFiles_2032_, v_shouldExport_boxed_2044_, v___x_5831__boxed_2045_, v___x_5832__boxed_2046_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t v_bootstrap_2048_, lean_object* v___y_2049_, uint8_t v_shouldExport_2050_, uint8_t v___x_2051_, size_t v___x_2052_, lean_object* v_oFiles_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___y_2065_; uint8_t v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2061_ = lean_box(v_bootstrap_2048_);
v___x_2062_ = lean_box(v_shouldExport_2050_);
v___x_2063_ = lean_box(v___x_2051_);
v___x_2064_ = lean_box_usize(v___x_2052_);
lean_inc_ref(v___y_2049_);
v___y_2065_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed), 13, 6);
lean_closure_set(v___y_2065_, 0, v___x_2061_);
lean_closure_set(v___y_2065_, 1, v___y_2049_);
lean_closure_set(v___y_2065_, 2, v_oFiles_2053_);
lean_closure_set(v___y_2065_, 3, v___x_2062_);
lean_closure_set(v___y_2065_, 4, v___x_2063_);
lean_closure_set(v___y_2065_, 5, v___x_2064_);
v___x_2066_ = 0;
v___x_2067_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_2068_ = l_Lake_buildArtifactUnlessUpToDate(v___y_2049_, v___y_2065_, v___x_2066_, v___x_2067_, v___x_2051_, v___x_2066_, v___x_2066_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2078_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_a_2070_ = lean_ctor_get(v___x_2068_, 1);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2072_ = v___x_2068_;
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v_path_2074_; lean_object* v___x_2076_; 
v_path_2074_ = lean_ctor_get(v_a_2069_, 1);
lean_inc_ref(v_path_2074_);
lean_dec(v_a_2069_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v_path_2074_);
v___x_2076_ = v___x_2072_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_path_2074_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_a_2070_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_a_2079_ = lean_ctor_get(v___x_2068_, 0);
v_a_2080_ = lean_ctor_get(v___x_2068_, 1);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2068_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_inc(v_a_2079_);
lean_dec(v___x_2068_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2079_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* v_bootstrap_2088_, lean_object* v___y_2089_, lean_object* v_shouldExport_2090_, lean_object* v___x_2091_, lean_object* v___x_2092_, lean_object* v_oFiles_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
uint8_t v_bootstrap_boxed_2101_; uint8_t v_shouldExport_boxed_2102_; uint8_t v___x_6231__boxed_2103_; size_t v___x_6232__boxed_2104_; lean_object* v_res_2105_; 
v_bootstrap_boxed_2101_ = lean_unbox(v_bootstrap_2088_);
v_shouldExport_boxed_2102_ = lean_unbox(v_shouldExport_2090_);
v___x_6231__boxed_2103_ = lean_unbox(v___x_2091_);
v___x_6232__boxed_2104_ = lean_unbox_usize(v___x_2092_);
lean_dec(v___x_2092_);
v_res_2105_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_boxed_2101_, v___y_2089_, v_shouldExport_boxed_2102_, v___x_6231__boxed_2103_, v___x_6232__boxed_2104_, v_oFiles_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec(v___y_2095_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* v_a_2106_, size_t v_sz_2107_, size_t v_i_2108_, lean_object* v_bs_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
uint8_t v___x_2117_; 
v___x_2117_ = lean_usize_dec_lt(v_i_2108_, v_sz_2107_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; 
lean_dec_ref(v___y_2110_);
lean_dec_ref(v_a_2106_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v_bs_2109_);
lean_ctor_set(v___x_2118_, 1, v___y_2115_);
return v___x_2118_;
}
else
{
lean_object* v_v_2119_; lean_object* v___x_2120_; lean_object* v_bs_x27_2121_; lean_object* v___x_2122_; 
v_v_2119_ = lean_array_uget(v_bs_2109_, v_i_2108_);
v___x_2120_ = lean_unsigned_to_nat(0u);
v_bs_x27_2121_ = lean_array_uset(v_bs_2109_, v_i_2108_, v___x_2120_);
lean_inc_ref(v___y_2110_);
lean_inc_ref(v_a_2106_);
v___x_2122_ = l_Lake_ModuleFacet_fetch___redArg(v_v_2119_, v_a_2106_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v_a_2124_; size_t v___x_2125_; size_t v___x_2126_; lean_object* v___x_2127_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
v_a_2124_ = lean_ctor_get(v___x_2122_, 1);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2122_, 2);
v___x_2125_ = ((size_t)1ULL);
v___x_2126_ = lean_usize_add(v_i_2108_, v___x_2125_);
v___x_2127_ = lean_array_uset(v_bs_x27_2121_, v_i_2108_, v_a_2123_);
v_i_2108_ = v___x_2126_;
v_bs_2109_ = v___x_2127_;
v___y_2115_ = v_a_2124_;
goto _start;
}
else
{
lean_object* v_a_2129_; lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec_ref(v_bs_x27_2121_);
lean_dec_ref(v___y_2110_);
lean_dec_ref(v_a_2106_);
v_a_2129_ = lean_ctor_get(v___x_2122_, 0);
v_a_2130_ = lean_ctor_get(v___x_2122_, 1);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2122_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_inc(v_a_2129_);
lean_dec(v___x_2122_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2129_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object* v_a_2138_, lean_object* v_sz_2139_, lean_object* v_i_2140_, lean_object* v_bs_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
size_t v_sz_boxed_2149_; size_t v_i_boxed_2150_; lean_object* v_res_2151_; 
v_sz_boxed_2149_ = lean_unbox_usize(v_sz_2139_);
lean_dec(v_sz_2139_);
v_i_boxed_2150_ = lean_unbox_usize(v_i_2140_);
lean_dec(v_i_2140_);
v_res_2151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_2138_, v_sz_boxed_2149_, v_i_boxed_2150_, v_bs_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec(v___y_2143_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(uint8_t v_shouldExport_2152_, lean_object* v_as_2153_, size_t v_i_2154_, size_t v_stop_2155_, lean_object* v_b_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
uint8_t v___x_2164_; 
v___x_2164_ = lean_usize_dec_eq(v_i_2154_, v_stop_2155_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v_lib_2166_; lean_object* v_config_2167_; lean_object* v_nativeFacets_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; size_t v_sz_2171_; size_t v___x_2172_; lean_object* v___x_2173_; 
v___x_2165_ = lean_array_uget_borrowed(v_as_2153_, v_i_2154_);
v_lib_2166_ = lean_ctor_get(v___x_2165_, 0);
v_config_2167_ = lean_ctor_get(v_lib_2166_, 2);
v_nativeFacets_2168_ = lean_ctor_get(v_config_2167_, 8);
v___x_2169_ = lean_box(v_shouldExport_2152_);
lean_inc_ref(v_nativeFacets_2168_);
v___x_2170_ = lean_apply_1(v_nativeFacets_2168_, v___x_2169_);
v_sz_2171_ = lean_array_size(v___x_2170_);
v___x_2172_ = ((size_t)0ULL);
lean_inc_ref(v___y_2157_);
lean_inc(v___x_2165_);
v___x_2173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2165_, v_sz_2171_, v___x_2172_, v___x_2170_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v_a_2175_; lean_object* v___x_2176_; size_t v___x_2177_; size_t v___x_2178_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
v_a_2175_ = lean_ctor_get(v___x_2173_, 1);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2173_, 2);
v___x_2176_ = l_Array_append___redArg(v_b_2156_, v_a_2174_);
lean_dec(v_a_2174_);
v___x_2177_ = ((size_t)1ULL);
v___x_2178_ = lean_usize_add(v_i_2154_, v___x_2177_);
v_i_2154_ = v___x_2178_;
v_b_2156_ = v___x_2176_;
v___y_2162_ = v_a_2175_;
goto _start;
}
else
{
lean_dec_ref(v___y_2157_);
lean_dec_ref(v_b_2156_);
return v___x_2173_;
}
}
else
{
lean_object* v___x_2180_; 
lean_dec_ref(v___y_2157_);
v___x_2180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2180_, 0, v_b_2156_);
lean_ctor_set(v___x_2180_, 1, v___y_2162_);
return v___x_2180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(lean_object* v_shouldExport_2181_, lean_object* v_as_2182_, lean_object* v_i_2183_, lean_object* v_stop_2184_, lean_object* v_b_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
uint8_t v_shouldExport_boxed_2193_; size_t v_i_boxed_2194_; size_t v_stop_boxed_2195_; lean_object* v_res_2196_; 
v_shouldExport_boxed_2193_ = lean_unbox(v_shouldExport_2181_);
v_i_boxed_2194_ = lean_unbox_usize(v_i_2183_);
lean_dec(v_i_2183_);
v_stop_boxed_2195_ = lean_unbox_usize(v_stop_2184_);
lean_dec(v_stop_2184_);
v_res_2196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_boxed_2193_, v_as_2182_, v_i_boxed_2194_, v_stop_boxed_2195_, v_b_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v_as_2182_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object* v_config_2197_, lean_object* v_config_2198_, uint8_t v_shouldExport_2199_, uint8_t v___x_2200_, lean_object* v___x_2201_, lean_object* v___x_2202_, lean_object* v_pkg_2203_, lean_object* v_dir_2204_, lean_object* v_self_2205_, lean_object* v___x_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
uint8_t v___y_2215_; size_t v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v_a_2235_; lean_object* v_a_2236_; lean_object* v___x_2278_; 
lean_inc_ref(v___y_2207_);
lean_inc_ref(v___y_2211_);
lean_inc(v___y_2210_);
lean_inc(v___y_2209_);
lean_inc(v___x_2202_);
v___x_2278_ = lean_apply_7(v___y_2207_, v___x_2206_, v___x_2202_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, lean_box(0));
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v_a_2280_; lean_object* v___x_2281_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
v_a_2280_ = lean_ctor_get(v___x_2278_, 1);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2278_, 2);
v___x_2281_ = l_Lake_Job_await___redArg(v_a_2279_, v_a_2280_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v_a_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
v_a_2283_ = lean_ctor_get(v___x_2281_, 1);
lean_inc(v_a_2283_);
lean_dec_ref_known(v___x_2281_, 2);
v___x_2284_ = lean_unsigned_to_nat(0u);
v___x_2285_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_2286_ = lean_array_get_size(v_a_2282_);
v___x_2287_ = lean_nat_dec_lt(v___x_2284_, v___x_2286_);
if (v___x_2287_ == 0)
{
lean_dec(v_a_2282_);
v_a_2235_ = v___x_2285_;
v_a_2236_ = v_a_2283_;
goto v___jp_2234_;
}
else
{
size_t v___x_2288_; size_t v___x_2289_; lean_object* v___x_2290_; 
v___x_2288_ = ((size_t)0ULL);
v___x_2289_ = lean_usize_of_nat(v___x_2286_);
lean_inc_ref(v___y_2207_);
v___x_2290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2199_, v_a_2282_, v___x_2288_, v___x_2289_, v___x_2285_, v___y_2207_, v___x_2202_, v___y_2209_, v___y_2210_, v___y_2211_, v_a_2283_);
lean_dec(v_a_2282_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v_a_2292_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
v_a_2292_ = lean_ctor_get(v___x_2290_, 1);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2290_, 2);
v_a_2235_ = v_a_2291_;
v_a_2236_ = v_a_2292_;
goto v___jp_2234_;
}
else
{
lean_object* v_a_2293_; lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec_ref(v___y_2207_);
lean_dec_ref(v_self_2205_);
lean_dec_ref(v_dir_2204_);
lean_dec_ref(v_pkg_2203_);
lean_dec(v___x_2202_);
lean_dec(v___x_2201_);
lean_dec_ref(v_config_2197_);
v_a_2293_ = lean_ctor_get(v___x_2290_, 0);
v_a_2294_ = lean_ctor_get(v___x_2290_, 1);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2290_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_inc(v_a_2293_);
lean_dec(v___x_2290_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2293_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
else
{
lean_object* v_a_2302_; lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec_ref(v___y_2207_);
lean_dec_ref(v_self_2205_);
lean_dec_ref(v_dir_2204_);
lean_dec_ref(v_pkg_2203_);
lean_dec(v___x_2202_);
lean_dec(v___x_2201_);
lean_dec_ref(v_config_2197_);
v_a_2302_ = lean_ctor_get(v___x_2281_, 0);
v_a_2303_ = lean_ctor_get(v___x_2281_, 1);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2281_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_inc(v_a_2302_);
lean_dec(v___x_2281_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2302_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v___y_2207_);
lean_dec_ref(v_self_2205_);
lean_dec_ref(v_dir_2204_);
lean_dec_ref(v_pkg_2203_);
lean_dec(v___x_2202_);
lean_dec(v___x_2201_);
lean_dec_ref(v_config_2197_);
v_a_2311_ = lean_ctor_get(v___x_2278_, 0);
v_a_2312_ = lean_ctor_get(v___x_2278_, 1);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2278_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_inc(v_a_2311_);
lean_dec(v___x_2278_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2311_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
v___jp_2214_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___f_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2221_ = lean_box(v___y_2215_);
v___x_2222_ = lean_box(v_shouldExport_2199_);
v___x_2223_ = lean_box(v___x_2200_);
v___x_2224_ = lean_box_usize(v___y_2216_);
v___f_2225_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2225_, 0, v___x_2221_);
lean_closure_set(v___f_2225_, 1, v___y_2220_);
lean_closure_set(v___f_2225_, 2, v___x_2222_);
lean_closure_set(v___f_2225_, 3, v___x_2223_);
lean_closure_set(v___f_2225_, 4, v___x_2224_);
v___x_2226_ = l_Array_append___redArg(v___y_2217_, v___y_2218_);
lean_dec_ref(v___y_2218_);
v___x_2227_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_2228_ = l_Lake_Job_collectArray___redArg(v___x_2226_, v___x_2227_);
lean_dec_ref(v___x_2226_);
v___x_2229_ = lean_unsigned_to_nat(0u);
v___x_2230_ = 0;
v___x_2231_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_2232_ = l_Lake_Job_mapM___redArg(v___x_2201_, v___x_2228_, v___f_2225_, v___x_2229_, v___x_2230_, v___y_2207_, v___x_2202_, v___y_2209_, v___y_2210_, v___y_2211_, v___x_2231_);
lean_dec(v___x_2202_);
v___x_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
lean_ctor_set(v___x_2233_, 1, v___y_2219_);
return v___x_2233_;
}
v___jp_2234_:
{
lean_object* v_toLeanConfig_2237_; lean_object* v_toLeanConfig_2238_; uint8_t v_bootstrap_2239_; lean_object* v_buildDir_2240_; lean_object* v_nativeLibDir_2241_; lean_object* v_moreLinkObjs_2242_; lean_object* v_moreLinkObjs_2243_; lean_object* v___x_2244_; size_t v_sz_2245_; size_t v___x_2246_; lean_object* v___x_2247_; 
v_toLeanConfig_2237_ = lean_ctor_get(v_config_2197_, 1);
lean_inc_ref(v_toLeanConfig_2237_);
v_toLeanConfig_2238_ = lean_ctor_get(v_config_2198_, 0);
v_bootstrap_2239_ = lean_ctor_get_uint8(v_config_2197_, sizeof(void*)*28);
v_buildDir_2240_ = lean_ctor_get(v_config_2197_, 5);
lean_inc_ref(v_buildDir_2240_);
v_nativeLibDir_2241_ = lean_ctor_get(v_config_2197_, 7);
lean_inc_ref(v_nativeLibDir_2241_);
lean_dec_ref(v_config_2197_);
v_moreLinkObjs_2242_ = lean_ctor_get(v_toLeanConfig_2237_, 6);
lean_inc_ref(v_moreLinkObjs_2242_);
lean_dec_ref(v_toLeanConfig_2237_);
v_moreLinkObjs_2243_ = lean_ctor_get(v_toLeanConfig_2238_, 6);
v___x_2244_ = l_Array_append___redArg(v_moreLinkObjs_2242_, v_moreLinkObjs_2243_);
v_sz_2245_ = lean_array_size(v___x_2244_);
v___x_2246_ = ((size_t)0ULL);
lean_inc_ref(v___y_2207_);
v___x_2247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_2203_, v_sz_2245_, v___x_2246_, v___x_2244_, v___y_2207_, v___x_2202_, v___y_2209_, v___y_2210_, v___y_2211_, v_a_2236_);
if (lean_obj_tag(v___x_2247_) == 0)
{
if (v_shouldExport_2199_ == 0)
{
lean_object* v_a_2248_; lean_object* v_a_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2248_);
v_a_2249_ = lean_ctor_get(v___x_2247_, 1);
lean_inc(v_a_2249_);
lean_dec_ref_known(v___x_2247_, 2);
v___x_2250_ = l_System_FilePath_normalize(v_buildDir_2240_);
v___x_2251_ = l_Lake_joinRelative(v_dir_2204_, v___x_2250_);
v___x_2252_ = l_System_FilePath_normalize(v_nativeLibDir_2241_);
v___x_2253_ = l_Lake_joinRelative(v___x_2251_, v___x_2252_);
v___x_2254_ = l_Lake_LeanLib_libName(v_self_2205_);
v___x_2255_ = l_Lake_nameToStaticLib(v___x_2254_, v_shouldExport_2199_);
v___x_2256_ = l_Lake_joinRelative(v___x_2253_, v___x_2255_);
v___y_2215_ = v_bootstrap_2239_;
v___y_2216_ = v___x_2246_;
v___y_2217_ = v_a_2235_;
v___y_2218_ = v_a_2248_;
v___y_2219_ = v_a_2249_;
v___y_2220_ = v___x_2256_;
goto v___jp_2214_;
}
else
{
lean_object* v_a_2257_; lean_object* v_a_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v_a_2257_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2257_);
v_a_2258_ = lean_ctor_get(v___x_2247_, 1);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2247_, 2);
v___x_2259_ = l_System_FilePath_normalize(v_buildDir_2240_);
v___x_2260_ = l_Lake_joinRelative(v_dir_2204_, v___x_2259_);
v___x_2261_ = l_System_FilePath_normalize(v_nativeLibDir_2241_);
v___x_2262_ = l_Lake_joinRelative(v___x_2260_, v___x_2261_);
v___x_2263_ = l_Lake_LeanLib_libName(v_self_2205_);
v___x_2264_ = 0;
v___x_2265_ = l_Lake_nameToStaticLib(v___x_2263_, v___x_2264_);
v___x_2266_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_2267_ = l_System_FilePath_addExtension(v___x_2265_, v___x_2266_);
v___x_2268_ = l_Lake_joinRelative(v___x_2262_, v___x_2267_);
v___y_2215_ = v_bootstrap_2239_;
v___y_2216_ = v___x_2246_;
v___y_2217_ = v_a_2235_;
v___y_2218_ = v_a_2257_;
v___y_2219_ = v_a_2258_;
v___y_2220_ = v___x_2268_;
goto v___jp_2214_;
}
}
else
{
lean_object* v_a_2269_; lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec_ref(v_nativeLibDir_2241_);
lean_dec_ref(v_buildDir_2240_);
lean_dec_ref(v_a_2235_);
lean_dec_ref(v___y_2207_);
lean_dec_ref(v_self_2205_);
lean_dec_ref(v_dir_2204_);
lean_dec(v___x_2202_);
lean_dec(v___x_2201_);
v_a_2269_ = lean_ctor_get(v___x_2247_, 0);
v_a_2270_ = lean_ctor_get(v___x_2247_, 1);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2247_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_inc(v_a_2269_);
lean_dec(v___x_2247_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2269_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(lean_object** _args){
lean_object* v_config_2320_ = _args[0];
lean_object* v_config_2321_ = _args[1];
lean_object* v_shouldExport_2322_ = _args[2];
lean_object* v___x_2323_ = _args[3];
lean_object* v___x_2324_ = _args[4];
lean_object* v___x_2325_ = _args[5];
lean_object* v_pkg_2326_ = _args[6];
lean_object* v_dir_2327_ = _args[7];
lean_object* v_self_2328_ = _args[8];
lean_object* v___x_2329_ = _args[9];
lean_object* v___y_2330_ = _args[10];
lean_object* v___y_2331_ = _args[11];
lean_object* v___y_2332_ = _args[12];
lean_object* v___y_2333_ = _args[13];
lean_object* v___y_2334_ = _args[14];
lean_object* v___y_2335_ = _args[15];
lean_object* v___y_2336_ = _args[16];
_start:
{
uint8_t v_shouldExport_boxed_2337_; uint8_t v___x_6429__boxed_2338_; lean_object* v_res_2339_; 
v_shouldExport_boxed_2337_ = lean_unbox(v_shouldExport_2322_);
v___x_6429__boxed_2338_ = lean_unbox(v___x_2323_);
v_res_2339_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v_config_2320_, v_config_2321_, v_shouldExport_boxed_2337_, v___x_6429__boxed_2338_, v___x_2324_, v___x_2325_, v_pkg_2326_, v_dir_2327_, v_self_2328_, v___x_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec(v_config_2321_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object* v___y_2340_, lean_object* v_self_2341_, uint8_t v_shouldExport_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v_toBuildConfig_2349_; lean_object* v_registeredJobs_2350_; uint8_t v_verbosity_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; uint8_t v___x_2357_; lean_object* v___y_2359_; 
v_toBuildConfig_2349_ = lean_ctor_get(v_a_2346_, 0);
v_registeredJobs_2350_ = lean_ctor_get(v_a_2346_, 4);
v_verbosity_2351_ = lean_ctor_get_uint8(v_toBuildConfig_2349_, sizeof(void*)*5 + 4);
v___x_2352_ = l_Lake_instDataKindFilePath;
v___x_2353_ = lean_box(v_verbosity_2351_);
v___x_2354_ = lean_obj_tag_nat(v___x_2353_);
lean_dec(v___x_2353_);
v___x_2355_ = lean_unsigned_to_nat(2u);
v___x_2356_ = lean_nat_dec_eq(v___x_2354_, v___x_2355_);
v___x_2357_ = 1;
if (v___x_2356_ == 0)
{
lean_object* v___x_2404_; 
v___x_2404_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_2359_ = v___x_2404_;
goto v___jp_2358_;
}
else
{
if (v_shouldExport_2342_ == 0)
{
lean_object* v___x_2405_; 
v___x_2405_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___y_2359_ = v___x_2405_;
goto v___jp_2358_;
}
else
{
lean_object* v___x_2406_; 
v___x_2406_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_2359_ = v___x_2406_;
goto v___jp_2358_;
}
}
v___jp_2358_:
{
lean_object* v_pkg_2360_; lean_object* v_name_2361_; lean_object* v_config_2362_; lean_object* v_keyName_2363_; lean_object* v_dir_2364_; lean_object* v_config_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___f_2377_; uint8_t v___x_2378_; lean_object* v___x_2379_; 
v_pkg_2360_ = lean_ctor_get(v_self_2341_, 0);
lean_inc_ref_n(v_pkg_2360_, 2);
v_name_2361_ = lean_ctor_get(v_self_2341_, 1);
v_config_2362_ = lean_ctor_get(v_self_2341_, 2);
lean_inc(v_config_2362_);
v_keyName_2363_ = lean_ctor_get(v_pkg_2360_, 2);
v_dir_2364_ = lean_ctor_get(v_pkg_2360_, 4);
lean_inc_ref(v_dir_2364_);
v_config_2365_ = lean_ctor_get(v_pkg_2360_, 6);
lean_inc_ref(v_config_2365_);
lean_inc_n(v_name_2361_, 2);
v___x_2366_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2361_, v___x_2357_);
v___x_2367_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0));
v___x_2368_ = lean_string_append(v___x_2366_, v___x_2367_);
v___x_2369_ = lean_string_append(v___x_2368_, v___y_2359_);
v___x_2370_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_2363_);
v___x_2371_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2371_, 0, v_keyName_2363_);
lean_ctor_set(v___x_2371_, 1, v_name_2361_);
v___x_2372_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_2341_);
v___x_2373_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
lean_ctor_set(v___x_2373_, 2, v_self_2341_);
lean_ctor_set(v___x_2373_, 3, v___x_2370_);
v___x_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2374_, 0, v_pkg_2360_);
v___x_2375_ = lean_box(v_shouldExport_2342_);
v___x_2376_ = lean_box(v___x_2357_);
v___f_2377_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed), 17, 10);
lean_closure_set(v___f_2377_, 0, v_config_2365_);
lean_closure_set(v___f_2377_, 1, v_config_2362_);
lean_closure_set(v___f_2377_, 2, v___x_2375_);
lean_closure_set(v___f_2377_, 3, v___x_2376_);
lean_closure_set(v___f_2377_, 4, v___x_2352_);
lean_closure_set(v___f_2377_, 5, v___x_2374_);
lean_closure_set(v___f_2377_, 6, v_pkg_2360_);
lean_closure_set(v___f_2377_, 7, v_dir_2364_);
lean_closure_set(v___f_2377_, 8, v_self_2341_);
lean_closure_set(v___f_2377_, 9, v___x_2373_);
v___x_2378_ = 0;
v___x_2379_ = l_Lake_ensureJob___redArg(v___x_2352_, v___f_2377_, v___y_2340_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2403_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_a_2381_ = lean_ctor_get(v___x_2379_, 1);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2383_ = v___x_2379_;
v_isShared_2384_ = v_isSharedCheck_2403_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2403_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v_task_2385_; lean_object* v_kind_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2401_; 
v_task_2385_ = lean_ctor_get(v_a_2380_, 0);
v_kind_2386_ = lean_ctor_get(v_a_2380_, 1);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_a_2380_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; 
v_unused_2402_ = lean_ctor_get(v_a_2380_, 2);
lean_dec(v_unused_2402_);
v___x_2388_ = v_a_2380_;
v_isShared_2389_ = v_isSharedCheck_2401_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_kind_2386_);
lean_inc(v_task_2385_);
lean_dec(v_a_2380_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2401_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v_job_2391_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 2, v___x_2369_);
v_job_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_task_2385_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_kind_2386_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v___x_2369_);
v_job_2391_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2398_; 
lean_ctor_set_uint8(v_job_2391_, sizeof(void*)*3, v___x_2378_);
v___x_2392_ = lean_st_ref_take(v_registeredJobs_2350_);
lean_inc_ref(v_job_2391_);
v___x_2393_ = l_Lake_Job_toOpaque___redArg(v_job_2391_);
v___x_2394_ = lean_array_push(v___x_2392_, v___x_2393_);
v___x_2395_ = lean_st_ref_put(v_registeredJobs_2350_, v___x_2394_);
v___x_2396_ = l_Lake_Job_renew___redArg(v_job_2391_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2396_);
v___x_2398_ = v___x_2383_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2396_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_a_2381_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2369_);
return v___x_2379_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* v___y_2407_, lean_object* v_self_2408_, lean_object* v_shouldExport_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
uint8_t v_shouldExport_boxed_2416_; lean_object* v_res_2417_; 
v_shouldExport_boxed_2416_ = lean_unbox(v_shouldExport_2409_);
v_res_2417_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2407_, v_self_2408_, v_shouldExport_boxed_2416_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec(v_a_2411_);
lean_dec(v_a_2410_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* v_x_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
uint8_t v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = 0;
v___x_2427_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2419_, v_x_2418_, v___x_2426_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object* v_x_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec(v___y_2430_);
return v_res_2436_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2439_; uint8_t v___x_2440_; lean_object* v___x_2441_; lean_object* v___f_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___f_2439_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2440_ = 1;
v___x_2441_ = l_Lake_instDataKindFilePath;
v___f_2442_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__0));
v___x_2443_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2444_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set(v___x_2444_, 1, v___f_2442_);
lean_ctor_set(v___x_2444_, 2, v___x_2441_);
lean_ctor_set(v___x_2444_, 3, v___f_2439_);
lean_ctor_set_uint8(v___x_2444_, sizeof(void*)*4, v___x_2440_);
lean_ctor_set_uint8(v___x_2444_, sizeof(void*)*4 + 1, v___x_2440_);
return v___x_2444_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = lean_obj_once(&l_Lake_LeanLib_staticFacetConfig___closed__2, &l_Lake_LeanLib_staticFacetConfig___closed__2_once, _init_l_Lake_LeanLib_staticFacetConfig___closed__2);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(lean_object* v_a_2446_, lean_object* v_as_2447_, size_t v_i_2448_, size_t v_stop_2449_, lean_object* v_b_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2446_, v_as_2447_, v_i_2448_, v_stop_2449_, v_b_2450_, v___y_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* v_a_2459_, lean_object* v_as_2460_, lean_object* v_i_2461_, lean_object* v_stop_2462_, lean_object* v_b_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
size_t v_i_boxed_2471_; size_t v_stop_boxed_2472_; lean_object* v_res_2473_; 
v_i_boxed_2471_ = lean_unbox_usize(v_i_2461_);
lean_dec(v_i_2461_);
v_stop_boxed_2472_ = lean_unbox_usize(v_stop_2462_);
lean_dec(v_stop_2462_);
v_res_2473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_2459_, v_as_2460_, v_i_boxed_2471_, v_stop_boxed_2472_, v_b_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec_ref(v_as_2460_);
lean_dec(v_a_2459_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* v_x_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = 1;
v___x_2483_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2475_, v_x_2474_, v___x_2482_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object* v_x_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec(v___y_2486_);
return v_res_2492_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2494_; uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___f_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___f_2494_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2495_ = 1;
v___x_2496_ = l_Lake_instDataKindFilePath;
v___f_2497_ = ((lean_object*)(l_Lake_LeanLib_staticExportFacetConfig___closed__0));
v___x_2498_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2499_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v___f_2497_);
lean_ctor_set(v___x_2499_, 2, v___x_2496_);
lean_ctor_set(v___x_2499_, 3, v___f_2494_);
lean_ctor_set_uint8(v___x_2499_, sizeof(void*)*4, v___x_2495_);
lean_ctor_set_uint8(v___x_2499_, sizeof(void*)*4 + 1, v___x_2495_);
return v___x_2499_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig(void){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_obj_once(&l_Lake_LeanLib_staticExportFacetConfig___closed__1, &l_Lake_LeanLib_staticExportFacetConfig___closed__1_once, _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1);
return v___x_2500_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0(void){
_start:
{
uint8_t v___x_2501_; lean_object* v_name_2502_; lean_object* v___x_2503_; 
v___x_2501_ = 1;
v_name_2502_ = l_Lake_instDataKindDynlib;
v___x_2503_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2502_, v___x_2501_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object* v_defaultPkg_2504_, lean_object* v_self_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_name_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; 
v_name_2513_ = l_Lake_instDataKindDynlib;
v___x_2514_ = 1;
lean_inc_ref_n(v_self_2505_, 2);
v___x_2515_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_2504_, v_self_2505_, v_self_2505_, v___x_2514_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2557_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_a_2517_ = lean_ctor_get(v___x_2515_, 1);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2519_ = v___x_2515_;
v_isShared_2520_ = v_isSharedCheck_2557_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2557_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___y_2522_; lean_object* v_snd_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2555_; 
v_snd_2540_ = lean_ctor_get(v_a_2516_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_a_2516_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; 
v_unused_2556_ = lean_ctor_get(v_a_2516_, 0);
lean_dec(v_unused_2556_);
v___x_2542_ = v_a_2516_;
v_isShared_2543_ = v_isSharedCheck_2555_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_snd_2540_);
lean_dec(v_a_2516_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2555_;
goto v_resetjp_2541_;
}
v___jp_2521_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2538_; 
v___x_2523_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_2524_ = l_Lake_PartialBuildKey_toString(v_self_2505_);
v___x_2525_ = lean_string_append(v___x_2523_, v___x_2524_);
lean_dec_ref(v___x_2524_);
v___x_2526_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_2527_ = lean_string_append(v___x_2525_, v___x_2526_);
v___x_2528_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0);
v___x_2529_ = lean_string_append(v___x_2527_, v___x_2528_);
v___x_2530_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_2531_ = lean_string_append(v___x_2529_, v___x_2530_);
v___x_2532_ = lean_string_append(v___x_2531_, v___y_2522_);
lean_dec_ref(v___y_2522_);
v___x_2533_ = 3;
v___x_2534_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2534_, 0, v___x_2532_);
lean_ctor_set_uint8(v___x_2534_, sizeof(void*)*1, v___x_2533_);
v___x_2535_ = lean_array_get_size(v_a_2517_);
v___x_2536_ = lean_array_push(v_a_2517_, v___x_2534_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set_tag(v___x_2519_, 1);
lean_ctor_set(v___x_2519_, 1, v___x_2536_);
lean_ctor_set(v___x_2519_, 0, v___x_2535_);
v___x_2538_ = v___x_2519_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
v_resetjp_2541_:
{
lean_object* v_kind_2544_; uint8_t v___x_2545_; 
v_kind_2544_ = lean_ctor_get(v_snd_2540_, 1);
v___x_2545_ = lean_name_eq(v_kind_2544_, v_name_2513_);
if (v___x_2545_ == 0)
{
uint8_t v___x_2546_; 
lean_inc(v_kind_2544_);
lean_del_object(v___x_2542_);
lean_dec(v_snd_2540_);
v___x_2546_ = l_Lean_Name_isAnonymous(v_kind_2544_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2547_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_2548_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2544_, v___x_2514_);
v___x_2549_ = lean_string_append(v___x_2547_, v___x_2548_);
lean_dec_ref(v___x_2548_);
v___x_2550_ = lean_string_append(v___x_2549_, v___x_2547_);
v___y_2522_ = v___x_2550_;
goto v___jp_2521_;
}
else
{
lean_object* v___x_2551_; 
lean_dec(v_kind_2544_);
v___x_2551_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_2522_ = v___x_2551_;
goto v___jp_2521_;
}
}
else
{
lean_object* v___x_2553_; 
lean_del_object(v___x_2519_);
lean_dec_ref(v_self_2505_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 1, v_a_2517_);
lean_ctor_set(v___x_2542_, 0, v_snd_2540_);
v___x_2553_ = v___x_2542_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_snd_2540_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_a_2517_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
}
else
{
lean_object* v_a_2558_; lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v_self_2505_);
v_a_2558_ = lean_ctor_get(v___x_2515_, 0);
v_a_2559_ = lean_ctor_get(v___x_2515_, 1);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2515_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_inc(v_a_2558_);
lean_dec(v___x_2515_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2558_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* v_defaultPkg_2567_, lean_object* v_self_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_2567_, v_self_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_);
lean_dec_ref(v_a_2573_);
lean_dec(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec(v_a_2570_);
return v_res_2576_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2579_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0));
v___x_2580_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
lean_ctor_set(v___x_2581_, 1, v___x_2579_);
return v___x_2581_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5(void){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object* v___x_2583_, lean_object* v_as_2584_, size_t v_i_2585_, size_t v_stop_2586_, lean_object* v_b_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
uint8_t v___x_2595_; 
v___x_2595_ = lean_usize_dec_eq(v_i_2585_, v_stop_2586_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_array_uget_borrowed(v_as_2584_, v_i_2585_);
lean_inc_ref(v___y_2588_);
lean_inc(v___x_2596_);
lean_inc_ref(v___x_2583_);
v___x_2597_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_2583_, v___x_2596_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v_a_2599_; lean_object* v___x_2600_; size_t v___x_2601_; size_t v___x_2602_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
v_a_2599_ = lean_ctor_get(v___x_2597_, 1);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2597_, 2);
v___x_2600_ = lean_array_push(v_b_2587_, v_a_2598_);
v___x_2601_ = ((size_t)1ULL);
v___x_2602_ = lean_usize_add(v_i_2585_, v___x_2601_);
v_i_2585_ = v___x_2602_;
v_b_2587_ = v___x_2600_;
v___y_2593_ = v_a_2599_;
goto _start;
}
else
{
lean_object* v_a_2604_; lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v___y_2588_);
lean_dec_ref(v_b_2587_);
lean_dec_ref(v___x_2583_);
v_a_2604_ = lean_ctor_get(v___x_2597_, 0);
v_a_2605_ = lean_ctor_get(v___x_2597_, 1);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2597_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_inc(v_a_2604_);
lean_dec(v___x_2597_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2604_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_object* v___x_2613_; 
lean_dec_ref(v___y_2588_);
lean_dec_ref(v___x_2583_);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v_b_2587_);
lean_ctor_set(v___x_2613_, 1, v___y_2593_);
return v___x_2613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* v___x_2614_, lean_object* v_as_2615_, lean_object* v_i_2616_, lean_object* v_stop_2617_, lean_object* v_b_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
size_t v_i_boxed_2626_; size_t v_stop_boxed_2627_; lean_object* v_res_2628_; 
v_i_boxed_2626_ = lean_unbox_usize(v_i_2616_);
lean_dec(v_i_2616_);
v_stop_boxed_2627_ = lean_unbox_usize(v_stop_2617_);
lean_dec(v_stop_2617_);
v_res_2628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_2614_, v_as_2615_, v_i_boxed_2626_, v_stop_boxed_2627_, v_b_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v_as_2615_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object* v_self_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v_toHashSet_2631_; lean_object* v_toArray_2632_; uint8_t v___x_2633_; 
v_toHashSet_2631_ = lean_ctor_get(v_self_2629_, 0);
v_toArray_2632_ = lean_ctor_get(v_self_2629_, 1);
v___x_2633_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_2631_, v_a_2630_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2643_; 
lean_inc_ref(v_toArray_2632_);
lean_inc_ref(v_toHashSet_2631_);
v_isSharedCheck_2643_ = !lean_is_exclusive(v_self_2629_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; lean_object* v_unused_2645_; 
v_unused_2644_ = lean_ctor_get(v_self_2629_, 1);
lean_dec(v_unused_2644_);
v_unused_2645_ = lean_ctor_get(v_self_2629_, 0);
lean_dec(v_unused_2645_);
v___x_2635_ = v_self_2629_;
v_isShared_2636_ = v_isSharedCheck_2643_;
goto v_resetjp_2634_;
}
else
{
lean_dec(v_self_2629_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2643_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2641_; 
v___x_2637_ = lean_box(0);
lean_inc_ref(v_a_2630_);
v___x_2638_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_toHashSet_2631_, v_a_2630_, v___x_2637_);
v___x_2639_ = lean_array_push(v_toArray_2632_, v_a_2630_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 1, v___x_2639_);
lean_ctor_set(v___x_2635_, 0, v___x_2638_);
v___x_2641_ = v___x_2635_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2642_, 1, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
else
{
lean_dec_ref(v_a_2630_);
return v_self_2629_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object* v_as_2646_, size_t v_i_2647_, size_t v_stop_2648_, lean_object* v_b_2649_){
_start:
{
uint8_t v___x_2650_; 
v___x_2650_ = lean_usize_dec_eq(v_i_2647_, v_stop_2648_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; lean_object* v___x_2652_; size_t v___x_2653_; size_t v___x_2654_; 
v___x_2651_ = lean_array_uget_borrowed(v_as_2646_, v_i_2647_);
lean_inc(v___x_2651_);
v___x_2652_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_2649_, v___x_2651_);
v___x_2653_ = ((size_t)1ULL);
v___x_2654_ = lean_usize_add(v_i_2647_, v___x_2653_);
v_i_2647_ = v___x_2654_;
v_b_2649_ = v___x_2652_;
goto _start;
}
else
{
return v_b_2649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object* v_as_2656_, lean_object* v_i_2657_, lean_object* v_stop_2658_, lean_object* v_b_2659_){
_start:
{
size_t v_i_boxed_2660_; size_t v_stop_boxed_2661_; lean_object* v_res_2662_; 
v_i_boxed_2660_ = lean_unbox_usize(v_i_2657_);
lean_dec(v_i_2657_);
v_stop_boxed_2661_ = lean_unbox_usize(v_stop_2658_);
lean_dec(v_stop_2658_);
v_res_2662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_2656_, v_i_boxed_2660_, v_stop_boxed_2661_, v_b_2659_);
lean_dec_ref(v_as_2656_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object* v_self_2663_, lean_object* v_arr_2664_){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2665_ = lean_unsigned_to_nat(0u);
v___x_2666_ = lean_array_get_size(v_arr_2664_);
v___x_2667_ = lean_nat_dec_lt(v___x_2665_, v___x_2666_);
if (v___x_2667_ == 0)
{
return v_self_2663_;
}
else
{
size_t v___x_2668_; size_t v___x_2669_; lean_object* v___x_2670_; 
v___x_2668_ = ((size_t)0ULL);
v___x_2669_ = lean_usize_of_nat(v___x_2666_);
v___x_2670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2664_, v___x_2668_, v___x_2669_, v_self_2663_);
return v___x_2670_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(lean_object* v_self_2671_, lean_object* v_arr_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_self_2671_, v_arr_2672_);
lean_dec_ref(v_arr_2672_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(lean_object* v_as_2674_, size_t v_i_2675_, size_t v_stop_2676_, lean_object* v_b_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
uint8_t v___x_2685_; 
v___x_2685_ = lean_usize_dec_eq(v_i_2675_, v_stop_2676_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; lean_object* v_lib_2687_; lean_object* v_pkg_2688_; lean_object* v_name_2689_; lean_object* v_keyName_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2686_ = lean_array_uget_borrowed(v_as_2674_, v_i_2675_);
v_lib_2687_ = lean_ctor_get(v___x_2686_, 0);
v_pkg_2688_ = lean_ctor_get(v_lib_2687_, 0);
v_name_2689_ = lean_ctor_get(v___x_2686_, 1);
v_keyName_2690_ = lean_ctor_get(v_pkg_2688_, 2);
v___x_2691_ = l_Lake_Module_transImportsFacet;
lean_inc(v_name_2689_);
lean_inc(v_keyName_2690_);
v___x_2692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2692_, 0, v_keyName_2690_);
lean_ctor_set(v___x_2692_, 1, v_name_2689_);
v___x_2693_ = l_Lake_Module_keyword;
lean_inc(v___x_2686_);
v___x_2694_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2692_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
lean_ctor_set(v___x_2694_, 2, v___x_2686_);
lean_ctor_set(v___x_2694_, 3, v___x_2691_);
lean_inc_ref(v___y_2678_);
lean_inc_ref(v___y_2682_);
lean_inc(v___y_2681_);
lean_inc(v___y_2680_);
lean_inc(v___y_2679_);
v___x_2695_ = lean_apply_7(v___y_2678_, v___x_2694_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, lean_box(0));
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v_a_2697_; lean_object* v___x_2698_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
v_a_2697_ = lean_ctor_get(v___x_2695_, 1);
lean_inc(v_a_2697_);
lean_dec_ref_known(v___x_2695_, 2);
v___x_2698_ = l_Lake_Job_await___redArg(v_a_2696_, v_a_2697_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v_a_2700_; lean_object* v___x_2701_; size_t v___x_2702_; size_t v___x_2703_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
v_a_2700_ = lean_ctor_get(v___x_2698_, 1);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2698_, 2);
v___x_2701_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_b_2677_, v_a_2699_);
lean_dec(v_a_2699_);
v___x_2702_ = ((size_t)1ULL);
v___x_2703_ = lean_usize_add(v_i_2675_, v___x_2702_);
v_i_2675_ = v___x_2703_;
v_b_2677_ = v___x_2701_;
v___y_2683_ = v_a_2700_;
goto _start;
}
else
{
lean_object* v_a_2705_; lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec_ref(v___y_2678_);
lean_dec_ref(v_b_2677_);
v_a_2705_ = lean_ctor_get(v___x_2698_, 0);
v_a_2706_ = lean_ctor_get(v___x_2698_, 1);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2698_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_inc(v_a_2705_);
lean_dec(v___x_2698_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2705_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
else
{
lean_object* v_a_2714_; lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec_ref(v___y_2678_);
lean_dec_ref(v_b_2677_);
v_a_2714_ = lean_ctor_get(v___x_2695_, 0);
v_a_2715_ = lean_ctor_get(v___x_2695_, 1);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2695_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_inc(v_a_2714_);
lean_dec(v___x_2695_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2714_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
else
{
lean_object* v___x_2723_; 
lean_dec_ref(v___y_2678_);
v___x_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2723_, 0, v_b_2677_);
lean_ctor_set(v___x_2723_, 1, v___y_2683_);
return v___x_2723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object* v_as_2724_, lean_object* v_i_2725_, lean_object* v_stop_2726_, lean_object* v_b_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
size_t v_i_boxed_2735_; size_t v_stop_boxed_2736_; lean_object* v_res_2737_; 
v_i_boxed_2735_ = lean_unbox_usize(v_i_2725_);
lean_dec(v_i_2725_);
v_stop_boxed_2736_ = lean_unbox_usize(v_stop_2726_);
lean_dec(v_stop_2726_);
v_res_2737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_as_2724_, v_i_boxed_2735_, v_stop_boxed_2736_, v_b_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v_as_2724_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(lean_object* v_as_2738_, size_t v_i_2739_, size_t v_stop_2740_, lean_object* v_b_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
uint8_t v___x_2749_; 
v___x_2749_ = lean_usize_dec_eq(v_i_2739_, v_stop_2740_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v_pkg_2751_; lean_object* v_name_2752_; lean_object* v_keyName_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2750_ = lean_array_uget_borrowed(v_as_2738_, v_i_2739_);
v_pkg_2751_ = lean_ctor_get(v___x_2750_, 0);
v_name_2752_ = lean_ctor_get(v___x_2750_, 1);
v_keyName_2753_ = lean_ctor_get(v_pkg_2751_, 2);
v___x_2754_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_2752_);
lean_inc(v_keyName_2753_);
v___x_2755_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_keyName_2753_);
lean_ctor_set(v___x_2755_, 1, v_name_2752_);
v___x_2756_ = l_Lake_ExternLib_keyword;
lean_inc(v___x_2750_);
v___x_2757_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
lean_ctor_set(v___x_2757_, 2, v___x_2750_);
lean_ctor_set(v___x_2757_, 3, v___x_2754_);
lean_inc_ref(v___y_2742_);
lean_inc_ref(v___y_2746_);
lean_inc(v___y_2745_);
lean_inc(v___y_2744_);
lean_inc(v___y_2743_);
v___x_2758_ = lean_apply_7(v___y_2742_, v___x_2757_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, lean_box(0));
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v_a_2760_; lean_object* v___x_2761_; size_t v___x_2762_; size_t v___x_2763_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
v_a_2760_ = lean_ctor_get(v___x_2758_, 1);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2758_, 2);
v___x_2761_ = lean_array_push(v_b_2741_, v_a_2759_);
v___x_2762_ = ((size_t)1ULL);
v___x_2763_ = lean_usize_add(v_i_2739_, v___x_2762_);
v_i_2739_ = v___x_2763_;
v_b_2741_ = v___x_2761_;
v___y_2747_ = v_a_2760_;
goto _start;
}
else
{
lean_object* v_a_2765_; lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec_ref(v___y_2742_);
lean_dec_ref(v_b_2741_);
v_a_2765_ = lean_ctor_get(v___x_2758_, 0);
v_a_2766_ = lean_ctor_get(v___x_2758_, 1);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2758_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_inc(v_a_2765_);
lean_dec(v___x_2758_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2765_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
else
{
lean_object* v___x_2774_; 
lean_dec_ref(v___y_2742_);
v___x_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2774_, 0, v_b_2741_);
lean_ctor_set(v___x_2774_, 1, v___y_2747_);
return v___x_2774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(lean_object* v_as_2775_, lean_object* v_i_2776_, lean_object* v_stop_2777_, lean_object* v_b_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
size_t v_i_boxed_2786_; size_t v_stop_boxed_2787_; lean_object* v_res_2788_; 
v_i_boxed_2786_ = lean_unbox_usize(v_i_2776_);
lean_dec(v_i_2776_);
v_stop_boxed_2787_ = lean_unbox_usize(v_stop_2777_);
lean_dec(v_stop_2777_);
v_res_2788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v_as_2775_, v_i_boxed_2786_, v_stop_boxed_2787_, v_b_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v_as_2775_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(lean_object* v_as_2789_, size_t v_i_2790_, size_t v_stop_2791_, lean_object* v_b_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v_a_2801_; lean_object* v_a_2802_; uint8_t v___x_2806_; 
v___x_2806_ = lean_usize_dec_eq(v_i_2790_, v_stop_2791_);
if (v___x_2806_ == 0)
{
lean_object* v_fst_2807_; lean_object* v_snd_2808_; lean_object* v___x_2809_; lean_object* v_lib_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2847_; 
v_fst_2807_ = lean_ctor_get(v_b_2792_, 0);
v_snd_2808_ = lean_ctor_get(v_b_2792_, 1);
v___x_2809_ = lean_array_uget(v_as_2789_, v_i_2790_);
v_lib_2810_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v___x_2809_, 1);
lean_dec(v_unused_2848_);
v___x_2812_ = v___x_2809_;
v_isShared_2813_ = v_isSharedCheck_2847_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_lib_2810_);
lean_dec(v___x_2809_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2847_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v_pkg_2814_; lean_object* v_name_2815_; uint8_t v___x_2816_; 
v_pkg_2814_ = lean_ctor_get(v_lib_2810_, 0);
v_name_2815_ = lean_ctor_get(v_lib_2810_, 1);
lean_inc(v_name_2815_);
v___x_2816_ = l_Lean_NameSet_contains(v_fst_2807_, v_name_2815_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2844_; 
lean_inc(v_snd_2808_);
lean_inc(v_fst_2807_);
v_isSharedCheck_2844_ = !lean_is_exclusive(v_b_2792_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; lean_object* v_unused_2846_; 
v_unused_2845_ = lean_ctor_get(v_b_2792_, 1);
lean_dec(v_unused_2845_);
v_unused_2846_ = lean_ctor_get(v_b_2792_, 0);
lean_dec(v_unused_2846_);
v___x_2818_ = v_b_2792_;
v_isShared_2819_ = v_isSharedCheck_2844_;
goto v_resetjp_2817_;
}
else
{
lean_dec(v_b_2792_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2844_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_keyName_2820_; lean_object* v___x_2821_; lean_object* v___x_2823_; 
v_keyName_2820_ = lean_ctor_get(v_pkg_2814_, 2);
v___x_2821_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_2815_);
lean_inc(v_keyName_2820_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set_tag(v___x_2812_, 3);
lean_ctor_set(v___x_2812_, 1, v_name_2815_);
lean_ctor_set(v___x_2812_, 0, v_keyName_2820_);
v___x_2823_ = v___x_2812_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_keyName_2820_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_name_2815_);
v___x_2823_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2824_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2825_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2823_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
lean_ctor_set(v___x_2825_, 2, v_lib_2810_);
lean_ctor_set(v___x_2825_, 3, v___x_2821_);
lean_inc_ref(v___y_2793_);
lean_inc_ref(v___y_2797_);
lean_inc(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc(v___y_2794_);
v___x_2826_ = lean_apply_7(v___y_2793_, v___x_2825_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, lean_box(0));
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v_a_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2832_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
v_a_2828_ = lean_ctor_get(v___x_2826_, 1);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2826_, 2);
v___x_2829_ = lean_array_push(v_snd_2808_, v_a_2827_);
v___x_2830_ = l_Lean_NameSet_insert(v_fst_2807_, v_name_2815_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 1, v___x_2829_);
lean_ctor_set(v___x_2818_, 0, v___x_2830_);
v___x_2832_ = v___x_2818_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v___x_2829_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
v_a_2801_ = v___x_2832_;
v_a_2802_ = v_a_2828_;
goto v___jp_2800_;
}
}
else
{
lean_object* v_a_2834_; lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_del_object(v___x_2818_);
lean_dec(v_name_2815_);
lean_dec(v_snd_2808_);
lean_dec(v_fst_2807_);
lean_dec_ref(v___y_2793_);
v_a_2834_ = lean_ctor_get(v___x_2826_, 0);
v_a_2835_ = lean_ctor_get(v___x_2826_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2826_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_inc(v_a_2834_);
lean_dec(v___x_2826_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2834_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
}
else
{
lean_dec(v_name_2815_);
lean_del_object(v___x_2812_);
lean_dec_ref(v_lib_2810_);
v_a_2801_ = v_b_2792_;
v_a_2802_ = v___y_2798_;
goto v___jp_2800_;
}
}
}
else
{
lean_object* v___x_2849_; 
lean_dec_ref(v___y_2793_);
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v_b_2792_);
lean_ctor_set(v___x_2849_, 1, v___y_2798_);
return v___x_2849_;
}
v___jp_2800_:
{
size_t v___x_2803_; size_t v___x_2804_; 
v___x_2803_ = ((size_t)1ULL);
v___x_2804_ = lean_usize_add(v_i_2790_, v___x_2803_);
v_i_2790_ = v___x_2804_;
v_b_2792_ = v_a_2801_;
v___y_2798_ = v_a_2802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object* v_as_2850_, lean_object* v_i_2851_, lean_object* v_stop_2852_, lean_object* v_b_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
size_t v_i_boxed_2861_; size_t v_stop_boxed_2862_; lean_object* v_res_2863_; 
v_i_boxed_2861_ = lean_unbox_usize(v_i_2851_);
lean_dec(v_i_2851_);
v_stop_boxed_2862_ = lean_unbox_usize(v_stop_2852_);
lean_dec(v_stop_2852_);
v_res_2863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_as_2850_, v_i_boxed_2861_, v_stop_boxed_2862_, v_b_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v_as_2850_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(lean_object* v___x_2864_, lean_object* v_as_2865_, size_t v_i_2866_, size_t v_stop_2867_, lean_object* v_b_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
uint8_t v___x_2876_; 
v___x_2876_ = lean_usize_dec_eq(v_i_2866_, v_stop_2867_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = lean_array_uget_borrowed(v_as_2865_, v_i_2866_);
lean_inc_ref(v___y_2869_);
lean_inc(v___x_2877_);
lean_inc_ref(v___x_2864_);
v___x_2878_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v___x_2864_, v___x_2877_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v_a_2880_; lean_object* v___x_2881_; size_t v___x_2882_; size_t v___x_2883_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
v_a_2880_ = lean_ctor_get(v___x_2878_, 1);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2878_, 2);
v___x_2881_ = lean_array_push(v_b_2868_, v_a_2879_);
v___x_2882_ = ((size_t)1ULL);
v___x_2883_ = lean_usize_add(v_i_2866_, v___x_2882_);
v_i_2866_ = v___x_2883_;
v_b_2868_ = v___x_2881_;
v___y_2874_ = v_a_2880_;
goto _start;
}
else
{
lean_object* v_a_2885_; lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec_ref(v___y_2869_);
lean_dec_ref(v_b_2868_);
lean_dec_ref(v___x_2864_);
v_a_2885_ = lean_ctor_get(v___x_2878_, 0);
v_a_2886_ = lean_ctor_get(v___x_2878_, 1);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2878_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_inc(v_a_2885_);
lean_dec(v___x_2878_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2885_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
else
{
lean_object* v___x_2894_; 
lean_dec_ref(v___y_2869_);
lean_dec_ref(v___x_2864_);
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v_b_2868_);
lean_ctor_set(v___x_2894_, 1, v___y_2874_);
return v___x_2894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object* v___x_2895_, lean_object* v_as_2896_, lean_object* v_i_2897_, lean_object* v_stop_2898_, lean_object* v_b_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
size_t v_i_boxed_2907_; size_t v_stop_boxed_2908_; lean_object* v_res_2909_; 
v_i_boxed_2907_ = lean_unbox_usize(v_i_2897_);
lean_dec(v_i_2897_);
v_stop_boxed_2908_ = lean_unbox_usize(v_stop_2898_);
lean_dec(v_stop_2898_);
v_res_2909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v___x_2895_, v_as_2896_, v_i_boxed_2907_, v_stop_boxed_2908_, v_b_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v_as_2896_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(lean_object* v___x_2910_, lean_object* v_as_2911_, size_t v_i_2912_, size_t v_stop_2913_, lean_object* v_b_2914_){
_start:
{
lean_object* v___y_2916_; uint8_t v___x_2920_; 
v___x_2920_ = lean_usize_dec_eq(v_i_2912_, v_stop_2913_);
if (v___x_2920_ == 0)
{
lean_object* v_toConfigDecl_2921_; lean_object* v_name_2922_; lean_object* v_kind_2923_; lean_object* v_config_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v_toConfigDecl_2921_ = lean_array_uget_borrowed(v_as_2911_, v_i_2912_);
v_name_2922_ = lean_ctor_get(v_toConfigDecl_2921_, 1);
v_kind_2923_ = lean_ctor_get(v_toConfigDecl_2921_, 2);
v_config_2924_ = lean_ctor_get(v_toConfigDecl_2921_, 3);
v___x_2925_ = l_Lake_ExternLib_keyword;
v___x_2926_ = lean_name_eq(v_kind_2923_, v___x_2925_);
if (v___x_2926_ == 0)
{
v___y_2916_ = v_b_2914_;
goto v___jp_2915_;
}
else
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
lean_inc(v_config_2924_);
lean_inc(v_name_2922_);
lean_inc_ref(v___x_2910_);
v___x_2927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2910_);
lean_ctor_set(v___x_2927_, 1, v_name_2922_);
lean_ctor_set(v___x_2927_, 2, v_config_2924_);
v___x_2928_ = lean_array_push(v_b_2914_, v___x_2927_);
v___y_2916_ = v___x_2928_;
goto v___jp_2915_;
}
}
else
{
lean_dec_ref(v___x_2910_);
return v_b_2914_;
}
v___jp_2915_:
{
size_t v___x_2917_; size_t v___x_2918_; 
v___x_2917_ = ((size_t)1ULL);
v___x_2918_ = lean_usize_add(v_i_2912_, v___x_2917_);
v_i_2912_ = v___x_2918_;
v_b_2914_ = v___y_2916_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(lean_object* v___x_2929_, lean_object* v_as_2930_, lean_object* v_i_2931_, lean_object* v_stop_2932_, lean_object* v_b_2933_){
_start:
{
size_t v_i_boxed_2934_; size_t v_stop_boxed_2935_; lean_object* v_res_2936_; 
v_i_boxed_2934_ = lean_unbox_usize(v_i_2931_);
lean_dec(v_i_2931_);
v_stop_boxed_2935_ = lean_unbox_usize(v_stop_2932_);
lean_dec(v_stop_2932_);
v_res_2936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v___x_2929_, v_as_2930_, v_i_boxed_2934_, v_stop_boxed_2935_, v_b_2933_);
lean_dec_ref(v_as_2930_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(lean_object* v_as_2937_, size_t v_i_2938_, size_t v_stop_2939_, lean_object* v_b_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
uint8_t v___x_2948_; 
v___x_2948_ = lean_usize_dec_eq(v_i_2938_, v_stop_2939_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; lean_object* v_lib_2950_; lean_object* v_config_2951_; lean_object* v_nativeFacets_2952_; uint8_t v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; size_t v_sz_2956_; size_t v___x_2957_; lean_object* v___x_2958_; 
v___x_2949_ = lean_array_uget_borrowed(v_as_2937_, v_i_2938_);
v_lib_2950_ = lean_ctor_get(v___x_2949_, 0);
v_config_2951_ = lean_ctor_get(v_lib_2950_, 2);
v_nativeFacets_2952_ = lean_ctor_get(v_config_2951_, 8);
v___x_2953_ = 1;
v___x_2954_ = lean_box(v___x_2953_);
lean_inc_ref(v_nativeFacets_2952_);
v___x_2955_ = lean_apply_1(v_nativeFacets_2952_, v___x_2954_);
v_sz_2956_ = lean_array_size(v___x_2955_);
v___x_2957_ = ((size_t)0ULL);
lean_inc_ref(v___y_2941_);
lean_inc(v___x_2949_);
v___x_2958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2949_, v_sz_2956_, v___x_2957_, v___x_2955_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v_a_2960_; lean_object* v___x_2961_; size_t v___x_2962_; size_t v___x_2963_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
v_a_2960_ = lean_ctor_get(v___x_2958_, 1);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2958_, 2);
v___x_2961_ = l_Array_append___redArg(v_b_2940_, v_a_2959_);
lean_dec(v_a_2959_);
v___x_2962_ = ((size_t)1ULL);
v___x_2963_ = lean_usize_add(v_i_2938_, v___x_2962_);
v_i_2938_ = v___x_2963_;
v_b_2940_ = v___x_2961_;
v___y_2946_ = v_a_2960_;
goto _start;
}
else
{
lean_dec_ref(v___y_2941_);
lean_dec_ref(v_b_2940_);
return v___x_2958_;
}
}
else
{
lean_object* v___x_2965_; 
lean_dec_ref(v___y_2941_);
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v_b_2940_);
lean_ctor_set(v___x_2965_, 1, v___y_2946_);
return v___x_2965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object* v_as_2966_, lean_object* v_i_2967_, lean_object* v_stop_2968_, lean_object* v_b_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
size_t v_i_boxed_2977_; size_t v_stop_boxed_2978_; lean_object* v_res_2979_; 
v_i_boxed_2977_ = lean_unbox_usize(v_i_2967_);
lean_dec(v_i_2967_);
v_stop_boxed_2978_ = lean_unbox_usize(v_stop_2968_);
lean_dec(v_stop_2968_);
v_res_2979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_as_2966_, v_i_boxed_2977_, v_stop_boxed_2978_, v_b_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v_as_2966_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(lean_object* v_self_2980_, lean_object* v_dir_2981_, lean_object* v___x_2982_, lean_object* v_targetDecls_2983_, lean_object* v_pkg_2984_, lean_object* v_name_2985_, lean_object* v___x_2986_, lean_object* v_config_2987_, lean_object* v_config_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_a_2997_; lean_object* v_a_2998_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v_a_3008_; lean_object* v_a_3009_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v_a_3056_; lean_object* v_a_3057_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v_snd_3075_; lean_object* v_a_3076_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v_a_3098_; lean_object* v_a_3099_; lean_object* v___x_3122_; 
lean_inc_ref(v___y_2989_);
lean_inc_ref(v___y_2993_);
lean_inc(v___y_2992_);
lean_inc(v___y_2991_);
lean_inc(v___x_2982_);
v___x_3122_ = lean_apply_7(v___y_2989_, v___x_2986_, v___x_2982_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, lean_box(0));
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v_a_3124_; lean_object* v___x_3125_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
v_a_3124_ = lean_ctor_get(v___x_3122_, 1);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3122_, 2);
v___x_3125_ = l_Lake_Job_await___redArg(v_a_3123_, v_a_3124_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; lean_object* v_a_3127_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v_a_3138_; lean_object* v_a_3139_; lean_object* v_a_3151_; lean_object* v_a_3152_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; uint8_t v___x_3186_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3126_);
v_a_3127_ = lean_ctor_get(v___x_3125_, 1);
lean_inc(v_a_3127_);
lean_dec_ref_known(v___x_3125_, 2);
v___x_3183_ = lean_unsigned_to_nat(0u);
v___x_3184_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_3185_ = lean_array_get_size(v_a_3126_);
v___x_3186_ = lean_nat_dec_lt(v___x_3183_, v___x_3185_);
if (v___x_3186_ == 0)
{
v_a_3151_ = v___x_3184_;
v_a_3152_ = v_a_3127_;
goto v___jp_3150_;
}
else
{
size_t v___x_3187_; size_t v___x_3188_; lean_object* v___x_3189_; 
v___x_3187_ = ((size_t)0ULL);
v___x_3188_ = lean_usize_of_nat(v___x_3185_);
lean_inc_ref(v___y_2989_);
v___x_3189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3126_, v___x_3187_, v___x_3188_, v___x_3184_, v___y_2989_, v___x_2982_, v___y_2991_, v___y_2992_, v___y_2993_, v_a_3127_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v_a_3191_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc(v_a_3190_);
v_a_3191_ = lean_ctor_get(v___x_3189_, 1);
lean_inc(v_a_3191_);
lean_dec_ref_known(v___x_3189_, 2);
v_a_3151_ = v_a_3190_;
v_a_3152_ = v_a_3191_;
goto v___jp_3150_;
}
else
{
lean_object* v_a_3192_; lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_a_3126_);
lean_dec_ref(v___y_2989_);
lean_dec_ref(v_config_2987_);
lean_dec(v_name_2985_);
lean_dec_ref(v_pkg_2984_);
lean_dec(v___x_2982_);
lean_dec_ref(v_dir_2981_);
lean_dec_ref(v_self_2980_);
v_a_3192_ = lean_ctor_get(v___x_3189_, 0);
v_a_3193_ = lean_ctor_get(v___x_3189_, 1);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3189_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_inc(v_a_3192_);
lean_dec(v___x_3189_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3192_);
lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
v___jp_3128_:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v___x_3140_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
v___x_3141_ = lean_array_get_size(v_a_3126_);
v___x_3142_ = lean_nat_dec_lt(v___y_3130_, v___x_3141_);
if (v___x_3142_ == 0)
{
lean_dec(v_a_3126_);
v___y_3088_ = v___y_3129_;
v___y_3089_ = v___y_3130_;
v___y_3090_ = v___y_3131_;
v___y_3091_ = v_a_3138_;
v___y_3092_ = v___y_3132_;
v___y_3093_ = v___y_3133_;
v___y_3094_ = v___y_3134_;
v___y_3095_ = v___y_3135_;
v___y_3096_ = v___y_3136_;
v___y_3097_ = v___y_3137_;
v_a_3098_ = v___x_3140_;
v_a_3099_ = v_a_3139_;
goto v___jp_3087_;
}
else
{
size_t v___x_3143_; size_t v___x_3144_; lean_object* v___x_3145_; 
v___x_3143_ = ((size_t)0ULL);
v___x_3144_ = lean_usize_of_nat(v___x_3141_);
lean_inc_ref(v___y_2989_);
v___x_3145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3126_, v___x_3143_, v___x_3144_, v___x_3140_, v___y_2989_, v___x_2982_, v___y_2991_, v___y_2992_, v___y_2993_, v_a_3139_);
lean_dec(v_a_3126_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v_a_3147_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3146_);
v_a_3147_ = lean_ctor_get(v___x_3145_, 1);
lean_inc(v_a_3147_);
lean_dec_ref_known(v___x_3145_, 2);
v___y_3088_ = v___y_3129_;
v___y_3089_ = v___y_3130_;
v___y_3090_ = v___y_3131_;
v___y_3091_ = v_a_3138_;
v___y_3092_ = v___y_3132_;
v___y_3093_ = v___y_3133_;
v___y_3094_ = v___y_3134_;
v___y_3095_ = v___y_3135_;
v___y_3096_ = v___y_3136_;
v___y_3097_ = v___y_3137_;
v_a_3098_ = v_a_3146_;
v_a_3099_ = v_a_3147_;
goto v___jp_3087_;
}
else
{
lean_object* v_a_3148_; lean_object* v_a_3149_; 
lean_dec_ref(v_a_3138_);
lean_dec_ref(v___y_3136_);
lean_dec_ref(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec_ref(v___y_3131_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v___y_2989_);
lean_dec(v_name_2985_);
lean_dec_ref(v_pkg_2984_);
lean_dec(v___x_2982_);
lean_dec_ref(v_dir_2981_);
lean_dec_ref(v_self_2980_);
v_a_3148_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3148_);
v_a_3149_ = lean_ctor_get(v___x_3145_, 1);
lean_inc(v_a_3149_);
lean_dec_ref_known(v___x_3145_, 2);
v_a_2997_ = v_a_3148_;
v_a_2998_ = v_a_3149_;
goto v___jp_2996_;
}
}
}
v___jp_3150_:
{
lean_object* v_toLeanConfig_3153_; lean_object* v_toLeanConfig_3154_; lean_object* v_buildDir_3155_; lean_object* v_nativeLibDir_3156_; lean_object* v_moreLinkObjs_3157_; lean_object* v_moreLinkLibs_3158_; lean_object* v_moreLinkArgs_3159_; lean_object* v_weakLinkArgs_3160_; lean_object* v_moreLinkObjs_3161_; lean_object* v_moreLinkLibs_3162_; lean_object* v_moreLinkArgs_3163_; lean_object* v_weakLinkArgs_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; uint8_t v___x_3168_; 
v_toLeanConfig_3153_ = lean_ctor_get(v_config_2987_, 1);
lean_inc_ref(v_toLeanConfig_3153_);
v_toLeanConfig_3154_ = lean_ctor_get(v_config_2988_, 0);
v_buildDir_3155_ = lean_ctor_get(v_config_2987_, 5);
lean_inc_ref(v_buildDir_3155_);
v_nativeLibDir_3156_ = lean_ctor_get(v_config_2987_, 7);
lean_inc_ref(v_nativeLibDir_3156_);
lean_dec_ref(v_config_2987_);
v_moreLinkObjs_3157_ = lean_ctor_get(v_toLeanConfig_3153_, 6);
lean_inc_ref(v_moreLinkObjs_3157_);
v_moreLinkLibs_3158_ = lean_ctor_get(v_toLeanConfig_3153_, 7);
lean_inc_ref(v_moreLinkLibs_3158_);
v_moreLinkArgs_3159_ = lean_ctor_get(v_toLeanConfig_3153_, 8);
lean_inc_ref(v_moreLinkArgs_3159_);
v_weakLinkArgs_3160_ = lean_ctor_get(v_toLeanConfig_3153_, 9);
lean_inc_ref(v_weakLinkArgs_3160_);
lean_dec_ref(v_toLeanConfig_3153_);
v_moreLinkObjs_3161_ = lean_ctor_get(v_toLeanConfig_3154_, 6);
v_moreLinkLibs_3162_ = lean_ctor_get(v_toLeanConfig_3154_, 7);
v_moreLinkArgs_3163_ = lean_ctor_get(v_toLeanConfig_3154_, 8);
v_weakLinkArgs_3164_ = lean_ctor_get(v_toLeanConfig_3154_, 9);
v___x_3165_ = l_Array_append___redArg(v_moreLinkObjs_3157_, v_moreLinkObjs_3161_);
v___x_3166_ = lean_unsigned_to_nat(0u);
v___x_3167_ = lean_array_get_size(v___x_3165_);
v___x_3168_ = lean_nat_dec_lt(v___x_3166_, v___x_3167_);
if (v___x_3168_ == 0)
{
lean_dec_ref(v___x_3165_);
v___y_3129_ = v_weakLinkArgs_3160_;
v___y_3130_ = v___x_3166_;
v___y_3131_ = v_nativeLibDir_3156_;
v___y_3132_ = v_moreLinkArgs_3163_;
v___y_3133_ = v_moreLinkArgs_3159_;
v___y_3134_ = v_moreLinkLibs_3158_;
v___y_3135_ = v_weakLinkArgs_3164_;
v___y_3136_ = v_buildDir_3155_;
v___y_3137_ = v_moreLinkLibs_3162_;
v_a_3138_ = v_a_3151_;
v_a_3139_ = v_a_3152_;
goto v___jp_3128_;
}
else
{
size_t v___x_3169_; size_t v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = ((size_t)0ULL);
v___x_3170_ = lean_usize_of_nat(v___x_3167_);
lean_inc_ref(v___y_2989_);
lean_inc_ref(v_pkg_2984_);
v___x_3171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2984_, v___x_3165_, v___x_3169_, v___x_3170_, v_a_3151_, v___y_2989_, v___x_2982_, v___y_2991_, v___y_2992_, v___y_2993_, v_a_3152_);
lean_dec_ref(v___x_3165_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v_a_3173_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3172_);
v_a_3173_ = lean_ctor_get(v___x_3171_, 1);
lean_inc(v_a_3173_);
lean_dec_ref_known(v___x_3171_, 2);
v___y_3129_ = v_weakLinkArgs_3160_;
v___y_3130_ = v___x_3166_;
v___y_3131_ = v_nativeLibDir_3156_;
v___y_3132_ = v_moreLinkArgs_3163_;
v___y_3133_ = v_moreLinkArgs_3159_;
v___y_3134_ = v_moreLinkLibs_3158_;
v___y_3135_ = v_weakLinkArgs_3164_;
v___y_3136_ = v_buildDir_3155_;
v___y_3137_ = v_moreLinkLibs_3162_;
v_a_3138_ = v_a_3172_;
v_a_3139_ = v_a_3173_;
goto v___jp_3128_;
}
else
{
lean_object* v_a_3174_; lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_dec_ref(v_weakLinkArgs_3160_);
lean_dec_ref(v_moreLinkArgs_3159_);
lean_dec_ref(v_moreLinkLibs_3158_);
lean_dec_ref(v_nativeLibDir_3156_);
lean_dec_ref(v_buildDir_3155_);
lean_dec(v_a_3126_);
lean_dec_ref(v___y_2989_);
lean_dec(v_name_2985_);
lean_dec_ref(v_pkg_2984_);
lean_dec(v___x_2982_);
lean_dec_ref(v_dir_2981_);
lean_dec_ref(v_self_2980_);
v_a_3174_ = lean_ctor_get(v___x_3171_, 0);
v_a_3175_ = lean_ctor_get(v___x_3171_, 1);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3171_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_inc(v_a_3174_);
lean_dec(v___x_3171_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3174_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref(v___y_2989_);
lean_dec_ref(v_config_2987_);
lean_dec(v_name_2985_);
lean_dec_ref(v_pkg_2984_);
lean_dec(v___x_2982_);
lean_dec_ref(v_dir_2981_);
lean_dec_ref(v_self_2980_);
v_a_3201_ = lean_ctor_get(v___x_3125_, 0);
v_a_3202_ = lean_ctor_get(v___x_3125_, 1);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3125_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_inc(v_a_3201_);
lean_dec(v___x_3125_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3201_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
lean_dec_ref(v___y_2989_);
lean_dec_ref(v_config_2987_);
lean_dec(v_name_2985_);
lean_dec_ref(v_pkg_2984_);
lean_dec(v___x_2982_);
lean_dec_ref(v_dir_2981_);
lean_dec_ref(v_self_2980_);
v_a_3210_ = lean_ctor_get(v___x_3122_, 0);
v_a_3211_ = lean_ctor_get(v___x_3122_, 1);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3122_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_inc(v_a_3210_);
lean_dec(v___x_3122_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3210_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
v___jp_2996_:
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2999_, 0, v_a_2997_);
lean_ctor_set(v___x_2999_, 1, v_a_2998_);
return v___x_2999_;
}
v___jp_3000_:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; uint8_t v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
lean_inc_ref(v_self_2980_);
v___x_3010_ = l_Lake_LeanLib_libName(v_self_2980_);
v___x_3011_ = l_System_FilePath_normalize(v___y_3007_);
v___x_3012_ = l_Lake_joinRelative(v_dir_2981_, v___x_3011_);
v___x_3013_ = l_System_FilePath_normalize(v___y_3002_);
v___x_3014_ = l_Lake_joinRelative(v___x_3012_, v___x_3013_);
v___x_3015_ = 0;
v___x_3016_ = l_Lake_nameToSharedLib(v___x_3010_, v___x_3015_);
v___x_3017_ = l_Lake_joinRelative(v___x_3014_, v___x_3016_);
v___x_3018_ = l_Array_append___redArg(v___y_3001_, v___y_3006_);
v___x_3019_ = l_Array_append___redArg(v___y_3005_, v___y_3004_);
v___x_3020_ = l_Lake_LeanLib_isPlugin(v_self_2980_);
v___x_3021_ = l_System_Platform_isWindows;
v___x_3022_ = lean_box(0);
v___x_3023_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_3024_ = l_Lake_buildLeanSharedLib(v___x_3010_, v___x_3017_, v___y_3003_, v_a_3008_, v___x_3018_, v___x_3019_, v___x_3020_, v___x_3021_, v___x_3022_, v___y_2989_, v___x_2982_, v___y_2991_, v___y_2992_, v___y_2993_, v___x_3023_);
lean_dec(v___x_2982_);
lean_dec_ref(v___y_3003_);
v___x_3025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3024_);
lean_ctor_set(v___x_3025_, 1, v_a_3009_);
return v___x_3025_;
}
v___jp_3026_:
{
lean_object* v___x_3038_; uint8_t v___x_3039_; 
v___x_3038_ = lean_array_get_size(v___y_3037_);
v___x_3039_ = lean_nat_dec_lt(v___y_3027_, v___x_3038_);
if (v___x_3039_ == 0)
{
lean_dec_ref(v___y_3037_);
v___y_3001_ = v___y_3028_;
v___y_3002_ = v___y_3029_;
v___y_3003_ = v___y_3031_;
v___y_3004_ = v___y_3032_;
v___y_3005_ = v___y_3033_;
v___y_3006_ = v___y_3036_;
v___y_3007_ = v___y_3035_;
v_a_3008_ = v___y_3034_;
v_a_3009_ = v___y_3030_;
goto v___jp_3000_;
}
else
{
size_t v___x_3040_; size_t v___x_3041_; lean_object* v___x_3042_; 
v___x_3040_ = ((size_t)0ULL);
v___x_3041_ = lean_usize_of_nat(v___x_3038_);
lean_inc_ref(v___y_2989_);
v___x_3042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_3037_, v___x_3040_, v___x_3041_, v___y_3034_, v___y_2989_, v___x_2982_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_3030_);
lean_dec_ref(v___y_3037_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v_a_3044_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
v_a_3044_ = lean_ctor_get(v___x_3042_, 1);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3042_, 2);
v___y_3001_ = v___y_3028_;
v___y_3002_ = v___y_3029_;
v___y_3003_ = v___y_3031_;
v___y_3004_ = v___y_3032_;
v___y_3005_ = v___y_3033_;
v___y_3006_ = v___y_3036_;
v___y_3007_ = v___y_3035_;
v_a_3008_ = v_a_3043_;
v_a_3009_ = v_a_3044_;
goto v___jp_3000_;
}
else
{
lean_object* v_a_3045_; lean_object* v_a_3046_; 
lean_dec_ref(v___y_3035_);
lean_dec_ref(v___y_3033_);
lean_dec_ref(v___y_3031_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec_ref(v___y_2989_);
lean_dec(v___x_2982_);
lean_dec_ref(v_dir_2981_);
lean_dec_ref(v_self_2980_);
v_a_3045_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3045_);
v_a_3046_ = lean_ctor_get(v___x_3042_, 1);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3042_, 2);
v_a_2997_ = v_a_3045_;
v_a_2998_ = v_a_3046_;
goto v___jp_2996_;
}
}
}
v___jp_3047_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3058_ = lean_mk_empty_array_with_capacity(v___y_3049_);
v___x_3059_ = lean_array_get_size(v_targetDecls_2983_);
v___x_3060_ = lean_nat_dec_lt(v___y_3049_, v___x_3059_);
if (v___x_3060_ == 0)
{
lean_dec_ref(v_pkg_2984_);
v___y_3027_ = v___y_3049_;
v___y_3028_ = v___y_3048_;
v___y_3029_ = v___y_3050_;
v___y_3030_ = v_a_3057_;
v___y_3031_ = v___y_3051_;
v___y_3032_ = v___y_3052_;
v___y_3033_ = v___y_3053_;
v___y_3034_ = v_a_3056_;
v___y_3035_ = v___y_3055_;
v___y_3036_ = v___y_3054_;
v___y_3037_ = v___x_3058_;
goto v___jp_3026_;
}
else
{
size_t v___x_3061_; size_t v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = ((size_t)0ULL);
v___x_3062_ = lean_usize_of_nat(v___x_3059_);
v___x_3063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2984_, v_targetDecls_2983_, v___x_3061_, v___x_3062_, v___x_3058_);
v___y_3027_ = v___y_3049_;
v___y_3028_ = v___y_3048_;
v___y_3029_ = v___y_3050_;
v___y_3030_ = v_a_3057_;
v___y_3031_ = v___y_3051_;
v___y_3032_ = v___y_3052_;
v___y_3033_ = v___y_3053_;
v___y_3034_ = v_a_3056_;
v___y_3035_ = v___y_3055_;
v___y_3036_ = v___y_3054_;
v___y_3037_ = v___x_3063_;
goto v___jp_3026_;
}
}
v___jp_3064_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3077_ = l_Array_append___redArg(v___y_3073_, v___y_3074_);
v___x_3078_ = lean_array_get_size(v___x_3077_);
v___x_3079_ = lean_nat_dec_lt(v___y_3065_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_dec_ref(v___x_3077_);
v___y_3048_ = v___y_3066_;
v___y_3049_ = v___y_3065_;
v___y_3050_ = v___y_3067_;
v___y_3051_ = v___y_3068_;
v___y_3052_ = v___y_3069_;
v___y_3053_ = v___y_3070_;
v___y_3054_ = v___y_3072_;
v___y_3055_ = v___y_3071_;
v_a_3056_ = v_snd_3075_;
v_a_3057_ = v_a_3076_;
goto v___jp_3047_;
}
else
{
size_t v___x_3080_; size_t v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = ((size_t)0ULL);
v___x_3081_ = lean_usize_of_nat(v___x_3078_);
lean_inc_ref(v___y_2989_);
lean_inc_ref(v_pkg_2984_);
v___x_3082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2984_, v___x_3077_, v___x_3080_, v___x_3081_, v_snd_3075_, v___y_2989_, v___x_2982_, v___y_2991_, v___y_2992_, v___y_2993_, v_a_3076_);
lean_dec_ref(v___x_3077_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v_a_3084_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
v_a_3084_ = lean_ctor_get(v___x_3082_, 1);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3082_, 2);
v___y_3048_ = v___y_3066_;
v___y_3049_ = v___y_3065_;
v___y_3050_ = v___y_3067_;
v___y_3051_ = v___y_3068_;
v___y_3052_ = v___y_3069_;
v___y_3053_ = v___y_3070_;
v___y_3054_ = v___y_3072_;
v___y_3055_ = v___y_3071_;
v_a_3056_ = v_a_3083_;
v_a_3057_ = v_a_3084_;
goto v___jp_3047_;
}
else
{
lean_object* v_a_3085_; lean_object* v_a_3086_; 
lean_dec_ref(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec_ref(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec_ref(v___y_2989_);
lean_dec_ref(v_pkg_2984_);
lean_dec(v___x_2982_);
lean_dec_ref(v_dir_2981_);
lean_dec_ref(v_self_2980_);
v_a_3085_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3085_);
v_a_3086_ = lean_ctor_get(v___x_3082_, 1);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3082_, 2);
v_a_2997_ = v_a_3085_;
v_a_2998_ = v_a_3086_;
goto v___jp_2996_;
}
}
}
v___jp_3087_:
{
lean_object* v_toArray_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3120_; 
v_toArray_3100_ = lean_ctor_get(v_a_3098_, 1);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_a_3098_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; 
v_unused_3121_ = lean_ctor_get(v_a_3098_, 0);
lean_dec(v_unused_3121_);
v___x_3102_ = v_a_3098_;
v_isShared_3103_ = v_isSharedCheck_3120_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_toArray_3100_);
lean_dec(v_a_3098_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3120_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v___x_3104_ = lean_mk_empty_array_with_capacity(v___y_3089_);
v___x_3105_ = lean_array_get_size(v_toArray_3100_);
v___x_3106_ = lean_nat_dec_lt(v___y_3089_, v___x_3105_);
if (v___x_3106_ == 0)
{
lean_del_object(v___x_3102_);
lean_dec_ref(v_toArray_3100_);
lean_dec(v_name_2985_);
v___y_3065_ = v___y_3089_;
v___y_3066_ = v___y_3088_;
v___y_3067_ = v___y_3090_;
v___y_3068_ = v___y_3091_;
v___y_3069_ = v___y_3092_;
v___y_3070_ = v___y_3093_;
v___y_3071_ = v___y_3096_;
v___y_3072_ = v___y_3095_;
v___y_3073_ = v___y_3094_;
v___y_3074_ = v___y_3097_;
v_snd_3075_ = v___x_3104_;
v_a_3076_ = v_a_3099_;
goto v___jp_3064_;
}
else
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3107_ = l_Lean_NameSet_empty;
v___x_3108_ = l_Lean_NameSet_insert(v___x_3107_, v_name_2985_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 1, v___x_3104_);
lean_ctor_set(v___x_3102_, 0, v___x_3108_);
v___x_3110_ = v___x_3102_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3108_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v___x_3104_);
v___x_3110_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
size_t v___x_3111_; size_t v___x_3112_; lean_object* v___x_3113_; 
v___x_3111_ = ((size_t)0ULL);
v___x_3112_ = lean_usize_of_nat(v___x_3105_);
lean_inc_ref(v___y_2989_);
v___x_3113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_3100_, v___x_3111_, v___x_3112_, v___x_3110_, v___y_2989_, v___x_2982_, v___y_2991_, v___y_2992_, v___y_2993_, v_a_3099_);
lean_dec_ref(v_toArray_3100_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v_a_3115_; lean_object* v_snd_3116_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
v_a_3115_ = lean_ctor_get(v___x_3113_, 1);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3113_, 2);
v_snd_3116_ = lean_ctor_get(v_a_3114_, 1);
lean_inc(v_snd_3116_);
lean_dec(v_a_3114_);
v___y_3065_ = v___y_3089_;
v___y_3066_ = v___y_3088_;
v___y_3067_ = v___y_3090_;
v___y_3068_ = v___y_3091_;
v___y_3069_ = v___y_3092_;
v___y_3070_ = v___y_3093_;
v___y_3071_ = v___y_3096_;
v___y_3072_ = v___y_3095_;
v___y_3073_ = v___y_3094_;
v___y_3074_ = v___y_3097_;
v_snd_3075_ = v_snd_3116_;
v_a_3076_ = v_a_3115_;
goto v___jp_3064_;
}
else
{
lean_object* v_a_3117_; lean_object* v_a_3118_; 
lean_dec_ref(v___y_3096_);
lean_dec_ref(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec_ref(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec_ref(v___y_3088_);
lean_dec_ref(v___y_2989_);
lean_dec_ref(v_pkg_2984_);
lean_dec(v___x_2982_);
lean_dec_ref(v_dir_2981_);
lean_dec_ref(v_self_2980_);
v_a_3117_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3117_);
v_a_3118_ = lean_ctor_get(v___x_3113_, 1);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3113_, 2);
v_a_2997_ = v_a_3117_;
v_a_2998_ = v_a_3118_;
goto v___jp_2996_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* v_self_3219_, lean_object* v_dir_3220_, lean_object* v___x_3221_, lean_object* v_targetDecls_3222_, lean_object* v_pkg_3223_, lean_object* v_name_3224_, lean_object* v___x_3225_, lean_object* v_config_3226_, lean_object* v_config_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v_self_3219_, v_dir_3220_, v___x_3221_, v_targetDecls_3222_, v_pkg_3223_, v_name_3224_, v___x_3225_, v_config_3226_, v_config_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec(v_config_3227_);
lean_dec_ref(v_targetDecls_3222_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object* v_self_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_){
_start:
{
lean_object* v_pkg_3245_; lean_object* v_name_3246_; lean_object* v_config_3247_; lean_object* v_keyName_3248_; lean_object* v_dir_3249_; lean_object* v_config_3250_; lean_object* v_targetDecls_3251_; lean_object* v___x_3252_; uint8_t v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___f_3262_; uint8_t v___x_3263_; lean_object* v___x_3264_; 
v_pkg_3245_ = lean_ctor_get(v_self_3237_, 0);
lean_inc_ref_n(v_pkg_3245_, 2);
v_name_3246_ = lean_ctor_get(v_self_3237_, 1);
lean_inc_n(v_name_3246_, 3);
v_config_3247_ = lean_ctor_get(v_self_3237_, 2);
lean_inc(v_config_3247_);
v_keyName_3248_ = lean_ctor_get(v_pkg_3245_, 2);
v_dir_3249_ = lean_ctor_get(v_pkg_3245_, 4);
lean_inc_ref(v_dir_3249_);
v_config_3250_ = lean_ctor_get(v_pkg_3245_, 6);
lean_inc_ref(v_config_3250_);
v_targetDecls_3251_ = lean_ctor_get(v_pkg_3245_, 15);
lean_inc_ref(v_targetDecls_3251_);
v___x_3252_ = l_Lake_instDataKindDynlib;
v___x_3253_ = 1;
v___x_3254_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3246_, v___x_3253_);
v___x_3255_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0));
v___x_3256_ = lean_string_append(v___x_3254_, v___x_3255_);
v___x_3257_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_3248_);
v___x_3258_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3258_, 0, v_keyName_3248_);
lean_ctor_set(v___x_3258_, 1, v_name_3246_);
v___x_3259_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3237_);
v___x_3260_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
lean_ctor_set(v___x_3260_, 2, v_self_3237_);
lean_ctor_set(v___x_3260_, 3, v___x_3257_);
v___x_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3261_, 0, v_pkg_3245_);
v___f_3262_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3262_, 0, v_self_3237_);
lean_closure_set(v___f_3262_, 1, v_dir_3249_);
lean_closure_set(v___f_3262_, 2, v___x_3261_);
lean_closure_set(v___f_3262_, 3, v_targetDecls_3251_);
lean_closure_set(v___f_3262_, 4, v_pkg_3245_);
lean_closure_set(v___f_3262_, 5, v_name_3246_);
lean_closure_set(v___f_3262_, 6, v___x_3260_);
lean_closure_set(v___f_3262_, 7, v_config_3250_);
lean_closure_set(v___f_3262_, 8, v_config_3247_);
v___x_3263_ = 0;
v___x_3264_ = l_Lake_ensureJob___redArg(v___x_3252_, v___f_3262_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3289_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
v_a_3266_ = lean_ctor_get(v___x_3264_, 1);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3268_ = v___x_3264_;
v_isShared_3269_ = v_isSharedCheck_3289_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_inc(v_a_3265_);
lean_dec(v___x_3264_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3289_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v_task_3270_; lean_object* v_kind_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3287_; 
v_task_3270_ = lean_ctor_get(v_a_3265_, 0);
v_kind_3271_ = lean_ctor_get(v_a_3265_, 1);
v_isSharedCheck_3287_ = !lean_is_exclusive(v_a_3265_);
if (v_isSharedCheck_3287_ == 0)
{
lean_object* v_unused_3288_; 
v_unused_3288_ = lean_ctor_get(v_a_3265_, 2);
lean_dec(v_unused_3288_);
v___x_3273_ = v_a_3265_;
v_isShared_3274_ = v_isSharedCheck_3287_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_kind_3271_);
lean_inc(v_task_3270_);
lean_dec(v_a_3265_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3287_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v_registeredJobs_3275_; lean_object* v_job_3277_; 
v_registeredJobs_3275_ = lean_ctor_get(v_a_3242_, 4);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 2, v___x_3256_);
v_job_3277_ = v___x_3273_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_task_3270_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_kind_3271_);
lean_ctor_set(v_reuseFailAlloc_3286_, 2, v___x_3256_);
v_job_3277_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3284_; 
lean_ctor_set_uint8(v_job_3277_, sizeof(void*)*3, v___x_3263_);
v___x_3278_ = lean_st_ref_take(v_registeredJobs_3275_);
lean_inc_ref(v_job_3277_);
v___x_3279_ = l_Lake_Job_toOpaque___redArg(v_job_3277_);
v___x_3280_ = lean_array_push(v___x_3278_, v___x_3279_);
v___x_3281_ = lean_st_ref_put(v_registeredJobs_3275_, v___x_3280_);
v___x_3282_ = l_Lake_Job_renew___redArg(v_job_3277_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v___x_3282_);
v___x_3284_ = v___x_3268_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3282_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_a_3266_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3256_);
return v___x_3264_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object* v_self_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_){
_start:
{
lean_object* v_res_3298_; 
v_res_3298_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_);
lean_dec_ref(v_a_3295_);
lean_dec(v_a_3294_);
lean_dec(v_a_3293_);
lean_dec(v_a_3292_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t v_fmt_3299_, lean_object* v_a_3300_){
_start:
{
if (v_fmt_3299_ == 0)
{
lean_object* v_path_3301_; 
v_path_3301_ = lean_ctor_get(v_a_3300_, 0);
lean_inc_ref(v_path_3301_);
return v_path_3301_;
}
else
{
lean_object* v_path_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_path_3302_ = lean_ctor_get(v_a_3300_, 0);
lean_inc_ref(v_path_3302_);
v___x_3303_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3303_, 0, v_path_3302_);
v___x_3304_ = l_Lean_Json_compress(v___x_3303_);
return v___x_3304_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* v_fmt_3305_, lean_object* v_a_3306_){
_start:
{
uint8_t v_fmt_boxed_3307_; lean_object* v_res_3308_; 
v_fmt_boxed_3307_ = lean_unbox(v_fmt_3305_);
v_res_3308_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_boxed_3307_, v_a_3306_);
lean_dec_ref(v_a_3306_);
return v_res_3308_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3311_; uint8_t v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___f_3311_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__0));
v___x_3312_ = 1;
v___x_3313_ = l_Lake_instDataKindDynlib;
v___x_3314_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__1));
v___x_3315_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3316_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
lean_ctor_set(v___x_3316_, 1, v___x_3314_);
lean_ctor_set(v___x_3316_, 2, v___x_3313_);
lean_ctor_set(v___x_3316_, 3, v___f_3311_);
lean_ctor_set_uint8(v___x_3316_, sizeof(void*)*4, v___x_3312_);
lean_ctor_set_uint8(v___x_3316_, sizeof(void*)*4 + 1, v___x_3312_);
return v___x_3316_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = lean_obj_once(&l_Lake_LeanLib_sharedFacetConfig___closed__2, &l_Lake_LeanLib_sharedFacetConfig___closed__2_once, _init_l_Lake_LeanLib_sharedFacetConfig___closed__2);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* v___x_3318_, lean_object* v_as_3319_, size_t v_sz_3320_, size_t v_i_3321_, lean_object* v_b_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
uint8_t v___x_3330_; 
v___x_3330_ = lean_usize_dec_lt(v_i_3321_, v_sz_3320_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; 
lean_dec_ref(v___y_3323_);
lean_dec_ref(v___x_3318_);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v_b_3322_);
lean_ctor_set(v___x_3331_, 1, v___y_3328_);
return v___x_3331_;
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3333_; 
v_a_3332_ = lean_array_uget_borrowed(v_as_3319_, v_i_3321_);
lean_inc_ref(v___y_3323_);
lean_inc_n(v_a_3332_, 2);
lean_inc_ref(v___x_3318_);
v___x_3333_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v___x_3318_, v_a_3332_, v_a_3332_, v___x_3330_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v_a_3335_; lean_object* v_snd_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; size_t v___x_3339_; size_t v___x_3340_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_a_3334_);
v_a_3335_ = lean_ctor_get(v___x_3333_, 1);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___x_3333_, 2);
v_snd_3336_ = lean_ctor_get(v_a_3334_, 1);
lean_inc(v_snd_3336_);
lean_dec(v_a_3334_);
v___x_3337_ = l_Lake_Job_toOpaque___redArg(v_snd_3336_);
v___x_3338_ = l_Lake_Job_mix___redArg(v_b_3322_, v___x_3337_);
v___x_3339_ = ((size_t)1ULL);
v___x_3340_ = lean_usize_add(v_i_3321_, v___x_3339_);
v_i_3321_ = v___x_3340_;
v_b_3322_ = v___x_3338_;
v___y_3328_ = v_a_3335_;
goto _start;
}
else
{
lean_object* v_a_3342_; lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec_ref(v___y_3323_);
lean_dec_ref(v_b_3322_);
lean_dec_ref(v___x_3318_);
v_a_3342_ = lean_ctor_get(v___x_3333_, 0);
v_a_3343_ = lean_ctor_get(v___x_3333_, 1);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3333_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_inc(v_a_3342_);
lean_dec(v___x_3333_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3342_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* v___x_3351_, lean_object* v_as_3352_, lean_object* v_sz_3353_, lean_object* v_i_3354_, lean_object* v_b_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
size_t v_sz_boxed_3363_; size_t v_i_boxed_3364_; lean_object* v_res_3365_; 
v_sz_boxed_3363_ = lean_unbox_usize(v_sz_3353_);
lean_dec(v_sz_3353_);
v_i_boxed_3364_ = lean_unbox_usize(v_i_3354_);
lean_dec(v_i_3354_);
v_res_3365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_3351_, v_as_3352_, v_sz_boxed_3363_, v_i_boxed_3364_, v_b_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec_ref(v_as_3352_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* v___x_3366_, lean_object* v_as_3367_, size_t v_sz_3368_, size_t v_i_3369_, lean_object* v_b_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_){
_start:
{
uint8_t v___x_3378_; 
v___x_3378_ = lean_usize_dec_lt(v_i_3369_, v_sz_3368_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; 
lean_dec_ref(v___y_3371_);
lean_dec_ref(v___x_3366_);
v___x_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3379_, 0, v_b_3370_);
lean_ctor_set(v___x_3379_, 1, v___y_3376_);
return v___x_3379_;
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3381_; 
v_a_3380_ = lean_array_uget_borrowed(v_as_3367_, v_i_3369_);
lean_inc_ref(v___y_3371_);
lean_inc(v_a_3380_);
lean_inc_ref(v___x_3366_);
v___x_3381_ = l_Lake_Package_fetchTargetJob(v___x_3366_, v_a_3380_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v_a_3383_; lean_object* v___x_3384_; size_t v___x_3385_; size_t v___x_3386_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
v_a_3383_ = lean_ctor_get(v___x_3381_, 1);
lean_inc(v_a_3383_);
lean_dec_ref_known(v___x_3381_, 2);
v___x_3384_ = l_Lake_Job_mix___redArg(v_b_3370_, v_a_3382_);
v___x_3385_ = ((size_t)1ULL);
v___x_3386_ = lean_usize_add(v_i_3369_, v___x_3385_);
v_i_3369_ = v___x_3386_;
v_b_3370_ = v___x_3384_;
v___y_3376_ = v_a_3383_;
goto _start;
}
else
{
lean_object* v_a_3388_; lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec_ref(v___y_3371_);
lean_dec_ref(v_b_3370_);
lean_dec_ref(v___x_3366_);
v_a_3388_ = lean_ctor_get(v___x_3381_, 0);
v_a_3389_ = lean_ctor_get(v___x_3381_, 1);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3381_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_inc(v_a_3388_);
lean_dec(v___x_3381_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3388_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* v___x_3397_, lean_object* v_as_3398_, lean_object* v_sz_3399_, lean_object* v_i_3400_, lean_object* v_b_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
size_t v_sz_boxed_3409_; size_t v_i_boxed_3410_; lean_object* v_res_3411_; 
v_sz_boxed_3409_ = lean_unbox_usize(v_sz_3399_);
lean_dec(v_sz_3399_);
v_i_boxed_3410_ = lean_unbox_usize(v_i_3400_);
lean_dec(v_i_3400_);
v_res_3411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_3397_, v_as_3398_, v_sz_boxed_3409_, v_i_boxed_3410_, v_b_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v_as_3398_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object* v_self_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_){
_start:
{
lean_object* v_pkg_3422_; lean_object* v_name_3423_; lean_object* v_config_3424_; lean_object* v_baseName_3425_; lean_object* v_keyName_3426_; uint8_t v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; uint8_t v___x_3439_; uint8_t v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v_job_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v_pkg_3422_ = lean_ctor_get(v_self_3414_, 0);
lean_inc_ref_n(v_pkg_3422_, 2);
v_name_3423_ = lean_ctor_get(v_self_3414_, 1);
lean_inc(v_name_3423_);
v_config_3424_ = lean_ctor_get(v_self_3414_, 2);
lean_inc(v_config_3424_);
lean_dec_ref(v_self_3414_);
v_baseName_3425_ = lean_ctor_get(v_pkg_3422_, 1);
v_keyName_3426_ = lean_ctor_get(v_pkg_3422_, 2);
v___x_3427_ = 1;
lean_inc(v_baseName_3425_);
v___x_3428_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3425_, v___x_3427_);
v___x_3429_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0));
v___x_3430_ = lean_string_append(v___x_3428_, v___x_3429_);
v___x_3431_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3423_, v___x_3427_);
v___x_3432_ = lean_string_append(v___x_3430_, v___x_3431_);
lean_dec_ref(v___x_3431_);
v___x_3433_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1));
v___x_3434_ = lean_string_append(v___x_3432_, v___x_3433_);
v___x_3435_ = lean_box(0);
v___x_3436_ = lean_box(0);
v___x_3437_ = lean_unsigned_to_nat(0u);
v___x_3438_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__0));
v___x_3439_ = 0;
v___x_3440_ = 0;
v___x_3441_ = l_Lake_BuildTrace_nil(v___x_3434_);
v___x_3442_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3442_, 0, v___x_3438_);
lean_ctor_set(v___x_3442_, 1, v___x_3441_);
lean_ctor_set(v___x_3442_, 2, v___x_3437_);
lean_ctor_set_uint8(v___x_3442_, sizeof(void*)*3, v___x_3439_);
lean_ctor_set_uint8(v___x_3442_, sizeof(void*)*3 + 1, v___x_3440_);
lean_ctor_set_uint8(v___x_3442_, sizeof(void*)*3 + 2, v___x_3440_);
v___x_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3435_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = lean_task_pure(v___x_3443_);
v___x_3445_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v_job_3446_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_3446_, 0, v___x_3444_);
lean_ctor_set(v_job_3446_, 1, v___x_3436_);
lean_ctor_set(v_job_3446_, 2, v___x_3445_);
lean_ctor_set_uint8(v_job_3446_, sizeof(void*)*3, v___x_3440_);
v___x_3447_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_3426_);
v___x_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3448_, 0, v_keyName_3426_);
v___x_3449_ = l_Lake_Package_keyword;
v___x_3450_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3448_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
lean_ctor_set(v___x_3450_, 2, v_pkg_3422_);
lean_ctor_set(v___x_3450_, 3, v___x_3447_);
lean_inc_ref(v_a_3415_);
lean_inc_ref(v_a_3419_);
lean_inc(v_a_3418_);
lean_inc(v_a_3417_);
lean_inc(v_a_3416_);
v___x_3451_ = lean_apply_7(v_a_3415_, v___x_3450_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, lean_box(0));
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v_a_3453_; lean_object* v_needs_3454_; lean_object* v_extraDepTargets_3455_; lean_object* v___x_3456_; size_t v_sz_3457_; size_t v___x_3458_; lean_object* v___x_3459_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
v_a_3453_ = lean_ctor_get(v___x_3451_, 1);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3451_, 2);
v_needs_3454_ = lean_ctor_get(v_config_3424_, 5);
lean_inc_ref(v_needs_3454_);
v_extraDepTargets_3455_ = lean_ctor_get(v_config_3424_, 6);
lean_inc_ref(v_extraDepTargets_3455_);
lean_dec(v_config_3424_);
v___x_3456_ = l_Lake_Job_mix___redArg(v_job_3446_, v_a_3452_);
v_sz_3457_ = lean_array_size(v_extraDepTargets_3455_);
v___x_3458_ = ((size_t)0ULL);
lean_inc_ref(v_a_3415_);
lean_inc_ref(v_pkg_3422_);
v___x_3459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_3422_, v_extraDepTargets_3455_, v_sz_3457_, v___x_3458_, v___x_3456_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3453_);
lean_dec_ref(v_extraDepTargets_3455_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v_a_3461_; size_t v_sz_3462_; lean_object* v___x_3463_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
v_a_3461_ = lean_ctor_get(v___x_3459_, 1);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3459_, 2);
v_sz_3462_ = lean_array_size(v_needs_3454_);
v___x_3463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_3422_, v_needs_3454_, v_sz_3462_, v___x_3458_, v_a_3460_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3461_);
lean_dec_ref(v_needs_3454_);
return v___x_3463_;
}
else
{
lean_dec_ref(v_needs_3454_);
lean_dec_ref(v_pkg_3422_);
lean_dec_ref(v_a_3415_);
return v___x_3459_;
}
}
else
{
lean_dec_ref_known(v_job_3446_, 3);
lean_dec(v_config_3424_);
lean_dec_ref(v_pkg_3422_);
lean_dec_ref(v_a_3415_);
return v___x_3451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object* v_self_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
lean_dec_ref(v_a_3469_);
lean_dec(v_a_3468_);
lean_dec(v_a_3467_);
lean_dec(v_a_3466_);
return v_res_3472_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3474_; uint8_t v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___f_3474_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_3475_ = 1;
v___x_3476_ = l_Lake_instDataKindUnit;
v___x_3477_ = ((lean_object*)(l_Lake_LeanLib_extraDepFacetConfig___closed__0));
v___x_3478_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3479_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
lean_ctor_set(v___x_3479_, 1, v___x_3477_);
lean_ctor_set(v___x_3479_, 2, v___x_3476_);
lean_ctor_set(v___x_3479_, 3, v___f_3474_);
lean_ctor_set_uint8(v___x_3479_, sizeof(void*)*4, v___x_3475_);
lean_ctor_set_uint8(v___x_3479_, sizeof(void*)*4 + 1, v___x_3475_);
return v___x_3479_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = lean_obj_once(&l_Lake_LeanLib_extraDepFacetConfig___closed__1, &l_Lake_LeanLib_extraDepFacetConfig___closed__1_once, _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* v_self_3481_, size_t v_sz_3482_, size_t v_i_3483_, lean_object* v_bs_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
uint8_t v___x_3492_; 
v___x_3492_ = lean_usize_dec_lt(v_i_3483_, v_sz_3482_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; 
lean_dec_ref(v___y_3485_);
lean_dec_ref(v_self_3481_);
v___x_3493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3493_, 0, v_bs_3484_);
lean_ctor_set(v___x_3493_, 1, v___y_3490_);
return v___x_3493_;
}
else
{
lean_object* v_pkg_3494_; lean_object* v_name_3495_; lean_object* v_keyName_3496_; lean_object* v_v_3497_; lean_object* v___x_3498_; lean_object* v_bs_x27_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v_pkg_3494_ = lean_ctor_get(v_self_3481_, 0);
v_name_3495_ = lean_ctor_get(v_self_3481_, 1);
v_keyName_3496_ = lean_ctor_get(v_pkg_3494_, 2);
v_v_3497_ = lean_array_uget(v_bs_3484_, v_i_3483_);
v___x_3498_ = lean_unsigned_to_nat(0u);
v_bs_x27_3499_ = lean_array_uset(v_bs_3484_, v_i_3483_, v___x_3498_);
lean_inc(v_name_3495_);
lean_inc(v_keyName_3496_);
v___x_3500_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3500_, 0, v_keyName_3496_);
lean_ctor_set(v___x_3500_, 1, v_name_3495_);
v___x_3501_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3481_);
v___x_3502_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3500_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
lean_ctor_set(v___x_3502_, 2, v_self_3481_);
lean_ctor_set(v___x_3502_, 3, v_v_3497_);
lean_inc_ref(v___y_3485_);
lean_inc_ref(v___y_3489_);
lean_inc(v___y_3488_);
lean_inc(v___y_3487_);
lean_inc(v___y_3486_);
v___x_3503_ = lean_apply_7(v___y_3485_, v___x_3502_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, lean_box(0));
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v_a_3505_; lean_object* v___x_3506_; size_t v___x_3507_; size_t v___x_3508_; lean_object* v___x_3509_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
v_a_3505_ = lean_ctor_get(v___x_3503_, 1);
lean_inc(v_a_3505_);
lean_dec_ref_known(v___x_3503_, 2);
v___x_3506_ = l_Lake_Job_toOpaque___redArg(v_a_3504_);
v___x_3507_ = ((size_t)1ULL);
v___x_3508_ = lean_usize_add(v_i_3483_, v___x_3507_);
v___x_3509_ = lean_array_uset(v_bs_x27_3499_, v_i_3483_, v___x_3506_);
v_i_3483_ = v___x_3508_;
v_bs_3484_ = v___x_3509_;
v___y_3490_ = v_a_3505_;
goto _start;
}
else
{
lean_object* v_a_3511_; lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec_ref(v_bs_x27_3499_);
lean_dec_ref(v___y_3485_);
lean_dec_ref(v_self_3481_);
v_a_3511_ = lean_ctor_get(v___x_3503_, 0);
v_a_3512_ = lean_ctor_get(v___x_3503_, 1);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3503_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_inc(v_a_3511_);
lean_dec(v___x_3503_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3511_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* v_self_3520_, lean_object* v_sz_3521_, lean_object* v_i_3522_, lean_object* v_bs_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
size_t v_sz_boxed_3531_; size_t v_i_boxed_3532_; lean_object* v_res_3533_; 
v_sz_boxed_3531_ = lean_unbox_usize(v_sz_3521_);
lean_dec(v_sz_3521_);
v_i_boxed_3532_ = lean_unbox_usize(v_i_3522_);
lean_dec(v_i_3522_);
v_res_3533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3520_, v_sz_boxed_3531_, v_i_boxed_3532_, v_bs_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec(v___y_3525_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object* v_self_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_config_3543_; lean_object* v_defaultFacets_3544_; size_t v_sz_3545_; size_t v___x_3546_; lean_object* v___x_3547_; 
v_config_3543_ = lean_ctor_get(v_self_3535_, 2);
v_defaultFacets_3544_ = lean_ctor_get(v_config_3543_, 7);
lean_inc_ref(v_defaultFacets_3544_);
v_sz_3545_ = lean_array_size(v_defaultFacets_3544_);
v___x_3546_ = ((size_t)0ULL);
v___x_3547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3535_, v_sz_3545_, v___x_3546_, v_defaultFacets_3544_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3558_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
v_a_3549_ = lean_ctor_get(v___x_3547_, 1);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3551_ = v___x_3547_;
v_isShared_3552_ = v_isSharedCheck_3558_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_inc(v_a_3548_);
lean_dec(v___x_3547_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3558_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3553_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0));
v___x_3554_ = l_Lake_Job_mixArray___redArg(v_a_3548_, v___x_3553_);
lean_dec(v_a_3548_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3554_);
v___x_3556_ = v___x_3551_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3554_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_a_3549_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
v_a_3559_ = lean_ctor_get(v___x_3547_, 0);
v_a_3560_ = lean_ctor_get(v___x_3547_, 1);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3547_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_inc(v_a_3559_);
lean_dec(v___x_3547_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3559_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_a_3560_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object* v_self_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
lean_dec_ref(v_a_3573_);
lean_dec(v_a_3572_);
lean_dec(v_a_3571_);
lean_dec(v_a_3570_);
return v_res_3576_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3578_; uint8_t v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___f_3578_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_3579_ = 1;
v___x_3580_ = l_Lake_instDataKindUnit;
v___x_3581_ = ((lean_object*)(l_Lake_LeanLib_defaultFacetConfig___closed__0));
v___x_3582_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3583_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
lean_ctor_set(v___x_3583_, 1, v___x_3581_);
lean_ctor_set(v___x_3583_, 2, v___x_3580_);
lean_ctor_set(v___x_3583_, 3, v___f_3578_);
lean_ctor_set_uint8(v___x_3583_, sizeof(void*)*4, v___x_3579_);
lean_ctor_set_uint8(v___x_3583_, sizeof(void*)*4 + 1, v___x_3579_);
return v___x_3583_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = lean_obj_once(&l_Lake_LeanLib_defaultFacetConfig___closed__1, &l_Lake_LeanLib_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanLib_defaultFacetConfig___closed__1);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_3585_, lean_object* v_v_3586_, lean_object* v_t_3587_){
_start:
{
if (lean_obj_tag(v_t_3587_) == 0)
{
lean_object* v_size_3588_; lean_object* v_k_3589_; lean_object* v_v_3590_; lean_object* v_l_3591_; lean_object* v_r_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3872_; 
v_size_3588_ = lean_ctor_get(v_t_3587_, 0);
v_k_3589_ = lean_ctor_get(v_t_3587_, 1);
v_v_3590_ = lean_ctor_get(v_t_3587_, 2);
v_l_3591_ = lean_ctor_get(v_t_3587_, 3);
v_r_3592_ = lean_ctor_get(v_t_3587_, 4);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_t_3587_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3594_ = v_t_3587_;
v_isShared_3595_ = v_isSharedCheck_3872_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_r_3592_);
lean_inc(v_l_3591_);
lean_inc(v_v_3590_);
lean_inc(v_k_3589_);
lean_inc(v_size_3588_);
lean_dec(v_t_3587_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3872_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
uint8_t v___x_3596_; 
v___x_3596_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3585_, v_k_3589_);
switch(v___x_3596_)
{
case 0:
{
lean_object* v_impl_3597_; lean_object* v___x_3598_; 
lean_dec(v_size_3588_);
v_impl_3597_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3585_, v_v_3586_, v_l_3591_);
v___x_3598_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3592_) == 0)
{
lean_object* v_size_3599_; lean_object* v_size_3600_; lean_object* v_k_3601_; lean_object* v_v_3602_; lean_object* v_l_3603_; lean_object* v_r_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; 
v_size_3599_ = lean_ctor_get(v_r_3592_, 0);
v_size_3600_ = lean_ctor_get(v_impl_3597_, 0);
v_k_3601_ = lean_ctor_get(v_impl_3597_, 1);
v_v_3602_ = lean_ctor_get(v_impl_3597_, 2);
v_l_3603_ = lean_ctor_get(v_impl_3597_, 3);
v_r_3604_ = lean_ctor_get(v_impl_3597_, 4);
lean_inc(v_r_3604_);
v___x_3605_ = lean_unsigned_to_nat(3u);
v___x_3606_ = lean_nat_mul(v___x_3605_, v_size_3599_);
v___x_3607_ = lean_nat_dec_lt(v___x_3606_, v_size_3600_);
lean_dec(v___x_3606_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3611_; 
lean_dec(v_r_3604_);
v___x_3608_ = lean_nat_add(v___x_3598_, v_size_3600_);
v___x_3609_ = lean_nat_add(v___x_3608_, v_size_3599_);
lean_dec(v___x_3608_);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 3, v_impl_3597_);
lean_ctor_set(v___x_3594_, 0, v___x_3609_);
v___x_3611_ = v___x_3594_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3609_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_k_3589_);
lean_ctor_set(v_reuseFailAlloc_3612_, 2, v_v_3590_);
lean_ctor_set(v_reuseFailAlloc_3612_, 3, v_impl_3597_);
lean_ctor_set(v_reuseFailAlloc_3612_, 4, v_r_3592_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
else
{
lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3678_; 
lean_inc(v_l_3603_);
lean_inc(v_v_3602_);
lean_inc(v_k_3601_);
lean_inc(v_size_3600_);
v_isSharedCheck_3678_ = !lean_is_exclusive(v_impl_3597_);
if (v_isSharedCheck_3678_ == 0)
{
lean_object* v_unused_3679_; lean_object* v_unused_3680_; lean_object* v_unused_3681_; lean_object* v_unused_3682_; lean_object* v_unused_3683_; 
v_unused_3679_ = lean_ctor_get(v_impl_3597_, 4);
lean_dec(v_unused_3679_);
v_unused_3680_ = lean_ctor_get(v_impl_3597_, 3);
lean_dec(v_unused_3680_);
v_unused_3681_ = lean_ctor_get(v_impl_3597_, 2);
lean_dec(v_unused_3681_);
v_unused_3682_ = lean_ctor_get(v_impl_3597_, 1);
lean_dec(v_unused_3682_);
v_unused_3683_ = lean_ctor_get(v_impl_3597_, 0);
lean_dec(v_unused_3683_);
v___x_3614_ = v_impl_3597_;
v_isShared_3615_ = v_isSharedCheck_3678_;
goto v_resetjp_3613_;
}
else
{
lean_dec(v_impl_3597_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3678_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v_size_3616_; lean_object* v_size_3617_; lean_object* v_k_3618_; lean_object* v_v_3619_; lean_object* v_l_3620_; lean_object* v_r_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; uint8_t v___x_3624_; 
v_size_3616_ = lean_ctor_get(v_l_3603_, 0);
v_size_3617_ = lean_ctor_get(v_r_3604_, 0);
v_k_3618_ = lean_ctor_get(v_r_3604_, 1);
v_v_3619_ = lean_ctor_get(v_r_3604_, 2);
v_l_3620_ = lean_ctor_get(v_r_3604_, 3);
v_r_3621_ = lean_ctor_get(v_r_3604_, 4);
v___x_3622_ = lean_unsigned_to_nat(2u);
v___x_3623_ = lean_nat_mul(v___x_3622_, v_size_3616_);
v___x_3624_ = lean_nat_dec_lt(v_size_3617_, v___x_3623_);
lean_dec(v___x_3623_);
if (v___x_3624_ == 0)
{
lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3653_; 
lean_inc(v_r_3621_);
lean_inc(v_l_3620_);
lean_inc(v_v_3619_);
lean_inc(v_k_3618_);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_r_3604_);
if (v_isSharedCheck_3653_ == 0)
{
lean_object* v_unused_3654_; lean_object* v_unused_3655_; lean_object* v_unused_3656_; lean_object* v_unused_3657_; lean_object* v_unused_3658_; 
v_unused_3654_ = lean_ctor_get(v_r_3604_, 4);
lean_dec(v_unused_3654_);
v_unused_3655_ = lean_ctor_get(v_r_3604_, 3);
lean_dec(v_unused_3655_);
v_unused_3656_ = lean_ctor_get(v_r_3604_, 2);
lean_dec(v_unused_3656_);
v_unused_3657_ = lean_ctor_get(v_r_3604_, 1);
lean_dec(v_unused_3657_);
v_unused_3658_ = lean_ctor_get(v_r_3604_, 0);
lean_dec(v_unused_3658_);
v___x_3626_ = v_r_3604_;
v_isShared_3627_ = v_isSharedCheck_3653_;
goto v_resetjp_3625_;
}
else
{
lean_dec(v_r_3604_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3653_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___x_3641_; lean_object* v___y_3643_; 
v___x_3628_ = lean_nat_add(v___x_3598_, v_size_3600_);
lean_dec(v_size_3600_);
v___x_3629_ = lean_nat_add(v___x_3628_, v_size_3599_);
lean_dec(v___x_3628_);
v___x_3641_ = lean_nat_add(v___x_3598_, v_size_3616_);
if (lean_obj_tag(v_l_3620_) == 0)
{
lean_object* v_size_3651_; 
v_size_3651_ = lean_ctor_get(v_l_3620_, 0);
lean_inc(v_size_3651_);
v___y_3643_ = v_size_3651_;
goto v___jp_3642_;
}
else
{
lean_object* v___x_3652_; 
v___x_3652_ = lean_unsigned_to_nat(0u);
v___y_3643_ = v___x_3652_;
goto v___jp_3642_;
}
v___jp_3630_:
{
lean_object* v___x_3634_; lean_object* v___x_3636_; 
v___x_3634_ = lean_nat_add(v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec(v___y_3632_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 4, v_r_3592_);
lean_ctor_set(v___x_3626_, 3, v_r_3621_);
lean_ctor_set(v___x_3626_, 2, v_v_3590_);
lean_ctor_set(v___x_3626_, 1, v_k_3589_);
lean_ctor_set(v___x_3626_, 0, v___x_3634_);
v___x_3636_ = v___x_3626_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3640_, 1, v_k_3589_);
lean_ctor_set(v_reuseFailAlloc_3640_, 2, v_v_3590_);
lean_ctor_set(v_reuseFailAlloc_3640_, 3, v_r_3621_);
lean_ctor_set(v_reuseFailAlloc_3640_, 4, v_r_3592_);
v___x_3636_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3638_; 
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 4, v___x_3636_);
lean_ctor_set(v___x_3614_, 3, v___y_3631_);
lean_ctor_set(v___x_3614_, 2, v_v_3619_);
lean_ctor_set(v___x_3614_, 1, v_k_3618_);
lean_ctor_set(v___x_3614_, 0, v___x_3629_);
v___x_3638_ = v___x_3614_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3629_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_k_3618_);
lean_ctor_set(v_reuseFailAlloc_3639_, 2, v_v_3619_);
lean_ctor_set(v_reuseFailAlloc_3639_, 3, v___y_3631_);
lean_ctor_set(v_reuseFailAlloc_3639_, 4, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
v___jp_3642_:
{
lean_object* v___x_3644_; lean_object* v___x_3646_; 
v___x_3644_ = lean_nat_add(v___x_3641_, v___y_3643_);
lean_dec(v___y_3643_);
lean_dec(v___x_3641_);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 4, v_l_3620_);
lean_ctor_set(v___x_3594_, 3, v_l_3603_);
lean_ctor_set(v___x_3594_, 2, v_v_3602_);
lean_ctor_set(v___x_3594_, 1, v_k_3601_);
lean_ctor_set(v___x_3594_, 0, v___x_3644_);
v___x_3646_ = v___x_3594_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3644_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_k_3601_);
lean_ctor_set(v_reuseFailAlloc_3650_, 2, v_v_3602_);
lean_ctor_set(v_reuseFailAlloc_3650_, 3, v_l_3603_);
lean_ctor_set(v_reuseFailAlloc_3650_, 4, v_l_3620_);
v___x_3646_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
lean_object* v___x_3647_; 
v___x_3647_ = lean_nat_add(v___x_3598_, v_size_3599_);
if (lean_obj_tag(v_r_3621_) == 0)
{
lean_object* v_size_3648_; 
v_size_3648_ = lean_ctor_get(v_r_3621_, 0);
lean_inc(v_size_3648_);
v___y_3631_ = v___x_3646_;
v___y_3632_ = v___x_3647_;
v___y_3633_ = v_size_3648_;
goto v___jp_3630_;
}
else
{
lean_object* v___x_3649_; 
v___x_3649_ = lean_unsigned_to_nat(0u);
v___y_3631_ = v___x_3646_;
v___y_3632_ = v___x_3647_;
v___y_3633_ = v___x_3649_;
goto v___jp_3630_;
}
}
}
}
}
else
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3664_; 
lean_del_object(v___x_3594_);
v___x_3659_ = lean_nat_add(v___x_3598_, v_size_3600_);
lean_dec(v_size_3600_);
v___x_3660_ = lean_nat_add(v___x_3659_, v_size_3599_);
lean_dec(v___x_3659_);
v___x_3661_ = lean_nat_add(v___x_3598_, v_size_3599_);
v___x_3662_ = lean_nat_add(v___x_3661_, v_size_3617_);
lean_dec(v___x_3661_);
lean_inc_ref(v_r_3592_);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 4, v_r_3592_);
lean_ctor_set(v___x_3614_, 3, v_r_3604_);
lean_ctor_set(v___x_3614_, 2, v_v_3590_);
lean_ctor_set(v___x_3614_, 1, v_k_3589_);
lean_ctor_set(v___x_3614_, 0, v___x_3662_);
v___x_3664_ = v___x_3614_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v_k_3589_);
lean_ctor_set(v_reuseFailAlloc_3677_, 2, v_v_3590_);
lean_ctor_set(v_reuseFailAlloc_3677_, 3, v_r_3604_);
lean_ctor_set(v_reuseFailAlloc_3677_, 4, v_r_3592_);
v___x_3664_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
v_isSharedCheck_3671_ = !lean_is_exclusive(v_r_3592_);
if (v_isSharedCheck_3671_ == 0)
{
lean_object* v_unused_3672_; lean_object* v_unused_3673_; lean_object* v_unused_3674_; lean_object* v_unused_3675_; lean_object* v_unused_3676_; 
v_unused_3672_ = lean_ctor_get(v_r_3592_, 4);
lean_dec(v_unused_3672_);
v_unused_3673_ = lean_ctor_get(v_r_3592_, 3);
lean_dec(v_unused_3673_);
v_unused_3674_ = lean_ctor_get(v_r_3592_, 2);
lean_dec(v_unused_3674_);
v_unused_3675_ = lean_ctor_get(v_r_3592_, 1);
lean_dec(v_unused_3675_);
v_unused_3676_ = lean_ctor_get(v_r_3592_, 0);
lean_dec(v_unused_3676_);
v___x_3666_ = v_r_3592_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_dec(v_r_3592_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 4, v___x_3664_);
lean_ctor_set(v___x_3666_, 3, v_l_3603_);
lean_ctor_set(v___x_3666_, 2, v_v_3602_);
lean_ctor_set(v___x_3666_, 1, v_k_3601_);
lean_ctor_set(v___x_3666_, 0, v___x_3660_);
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_k_3601_);
lean_ctor_set(v_reuseFailAlloc_3670_, 2, v_v_3602_);
lean_ctor_set(v_reuseFailAlloc_3670_, 3, v_l_3603_);
lean_ctor_set(v_reuseFailAlloc_3670_, 4, v___x_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3684_; 
v_l_3684_ = lean_ctor_get(v_impl_3597_, 3);
if (lean_obj_tag(v_l_3684_) == 0)
{
lean_object* v_r_3685_; lean_object* v_k_3686_; lean_object* v_v_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3698_; 
lean_inc_ref(v_l_3684_);
v_r_3685_ = lean_ctor_get(v_impl_3597_, 4);
v_k_3686_ = lean_ctor_get(v_impl_3597_, 1);
v_v_3687_ = lean_ctor_get(v_impl_3597_, 2);
v_isSharedCheck_3698_ = !lean_is_exclusive(v_impl_3597_);
if (v_isSharedCheck_3698_ == 0)
{
lean_object* v_unused_3699_; lean_object* v_unused_3700_; 
v_unused_3699_ = lean_ctor_get(v_impl_3597_, 3);
lean_dec(v_unused_3699_);
v_unused_3700_ = lean_ctor_get(v_impl_3597_, 0);
lean_dec(v_unused_3700_);
v___x_3689_ = v_impl_3597_;
v_isShared_3690_ = v_isSharedCheck_3698_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_r_3685_);
lean_inc(v_v_3687_);
lean_inc(v_k_3686_);
lean_dec(v_impl_3597_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3698_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3691_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3685_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 3, v_r_3685_);
lean_ctor_set(v___x_3689_, 2, v_v_3590_);
lean_ctor_set(v___x_3689_, 1, v_k_3589_);
lean_ctor_set(v___x_3689_, 0, v___x_3598_);
v___x_3693_ = v___x_3689_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3598_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_k_3589_);
lean_ctor_set(v_reuseFailAlloc_3697_, 2, v_v_3590_);
lean_ctor_set(v_reuseFailAlloc_3697_, 3, v_r_3685_);
lean_ctor_set(v_reuseFailAlloc_3697_, 4, v_r_3685_);
v___x_3693_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3695_; 
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 4, v___x_3693_);
lean_ctor_set(v___x_3594_, 3, v_l_3684_);
lean_ctor_set(v___x_3594_, 2, v_v_3687_);
lean_ctor_set(v___x_3594_, 1, v_k_3686_);
lean_ctor_set(v___x_3594_, 0, v___x_3691_);
v___x_3695_ = v___x_3594_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_k_3686_);
lean_ctor_set(v_reuseFailAlloc_3696_, 2, v_v_3687_);
lean_ctor_set(v_reuseFailAlloc_3696_, 3, v_l_3684_);
lean_ctor_set(v_reuseFailAlloc_3696_, 4, v___x_3693_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
else
{
lean_object* v_r_3701_; 
v_r_3701_ = lean_ctor_get(v_impl_3597_, 4);
lean_inc(v_r_3701_);
if (lean_obj_tag(v_r_3701_) == 0)
{
lean_object* v_k_3702_; lean_object* v_v_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3726_; 
lean_inc(v_l_3684_);
v_k_3702_ = lean_ctor_get(v_impl_3597_, 1);
v_v_3703_ = lean_ctor_get(v_impl_3597_, 2);
v_isSharedCheck_3726_ = !lean_is_exclusive(v_impl_3597_);
if (v_isSharedCheck_3726_ == 0)
{
lean_object* v_unused_3727_; lean_object* v_unused_3728_; lean_object* v_unused_3729_; 
v_unused_3727_ = lean_ctor_get(v_impl_3597_, 4);
lean_dec(v_unused_3727_);
v_unused_3728_ = lean_ctor_get(v_impl_3597_, 3);
lean_dec(v_unused_3728_);
v_unused_3729_ = lean_ctor_get(v_impl_3597_, 0);
lean_dec(v_unused_3729_);
v___x_3705_ = v_impl_3597_;
v_isShared_3706_ = v_isSharedCheck_3726_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_v_3703_);
lean_inc(v_k_3702_);
lean_dec(v_impl_3597_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3726_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v_k_3707_; lean_object* v_v_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3722_; 
v_k_3707_ = lean_ctor_get(v_r_3701_, 1);
v_v_3708_ = lean_ctor_get(v_r_3701_, 2);
v_isSharedCheck_3722_ = !lean_is_exclusive(v_r_3701_);
if (v_isSharedCheck_3722_ == 0)
{
lean_object* v_unused_3723_; lean_object* v_unused_3724_; lean_object* v_unused_3725_; 
v_unused_3723_ = lean_ctor_get(v_r_3701_, 4);
lean_dec(v_unused_3723_);
v_unused_3724_ = lean_ctor_get(v_r_3701_, 3);
lean_dec(v_unused_3724_);
v_unused_3725_ = lean_ctor_get(v_r_3701_, 0);
lean_dec(v_unused_3725_);
v___x_3710_ = v_r_3701_;
v_isShared_3711_ = v_isSharedCheck_3722_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_v_3708_);
lean_inc(v_k_3707_);
lean_dec(v_r_3701_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3722_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3712_; lean_object* v___x_3714_; 
v___x_3712_ = lean_unsigned_to_nat(3u);
if (v_isShared_3711_ == 0)
{
lean_ctor_set(v___x_3710_, 4, v_l_3684_);
lean_ctor_set(v___x_3710_, 3, v_l_3684_);
lean_ctor_set(v___x_3710_, 2, v_v_3703_);
lean_ctor_set(v___x_3710_, 1, v_k_3702_);
lean_ctor_set(v___x_3710_, 0, v___x_3598_);
v___x_3714_ = v___x_3710_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3598_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_k_3702_);
lean_ctor_set(v_reuseFailAlloc_3721_, 2, v_v_3703_);
lean_ctor_set(v_reuseFailAlloc_3721_, 3, v_l_3684_);
lean_ctor_set(v_reuseFailAlloc_3721_, 4, v_l_3684_);
v___x_3714_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v___x_3716_; 
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 4, v_l_3684_);
lean_ctor_set(v___x_3705_, 2, v_v_3590_);
lean_ctor_set(v___x_3705_, 1, v_k_3589_);
lean_ctor_set(v___x_3705_, 0, v___x_3598_);
v___x_3716_ = v___x_3705_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v___x_3598_);
lean_ctor_set(v_reuseFailAlloc_3720_, 1, v_k_3589_);
lean_ctor_set(v_reuseFailAlloc_3720_, 2, v_v_3590_);
lean_ctor_set(v_reuseFailAlloc_3720_, 3, v_l_3684_);
lean_ctor_set(v_reuseFailAlloc_3720_, 4, v_l_3684_);
v___x_3716_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
lean_object* v___x_3718_; 
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 4, v___x_3716_);
lean_ctor_set(v___x_3594_, 3, v___x_3714_);
lean_ctor_set(v___x_3594_, 2, v_v_3708_);
lean_ctor_set(v___x_3594_, 1, v_k_3707_);
lean_ctor_set(v___x_3594_, 0, v___x_3712_);
v___x_3718_ = v___x_3594_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_k_3707_);
lean_ctor_set(v_reuseFailAlloc_3719_, 2, v_v_3708_);
lean_ctor_set(v_reuseFailAlloc_3719_, 3, v___x_3714_);
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
}
}
}
else
{
lean_object* v___x_3730_; lean_object* v___x_3732_; 
v___x_3730_ = lean_unsigned_to_nat(2u);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 4, v_r_3701_);
lean_ctor_set(v___x_3594_, 3, v_impl_3597_);
lean_ctor_set(v___x_3594_, 0, v___x_3730_);
v___x_3732_ = v___x_3594_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3730_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_k_3589_);
lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_v_3590_);
lean_ctor_set(v_reuseFailAlloc_3733_, 3, v_impl_3597_);
lean_ctor_set(v_reuseFailAlloc_3733_, 4, v_r_3701_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3735_; 
lean_dec(v_v_3590_);
lean_dec(v_k_3589_);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 2, v_v_3586_);
lean_ctor_set(v___x_3594_, 1, v_k_3585_);
v___x_3735_ = v___x_3594_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_size_3588_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v_k_3585_);
lean_ctor_set(v_reuseFailAlloc_3736_, 2, v_v_3586_);
lean_ctor_set(v_reuseFailAlloc_3736_, 3, v_l_3591_);
lean_ctor_set(v_reuseFailAlloc_3736_, 4, v_r_3592_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
default: 
{
lean_object* v_impl_3737_; lean_object* v___x_3738_; 
lean_dec(v_size_3588_);
v_impl_3737_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3585_, v_v_3586_, v_r_3592_);
v___x_3738_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3591_) == 0)
{
lean_object* v_size_3739_; lean_object* v_size_3740_; lean_object* v_k_3741_; lean_object* v_v_3742_; lean_object* v_l_3743_; lean_object* v_r_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; uint8_t v___x_3747_; 
v_size_3739_ = lean_ctor_get(v_l_3591_, 0);
v_size_3740_ = lean_ctor_get(v_impl_3737_, 0);
v_k_3741_ = lean_ctor_get(v_impl_3737_, 1);
v_v_3742_ = lean_ctor_get(v_impl_3737_, 2);
v_l_3743_ = lean_ctor_get(v_impl_3737_, 3);
lean_inc(v_l_3743_);
v_r_3744_ = lean_ctor_get(v_impl_3737_, 4);
v___x_3745_ = lean_unsigned_to_nat(3u);
v___x_3746_ = lean_nat_mul(v___x_3745_, v_size_3739_);
v___x_3747_ = lean_nat_dec_lt(v___x_3746_, v_size_3740_);
lean_dec(v___x_3746_);
if (v___x_3747_ == 0)
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3751_; 
lean_dec(v_l_3743_);
v___x_3748_ = lean_nat_add(v___x_3738_, v_size_3739_);
v___x_3749_ = lean_nat_add(v___x_3748_, v_size_3740_);
lean_dec(v___x_3748_);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 4, v_impl_3737_);
lean_ctor_set(v___x_3594_, 0, v___x_3749_);
v___x_3751_ = v___x_3594_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_k_3589_);
lean_ctor_set(v_reuseFailAlloc_3752_, 2, v_v_3590_);
lean_ctor_set(v_reuseFailAlloc_3752_, 3, v_l_3591_);
lean_ctor_set(v_reuseFailAlloc_3752_, 4, v_impl_3737_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
else
{
lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3816_; 
lean_inc(v_r_3744_);
lean_inc(v_v_3742_);
lean_inc(v_k_3741_);
lean_inc(v_size_3740_);
v_isSharedCheck_3816_ = !lean_is_exclusive(v_impl_3737_);
if (v_isSharedCheck_3816_ == 0)
{
lean_object* v_unused_3817_; lean_object* v_unused_3818_; lean_object* v_unused_3819_; lean_object* v_unused_3820_; lean_object* v_unused_3821_; 
v_unused_3817_ = lean_ctor_get(v_impl_3737_, 4);
lean_dec(v_unused_3817_);
v_unused_3818_ = lean_ctor_get(v_impl_3737_, 3);
lean_dec(v_unused_3818_);
v_unused_3819_ = lean_ctor_get(v_impl_3737_, 2);
lean_dec(v_unused_3819_);
v_unused_3820_ = lean_ctor_get(v_impl_3737_, 1);
lean_dec(v_unused_3820_);
v_unused_3821_ = lean_ctor_get(v_impl_3737_, 0);
lean_dec(v_unused_3821_);
v___x_3754_ = v_impl_3737_;
v_isShared_3755_ = v_isSharedCheck_3816_;
goto v_resetjp_3753_;
}
else
{
lean_dec(v_impl_3737_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3816_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v_size_3756_; lean_object* v_k_3757_; lean_object* v_v_3758_; lean_object* v_l_3759_; lean_object* v_r_3760_; lean_object* v_size_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; 
v_size_3756_ = lean_ctor_get(v_l_3743_, 0);
v_k_3757_ = lean_ctor_get(v_l_3743_, 1);
v_v_3758_ = lean_ctor_get(v_l_3743_, 2);
v_l_3759_ = lean_ctor_get(v_l_3743_, 3);
v_r_3760_ = lean_ctor_get(v_l_3743_, 4);
v_size_3761_ = lean_ctor_get(v_r_3744_, 0);
v___x_3762_ = lean_unsigned_to_nat(2u);
v___x_3763_ = lean_nat_mul(v___x_3762_, v_size_3761_);
v___x_3764_ = lean_nat_dec_lt(v_size_3756_, v___x_3763_);
lean_dec(v___x_3763_);
if (v___x_3764_ == 0)
{
lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3792_; 
lean_inc(v_r_3760_);
lean_inc(v_l_3759_);
lean_inc(v_v_3758_);
lean_inc(v_k_3757_);
v_isSharedCheck_3792_ = !lean_is_exclusive(v_l_3743_);
if (v_isSharedCheck_3792_ == 0)
{
lean_object* v_unused_3793_; lean_object* v_unused_3794_; lean_object* v_unused_3795_; lean_object* v_unused_3796_; lean_object* v_unused_3797_; 
v_unused_3793_ = lean_ctor_get(v_l_3743_, 4);
lean_dec(v_unused_3793_);
v_unused_3794_ = lean_ctor_get(v_l_3743_, 3);
lean_dec(v_unused_3794_);
v_unused_3795_ = lean_ctor_get(v_l_3743_, 2);
lean_dec(v_unused_3795_);
v_unused_3796_ = lean_ctor_get(v_l_3743_, 1);
lean_dec(v_unused_3796_);
v_unused_3797_ = lean_ctor_get(v_l_3743_, 0);
lean_dec(v_unused_3797_);
v___x_3766_ = v_l_3743_;
v_isShared_3767_ = v_isSharedCheck_3792_;
goto v_resetjp_3765_;
}
else
{
lean_dec(v_l_3743_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3792_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3782_; 
v___x_3768_ = lean_nat_add(v___x_3738_, v_size_3739_);
v___x_3769_ = lean_nat_add(v___x_3768_, v_size_3740_);
lean_dec(v_size_3740_);
if (lean_obj_tag(v_l_3759_) == 0)
{
lean_object* v_size_3790_; 
v_size_3790_ = lean_ctor_get(v_l_3759_, 0);
lean_inc(v_size_3790_);
v___y_3782_ = v_size_3790_;
goto v___jp_3781_;
}
else
{
lean_object* v___x_3791_; 
v___x_3791_ = lean_unsigned_to_nat(0u);
v___y_3782_ = v___x_3791_;
goto v___jp_3781_;
}
v___jp_3770_:
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
v___x_3774_ = lean_nat_add(v___y_3771_, v___y_3773_);
lean_dec(v___y_3773_);
lean_dec(v___y_3771_);
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 4, v_r_3744_);
lean_ctor_set(v___x_3766_, 3, v_r_3760_);
lean_ctor_set(v___x_3766_, 2, v_v_3742_);
lean_ctor_set(v___x_3766_, 1, v_k_3741_);
lean_ctor_set(v___x_3766_, 0, v___x_3774_);
v___x_3776_ = v___x_3766_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_k_3741_);
lean_ctor_set(v_reuseFailAlloc_3780_, 2, v_v_3742_);
lean_ctor_set(v_reuseFailAlloc_3780_, 3, v_r_3760_);
lean_ctor_set(v_reuseFailAlloc_3780_, 4, v_r_3744_);
v___x_3776_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
lean_object* v___x_3778_; 
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 4, v___x_3776_);
lean_ctor_set(v___x_3754_, 3, v___y_3772_);
lean_ctor_set(v___x_3754_, 2, v_v_3758_);
lean_ctor_set(v___x_3754_, 1, v_k_3757_);
lean_ctor_set(v___x_3754_, 0, v___x_3769_);
v___x_3778_ = v___x_3754_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3769_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_k_3757_);
lean_ctor_set(v_reuseFailAlloc_3779_, 2, v_v_3758_);
lean_ctor_set(v_reuseFailAlloc_3779_, 3, v___y_3772_);
lean_ctor_set(v_reuseFailAlloc_3779_, 4, v___x_3776_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
v___jp_3781_:
{
lean_object* v___x_3783_; lean_object* v___x_3785_; 
v___x_3783_ = lean_nat_add(v___x_3768_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec(v___x_3768_);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 4, v_l_3759_);
lean_ctor_set(v___x_3594_, 0, v___x_3783_);
v___x_3785_ = v___x_3594_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3783_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_k_3589_);
lean_ctor_set(v_reuseFailAlloc_3789_, 2, v_v_3590_);
lean_ctor_set(v_reuseFailAlloc_3789_, 3, v_l_3591_);
lean_ctor_set(v_reuseFailAlloc_3789_, 4, v_l_3759_);
v___x_3785_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
lean_object* v___x_3786_; 
v___x_3786_ = lean_nat_add(v___x_3738_, v_size_3761_);
if (lean_obj_tag(v_r_3760_) == 0)
{
lean_object* v_size_3787_; 
v_size_3787_ = lean_ctor_get(v_r_3760_, 0);
lean_inc(v_size_3787_);
v___y_3771_ = v___x_3786_;
v___y_3772_ = v___x_3785_;
v___y_3773_ = v_size_3787_;
goto v___jp_3770_;
}
else
{
lean_object* v___x_3788_; 
v___x_3788_ = lean_unsigned_to_nat(0u);
v___y_3771_ = v___x_3786_;
v___y_3772_ = v___x_3785_;
v___y_3773_ = v___x_3788_;
goto v___jp_3770_;
}
}
}
}
}
else
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3802_; 
lean_del_object(v___x_3594_);
v___x_3798_ = lean_nat_add(v___x_3738_, v_size_3739_);
v___x_3799_ = lean_nat_add(v___x_3798_, v_size_3740_);
lean_dec(v_size_3740_);
v___x_3800_ = lean_nat_add(v___x_3798_, v_size_3756_);
lean_dec(v___x_3798_);
lean_inc_ref(v_l_3591_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 4, v_l_3743_);
lean_ctor_set(v___x_3754_, 3, v_l_3591_);
lean_ctor_set(v___x_3754_, 2, v_v_3590_);
lean_ctor_set(v___x_3754_, 1, v_k_3589_);
lean_ctor_set(v___x_3754_, 0, v___x_3800_);
v___x_3802_ = v___x_3754_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3800_);
lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_k_3589_);
lean_ctor_set(v_reuseFailAlloc_3815_, 2, v_v_3590_);
lean_ctor_set(v_reuseFailAlloc_3815_, 3, v_l_3591_);
lean_ctor_set(v_reuseFailAlloc_3815_, 4, v_l_3743_);
v___x_3802_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
v_isSharedCheck_3809_ = !lean_is_exclusive(v_l_3591_);
if (v_isSharedCheck_3809_ == 0)
{
lean_object* v_unused_3810_; lean_object* v_unused_3811_; lean_object* v_unused_3812_; lean_object* v_unused_3813_; lean_object* v_unused_3814_; 
v_unused_3810_ = lean_ctor_get(v_l_3591_, 4);
lean_dec(v_unused_3810_);
v_unused_3811_ = lean_ctor_get(v_l_3591_, 3);
lean_dec(v_unused_3811_);
v_unused_3812_ = lean_ctor_get(v_l_3591_, 2);
lean_dec(v_unused_3812_);
v_unused_3813_ = lean_ctor_get(v_l_3591_, 1);
lean_dec(v_unused_3813_);
v_unused_3814_ = lean_ctor_get(v_l_3591_, 0);
lean_dec(v_unused_3814_);
v___x_3804_ = v_l_3591_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_dec(v_l_3591_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 4, v_r_3744_);
lean_ctor_set(v___x_3804_, 3, v___x_3802_);
lean_ctor_set(v___x_3804_, 2, v_v_3742_);
lean_ctor_set(v___x_3804_, 1, v_k_3741_);
lean_ctor_set(v___x_3804_, 0, v___x_3799_);
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_k_3741_);
lean_ctor_set(v_reuseFailAlloc_3808_, 2, v_v_3742_);
lean_ctor_set(v_reuseFailAlloc_3808_, 3, v___x_3802_);
lean_ctor_set(v_reuseFailAlloc_3808_, 4, v_r_3744_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3822_; 
v_l_3822_ = lean_ctor_get(v_impl_3737_, 3);
lean_inc(v_l_3822_);
if (lean_obj_tag(v_l_3822_) == 0)
{
lean_object* v_r_3823_; lean_object* v_k_3824_; lean_object* v_v_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3848_; 
v_r_3823_ = lean_ctor_get(v_impl_3737_, 4);
v_k_3824_ = lean_ctor_get(v_impl_3737_, 1);
v_v_3825_ = lean_ctor_get(v_impl_3737_, 2);
v_isSharedCheck_3848_ = !lean_is_exclusive(v_impl_3737_);
if (v_isSharedCheck_3848_ == 0)
{
lean_object* v_unused_3849_; lean_object* v_unused_3850_; 
v_unused_3849_ = lean_ctor_get(v_impl_3737_, 3);
lean_dec(v_unused_3849_);
v_unused_3850_ = lean_ctor_get(v_impl_3737_, 0);
lean_dec(v_unused_3850_);
v___x_3827_ = v_impl_3737_;
v_isShared_3828_ = v_isSharedCheck_3848_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_r_3823_);
lean_inc(v_v_3825_);
lean_inc(v_k_3824_);
lean_dec(v_impl_3737_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3848_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v_k_3829_; lean_object* v_v_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3844_; 
v_k_3829_ = lean_ctor_get(v_l_3822_, 1);
v_v_3830_ = lean_ctor_get(v_l_3822_, 2);
v_isSharedCheck_3844_ = !lean_is_exclusive(v_l_3822_);
if (v_isSharedCheck_3844_ == 0)
{
lean_object* v_unused_3845_; lean_object* v_unused_3846_; lean_object* v_unused_3847_; 
v_unused_3845_ = lean_ctor_get(v_l_3822_, 4);
lean_dec(v_unused_3845_);
v_unused_3846_ = lean_ctor_get(v_l_3822_, 3);
lean_dec(v_unused_3846_);
v_unused_3847_ = lean_ctor_get(v_l_3822_, 0);
lean_dec(v_unused_3847_);
v___x_3832_ = v_l_3822_;
v_isShared_3833_ = v_isSharedCheck_3844_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_v_3830_);
lean_inc(v_k_3829_);
lean_dec(v_l_3822_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3844_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3834_; lean_object* v___x_3836_; 
v___x_3834_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3823_, 2);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 4, v_r_3823_);
lean_ctor_set(v___x_3832_, 3, v_r_3823_);
lean_ctor_set(v___x_3832_, 2, v_v_3590_);
lean_ctor_set(v___x_3832_, 1, v_k_3589_);
lean_ctor_set(v___x_3832_, 0, v___x_3738_);
v___x_3836_ = v___x_3832_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3738_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_k_3589_);
lean_ctor_set(v_reuseFailAlloc_3843_, 2, v_v_3590_);
lean_ctor_set(v_reuseFailAlloc_3843_, 3, v_r_3823_);
lean_ctor_set(v_reuseFailAlloc_3843_, 4, v_r_3823_);
v___x_3836_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v___x_3838_; 
lean_inc(v_r_3823_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 3, v_r_3823_);
lean_ctor_set(v___x_3827_, 0, v___x_3738_);
v___x_3838_ = v___x_3827_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3738_);
lean_ctor_set(v_reuseFailAlloc_3842_, 1, v_k_3824_);
lean_ctor_set(v_reuseFailAlloc_3842_, 2, v_v_3825_);
lean_ctor_set(v_reuseFailAlloc_3842_, 3, v_r_3823_);
lean_ctor_set(v_reuseFailAlloc_3842_, 4, v_r_3823_);
v___x_3838_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
lean_object* v___x_3840_; 
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 4, v___x_3838_);
lean_ctor_set(v___x_3594_, 3, v___x_3836_);
lean_ctor_set(v___x_3594_, 2, v_v_3830_);
lean_ctor_set(v___x_3594_, 1, v_k_3829_);
lean_ctor_set(v___x_3594_, 0, v___x_3834_);
v___x_3840_ = v___x_3594_;
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
lean_object* v_r_3851_; 
v_r_3851_ = lean_ctor_get(v_impl_3737_, 4);
lean_inc(v_r_3851_);
if (lean_obj_tag(v_r_3851_) == 0)
{
lean_object* v_k_3852_; lean_object* v_v_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3864_; 
v_k_3852_ = lean_ctor_get(v_impl_3737_, 1);
v_v_3853_ = lean_ctor_get(v_impl_3737_, 2);
v_isSharedCheck_3864_ = !lean_is_exclusive(v_impl_3737_);
if (v_isSharedCheck_3864_ == 0)
{
lean_object* v_unused_3865_; lean_object* v_unused_3866_; lean_object* v_unused_3867_; 
v_unused_3865_ = lean_ctor_get(v_impl_3737_, 4);
lean_dec(v_unused_3865_);
v_unused_3866_ = lean_ctor_get(v_impl_3737_, 3);
lean_dec(v_unused_3866_);
v_unused_3867_ = lean_ctor_get(v_impl_3737_, 0);
lean_dec(v_unused_3867_);
v___x_3855_ = v_impl_3737_;
v_isShared_3856_ = v_isSharedCheck_3864_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_v_3853_);
lean_inc(v_k_3852_);
lean_dec(v_impl_3737_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3864_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3857_; lean_object* v___x_3859_; 
v___x_3857_ = lean_unsigned_to_nat(3u);
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 4, v_l_3822_);
lean_ctor_set(v___x_3855_, 2, v_v_3590_);
lean_ctor_set(v___x_3855_, 1, v_k_3589_);
lean_ctor_set(v___x_3855_, 0, v___x_3738_);
v___x_3859_ = v___x_3855_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3738_);
lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_k_3589_);
lean_ctor_set(v_reuseFailAlloc_3863_, 2, v_v_3590_);
lean_ctor_set(v_reuseFailAlloc_3863_, 3, v_l_3822_);
lean_ctor_set(v_reuseFailAlloc_3863_, 4, v_l_3822_);
v___x_3859_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
lean_object* v___x_3861_; 
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 4, v_r_3851_);
lean_ctor_set(v___x_3594_, 3, v___x_3859_);
lean_ctor_set(v___x_3594_, 2, v_v_3853_);
lean_ctor_set(v___x_3594_, 1, v_k_3852_);
lean_ctor_set(v___x_3594_, 0, v___x_3857_);
v___x_3861_ = v___x_3594_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_k_3852_);
lean_ctor_set(v_reuseFailAlloc_3862_, 2, v_v_3853_);
lean_ctor_set(v_reuseFailAlloc_3862_, 3, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3862_, 4, v_r_3851_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3870_; 
v___x_3868_ = lean_unsigned_to_nat(2u);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 4, v_impl_3737_);
lean_ctor_set(v___x_3594_, 3, v_r_3851_);
lean_ctor_set(v___x_3594_, 0, v___x_3868_);
v___x_3870_ = v___x_3594_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3868_);
lean_ctor_set(v_reuseFailAlloc_3871_, 1, v_k_3589_);
lean_ctor_set(v_reuseFailAlloc_3871_, 2, v_v_3590_);
lean_ctor_set(v_reuseFailAlloc_3871_, 3, v_r_3851_);
lean_ctor_set(v_reuseFailAlloc_3871_, 4, v_impl_3737_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
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
lean_object* v___x_3873_; lean_object* v___x_3874_; 
v___x_3873_ = lean_unsigned_to_nat(1u);
v___x_3874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
lean_ctor_set(v___x_3874_, 1, v_k_3585_);
lean_ctor_set(v___x_3874_, 2, v_v_3586_);
lean_ctor_set(v___x_3874_, 3, v_t_3587_);
lean_ctor_set(v___x_3874_, 4, v_t_3587_);
return v___x_3874_;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3875_ = lean_box(1);
v___x_3876_ = l_Lake_LeanLib_defaultFacetConfig;
v___x_3877_ = l_Lake_LeanLib_defaultFacet;
v___x_3878_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3877_, v___x_3876_, v___x_3875_);
return v___x_3878_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3879_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__0, &l_Lake_LeanLib_initFacetConfigs___closed__0_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__0);
v___x_3880_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig));
v___x_3881_ = l_Lake_LeanLib_modulesFacet;
v___x_3882_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3881_, v___x_3880_, v___x_3879_);
return v___x_3882_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3883_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__1, &l_Lake_LeanLib_initFacetConfigs___closed__1_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__1);
v___x_3884_ = l_Lake_LeanLib_elabArtsFacetConfig;
v___x_3885_ = l_Lake_LeanLib_elabArtsFacet;
v___x_3886_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3885_, v___x_3884_, v___x_3883_);
return v___x_3886_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3887_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__2, &l_Lake_LeanLib_initFacetConfigs___closed__2_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__2);
v___x_3888_ = l_Lake_LeanLib_irArtsFacetConfig;
v___x_3889_ = l_Lake_LeanLib_irArtsFacet;
v___x_3890_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3889_, v___x_3888_, v___x_3887_);
return v___x_3890_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3891_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__3, &l_Lake_LeanLib_initFacetConfigs___closed__3_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__3);
v___x_3892_ = l_Lake_LeanLib_leanArtsFacetConfig;
v___x_3893_ = l_Lake_LeanLib_leanArtsFacet;
v___x_3894_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3893_, v___x_3892_, v___x_3891_);
return v___x_3894_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3895_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__4, &l_Lake_LeanLib_initFacetConfigs___closed__4_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__4);
v___x_3896_ = l_Lake_LeanLib_staticFacetConfig;
v___x_3897_ = l_Lake_LeanLib_staticFacet;
v___x_3898_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3897_, v___x_3896_, v___x_3895_);
return v___x_3898_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3899_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__5, &l_Lake_LeanLib_initFacetConfigs___closed__5_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__5);
v___x_3900_ = l_Lake_LeanLib_staticExportFacetConfig;
v___x_3901_ = l_Lake_LeanLib_staticExportFacet;
v___x_3902_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3901_, v___x_3900_, v___x_3899_);
return v___x_3902_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3903_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__6, &l_Lake_LeanLib_initFacetConfigs___closed__6_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__6);
v___x_3904_ = l_Lake_LeanLib_sharedFacetConfig;
v___x_3905_ = l_Lake_LeanLib_sharedFacet;
v___x_3906_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3905_, v___x_3904_, v___x_3903_);
return v___x_3906_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3907_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__7, &l_Lake_LeanLib_initFacetConfigs___closed__7_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__7);
v___x_3908_ = l_Lake_LeanLib_extraDepFacetConfig;
v___x_3909_ = l_Lake_LeanLib_extraDepFacet;
v___x_3910_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3909_, v___x_3908_, v___x_3907_);
return v___x_3910_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_3911_; 
v___x_3911_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__8, &l_Lake_LeanLib_initFacetConfigs___closed__8_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__8);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3912_, lean_object* v_k_3913_, lean_object* v_v_3914_, lean_object* v_t_3915_, lean_object* v_hl_3916_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3913_, v_v_3914_, v_t_3915_);
return v___x_3917_;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs(void){
_start:
{
lean_object* v___x_3918_; 
v___x_3918_ = l_Lake_LeanLib_initFacetConfigs;
return v___x_3918_;
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
