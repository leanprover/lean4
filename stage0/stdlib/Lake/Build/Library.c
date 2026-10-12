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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
uint8_t v_res_10_;
v_res_10_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_1_, v_x_2_);
stack->m_num = v_res_10_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_11_, lean_object* v_x_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_11_, v_x_12_);
lean_dec(v_x_12_);
lean_dec_ref(v_a_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
return v_x_15_;
}
else
{
lean_object* v_key_17_; lean_object* v_value_18_; lean_object* v_tail_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_46_; 
v_key_17_ = lean_ctor_get(v_x_16_, 0);
v_value_18_ = lean_ctor_get(v_x_16_, 1);
v_tail_19_ = lean_ctor_get(v_x_16_, 2);
v_isSharedCheck_46_ = !lean_is_exclusive(v_x_16_);
if (v_isSharedCheck_46_ == 0)
{
v___x_21_ = v_x_16_;
v_isShared_22_ = v_isSharedCheck_46_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_tail_19_);
lean_inc(v_value_18_);
lean_inc(v_key_17_);
lean_dec(v_x_16_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_46_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v_name_23_; lean_object* v___x_24_; uint64_t v___y_26_; 
v_name_23_ = lean_ctor_get(v_key_17_, 1);
v___x_24_ = lean_array_get_size(v_x_15_);
if (lean_obj_tag(v_name_23_) == 0)
{
uint64_t v___x_44_; 
v___x_44_ = 1723ULL;
v___y_26_ = v___x_44_;
goto v___jp_25_;
}
else
{
uint64_t v_hash_45_; 
v_hash_45_ = lean_ctor_get_uint64(v_name_23_, sizeof(void*)*2);
v___y_26_ = v_hash_45_;
goto v___jp_25_;
}
v___jp_25_:
{
uint64_t v___x_27_; uint64_t v___x_28_; uint64_t v_fold_29_; uint64_t v___x_30_; uint64_t v___x_31_; uint64_t v___x_32_; size_t v___x_33_; size_t v___x_34_; size_t v___x_35_; size_t v___x_36_; size_t v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_27_ = 32ULL;
v___x_28_ = lean_uint64_shift_right(v___y_26_, v___x_27_);
v_fold_29_ = lean_uint64_xor(v___y_26_, v___x_28_);
v___x_30_ = 16ULL;
v___x_31_ = lean_uint64_shift_right(v_fold_29_, v___x_30_);
v___x_32_ = lean_uint64_xor(v_fold_29_, v___x_31_);
v___x_33_ = lean_uint64_to_usize(v___x_32_);
v___x_34_ = lean_usize_of_nat(v___x_24_);
v___x_35_ = ((size_t)1ULL);
v___x_36_ = lean_usize_sub(v___x_34_, v___x_35_);
v___x_37_ = lean_usize_land(v___x_33_, v___x_36_);
v___x_38_ = lean_array_uget_borrowed(v_x_15_, v___x_37_);
lean_inc(v___x_38_);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 2, v___x_38_);
v___x_40_ = v___x_21_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_key_17_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v_value_18_);
lean_ctor_set(v_reuseFailAlloc_43_, 2, v___x_38_);
v___x_40_ = v_reuseFailAlloc_43_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; 
v___x_41_ = lean_array_uset(v_x_15_, v___x_37_, v___x_40_);
v_x_15_ = v___x_41_;
v_x_16_ = v_tail_19_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(lean_object* v_i_47_, lean_object* v_source_48_, lean_object* v_target_49_){
_start:
{
lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = lean_array_get_size(v_source_48_);
v___x_51_ = lean_nat_dec_lt(v_i_47_, v___x_50_);
if (v___x_51_ == 0)
{
lean_dec_ref(v_source_48_);
lean_dec(v_i_47_);
return v_target_49_;
}
else
{
lean_object* v_es_52_; lean_object* v___x_53_; lean_object* v_source_54_; lean_object* v_target_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_es_52_ = lean_array_fget(v_source_48_, v_i_47_);
v___x_53_ = lean_box(0);
v_source_54_ = lean_array_fset(v_source_48_, v_i_47_, v___x_53_);
v_target_55_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(v_target_49_, v_es_52_);
v___x_56_ = lean_unsigned_to_nat(1u);
v___x_57_ = lean_nat_add(v_i_47_, v___x_56_);
lean_dec(v_i_47_);
v_i_47_ = v___x_57_;
v_source_48_ = v_source_54_;
v_target_49_ = v_target_55_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(lean_object* v_data_59_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v_nbuckets_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_60_ = lean_array_get_size(v_data_59_);
v___x_61_ = lean_unsigned_to_nat(2u);
v_nbuckets_62_ = lean_nat_mul(v___x_60_, v___x_61_);
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_box(0);
v___x_65_ = lean_mk_array(v_nbuckets_62_, v___x_64_);
v___x_66_ = lean_array_propagate_mark(v_data_59_, v___x_65_);
v___x_67_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(v___x_63_, v_data_59_, v___x_66_);
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
v___x_113_ = 1723ULL;
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
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(lean_object* v_m_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_buckets_117_; lean_object* v_name_118_; lean_object* v___x_119_; uint64_t v___y_121_; 
v_buckets_117_ = lean_ctor_get(v_m_115_, 1);
v_name_118_ = lean_ctor_get(v_a_116_, 1);
v___x_119_ = lean_array_get_size(v_buckets_117_);
if (lean_obj_tag(v_name_118_) == 0)
{
uint64_t v___x_135_; 
v___x_135_ = 1723ULL;
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
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_115_ = stack[0].m_obj;
lean_object* v_a_116_ = stack[1].m_obj;
uint8_t v_res_137_;
v_res_137_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_115_, v_a_116_);
stack->m_num = v_res_137_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg___boxed(lean_object* v_m_138_, lean_object* v_a_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_138_, v_a_139_);
lean_dec_ref(v_a_139_);
lean_dec_ref(v_m_138_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__0));
v___x_144_ = l_Lake_BuildTrace_nil(v___x_143_);
return v___x_144_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(lean_object* v_self_145_, lean_object* v_root_146_, lean_object* v_col_147_, uint8_t v_viaImport_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_col_157_; lean_object* v___y_158_; lean_object* v_mods_160_; lean_object* v_modSet_161_; uint8_t v_hasErrors_162_; uint8_t v___x_163_; 
v_mods_160_ = lean_ctor_get(v_col_147_, 0);
v_modSet_161_ = lean_ctor_get(v_col_147_, 1);
v_hasErrors_162_ = lean_ctor_get_uint8(v_col_147_, sizeof(void*)*2);
v___x_163_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_modSet_161_, v_root_146_);
if (v___x_163_ == 0)
{
lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_240_; 
lean_inc_ref(v_modSet_161_);
lean_inc_ref(v_mods_160_);
v_isSharedCheck_240_ = !lean_is_exclusive(v_col_147_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; lean_object* v_unused_242_; 
v_unused_241_ = lean_ctor_get(v_col_147_, 1);
lean_dec(v_unused_241_);
v_unused_242_ = lean_ctor_get(v_col_147_, 0);
lean_dec(v_unused_242_);
v___x_165_ = v_col_147_;
v_isShared_166_ = v_isSharedCheck_240_;
goto v_resetjp_164_;
}
else
{
lean_dec(v_col_147_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_240_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_lib_167_; lean_object* v_pkg_168_; lean_object* v_name_169_; lean_object* v_keyName_170_; uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v_col_175_; 
v_lib_167_ = lean_ctor_get(v_root_146_, 0);
v_pkg_168_ = lean_ctor_get(v_lib_167_, 0);
v_name_169_ = lean_ctor_get(v_root_146_, 1);
v_keyName_170_ = lean_ctor_get(v_pkg_168_, 2);
v___x_171_ = 1;
v___x_172_ = lean_box(0);
lean_inc_ref(v_root_146_);
v___x_173_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_modSet_161_, v_root_146_, v___x_172_);
lean_inc_ref(v___x_173_);
lean_inc_ref(v_mods_160_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v___x_173_);
v_col_175_ = v___x_165_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_mods_160_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___x_173_);
lean_ctor_set_uint8(v_reuseFailAlloc_239_, sizeof(void*)*2, v_hasErrors_162_);
v_col_175_ = v_reuseFailAlloc_239_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_176_ = l_Lake_Module_importsFacet;
lean_inc(v_name_169_);
lean_inc(v_keyName_170_);
v___x_177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_177_, 0, v_keyName_170_);
lean_ctor_set(v___x_177_, 1, v_name_169_);
v___x_178_ = l_Lake_Module_keyword;
lean_inc_ref(v_root_146_);
v___x_179_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
lean_ctor_set(v___x_179_, 2, v_root_146_);
lean_ctor_set(v___x_179_, 3, v___x_176_);
lean_inc_ref(v_a_149_);
lean_inc_ref(v_a_153_);
lean_inc(v_a_152_);
lean_inc(v_a_151_);
lean_inc(v_a_150_);
v___x_180_ = lean_apply_7(v_a_149_, v___x_179_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, lean_box(0));
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v_a_182_; uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
v_a_182_ = lean_ctor_get(v___x_180_, 1);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_180_, 2);
v___x_183_ = 0;
v___x_184_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_186_, 0, v_a_182_);
lean_ctor_set(v___x_186_, 1, v___x_184_);
lean_ctor_set(v___x_186_, 2, v___x_185_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*3, v___x_183_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*3 + 1, v___x_163_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*3 + 2, v___x_163_);
v___x_187_ = l_Lake_Job_waitUnlessCanceled_x3f___redArg(v_a_181_, v___x_186_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_219_; 
v_a_188_ = lean_ctor_get(v___x_187_, 1);
v_a_189_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_219_ == 0)
{
v___x_191_ = v___x_187_;
v_isShared_192_ = v_isSharedCheck_219_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_188_);
lean_inc(v_a_189_);
lean_dec(v___x_187_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_219_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v_log_193_; lean_object* v___y_195_; 
v_log_193_ = lean_ctor_get(v_a_188_, 0);
lean_inc_ref(v_log_193_);
lean_dec(v_a_188_);
if (lean_obj_tag(v_a_189_) == 1)
{
lean_object* v_val_199_; size_t v_sz_200_; size_t v___x_201_; lean_object* v___x_202_; 
lean_del_object(v___x_191_);
lean_dec_ref(v___x_173_);
lean_dec_ref(v_mods_160_);
v_val_199_ = lean_ctor_get(v_a_189_, 0);
lean_inc(v_val_199_);
lean_dec_ref_known(v_a_189_, 1);
v_sz_200_ = lean_array_size(v_val_199_);
v___x_201_ = ((size_t)0ULL);
v___x_202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_145_, v_val_199_, v_sz_200_, v___x_201_, v_col_175_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_log_193_);
lean_dec(v_val_199_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v_a_204_; lean_object* v_mods_205_; lean_object* v_modSet_206_; uint8_t v_hasErrors_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_215_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
v_a_204_ = lean_ctor_get(v___x_202_, 1);
lean_inc(v_a_204_);
lean_dec_ref_known(v___x_202_, 2);
v_mods_205_ = lean_ctor_get(v_a_203_, 0);
v_modSet_206_ = lean_ctor_get(v_a_203_, 1);
v_hasErrors_207_ = lean_ctor_get_uint8(v_a_203_, sizeof(void*)*2);
v_isSharedCheck_215_ = !lean_is_exclusive(v_a_203_);
if (v_isSharedCheck_215_ == 0)
{
v___x_209_ = v_a_203_;
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_modSet_206_);
lean_inc(v_mods_205_);
lean_dec(v_a_203_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_215_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = lean_array_push(v_mods_205_, v_root_146_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_211_);
v___x_213_ = v___x_209_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_modSet_206_);
lean_ctor_set_uint8(v_reuseFailAlloc_214_, sizeof(void*)*2, v_hasErrors_207_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
v_col_157_ = v___x_213_;
v___y_158_ = v_a_204_;
goto v___jp_156_;
}
}
}
else
{
lean_dec_ref(v_root_146_);
return v___x_202_;
}
}
else
{
lean_dec(v_a_189_);
lean_dec_ref(v_col_175_);
lean_dec_ref(v_a_149_);
if (v_viaImport_148_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_array_push(v_mods_160_, v_root_146_);
v___x_217_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_173_);
lean_ctor_set_uint8(v___x_217_, sizeof(void*)*2, v___x_171_);
v___y_195_ = v___x_217_;
goto v___jp_194_;
}
else
{
lean_object* v___x_218_; 
lean_dec_ref(v_root_146_);
v___x_218_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_218_, 0, v_mods_160_);
lean_ctor_set(v___x_218_, 1, v___x_173_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*2, v___x_171_);
v___y_195_ = v___x_218_;
goto v___jp_194_;
}
}
v___jp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v_log_193_);
lean_ctor_set(v___x_191_, 0, v___y_195_);
v___x_197_ = v___x_191_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___y_195_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v_log_193_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v_a_220_; lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v_col_175_);
lean_dec_ref(v___x_173_);
lean_dec_ref(v_mods_160_);
lean_dec_ref(v_a_149_);
lean_dec_ref(v_root_146_);
v_a_220_ = lean_ctor_get(v___x_187_, 1);
v_a_221_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_229_ == 0)
{
v___x_223_ = v___x_187_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_220_);
lean_inc(v_a_221_);
lean_dec(v___x_187_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_log_225_; lean_object* v___x_227_; 
v_log_225_ = lean_ctor_get(v_a_220_, 0);
lean_inc_ref(v_log_225_);
lean_dec(v_a_220_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v_log_225_);
v___x_227_ = v___x_223_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_221_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_log_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
else
{
lean_object* v_a_230_; lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
lean_dec_ref(v_col_175_);
lean_dec_ref(v___x_173_);
lean_dec_ref(v_mods_160_);
lean_dec_ref(v_a_149_);
lean_dec_ref(v_root_146_);
v_a_230_ = lean_ctor_get(v___x_180_, 0);
v_a_231_ = lean_ctor_get(v___x_180_, 1);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_180_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_inc(v_a_230_);
lean_dec(v___x_180_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_230_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_a_149_);
lean_dec_ref(v_root_146_);
v_col_157_ = v_col_147_;
v___y_158_ = v_a_154_;
goto v___jp_156_;
}
v___jp_156_:
{
lean_object* v___x_159_; 
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v_col_157_);
lean_ctor_set(v___x_159_, 1, v___y_158_);
return v___x_159_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_145_ = stack[0].m_obj;
lean_object* v_root_146_ = stack[1].m_obj;
lean_object* v_col_147_ = stack[2].m_obj;
uint8_t v_viaImport_148_ = stack[3].m_num;
lean_object* v_a_149_ = stack[4].m_obj;
lean_object* v_a_150_ = stack[5].m_obj;
lean_object* v_a_151_ = stack[6].m_obj;
lean_object* v_a_152_ = stack[7].m_obj;
lean_object* v_a_153_ = stack[8].m_obj;
lean_object* v_a_154_ = stack[9].m_obj;
lean_object* v_res_243_;
v_res_243_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_145_, v_root_146_, v_col_147_, v_viaImport_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
stack->m_obj
 = v_res_243_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(lean_object* v_self_244_, lean_object* v_as_245_, size_t v_sz_246_, size_t v_i_247_, lean_object* v_b_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_a_257_; lean_object* v_a_258_; uint8_t v___x_262_; 
v___x_262_ = lean_usize_dec_lt(v_i_247_, v_sz_246_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; 
lean_dec_ref(v___y_249_);
v___x_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_263_, 0, v_b_248_);
lean_ctor_set(v___x_263_, 1, v___y_254_);
return v___x_263_;
}
else
{
lean_object* v_a_264_; lean_object* v_lib_265_; lean_object* v_name_266_; lean_object* v_name_267_; uint8_t v___x_268_; 
v_a_264_ = lean_array_uget_borrowed(v_as_245_, v_i_247_);
v_lib_265_ = lean_ctor_get(v_a_264_, 0);
v_name_266_ = lean_ctor_get(v_lib_265_, 1);
v_name_267_ = lean_ctor_get(v_self_244_, 1);
v___x_268_ = lean_name_eq(v_name_266_, v_name_267_);
if (v___x_268_ == 0)
{
v_a_257_ = v_b_248_;
v_a_258_ = v___y_254_;
goto v___jp_256_;
}
else
{
lean_object* v___x_269_; 
lean_inc_ref(v___y_249_);
lean_inc(v_a_264_);
v___x_269_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_244_, v_a_264_, v_b_248_, v___x_268_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v_a_271_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc(v_a_270_);
v_a_271_ = lean_ctor_get(v___x_269_, 1);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_269_, 2);
v_a_257_ = v_a_270_;
v_a_258_ = v_a_271_;
goto v___jp_256_;
}
else
{
lean_dec_ref(v___y_249_);
return v___x_269_;
}
}
}
v___jp_256_:
{
size_t v___x_259_; size_t v___x_260_; 
v___x_259_ = ((size_t)1ULL);
v___x_260_ = lean_usize_add(v_i_247_, v___x_259_);
v_i_247_ = v___x_260_;
v_b_248_ = v_a_257_;
v___y_254_ = v_a_258_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_244_ = stack[0].m_obj;
lean_object* v_as_245_ = stack[1].m_obj;
size_t v_sz_246_ = stack[2].m_num;
size_t v_i_247_ = stack[3].m_num;
lean_object* v_b_248_ = stack[4].m_obj;
lean_object* v___y_249_ = stack[5].m_obj;
lean_object* v___y_250_ = stack[6].m_obj;
lean_object* v___y_251_ = stack[7].m_obj;
lean_object* v___y_252_ = stack[8].m_obj;
lean_object* v___y_253_ = stack[9].m_obj;
lean_object* v___y_254_ = stack[10].m_obj;
lean_object* v_res_272_;
v_res_272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_244_, v_as_245_, v_sz_246_, v_i_247_, v_b_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
stack->m_obj
 = v_res_272_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(lean_object* v_self_273_, lean_object* v_as_274_, lean_object* v_sz_275_, lean_object* v_i_276_, lean_object* v_b_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
size_t v_sz_boxed_285_; size_t v_i_boxed_286_; lean_object* v_res_287_; 
v_sz_boxed_285_ = lean_unbox_usize(v_sz_275_);
lean_dec(v_sz_275_);
v_i_boxed_286_ = lean_unbox_usize(v_i_276_);
lean_dec(v_i_276_);
v_res_287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_273_, v_as_274_, v_sz_boxed_285_, v_i_boxed_286_, v_b_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v_as_274_);
lean_dec_ref(v_self_273_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object* v_self_288_, lean_object* v_root_289_, lean_object* v_col_290_, lean_object* v_viaImport_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_){
_start:
{
uint8_t v_viaImport_boxed_299_; lean_object* v_res_300_; 
v_viaImport_boxed_299_ = lean_unbox(v_viaImport_291_);
v_res_300_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_288_, v_root_289_, v_col_290_, v_viaImport_boxed_299_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_self_288_);
return v_res_300_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_object* v_00_u03b2_301_, lean_object* v_m_302_, lean_object* v_a_303_){
_start:
{
uint8_t v___x_304_; 
v___x_304_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_302_, v_a_303_);
return v___x_304_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_302_ = stack[1].m_obj;
lean_object* v_a_303_ = stack[2].m_obj;
uint8_t v_res_305_;
v_res_305_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_box(0), v_m_302_, v_a_303_);
stack->m_num = v_res_305_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(lean_object* v_00_u03b2_306_, lean_object* v_m_307_, lean_object* v_a_308_){
_start:
{
uint8_t v_res_309_; lean_object* v_r_310_; 
v_res_309_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(v_00_u03b2_306_, v_m_307_, v_a_308_);
lean_dec_ref(v_a_308_);
lean_dec_ref(v_m_307_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1(lean_object* v_00_u03b2_311_, lean_object* v_m_312_, lean_object* v_a_313_, lean_object* v_b_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_m_312_, v_a_313_, v_b_314_);
return v___x_315_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(lean_object* v_00_u03b2_316_, lean_object* v_a_317_, lean_object* v_x_318_){
_start:
{
uint8_t v___x_319_; 
v___x_319_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_317_, v_x_318_);
return v___x_319_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_317_ = stack[1].m_obj;
lean_object* v_x_318_ = stack[2].m_obj;
uint8_t v_res_320_;
v_res_320_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(lean_box(0), v_a_317_, v_x_318_);
stack->m_num = v_res_320_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_321_, lean_object* v_a_322_, lean_object* v_x_323_){
_start:
{
uint8_t v_res_324_; lean_object* v_r_325_; 
v_res_324_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(v_00_u03b2_321_, v_a_322_, v_x_323_);
lean_dec(v_x_323_);
lean_dec_ref(v_a_322_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2(lean_object* v_00_u03b2_326_, lean_object* v_data_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(v_data_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_329_, lean_object* v_i_330_, lean_object* v_source_331_, lean_object* v_target_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(v_i_330_, v_source_331_, v_target_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(v_x_335_, v_x_336_);
return v___x_337_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(lean_object* v_self_338_, lean_object* v_as_339_, size_t v_sz_340_, size_t v_i_341_, lean_object* v_b_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
uint8_t v___x_350_; 
v___x_350_ = lean_usize_dec_lt(v_i_341_, v_sz_340_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; 
lean_dec_ref(v___y_343_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v_b_342_);
lean_ctor_set(v___x_351_, 1, v___y_348_);
return v___x_351_;
}
else
{
uint8_t v___x_352_; lean_object* v_a_353_; lean_object* v___x_354_; 
v___x_352_ = 0;
v_a_353_ = lean_array_uget_borrowed(v_as_339_, v_i_341_);
lean_inc_ref(v___y_343_);
lean_inc(v_a_353_);
v___x_354_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_338_, v_a_353_, v_b_342_, v___x_352_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v_a_356_; size_t v___x_357_; size_t v___x_358_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
v_a_356_ = lean_ctor_get(v___x_354_, 1);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_354_, 2);
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_add(v_i_341_, v___x_357_);
v_i_341_ = v___x_358_;
v_b_342_ = v_a_355_;
v___y_348_ = v_a_356_;
goto _start;
}
else
{
lean_dec_ref(v___y_343_);
return v___x_354_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_338_ = stack[0].m_obj;
lean_object* v_as_339_ = stack[1].m_obj;
size_t v_sz_340_ = stack[2].m_num;
size_t v_i_341_ = stack[3].m_num;
lean_object* v_b_342_ = stack[4].m_obj;
lean_object* v___y_343_ = stack[5].m_obj;
lean_object* v___y_344_ = stack[6].m_obj;
lean_object* v___y_345_ = stack[7].m_obj;
lean_object* v___y_346_ = stack[8].m_obj;
lean_object* v___y_347_ = stack[9].m_obj;
lean_object* v___y_348_ = stack[10].m_obj;
lean_object* v_res_360_;
v_res_360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_338_, v_as_339_, v_sz_340_, v_i_341_, v_b_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
stack->m_obj
 = v_res_360_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0___boxed(lean_object* v_self_361_, lean_object* v_as_362_, lean_object* v_sz_363_, lean_object* v_i_364_, lean_object* v_b_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
size_t v_sz_boxed_373_; size_t v_i_boxed_374_; lean_object* v_res_375_; 
v_sz_boxed_373_ = lean_unbox_usize(v_sz_363_);
lean_dec(v_sz_363_);
v_i_boxed_374_ = lean_unbox_usize(v_i_364_);
lean_dec(v_i_364_);
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_361_, v_as_362_, v_sz_boxed_373_, v_i_boxed_374_, v_b_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v_as_362_);
lean_dec_ref(v_self_361_);
return v_res_375_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(lean_object* v_self_378_, lean_object* v_col_379_, lean_object* v___x_380_, uint8_t v___x_381_, lean_object* v___x_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; 
lean_inc_ref(v_self_378_);
v___x_390_ = l_Lake_LeanLib_getModuleArray(v_self_378_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; size_t v_sz_392_; size_t v___x_393_; lean_object* v___x_394_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
v_sz_392_ = lean_array_size(v_a_391_);
v___x_393_ = ((size_t)0ULL);
v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_378_, v_a_391_, v_sz_392_, v___x_393_, v_col_379_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v_a_391_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_422_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_a_396_ = lean_ctor_get(v___x_394_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_422_ == 0)
{
v___x_398_ = v___x_394_;
v_isShared_399_ = v_isSharedCheck_422_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_422_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v_mods_400_; uint8_t v_hasErrors_401_; lean_object* v___y_403_; 
v_mods_400_ = lean_ctor_get(v_a_395_, 0);
lean_inc_ref(v_mods_400_);
v_hasErrors_401_ = lean_ctor_get_uint8(v_a_395_, sizeof(void*)*2);
lean_dec(v_a_395_);
if (v_hasErrors_401_ == 0)
{
lean_dec_ref(v_self_378_);
v___y_403_ = v_a_396_;
goto v___jp_402_;
}
else
{
lean_object* v_name_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_name_415_ = lean_ctor_get(v_self_378_, 1);
lean_inc(v_name_415_);
lean_dec_ref(v_self_378_);
v___x_416_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_415_, v_hasErrors_401_);
v___x_417_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1));
v___x_418_ = lean_string_append(v___x_416_, v___x_417_);
v___x_419_ = 3;
v___x_420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*1, v___x_419_);
v___x_421_ = lean_array_push(v_a_396_, v___x_420_);
v___y_403_ = v___x_421_;
goto v___jp_402_;
}
v___jp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_404_ = lean_mk_empty_array_with_capacity(v___x_380_);
v___x_405_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_406_ = 0;
v___x_407_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_408_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_408_, 0, v___x_404_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
lean_ctor_set(v___x_408_, 2, v___x_380_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*3, v___x_406_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*3 + 1, v___x_381_);
lean_ctor_set_uint8(v___x_408_, sizeof(void*)*3 + 2, v___x_381_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 1, v___x_408_);
lean_ctor_set(v___x_398_, 0, v_mods_400_);
v___x_410_ = v___x_398_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_mods_400_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v___x_408_);
v___x_410_ = v_reuseFailAlloc_414_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = lean_task_pure(v___x_410_);
v___x_412_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v___x_382_);
lean_ctor_set(v___x_412_, 2, v___x_405_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*3, v___x_381_);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___y_403_);
return v___x_413_;
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec(v___x_382_);
lean_dec(v___x_380_);
lean_dec_ref(v_self_378_);
v_a_423_ = lean_ctor_get(v___x_394_, 0);
v_a_424_ = lean_ctor_get(v___x_394_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_394_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_inc(v_a_423_);
lean_dec(v___x_394_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_423_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_433_; uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
lean_dec_ref(v___y_383_);
lean_dec(v___x_382_);
lean_dec(v___x_380_);
lean_dec_ref(v_col_379_);
lean_dec_ref(v_self_378_);
v_a_432_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_432_);
lean_dec_ref_known(v___x_390_, 1);
v___x_433_ = lean_io_error_to_string(v_a_432_);
v___x_434_ = 3;
v___x_435_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set_uint8(v___x_435_, sizeof(void*)*1, v___x_434_);
v___x_436_ = lean_array_get_size(v___y_388_);
v___x_437_ = lean_array_push(v___y_388_, v___x_435_);
v___x_438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
return v___x_438_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_378_ = stack[0].m_obj;
lean_object* v_col_379_ = stack[1].m_obj;
lean_object* v___x_380_ = stack[2].m_obj;
uint8_t v___x_381_ = stack[3].m_num;
lean_object* v___x_382_ = stack[4].m_obj;
lean_object* v___y_383_ = stack[5].m_obj;
lean_object* v___y_384_ = stack[6].m_obj;
lean_object* v___y_385_ = stack[7].m_obj;
lean_object* v___y_386_ = stack[8].m_obj;
lean_object* v___y_387_ = stack[9].m_obj;
lean_object* v___y_388_ = stack[10].m_obj;
lean_object* v_res_439_;
v_res_439_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(v_self_378_, v_col_379_, v___x_380_, v___x_381_, v___x_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
stack->m_obj
 = v_res_439_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed(lean_object* v_self_440_, lean_object* v_col_441_, lean_object* v___x_442_, lean_object* v___x_443_, lean_object* v___x_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
uint8_t v___x_7390__boxed_452_; lean_object* v_res_453_; 
v___x_7390__boxed_452_ = lean_unbox(v___x_443_);
v_res_453_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(v_self_440_, v_col_441_, v___x_442_, v___x_7390__boxed_452_, v___x_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
return v_res_453_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_box(0);
v___x_457_ = lean_unsigned_to_nat(16u);
v___x_458_ = lean_mk_array(v___x_457_, v___x_456_);
return v___x_458_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1);
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___x_459_);
return v___x_461_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3(void){
_start:
{
uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v_col_465_; 
v___x_462_ = 0;
v___x_463_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_464_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0));
v_col_465_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_col_465_, 0, v___x_464_);
lean_ctor_set(v_col_465_, 1, v___x_463_);
lean_ctor_set_uint8(v_col_465_, sizeof(void*)*2, v___x_462_);
return v_col_465_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(lean_object* v_self_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; lean_object* v_col_477_; lean_object* v___x_478_; lean_object* v___f_479_; lean_object* v___x_480_; 
v___x_474_ = lean_box(0);
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = 0;
v_col_477_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3);
v___x_478_ = lean_box(v___x_476_);
v___f_479_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed), 12, 5);
lean_closure_set(v___f_479_, 0, v_self_466_);
lean_closure_set(v___f_479_, 1, v_col_477_);
lean_closure_set(v___f_479_, 2, v___x_475_);
lean_closure_set(v___f_479_, 3, v___x_478_);
lean_closure_set(v___f_479_, 4, v___x_474_);
v___x_480_ = l_Lake_ensureJob___redArg(v___x_474_, v___f_479_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
return v___x_480_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_466_ = stack[0].m_obj;
lean_object* v_a_467_ = stack[1].m_obj;
lean_object* v_a_468_ = stack[2].m_obj;
lean_object* v_a_469_ = stack[3].m_obj;
lean_object* v_a_470_ = stack[4].m_obj;
lean_object* v_a_471_ = stack[5].m_obj;
lean_object* v_a_472_ = stack[6].m_obj;
lean_object* v_res_481_;
v_res_481_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(v_self_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
stack->m_obj
 = v_res_481_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___boxed(lean_object* v_self_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(v_self_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
lean_dec(v_a_484_);
return v_res_490_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(lean_object* v_as_492_, size_t v_i_493_, size_t v_stop_494_, lean_object* v_b_495_){
_start:
{
uint8_t v___x_496_; 
v___x_496_ = lean_usize_dec_eq(v_i_493_, v_stop_494_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v_name_498_; uint8_t v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; size_t v___x_504_; size_t v___x_505_; 
v___x_497_ = lean_array_uget_borrowed(v_as_492_, v_i_493_);
v_name_498_ = lean_ctor_get(v___x_497_, 1);
v___x_499_ = 1;
lean_inc(v_name_498_);
v___x_500_ = l_Lean_Name_toString(v_name_498_, v___x_499_);
v___x_501_ = lean_string_append(v_b_495_, v___x_500_);
lean_dec_ref(v___x_500_);
v___x_502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_503_ = lean_string_append(v___x_501_, v___x_502_);
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_add(v_i_493_, v___x_504_);
v_i_493_ = v___x_505_;
v_b_495_ = v___x_503_;
goto _start;
}
else
{
return v_b_495_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_492_ = stack[0].m_obj;
size_t v_i_493_ = stack[1].m_num;
size_t v_stop_494_ = stack[2].m_num;
lean_object* v_b_495_ = stack[3].m_obj;
lean_object* v_res_507_;
v_res_507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_as_492_, v_i_493_, v_stop_494_, v_b_495_);
stack->m_obj
 = v_res_507_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_508_, lean_object* v_i_509_, lean_object* v_stop_510_, lean_object* v_b_511_){
_start:
{
size_t v_i_boxed_512_; size_t v_stop_boxed_513_; lean_object* v_res_514_; 
v_i_boxed_512_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_stop_boxed_513_ = lean_unbox_usize(v_stop_510_);
lean_dec(v_stop_510_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_as_508_, v_i_boxed_512_, v_stop_boxed_513_, v_b_511_);
lean_dec_ref(v_as_508_);
return v_res_514_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(size_t v_sz_515_, size_t v_i_516_, lean_object* v_bs_517_){
_start:
{
uint8_t v___x_518_; 
v___x_518_ = lean_usize_dec_lt(v_i_516_, v_sz_515_);
if (v___x_518_ == 0)
{
return v_bs_517_;
}
else
{
lean_object* v_v_519_; lean_object* v_name_520_; lean_object* v___x_521_; lean_object* v_bs_x27_522_; lean_object* v___x_523_; lean_object* v___x_524_; size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v_v_519_ = lean_array_uget_borrowed(v_bs_517_, v_i_516_);
v_name_520_ = lean_ctor_get(v_v_519_, 1);
lean_inc(v_name_520_);
v___x_521_ = lean_unsigned_to_nat(0u);
v_bs_x27_522_ = lean_array_uset(v_bs_517_, v_i_516_, v___x_521_);
v___x_523_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_520_, v___x_518_);
v___x_524_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
v___x_525_ = ((size_t)1ULL);
v___x_526_ = lean_usize_add(v_i_516_, v___x_525_);
v___x_527_ = lean_array_uset(v_bs_x27_522_, v_i_516_, v___x_524_);
v_i_516_ = v___x_526_;
v_bs_517_ = v___x_527_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_515_ = stack[0].m_num;
size_t v_i_516_ = stack[1].m_num;
lean_object* v_bs_517_ = stack[2].m_obj;
lean_object* v_res_529_;
v_res_529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_515_, v_i_516_, v_bs_517_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_530_, lean_object* v_i_531_, lean_object* v_bs_532_){
_start:
{
size_t v_sz_boxed_533_; size_t v_i_boxed_534_; lean_object* v_res_535_; 
v_sz_boxed_533_ = lean_unbox_usize(v_sz_530_);
lean_dec(v_sz_530_);
v_i_boxed_534_ = lean_unbox_usize(v_i_531_);
lean_dec(v_i_531_);
v_res_535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_533_, v_i_boxed_534_, v_bs_532_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(lean_object* v_a_536_){
_start:
{
size_t v_sz_537_; size_t v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_sz_537_ = lean_array_size(v_a_536_);
v___x_538_ = ((size_t)0ULL);
v___x_539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_537_, v___x_538_, v_a_536_);
v___x_540_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(uint8_t v_fmt_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___y_544_; 
if (v_fmt_541_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_551_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_array_get_size(v_a_542_);
v___x_554_ = lean_nat_dec_lt(v___x_552_, v___x_553_);
if (v___x_554_ == 0)
{
lean_dec_ref(v_a_542_);
v___y_544_ = v___x_551_;
goto v___jp_543_;
}
else
{
size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; 
v___x_555_ = ((size_t)0ULL);
v___x_556_ = lean_usize_of_nat(v___x_553_);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_542_, v___x_555_, v___x_556_, v___x_551_);
lean_dec_ref(v_a_542_);
v___y_544_ = v___x_557_;
goto v___jp_543_;
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(v_a_542_);
v___x_559_ = l_Lean_Json_compress(v___x_558_);
return v___x_559_;
}
v___jp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_545_ = lean_unsigned_to_nat(1u);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_string_utf8_byte_size(v___y_544_);
lean_inc_ref(v___y_544_);
v___x_548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_548_, 0, v___y_544_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
lean_ctor_set(v___x_548_, 2, v___x_547_);
v___x_549_ = l_String_Slice_Pos_prevn(v___x_548_, v___x_547_, v___x_545_);
lean_dec_ref_known(v___x_548_, 3);
v___x_550_ = lean_string_utf8_extract_fast(v___y_544_, v___x_546_, v___x_549_);
lean_dec(v___x_549_);
lean_dec_ref(v___y_544_);
return v___x_550_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_541_ = stack[0].m_num;
lean_object* v_a_542_ = stack[1].m_obj;
lean_object* v_res_560_;
v_res_560_ = l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(v_fmt_541_, v_a_542_);
stack->m_obj
 = v_res_560_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0___boxed(lean_object* v_fmt_561_, lean_object* v_a_562_){
_start:
{
uint8_t v_fmt_boxed_563_; lean_object* v_res_564_; 
v_fmt_boxed_563_ = lean_unbox(v_fmt_561_);
v_res_564_ = l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(v_fmt_boxed_563_, v_a_562_);
return v_res_564_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0(lean_object* v_as_578_, size_t v_i_579_, size_t v_stop_580_, lean_object* v_b_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
uint8_t v___x_589_; 
v___x_589_ = lean_usize_dec_eq(v_i_579_, v_stop_580_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v_lib_591_; lean_object* v_pkg_592_; lean_object* v_name_593_; lean_object* v_keyName_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_590_ = lean_array_uget_borrowed(v_as_578_, v_i_579_);
v_lib_591_ = lean_ctor_get(v___x_590_, 0);
v_pkg_592_ = lean_ctor_get(v_lib_591_, 0);
v_name_593_ = lean_ctor_get(v___x_590_, 1);
v_keyName_594_ = lean_ctor_get(v_pkg_592_, 2);
v___x_595_ = l_Lake_Module_elabArtsFacet;
lean_inc(v_name_593_);
lean_inc(v_keyName_594_);
v___x_596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_596_, 0, v_keyName_594_);
lean_ctor_set(v___x_596_, 1, v_name_593_);
v___x_597_ = l_Lake_Module_keyword;
lean_inc(v___x_590_);
v___x_598_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
lean_ctor_set(v___x_598_, 2, v___x_590_);
lean_ctor_set(v___x_598_, 3, v___x_595_);
lean_inc_ref(v___y_582_);
lean_inc_ref(v___y_586_);
lean_inc(v___y_585_);
lean_inc(v___y_584_);
lean_inc(v___y_583_);
v___x_599_ = lean_apply_7(v___y_582_, v___x_598_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, lean_box(0));
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v_a_601_; lean_object* v___x_602_; size_t v___x_603_; size_t v___x_604_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
v_a_601_ = lean_ctor_get(v___x_599_, 1);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_599_, 2);
v___x_602_ = l_Lake_Job_mix___redArg(v_b_581_, v_a_600_);
v___x_603_ = ((size_t)1ULL);
v___x_604_ = lean_usize_add(v_i_579_, v___x_603_);
v_i_579_ = v___x_604_;
v_b_581_ = v___x_602_;
v___y_587_ = v_a_601_;
goto _start;
}
else
{
lean_object* v_a_606_; lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v___y_582_);
lean_dec_ref(v_b_581_);
v_a_606_ = lean_ctor_get(v___x_599_, 0);
v_a_607_ = lean_ctor_get(v___x_599_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_599_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_inc(v_a_606_);
lean_dec(v___x_599_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_606_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
else
{
lean_object* v___x_615_; 
lean_dec_ref(v___y_582_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v_b_581_);
lean_ctor_set(v___x_615_, 1, v___y_587_);
return v___x_615_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_578_ = stack[0].m_obj;
size_t v_i_579_ = stack[1].m_num;
size_t v_stop_580_ = stack[2].m_num;
lean_object* v_b_581_ = stack[3].m_obj;
lean_object* v___y_582_ = stack[4].m_obj;
lean_object* v___y_583_ = stack[5].m_obj;
lean_object* v___y_584_ = stack[6].m_obj;
lean_object* v___y_585_ = stack[7].m_obj;
lean_object* v___y_586_ = stack[8].m_obj;
lean_object* v___y_587_ = stack[9].m_obj;
lean_object* v_res_616_;
v_res_616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0(v_as_578_, v_i_579_, v_stop_580_, v_b_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
stack->m_obj
 = v_res_616_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0___boxed(lean_object* v_as_617_, lean_object* v_i_618_, lean_object* v_stop_619_, lean_object* v_b_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
size_t v_i_boxed_628_; size_t v_stop_boxed_629_; lean_object* v_res_630_; 
v_i_boxed_628_ = lean_unbox_usize(v_i_618_);
lean_dec(v_i_618_);
v_stop_boxed_629_ = lean_unbox_usize(v_stop_619_);
lean_dec(v_stop_619_);
v_res_630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0(v_as_617_, v_i_boxed_628_, v_stop_boxed_629_, v_b_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v_as_617_);
return v_res_630_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__1(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; uint8_t v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_635_ = 0;
v___x_636_ = 0;
v___x_637_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__0));
v___x_638_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_634_);
lean_ctor_set(v___x_638_, 2, v___x_633_);
lean_ctor_set_uint8(v___x_638_, sizeof(void*)*3, v___x_636_);
lean_ctor_set_uint8(v___x_638_, sizeof(void*)*3 + 1, v___x_635_);
lean_ctor_set_uint8(v___x_638_, sizeof(void*)*3 + 2, v___x_635_);
return v___x_638_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__2(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__1);
v___x_640_ = lean_box(0);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
return v___x_641_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__3(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__2);
v___x_643_ = lean_task_pure(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4(void){
_start:
{
uint8_t v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_644_ = 0;
v___x_645_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_646_ = lean_box(0);
v___x_647_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__3);
v___x_648_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_648_, 0, v___x_647_);
lean_ctor_set(v___x_648_, 1, v___x_646_);
lean_ctor_set(v___x_648_, 2, v___x_645_);
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*3, v___x_644_);
return v___x_648_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts(lean_object* v_self_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_pkg_657_; lean_object* v_name_658_; lean_object* v_keyName_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_pkg_657_ = lean_ctor_get(v_self_649_, 0);
v_name_658_ = lean_ctor_get(v_self_649_, 1);
v_keyName_659_ = lean_ctor_get(v_pkg_657_, 2);
v___x_660_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_658_);
lean_inc(v_keyName_659_);
v___x_661_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_661_, 0, v_keyName_659_);
lean_ctor_set(v___x_661_, 1, v_name_658_);
v___x_662_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_663_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
lean_ctor_set(v___x_663_, 2, v_self_649_);
lean_ctor_set(v___x_663_, 3, v___x_660_);
lean_inc_ref(v_a_650_);
lean_inc_ref(v_a_654_);
lean_inc(v_a_653_);
lean_inc(v_a_652_);
lean_inc(v_a_651_);
v___x_664_ = lean_apply_7(v_a_650_, v___x_663_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, lean_box(0));
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v_a_666_; lean_object* v___x_667_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
v_a_666_ = lean_ctor_get(v___x_664_, 1);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_664_, 2);
v___x_667_ = l_Lake_Job_await___redArg(v_a_665_, v_a_666_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_690_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_a_669_ = lean_ctor_get(v___x_667_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_690_ == 0)
{
v___x_671_ = v___x_667_;
v_isShared_672_ = v_isSharedCheck_690_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_690_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4);
v___x_675_ = lean_array_get_size(v_a_668_);
v___x_676_ = lean_nat_dec_lt(v___x_673_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_678_; 
lean_dec(v_a_668_);
lean_dec_ref(v_a_650_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_674_);
v___x_678_ = v___x_671_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_a_669_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
else
{
uint8_t v___x_680_; 
v___x_680_ = lean_nat_dec_le(v___x_675_, v___x_675_);
if (v___x_680_ == 0)
{
if (v___x_676_ == 0)
{
lean_object* v___x_682_; 
lean_dec(v_a_668_);
lean_dec_ref(v_a_650_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_674_);
v___x_682_ = v___x_671_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_a_669_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
else
{
size_t v___x_684_; size_t v___x_685_; lean_object* v___x_686_; 
lean_del_object(v___x_671_);
v___x_684_ = ((size_t)0ULL);
v___x_685_ = lean_usize_of_nat(v___x_675_);
v___x_686_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0(v_a_668_, v___x_684_, v___x_685_, v___x_674_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_669_);
lean_dec(v_a_668_);
return v___x_686_;
}
}
else
{
size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; 
lean_del_object(v___x_671_);
v___x_687_ = ((size_t)0ULL);
v___x_688_ = lean_usize_of_nat(v___x_675_);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_spec__0(v_a_668_, v___x_687_, v___x_688_, v___x_674_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_669_);
lean_dec(v_a_668_);
return v___x_689_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec_ref(v_a_650_);
v_a_691_ = lean_ctor_get(v___x_667_, 0);
v_a_692_ = lean_ctor_get(v___x_667_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_667_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_inc(v_a_691_);
lean_dec(v___x_667_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_691_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v_a_700_; lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec_ref(v_a_650_);
v_a_700_ = lean_ctor_get(v___x_664_, 0);
v_a_701_ = lean_ctor_get(v___x_664_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_664_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_inc(v_a_700_);
lean_dec(v___x_664_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_700_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_649_ = stack[0].m_obj;
lean_object* v_a_650_ = stack[1].m_obj;
lean_object* v_a_651_ = stack[2].m_obj;
lean_object* v_a_652_ = stack[3].m_obj;
lean_object* v_a_653_ = stack[4].m_obj;
lean_object* v_a_654_ = stack[5].m_obj;
lean_object* v_a_655_ = stack[6].m_obj;
lean_object* v_res_709_;
v_res_709_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts(v_self_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
stack->m_obj
 = v_res_709_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___boxed(lean_object* v_self_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts(v_self_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_a_713_);
lean_dec(v_a_712_);
return v_res_718_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_box(0);
v___x_720_ = l_Lean_Json_compress(v___x_719_);
return v___x_720_;
}
}
lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(uint8_t v_fmt_721_){
_start:
{
if (v_fmt_721_ == 0)
{
lean_object* v___x_722_; 
v___x_722_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
return v___x_722_;
}
else
{
lean_object* v___x_723_; 
v___x_723_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___closed__0);
return v___x_723_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_721_ = stack[0].m_num;
lean_object* v_res_724_;
v_res_724_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(v_fmt_721_);
stack->m_obj
 = v_res_724_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_725_){
_start:
{
uint8_t v_fmt_boxed_726_; lean_object* v_res_727_; 
v_fmt_boxed_726_ = lean_unbox(v_fmt_725_);
v_res_727_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(v_fmt_boxed_726_);
return v_res_727_;
}
}
lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0(uint8_t v_fmt_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(v_fmt_728_);
return v___x_730_;
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_728_ = stack[0].m_num;
lean_object* v_a_729_ = stack[1].m_obj;
lean_object* v_res_731_;
v_res_731_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0(v_fmt_728_, v_a_729_);
stack->m_obj
 = v_res_731_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___boxed(lean_object* v_fmt_732_, lean_object* v_a_733_){
_start:
{
uint8_t v_fmt_boxed_734_; lean_object* v_res_735_; 
v_fmt_boxed_734_ = lean_unbox(v_fmt_732_);
v_res_735_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0(v_fmt_boxed_734_, v_a_733_);
return v_res_735_;
}
}
lean_object* l_Lake_LeanLib_elabArtsFacetConfig___lam__0(uint8_t v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lake_formatQuery___at___00Lake_LeanLib_elabArtsFacetConfig_spec__0___redArg(v___y_736_);
return v___x_738_;
}
}
LEAN_EXPORT void l_Lake_LeanLib_elabArtsFacetConfig___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___y_736_ = stack[0].m_num;
lean_object* v___y_737_ = stack[1].m_obj;
lean_object* v_res_739_;
v_res_739_ = l_Lake_LeanLib_elabArtsFacetConfig___lam__0(v___y_736_, v___y_737_);
stack->m_obj
 = v_res_739_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_elabArtsFacetConfig___lam__0___boxed(lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
uint8_t v___y_73__boxed_742_; lean_object* v_res_743_; 
v___y_73__boxed_742_ = lean_unbox(v___y_740_);
v_res_743_ = l_Lake_LeanLib_elabArtsFacetConfig___lam__0(v___y_73__boxed_742_, v___y_741_);
return v_res_743_;
}
}
static lean_object* _init_l_Lake_LeanLib_elabArtsFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___f_746_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_747_ = 1;
v___x_748_ = l_Lake_instDataKindUnit;
v___x_749_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__1));
v___x_750_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_751_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___x_749_);
lean_ctor_set(v___x_751_, 2, v___x_748_);
lean_ctor_set(v___x_751_, 3, v___f_746_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*4, v___x_747_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*4 + 1, v___x_747_);
return v___x_751_;
}
}
static lean_object* _init_l_Lake_LeanLib_elabArtsFacetConfig(void){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_obj_once(&l_Lake_LeanLib_elabArtsFacetConfig___closed__2, &l_Lake_LeanLib_elabArtsFacetConfig___closed__2_once, _init_l_Lake_LeanLib_elabArtsFacetConfig___closed__2);
return v___x_752_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(lean_object* v_as_753_, size_t v_i_754_, size_t v_stop_755_, lean_object* v_b_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = lean_usize_dec_eq(v_i_754_, v_stop_755_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v_lib_766_; lean_object* v_pkg_767_; lean_object* v_name_768_; lean_object* v_keyName_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_765_ = lean_array_uget_borrowed(v_as_753_, v_i_754_);
v_lib_766_ = lean_ctor_get(v___x_765_, 0);
v_pkg_767_ = lean_ctor_get(v_lib_766_, 0);
v_name_768_ = lean_ctor_get(v___x_765_, 1);
v_keyName_769_ = lean_ctor_get(v_pkg_767_, 2);
v___x_770_ = l_Lake_Module_irArtsFacet;
lean_inc(v_name_768_);
lean_inc(v_keyName_769_);
v___x_771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_771_, 0, v_keyName_769_);
lean_ctor_set(v___x_771_, 1, v_name_768_);
v___x_772_ = l_Lake_Module_keyword;
lean_inc(v___x_765_);
v___x_773_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
lean_ctor_set(v___x_773_, 2, v___x_765_);
lean_ctor_set(v___x_773_, 3, v___x_770_);
lean_inc_ref(v___y_757_);
lean_inc_ref(v___y_761_);
lean_inc(v___y_760_);
lean_inc(v___y_759_);
lean_inc(v___y_758_);
v___x_774_ = lean_apply_7(v___y_757_, v___x_773_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, lean_box(0));
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v_a_776_; lean_object* v___x_777_; size_t v___x_778_; size_t v___x_779_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
v_a_776_ = lean_ctor_get(v___x_774_, 1);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_774_, 2);
v___x_777_ = l_Lake_Job_mix___redArg(v_b_756_, v_a_775_);
v___x_778_ = ((size_t)1ULL);
v___x_779_ = lean_usize_add(v_i_754_, v___x_778_);
v_i_754_ = v___x_779_;
v_b_756_ = v___x_777_;
v___y_762_ = v_a_776_;
goto _start;
}
else
{
lean_object* v_a_781_; lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec_ref(v___y_757_);
lean_dec_ref(v_b_756_);
v_a_781_ = lean_ctor_get(v___x_774_, 0);
v_a_782_ = lean_ctor_get(v___x_774_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_774_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_inc(v_a_781_);
lean_dec(v___x_774_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_781_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
else
{
lean_object* v___x_790_; 
lean_dec_ref(v___y_757_);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v_b_756_);
lean_ctor_set(v___x_790_, 1, v___y_762_);
return v___x_790_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_753_ = stack[0].m_obj;
size_t v_i_754_ = stack[1].m_num;
size_t v_stop_755_ = stack[2].m_num;
lean_object* v_b_756_ = stack[3].m_obj;
lean_object* v___y_757_ = stack[4].m_obj;
lean_object* v___y_758_ = stack[5].m_obj;
lean_object* v___y_759_ = stack[6].m_obj;
lean_object* v___y_760_ = stack[7].m_obj;
lean_object* v___y_761_ = stack[8].m_obj;
lean_object* v___y_762_ = stack[9].m_obj;
lean_object* v_res_791_;
v_res_791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(v_as_753_, v_i_754_, v_stop_755_, v_b_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
stack->m_obj
 = v_res_791_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0___boxed(lean_object* v_as_792_, lean_object* v_i_793_, lean_object* v_stop_794_, lean_object* v_b_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
size_t v_i_boxed_803_; size_t v_stop_boxed_804_; lean_object* v_res_805_; 
v_i_boxed_803_ = lean_unbox_usize(v_i_793_);
lean_dec(v_i_793_);
v_stop_boxed_804_ = lean_unbox_usize(v_stop_794_);
lean_dec(v_stop_794_);
v_res_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(v_as_792_, v_i_boxed_803_, v_stop_boxed_804_, v_b_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v_as_792_);
return v_res_805_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts(lean_object* v_self_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_pkg_814_; lean_object* v_name_815_; lean_object* v_keyName_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_pkg_814_ = lean_ctor_get(v_self_806_, 0);
v_name_815_ = lean_ctor_get(v_self_806_, 1);
v_keyName_816_ = lean_ctor_get(v_pkg_814_, 2);
v___x_817_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_815_);
lean_inc(v_keyName_816_);
v___x_818_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_818_, 0, v_keyName_816_);
lean_ctor_set(v___x_818_, 1, v_name_815_);
v___x_819_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_820_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
lean_ctor_set(v___x_820_, 2, v_self_806_);
lean_ctor_set(v___x_820_, 3, v___x_817_);
lean_inc_ref(v_a_807_);
lean_inc_ref(v_a_811_);
lean_inc(v_a_810_);
lean_inc(v_a_809_);
lean_inc(v_a_808_);
v___x_821_ = lean_apply_7(v_a_807_, v___x_820_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, lean_box(0));
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v_a_823_; lean_object* v___x_824_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
v_a_823_ = lean_ctor_get(v___x_821_, 1);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_821_, 2);
v___x_824_ = l_Lake_Job_await___redArg(v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_847_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_a_826_ = lean_ctor_get(v___x_824_, 1);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_847_ == 0)
{
v___x_828_ = v___x_824_;
v_isShared_829_ = v_isSharedCheck_847_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_847_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__4);
v___x_832_ = lean_array_get_size(v_a_825_);
v___x_833_ = lean_nat_dec_lt(v___x_830_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_835_; 
lean_dec(v_a_825_);
lean_dec_ref(v_a_807_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_831_);
v___x_835_ = v___x_828_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_a_826_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
uint8_t v___x_837_; 
v___x_837_ = lean_nat_dec_le(v___x_832_, v___x_832_);
if (v___x_837_ == 0)
{
if (v___x_833_ == 0)
{
lean_object* v___x_839_; 
lean_dec(v_a_825_);
lean_dec_ref(v_a_807_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_831_);
v___x_839_ = v___x_828_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_831_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v_a_826_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
size_t v___x_841_; size_t v___x_842_; lean_object* v___x_843_; 
lean_del_object(v___x_828_);
v___x_841_ = ((size_t)0ULL);
v___x_842_ = lean_usize_of_nat(v___x_832_);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(v_a_825_, v___x_841_, v___x_842_, v___x_831_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_826_);
lean_dec(v_a_825_);
return v___x_843_;
}
}
else
{
size_t v___x_844_; size_t v___x_845_; lean_object* v___x_846_; 
lean_del_object(v___x_828_);
v___x_844_ = ((size_t)0ULL);
v___x_845_ = lean_usize_of_nat(v___x_832_);
v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_spec__0(v_a_825_, v___x_844_, v___x_845_, v___x_831_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_826_);
lean_dec(v_a_825_);
return v___x_846_;
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref(v_a_807_);
v_a_848_ = lean_ctor_get(v___x_824_, 0);
v_a_849_ = lean_ctor_get(v___x_824_, 1);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_824_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_inc(v_a_848_);
lean_dec(v___x_824_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_848_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_object* v_a_857_; lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref(v_a_807_);
v_a_857_ = lean_ctor_get(v___x_821_, 0);
v_a_858_ = lean_ctor_get(v___x_821_, 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_821_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_inc(v_a_857_);
lean_dec(v___x_821_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_857_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_806_ = stack[0].m_obj;
lean_object* v_a_807_ = stack[1].m_obj;
lean_object* v_a_808_ = stack[2].m_obj;
lean_object* v_a_809_ = stack[3].m_obj;
lean_object* v_a_810_ = stack[4].m_obj;
lean_object* v_a_811_ = stack[5].m_obj;
lean_object* v_a_812_ = stack[6].m_obj;
lean_object* v_res_866_;
v_res_866_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts(v_self_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
stack->m_obj
 = v_res_866_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts___boxed(lean_object* v_self_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildIRArts(v_self_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec(v_a_870_);
lean_dec(v_a_869_);
return v_res_875_;
}
}
static lean_object* _init_l_Lake_LeanLib_irArtsFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_877_; uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___f_877_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_878_ = 1;
v___x_879_ = l_Lake_instDataKindUnit;
v___x_880_ = ((lean_object*)(l_Lake_LeanLib_irArtsFacetConfig___closed__0));
v___x_881_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_882_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___x_880_);
lean_ctor_set(v___x_882_, 2, v___x_879_);
lean_ctor_set(v___x_882_, 3, v___f_877_);
lean_ctor_set_uint8(v___x_882_, sizeof(void*)*4, v___x_878_);
lean_ctor_set_uint8(v___x_882_, sizeof(void*)*4 + 1, v___x_878_);
return v___x_882_;
}
}
static lean_object* _init_l_Lake_LeanLib_irArtsFacetConfig(void){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = lean_obj_once(&l_Lake_LeanLib_irArtsFacetConfig___closed__1, &l_Lake_LeanLib_irArtsFacetConfig___closed__1_once, _init_l_Lake_LeanLib_irArtsFacetConfig___closed__1);
return v___x_883_;
}
}
lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0(lean_object* v_x_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_pkg_892_; lean_object* v_name_893_; lean_object* v_keyName_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_pkg_892_ = lean_ctor_get(v_x_884_, 0);
v_name_893_ = lean_ctor_get(v_x_884_, 1);
v_keyName_894_ = lean_ctor_get(v_pkg_892_, 2);
v___x_895_ = l_Lake_LeanLib_irArtsFacet;
lean_inc(v_name_893_);
lean_inc(v_keyName_894_);
v___x_896_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_896_, 0, v_keyName_894_);
lean_ctor_set(v___x_896_, 1, v_name_893_);
v___x_897_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_898_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
lean_ctor_set(v___x_898_, 2, v_x_884_);
lean_ctor_set(v___x_898_, 3, v___x_895_);
lean_inc_ref(v___y_889_);
lean_inc(v___y_888_);
lean_inc(v___y_887_);
lean_inc(v___y_886_);
v___x_899_ = lean_apply_7(v___y_885_, v___x_898_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, lean_box(0));
return v___x_899_;
}
}
LEAN_EXPORT void l_Lake_LeanLib_leanArtsFacetConfig___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_884_ = stack[0].m_obj;
lean_object* v___y_885_ = stack[1].m_obj;
lean_object* v___y_886_ = stack[2].m_obj;
lean_object* v___y_887_ = stack[3].m_obj;
lean_object* v___y_888_ = stack[4].m_obj;
lean_object* v___y_889_ = stack[5].m_obj;
lean_object* v___y_890_ = stack[6].m_obj;
lean_object* v_res_900_;
v_res_900_ = l_Lake_LeanLib_leanArtsFacetConfig___lam__0(v_x_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
stack->m_obj
 = v_res_900_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(lean_object* v_x_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lake_LeanLib_leanArtsFacetConfig___lam__0(v_x_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec(v___y_904_);
lean_dec(v___y_903_);
return v_res_909_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_911_; lean_object* v___f_912_; uint8_t v___x_913_; lean_object* v___x_914_; lean_object* v___f_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_911_ = 0;
v___f_912_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_913_ = 1;
v___x_914_ = l_Lake_instDataKindUnit;
v___f_915_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_916_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_917_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___f_915_);
lean_ctor_set(v___x_917_, 2, v___x_914_);
lean_ctor_set(v___x_917_, 3, v___f_912_);
lean_ctor_set_uint8(v___x_917_, sizeof(void*)*4, v___x_913_);
lean_ctor_set_uint8(v___x_917_, sizeof(void*)*4 + 1, v___x_911_);
return v___x_917_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig(void){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = lean_obj_once(&l_Lake_LeanLib_leanArtsFacetConfig___closed__1, &l_Lake_LeanLib_leanArtsFacetConfig___closed__1_once, _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__1);
return v___x_918_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(lean_object* v_a_919_, lean_object* v_x_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lake_ModuleFacet_fetch___redArg(v_x_920_, v_a_919_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_928_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_919_ = stack[0].m_obj;
lean_object* v_x_920_ = stack[1].m_obj;
lean_object* v___y_921_ = stack[2].m_obj;
lean_object* v___y_922_ = stack[3].m_obj;
lean_object* v___y_923_ = stack[4].m_obj;
lean_object* v___y_924_ = stack[5].m_obj;
lean_object* v___y_925_ = stack[6].m_obj;
lean_object* v___y_926_ = stack[7].m_obj;
lean_object* v_res_929_;
v_res_929_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(v_a_919_, v_x_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
stack->m_obj
 = v_res_929_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object* v_a_930_, lean_object* v_x_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(v_a_930_, v_x_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec(v___y_934_);
lean_dec(v___y_933_);
return v_res_939_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(uint8_t v_shouldExport_940_, lean_object* v___x_941_, lean_object* v_bs_942_, lean_object* v_a_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_lib_951_; lean_object* v_config_952_; lean_object* v_nativeFacets_953_; lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v___x_956_; size_t v_sz_957_; size_t v___x_958_; lean_object* v___x_189763__overap_959_; lean_object* v___x_960_; 
v_lib_951_ = lean_ctor_get(v_a_943_, 0);
v_config_952_ = lean_ctor_get(v_lib_951_, 2);
v_nativeFacets_953_ = lean_ctor_get(v_config_952_, 8);
lean_inc_ref(v_nativeFacets_953_);
v___f_954_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed), 9, 1);
lean_closure_set(v___f_954_, 0, v_a_943_);
v___x_955_ = lean_box(v_shouldExport_940_);
v___x_956_ = lean_apply_1(v_nativeFacets_953_, v___x_955_);
v_sz_957_ = lean_array_size(v___x_956_);
v___x_958_ = ((size_t)0ULL);
v___x_189763__overap_959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_941_, v___f_954_, v_sz_957_, v___x_958_, v___x_956_);
lean_inc_ref(v___y_948_);
lean_inc(v___y_947_);
lean_inc(v___y_946_);
lean_inc(v___y_945_);
v___x_960_ = lean_apply_7(v___x_189763__overap_959_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, lean_box(0));
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_970_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_a_962_ = lean_ctor_get(v___x_960_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_970_ == 0)
{
v___x_964_ = v___x_960_;
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_970_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = l_Array_append___redArg(v_bs_942_, v_a_961_);
lean_dec(v_a_961_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_966_);
v___x_968_ = v___x_964_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_a_962_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
else
{
lean_dec_ref(v_bs_942_);
return v___x_960_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_shouldExport_940_ = stack[0].m_num;
lean_object* v___x_941_ = stack[1].m_obj;
lean_object* v_bs_942_ = stack[2].m_obj;
lean_object* v_a_943_ = stack[3].m_obj;
lean_object* v___y_944_ = stack[4].m_obj;
lean_object* v___y_945_ = stack[5].m_obj;
lean_object* v___y_946_ = stack[6].m_obj;
lean_object* v___y_947_ = stack[7].m_obj;
lean_object* v___y_948_ = stack[8].m_obj;
lean_object* v___y_949_ = stack[9].m_obj;
lean_object* v_res_971_;
v_res_971_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(v_shouldExport_940_, v___x_941_, v_bs_942_, v_a_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
stack->m_obj
 = v_res_971_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed(lean_object* v_shouldExport_972_, lean_object* v___x_973_, lean_object* v_bs_974_, lean_object* v_a_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
uint8_t v_shouldExport_boxed_983_; lean_object* v_res_984_; 
v_shouldExport_boxed_983_ = lean_unbox(v_shouldExport_972_);
v_res_984_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(v_shouldExport_boxed_983_, v___x_973_, v_bs_974_, v_a_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec(v___y_978_);
lean_dec(v___y_977_);
return v_res_984_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(lean_object* v___x_985_, lean_object* v_pkg_986_, lean_object* v_x_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lake_Target_fetchIn___redArg(v___x_985_, v_pkg_986_, v_x_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
return v___x_995_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_985_ = stack[0].m_obj;
lean_object* v_pkg_986_ = stack[1].m_obj;
lean_object* v_x_987_ = stack[2].m_obj;
lean_object* v___y_988_ = stack[3].m_obj;
lean_object* v___y_989_ = stack[4].m_obj;
lean_object* v___y_990_ = stack[5].m_obj;
lean_object* v___y_991_ = stack[6].m_obj;
lean_object* v___y_992_ = stack[7].m_obj;
lean_object* v___y_993_ = stack[8].m_obj;
lean_object* v_res_996_;
v_res_996_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(v___x_985_, v_pkg_986_, v_x_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
stack->m_obj
 = v_res_996_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object* v___x_997_, lean_object* v_pkg_998_, lean_object* v_x_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(v___x_997_, v_pkg_998_, v_x_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec(v___y_1001_);
return v_res_1007_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object* v_a_1008_, lean_object* v_x_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_log_1018_; uint8_t v_action_1019_; uint8_t v_wantsRebuild_1020_; uint8_t v_canceled_1021_; lean_object* v_trace_1022_; lean_object* v_buildTime_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v_log_1018_ = lean_ctor_get(v___y_1016_, 0);
v_action_1019_ = lean_ctor_get_uint8(v___y_1016_, sizeof(void*)*3);
v_wantsRebuild_1020_ = lean_ctor_get_uint8(v___y_1016_, sizeof(void*)*3 + 1);
v_canceled_1021_ = lean_ctor_get_uint8(v___y_1016_, sizeof(void*)*3 + 2);
v_trace_1022_ = lean_ctor_get(v___y_1016_, 1);
v_buildTime_1023_ = lean_ctor_get(v___y_1016_, 2);
v___x_1024_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_1025_ = lean_string_append(v___y_1010_, v___x_1024_);
v___x_1026_ = lean_io_prim_handle_put_str(v_a_1008_, v___x_1025_);
lean_dec_ref(v___x_1025_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1028_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v_a_1027_);
lean_ctor_set(v___x_1028_, 1, v___y_1016_);
return v___x_1028_;
}
else
{
lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1042_; 
lean_inc(v_buildTime_1023_);
lean_inc_ref(v_trace_1022_);
lean_inc_ref(v_log_1018_);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___y_1016_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; lean_object* v_unused_1044_; lean_object* v_unused_1045_; 
v_unused_1043_ = lean_ctor_get(v___y_1016_, 2);
lean_dec(v_unused_1043_);
v_unused_1044_ = lean_ctor_get(v___y_1016_, 1);
lean_dec(v_unused_1044_);
v_unused_1045_ = lean_ctor_get(v___y_1016_, 0);
lean_dec(v_unused_1045_);
v___x_1030_ = v___y_1016_;
v_isShared_1031_ = v_isSharedCheck_1042_;
goto v_resetjp_1029_;
}
else
{
lean_dec(v___y_1016_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1042_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_a_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v_a_1032_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1026_, 1);
v___x_1033_ = lean_io_error_to_string(v_a_1032_);
v___x_1034_ = 3;
v___x_1035_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set_uint8(v___x_1035_, sizeof(void*)*1, v___x_1034_);
v___x_1036_ = lean_array_get_size(v_log_1018_);
v___x_1037_ = lean_array_push(v_log_1018_, v___x_1035_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1037_);
v___x_1039_ = v___x_1030_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_trace_1022_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_buildTime_1023_);
lean_ctor_set_uint8(v_reuseFailAlloc_1041_, sizeof(void*)*3, v_action_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1041_, sizeof(void*)*3 + 1, v_wantsRebuild_1020_);
lean_ctor_set_uint8(v_reuseFailAlloc_1041_, sizeof(void*)*3 + 2, v_canceled_1021_);
v___x_1039_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1036_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1008_ = stack[0].m_obj;
lean_object* v_x_1009_ = stack[1].m_obj;
lean_object* v___y_1010_ = stack[2].m_obj;
lean_object* v___y_1011_ = stack[3].m_obj;
lean_object* v___y_1012_ = stack[4].m_obj;
lean_object* v___y_1013_ = stack[5].m_obj;
lean_object* v___y_1014_ = stack[6].m_obj;
lean_object* v___y_1015_ = stack[7].m_obj;
lean_object* v___y_1016_ = stack[8].m_obj;
lean_object* v_res_1046_;
v_res_1046_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(v_a_1008_, v_x_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
stack->m_obj
 = v_res_1046_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object* v_a_1047_, lean_object* v_x_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(v_a_1047_, v_x_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v_a_1047_);
return v_res_1057_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1065_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3));
v___x_1066_ = lean_unsigned_to_nat(5u);
v___x_1067_ = lean_mk_empty_array_with_capacity(v___x_1066_);
v___x_1068_ = lean_array_push(v___x_1067_, v___x_1065_);
return v___x_1068_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4));
v___x_1070_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6);
v___x_1071_ = lean_array_push(v___x_1070_, v___x_1069_);
return v___x_1071_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(uint8_t v_bootstrap_1074_, lean_object* v___y_1075_, lean_object* v_oFiles_1076_, uint8_t v_shouldExport_1077_, uint8_t v___x_1078_, lean_object* v___x_1079_, size_t v___x_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
if (v_bootstrap_1074_ == 0)
{
lean_object* v_toContext_1088_; lean_object* v_lakeEnv_1089_; lean_object* v_lean_1090_; lean_object* v_log_1091_; uint8_t v_action_1092_; uint8_t v_wantsRebuild_1093_; uint8_t v_canceled_1094_; lean_object* v_trace_1095_; lean_object* v_buildTime_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1126_; 
lean_dec_ref(v___y_1081_);
lean_dec_ref(v___x_1079_);
v_toContext_1088_ = lean_ctor_get(v___y_1085_, 1);
v_lakeEnv_1089_ = lean_ctor_get(v_toContext_1088_, 0);
v_lean_1090_ = lean_ctor_get(v_lakeEnv_1089_, 1);
v_log_1091_ = lean_ctor_get(v___y_1086_, 0);
v_action_1092_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*3);
v_wantsRebuild_1093_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*3 + 1);
v_canceled_1094_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*3 + 2);
v_trace_1095_ = lean_ctor_get(v___y_1086_, 1);
v_buildTime_1096_ = lean_ctor_get(v___y_1086_, 2);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___y_1086_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1098_ = v___y_1086_;
v_isShared_1099_ = v_isSharedCheck_1126_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_buildTime_1096_);
lean_inc(v_trace_1095_);
lean_inc(v_log_1091_);
lean_dec(v___y_1086_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1126_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v_ar_1100_; lean_object* v___x_1101_; 
v_ar_1100_ = lean_ctor_get(v_lean_1090_, 13);
lean_inc_ref(v_ar_1100_);
v___x_1101_ = l_Lake_compileStaticLib(v___y_1075_, v_oFiles_1076_, v_ar_1100_, v_bootstrap_1074_, v_log_1091_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1113_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_a_1103_ = lean_ctor_get(v___x_1101_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1105_ = v___x_1101_;
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1113_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v_a_1103_);
v___x_1108_ = v___x_1098_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1103_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_trace_1095_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_buildTime_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*3, v_action_1092_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*3 + 1, v_wantsRebuild_1093_);
lean_ctor_set_uint8(v_reuseFailAlloc_1112_, sizeof(void*)*3 + 2, v_canceled_1094_);
v___x_1108_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1110_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 1, v___x_1108_);
v___x_1110_ = v___x_1105_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1102_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1125_; 
v_a_1114_ = lean_ctor_get(v___x_1101_, 0);
v_a_1115_ = lean_ctor_get(v___x_1101_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1117_ = v___x_1101_;
v_isShared_1118_ = v_isSharedCheck_1125_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_inc(v_a_1114_);
lean_dec(v___x_1101_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1125_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v_a_1115_);
v___x_1120_ = v___x_1098_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1115_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_trace_1095_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_buildTime_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*3, v_action_1092_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*3 + 1, v_wantsRebuild_1093_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*3 + 2, v_canceled_1094_);
v___x_1120_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1122_; 
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 1, v___x_1120_);
v___x_1122_ = v___x_1117_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1114_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
else
{
uint8_t v___x_1127_; 
v___x_1127_ = l_System_Platform_isOSX;
if (v___x_1127_ == 0)
{
uint8_t v___x_1128_; 
lean_dec_ref(v___y_1081_);
lean_dec_ref(v___x_1079_);
v___x_1128_ = l_System_Platform_isWindows;
if (v___x_1128_ == 0)
{
lean_object* v_toContext_1129_; lean_object* v_lakeEnv_1130_; lean_object* v_lean_1131_; lean_object* v_log_1132_; uint8_t v_action_1133_; uint8_t v_wantsRebuild_1134_; uint8_t v_canceled_1135_; lean_object* v_trace_1136_; lean_object* v_buildTime_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1167_; 
v_toContext_1129_ = lean_ctor_get(v___y_1085_, 1);
v_lakeEnv_1130_ = lean_ctor_get(v_toContext_1129_, 0);
v_lean_1131_ = lean_ctor_get(v_lakeEnv_1130_, 1);
v_log_1132_ = lean_ctor_get(v___y_1086_, 0);
v_action_1133_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*3);
v_wantsRebuild_1134_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*3 + 1);
v_canceled_1135_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*3 + 2);
v_trace_1136_ = lean_ctor_get(v___y_1086_, 1);
v_buildTime_1137_ = lean_ctor_get(v___y_1086_, 2);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___y_1086_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1139_ = v___y_1086_;
v_isShared_1140_ = v_isSharedCheck_1167_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_buildTime_1137_);
lean_inc(v_trace_1136_);
lean_inc(v_log_1132_);
lean_dec(v___y_1086_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1167_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v_ar_1141_; lean_object* v___x_1142_; 
v_ar_1141_ = lean_ctor_get(v_lean_1131_, 13);
lean_inc_ref(v_ar_1141_);
v___x_1142_ = l_Lake_compileStaticLib(v___y_1075_, v_oFiles_1076_, v_ar_1141_, v___x_1128_, v_log_1132_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1154_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_a_1144_ = lean_ctor_get(v___x_1142_, 1);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1146_ = v___x_1142_;
v_isShared_1147_ = v_isSharedCheck_1154_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1154_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v_a_1144_);
v___x_1149_ = v___x_1139_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1144_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_trace_1136_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_buildTime_1137_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, sizeof(void*)*3, v_action_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, sizeof(void*)*3 + 1, v_wantsRebuild_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, sizeof(void*)*3 + 2, v_canceled_1135_);
v___x_1149_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1151_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 1, v___x_1149_);
v___x_1151_ = v___x_1146_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1143_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v___x_1149_);
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
else
{
lean_object* v_a_1155_; lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1166_; 
v_a_1155_ = lean_ctor_get(v___x_1142_, 0);
v_a_1156_ = lean_ctor_get(v___x_1142_, 1);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1158_ = v___x_1142_;
v_isShared_1159_ = v_isSharedCheck_1166_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_inc(v_a_1155_);
lean_dec(v___x_1142_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1166_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v_a_1156_);
v___x_1161_ = v___x_1139_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1156_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_trace_1136_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_buildTime_1137_);
lean_ctor_set_uint8(v_reuseFailAlloc_1165_, sizeof(void*)*3, v_action_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1165_, sizeof(void*)*3 + 1, v_wantsRebuild_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1165_, sizeof(void*)*3 + 2, v_canceled_1135_);
v___x_1161_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 1, v___x_1161_);
v___x_1163_ = v___x_1158_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1155_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1168_; lean_object* v_lakeEnv_1169_; lean_object* v_lean_1170_; lean_object* v_log_1171_; uint8_t v_action_1172_; uint8_t v_wantsRebuild_1173_; uint8_t v_canceled_1174_; lean_object* v_trace_1175_; lean_object* v_buildTime_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1206_; 
v_toContext_1168_ = lean_ctor_get(v___y_1085_, 1);
v_lakeEnv_1169_ = lean_ctor_get(v_toContext_1168_, 0);
v_lean_1170_ = lean_ctor_get(v_lakeEnv_1169_, 1);
v_log_1171_ = lean_ctor_get(v___y_1086_, 0);
v_action_1172_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*3);
v_wantsRebuild_1173_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*3 + 1);
v_canceled_1174_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*3 + 2);
v_trace_1175_ = lean_ctor_get(v___y_1086_, 1);
v_buildTime_1176_ = lean_ctor_get(v___y_1086_, 2);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___y_1086_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1178_ = v___y_1086_;
v_isShared_1179_ = v_isSharedCheck_1206_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_buildTime_1176_);
lean_inc(v_trace_1175_);
lean_inc(v_log_1171_);
lean_dec(v___y_1086_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1206_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_ar_1180_; lean_object* v___x_1181_; 
v_ar_1180_ = lean_ctor_get(v_lean_1170_, 13);
lean_inc_ref(v_ar_1180_);
v___x_1181_ = l_Lake_compileStaticLib(v___y_1075_, v_oFiles_1076_, v_ar_1180_, v_shouldExport_1077_, v_log_1171_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1193_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_a_1183_ = lean_ctor_get(v___x_1181_, 1);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1185_ = v___x_1181_;
v_isShared_1186_ = v_isSharedCheck_1193_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1193_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v_a_1183_);
v___x_1188_ = v___x_1178_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1183_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_trace_1175_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_buildTime_1176_);
lean_ctor_set_uint8(v_reuseFailAlloc_1192_, sizeof(void*)*3, v_action_1172_);
lean_ctor_set_uint8(v_reuseFailAlloc_1192_, sizeof(void*)*3 + 1, v_wantsRebuild_1173_);
lean_ctor_set_uint8(v_reuseFailAlloc_1192_, sizeof(void*)*3 + 2, v_canceled_1174_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1190_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v___x_1188_);
v___x_1190_ = v___x_1185_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1182_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1205_; 
v_a_1194_ = lean_ctor_get(v___x_1181_, 0);
v_a_1195_ = lean_ctor_get(v___x_1181_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1197_ = v___x_1181_;
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_inc(v_a_1194_);
lean_dec(v___x_1181_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v_a_1195_);
v___x_1200_ = v___x_1178_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1195_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_trace_1175_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_buildTime_1176_);
lean_ctor_set_uint8(v_reuseFailAlloc_1204_, sizeof(void*)*3, v_action_1172_);
lean_ctor_set_uint8(v_reuseFailAlloc_1204_, sizeof(void*)*3 + 1, v_wantsRebuild_1173_);
lean_ctor_set_uint8(v_reuseFailAlloc_1204_, sizeof(void*)*3 + 2, v_canceled_1174_);
v___x_1200_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1202_; 
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 1, v___x_1200_);
v___x_1202_ = v___x_1197_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1194_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1207_; uint8_t v_action_1208_; uint8_t v_wantsRebuild_1209_; uint8_t v_canceled_1210_; lean_object* v_trace_1211_; lean_object* v_buildTime_1212_; lean_object* v___x_1213_; 
v_log_1207_ = lean_ctor_get(v___y_1086_, 0);
v_action_1208_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*3);
v_wantsRebuild_1209_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*3 + 1);
v_canceled_1210_ = lean_ctor_get_uint8(v___y_1086_, sizeof(void*)*3 + 2);
v_trace_1211_ = lean_ctor_get(v___y_1086_, 1);
v_buildTime_1212_ = lean_ctor_get(v___y_1086_, 2);
lean_inc_ref(v___y_1075_);
v___x_1213_ = l_Lake_createParentDirs(v___y_1075_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_a_1217_; lean_object* v___y_1265_; uint8_t v___x_1267_; lean_object* v___x_1268_; 
lean_dec_ref_known(v___x_1213_, 1);
v___x_1214_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1075_);
v___x_1215_ = l_System_FilePath_addExtension(v___y_1075_, v___x_1214_);
v___x_1267_ = 1;
v___x_1268_ = lean_io_prim_handle_mk(v___x_1215_, v___x_1267_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_array_get_size(v_oFiles_1076_);
v___x_1272_ = lean_nat_dec_lt(v___x_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_dec(v_a_1269_);
lean_dec_ref(v___y_1081_);
lean_dec_ref(v___x_1079_);
lean_dec_ref(v_oFiles_1076_);
v_a_1217_ = v___y_1086_;
goto v___jp_1216_;
}
else
{
lean_object* v___f_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___f_1273_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1273_, 0, v_a_1269_);
v___x_1274_ = lean_box(0);
v___x_1275_ = lean_nat_dec_le(v___x_1271_, v___x_1271_);
if (v___x_1275_ == 0)
{
if (v___x_1272_ == 0)
{
lean_dec_ref(v___f_1273_);
lean_dec_ref(v___y_1081_);
lean_dec_ref(v___x_1079_);
lean_dec_ref(v_oFiles_1076_);
v_a_1217_ = v___y_1086_;
goto v___jp_1216_;
}
else
{
size_t v___x_1276_; lean_object* v___x_189921__overap_1277_; lean_object* v___x_1278_; 
v___x_1276_ = lean_usize_of_nat(v___x_1271_);
v___x_189921__overap_1277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1079_, v___f_1273_, v_oFiles_1076_, v___x_1080_, v___x_1276_, v___x_1274_);
lean_inc_ref(v___y_1085_);
lean_inc(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc(v___y_1082_);
v___x_1278_ = lean_apply_7(v___x_189921__overap_1277_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, lean_box(0));
v___y_1265_ = v___x_1278_;
goto v___jp_1264_;
}
}
else
{
size_t v___x_1279_; lean_object* v___x_189923__overap_1280_; lean_object* v___x_1281_; 
v___x_1279_ = lean_usize_of_nat(v___x_1271_);
v___x_189923__overap_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1079_, v___f_1273_, v_oFiles_1076_, v___x_1080_, v___x_1279_, v___x_1274_);
lean_inc_ref(v___y_1085_);
lean_inc(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc(v___y_1082_);
v___x_1281_ = lean_apply_7(v___x_189923__overap_1280_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, lean_box(0));
v___y_1265_ = v___x_1281_;
goto v___jp_1264_;
}
}
}
else
{
lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1295_; 
lean_inc(v_buildTime_1212_);
lean_inc_ref(v_trace_1211_);
lean_inc_ref(v_log_1207_);
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___y_1081_);
lean_dec_ref(v___x_1079_);
lean_dec_ref(v_oFiles_1076_);
lean_dec_ref(v___y_1075_);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___y_1086_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; lean_object* v_unused_1297_; lean_object* v_unused_1298_; 
v_unused_1296_ = lean_ctor_get(v___y_1086_, 2);
lean_dec(v_unused_1296_);
v_unused_1297_ = lean_ctor_get(v___y_1086_, 1);
lean_dec(v_unused_1297_);
v_unused_1298_ = lean_ctor_get(v___y_1086_, 0);
lean_dec(v_unused_1298_);
v___x_1283_ = v___y_1086_;
v_isShared_1284_ = v_isSharedCheck_1295_;
goto v_resetjp_1282_;
}
else
{
lean_dec(v___y_1086_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1295_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_a_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v_a_1285_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1268_, 1);
v___x_1286_ = lean_io_error_to_string(v_a_1285_);
v___x_1287_ = 3;
v___x_1288_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1288_, 0, v___x_1286_);
lean_ctor_set_uint8(v___x_1288_, sizeof(void*)*1, v___x_1287_);
v___x_1289_ = lean_array_get_size(v_log_1207_);
v___x_1290_ = lean_array_push(v_log_1207_, v___x_1288_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1290_);
v___x_1292_ = v___x_1283_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_trace_1211_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v_buildTime_1212_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*3, v_action_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*3 + 1, v_wantsRebuild_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*3 + 2, v_canceled_1210_);
v___x_1292_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1289_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
return v___x_1293_;
}
}
}
v___jp_1216_:
{
lean_object* v___x_1218_; lean_object* v_log_1219_; uint8_t v_action_1220_; uint8_t v_wantsRebuild_1221_; uint8_t v_canceled_1222_; lean_object* v_trace_1223_; lean_object* v_buildTime_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1263_; 
v___x_1218_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1219_ = lean_ctor_get(v_a_1217_, 0);
v_action_1220_ = lean_ctor_get_uint8(v_a_1217_, sizeof(void*)*3);
v_wantsRebuild_1221_ = lean_ctor_get_uint8(v_a_1217_, sizeof(void*)*3 + 1);
v_canceled_1222_ = lean_ctor_get_uint8(v_a_1217_, sizeof(void*)*3 + 2);
v_trace_1223_ = lean_ctor_get(v_a_1217_, 1);
v_buildTime_1224_ = lean_ctor_get(v_a_1217_, 2);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_a_1217_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1226_ = v_a_1217_;
v_isShared_1227_ = v_isSharedCheck_1263_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_buildTime_1224_);
lean_inc(v_trace_1223_);
lean_inc(v_log_1219_);
lean_dec(v_a_1217_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1263_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1228_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1229_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1230_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1231_ = lean_array_push(v___x_1230_, v___y_1075_);
v___x_1232_ = lean_array_push(v___x_1231_, v___x_1229_);
v___x_1233_ = lean_array_push(v___x_1232_, v___x_1215_);
v___x_1234_ = lean_box(0);
v___x_1235_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1236_ = 0;
v___x_1237_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1237_, 0, v___x_1218_);
lean_ctor_set(v___x_1237_, 1, v___x_1228_);
lean_ctor_set(v___x_1237_, 2, v___x_1233_);
lean_ctor_set(v___x_1237_, 3, v___x_1234_);
lean_ctor_set(v___x_1237_, 4, v___x_1235_);
lean_ctor_set_uint8(v___x_1237_, sizeof(void*)*5, v___x_1078_);
lean_ctor_set_uint8(v___x_1237_, sizeof(void*)*5 + 1, v___x_1236_);
v___x_1238_ = l_Lake_proc(v___x_1237_, v___x_1236_, v___x_1234_, v_log_1219_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1250_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_a_1240_ = lean_ctor_get(v___x_1238_, 1);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1242_ = v___x_1238_;
v_isShared_1243_ = v_isSharedCheck_1250_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1250_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v_a_1240_);
v___x_1245_ = v___x_1226_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1240_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_trace_1223_);
lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_buildTime_1224_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*3, v_action_1220_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*3 + 1, v_wantsRebuild_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*3 + 2, v_canceled_1222_);
v___x_1245_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1247_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___x_1245_);
v___x_1247_ = v___x_1242_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1239_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1262_; 
v_a_1251_ = lean_ctor_get(v___x_1238_, 0);
v_a_1252_ = lean_ctor_get(v___x_1238_, 1);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1254_ = v___x_1238_;
v_isShared_1255_ = v_isSharedCheck_1262_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_inc(v_a_1251_);
lean_dec(v___x_1238_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1262_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v_a_1252_);
v___x_1257_ = v___x_1226_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1252_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_trace_1223_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_buildTime_1224_);
lean_ctor_set_uint8(v_reuseFailAlloc_1261_, sizeof(void*)*3, v_action_1220_);
lean_ctor_set_uint8(v_reuseFailAlloc_1261_, sizeof(void*)*3 + 1, v_wantsRebuild_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1261_, sizeof(void*)*3 + 2, v_canceled_1222_);
v___x_1257_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1259_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 1, v___x_1257_);
v___x_1259_ = v___x_1254_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1251_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1257_);
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
}
}
v___jp_1264_:
{
if (lean_obj_tag(v___y_1265_) == 0)
{
lean_object* v_a_1266_; 
v_a_1266_ = lean_ctor_get(v___y_1265_, 1);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___y_1265_, 2);
v_a_1217_ = v_a_1266_;
goto v___jp_1216_;
}
else
{
lean_dec_ref(v___x_1215_);
lean_dec_ref(v___y_1075_);
return v___y_1265_;
}
}
}
else
{
lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1312_; 
lean_inc(v_buildTime_1212_);
lean_inc_ref(v_trace_1211_);
lean_inc_ref(v_log_1207_);
lean_dec_ref(v___y_1081_);
lean_dec_ref(v___x_1079_);
lean_dec_ref(v_oFiles_1076_);
lean_dec_ref(v___y_1075_);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___y_1086_);
if (v_isSharedCheck_1312_ == 0)
{
lean_object* v_unused_1313_; lean_object* v_unused_1314_; lean_object* v_unused_1315_; 
v_unused_1313_ = lean_ctor_get(v___y_1086_, 2);
lean_dec(v_unused_1313_);
v_unused_1314_ = lean_ctor_get(v___y_1086_, 1);
lean_dec(v_unused_1314_);
v_unused_1315_ = lean_ctor_get(v___y_1086_, 0);
lean_dec(v_unused_1315_);
v___x_1300_ = v___y_1086_;
v_isShared_1301_ = v_isSharedCheck_1312_;
goto v_resetjp_1299_;
}
else
{
lean_dec(v___y_1086_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1312_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v_a_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1309_; 
v_a_1302_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1302_);
lean_dec_ref_known(v___x_1213_, 1);
v___x_1303_ = lean_io_error_to_string(v_a_1302_);
v___x_1304_ = 3;
v___x_1305_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1305_, 0, v___x_1303_);
lean_ctor_set_uint8(v___x_1305_, sizeof(void*)*1, v___x_1304_);
v___x_1306_ = lean_array_get_size(v_log_1207_);
v___x_1307_ = lean_array_push(v_log_1207_, v___x_1305_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1307_);
v___x_1309_ = v___x_1300_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_trace_1211_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v_buildTime_1212_);
lean_ctor_set_uint8(v_reuseFailAlloc_1311_, sizeof(void*)*3, v_action_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1311_, sizeof(void*)*3 + 1, v_wantsRebuild_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1311_, sizeof(void*)*3 + 2, v_canceled_1210_);
v___x_1309_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1306_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
return v___x_1310_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_bootstrap_1074_ = stack[0].m_num;
lean_object* v___y_1075_ = stack[1].m_obj;
lean_object* v_oFiles_1076_ = stack[2].m_obj;
uint8_t v_shouldExport_1077_ = stack[3].m_num;
uint8_t v___x_1078_ = stack[4].m_num;
lean_object* v___x_1079_ = stack[5].m_obj;
size_t v___x_1080_ = stack[6].m_num;
lean_object* v___y_1081_ = stack[7].m_obj;
lean_object* v___y_1082_ = stack[8].m_obj;
lean_object* v___y_1083_ = stack[9].m_obj;
lean_object* v___y_1084_ = stack[10].m_obj;
lean_object* v___y_1085_ = stack[11].m_obj;
lean_object* v___y_1086_ = stack[12].m_obj;
lean_object* v_res_1316_;
v_res_1316_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(v_bootstrap_1074_, v___y_1075_, v_oFiles_1076_, v_shouldExport_1077_, v___x_1078_, v___x_1079_, v___x_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
stack->m_obj
 = v_res_1316_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object* v_bootstrap_1317_, lean_object* v___y_1318_, lean_object* v_oFiles_1319_, lean_object* v_shouldExport_1320_, lean_object* v___x_1321_, lean_object* v___x_1322_, lean_object* v___x_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v_bootstrap_boxed_1331_; uint8_t v_shouldExport_boxed_1332_; uint8_t v___x_190400__boxed_1333_; size_t v___x_190402__boxed_1334_; lean_object* v_res_1335_; 
v_bootstrap_boxed_1331_ = lean_unbox(v_bootstrap_1317_);
v_shouldExport_boxed_1332_ = lean_unbox(v_shouldExport_1320_);
v___x_190400__boxed_1333_ = lean_unbox(v___x_1321_);
v___x_190402__boxed_1334_ = lean_unbox_usize(v___x_1323_);
lean_dec(v___x_1323_);
v_res_1335_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(v_bootstrap_boxed_1331_, v___y_1318_, v_oFiles_1319_, v_shouldExport_boxed_1332_, v___x_190400__boxed_1333_, v___x_1322_, v___x_190402__boxed_1334_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec(v___y_1325_);
return v_res_1335_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(uint8_t v_bootstrap_1337_, lean_object* v___y_1338_, uint8_t v_shouldExport_1339_, uint8_t v___x_1340_, lean_object* v___x_1341_, size_t v___x_1342_, lean_object* v_oFiles_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___y_1355_; uint8_t v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1351_ = lean_box(v_bootstrap_1337_);
v___x_1352_ = lean_box(v_shouldExport_1339_);
v___x_1353_ = lean_box(v___x_1340_);
v___x_1354_ = lean_box_usize(v___x_1342_);
lean_inc_ref(v___y_1338_);
v___y_1355_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed), 14, 7);
lean_closure_set(v___y_1355_, 0, v___x_1351_);
lean_closure_set(v___y_1355_, 1, v___y_1338_);
lean_closure_set(v___y_1355_, 2, v_oFiles_1343_);
lean_closure_set(v___y_1355_, 3, v___x_1352_);
lean_closure_set(v___y_1355_, 4, v___x_1353_);
lean_closure_set(v___y_1355_, 5, v___x_1341_);
lean_closure_set(v___y_1355_, 6, v___x_1354_);
v___x_1356_ = 0;
v___x_1357_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1358_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1338_, v___y_1355_, v___x_1356_, v___x_1357_, v___x_1340_, v___x_1356_, v___x_1356_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1368_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_a_1360_ = lean_ctor_get(v___x_1358_, 1);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1362_ = v___x_1358_;
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v_path_1364_; lean_object* v___x_1366_; 
v_path_1364_ = lean_ctor_get(v_a_1359_, 1);
lean_inc_ref(v_path_1364_);
lean_dec(v_a_1359_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v_path_1364_);
v___x_1366_ = v___x_1362_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_path_1364_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_a_1360_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
else
{
lean_object* v_a_1369_; lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
v_a_1369_ = lean_ctor_get(v___x_1358_, 0);
v_a_1370_ = lean_ctor_get(v___x_1358_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1358_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_inc(v_a_1369_);
lean_dec(v___x_1358_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1369_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5_0interp(lean_interpreter_value* stack)
{
uint8_t v_bootstrap_1337_ = stack[0].m_num;
lean_object* v___y_1338_ = stack[1].m_obj;
uint8_t v_shouldExport_1339_ = stack[2].m_num;
uint8_t v___x_1340_ = stack[3].m_num;
lean_object* v___x_1341_ = stack[4].m_obj;
size_t v___x_1342_ = stack[5].m_num;
lean_object* v_oFiles_1343_ = stack[6].m_obj;
lean_object* v___y_1344_ = stack[7].m_obj;
lean_object* v___y_1345_ = stack[8].m_obj;
lean_object* v___y_1346_ = stack[9].m_obj;
lean_object* v___y_1347_ = stack[10].m_obj;
lean_object* v___y_1348_ = stack[11].m_obj;
lean_object* v___y_1349_ = stack[12].m_obj;
lean_object* v_res_1378_;
v_res_1378_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(v_bootstrap_1337_, v___y_1338_, v_shouldExport_1339_, v___x_1340_, v___x_1341_, v___x_1342_, v_oFiles_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
stack->m_obj
 = v_res_1378_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object* v_bootstrap_1379_, lean_object* v___y_1380_, lean_object* v_shouldExport_1381_, lean_object* v___x_1382_, lean_object* v___x_1383_, lean_object* v___x_1384_, lean_object* v_oFiles_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
uint8_t v_bootstrap_boxed_1393_; uint8_t v_shouldExport_boxed_1394_; uint8_t v___x_191045__boxed_1395_; size_t v___x_191047__boxed_1396_; lean_object* v_res_1397_; 
v_bootstrap_boxed_1393_ = lean_unbox(v_bootstrap_1379_);
v_shouldExport_boxed_1394_ = lean_unbox(v_shouldExport_1381_);
v___x_191045__boxed_1395_ = lean_unbox(v___x_1382_);
v___x_191047__boxed_1396_ = lean_unbox_usize(v___x_1384_);
lean_dec(v___x_1384_);
v_res_1397_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(v_bootstrap_boxed_1393_, v___y_1380_, v_shouldExport_boxed_1394_, v___x_191045__boxed_1395_, v___x_1383_, v___x_191047__boxed_1396_, v_oFiles_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec(v___y_1387_);
return v_res_1397_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object* v_config_1402_, lean_object* v_config_1403_, uint8_t v_shouldExport_1404_, uint8_t v___x_1405_, lean_object* v___x_1406_, lean_object* v___x_1407_, lean_object* v___x_1408_, lean_object* v___x_1409_, lean_object* v___f_1410_, lean_object* v_dir_1411_, lean_object* v_self_1412_, lean_object* v___x_1413_, lean_object* v___f_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
uint8_t v___y_1423_; size_t v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v_a_1443_; lean_object* v_a_1444_; lean_object* v___x_1487_; 
lean_inc_ref(v___y_1415_);
lean_inc_ref(v___y_1419_);
lean_inc(v___y_1418_);
lean_inc(v___y_1417_);
lean_inc(v___x_1408_);
v___x_1487_ = lean_apply_7(v___y_1415_, v___x_1413_, v___x_1408_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, lean_box(0));
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v_a_1489_; lean_object* v___x_1490_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
v_a_1489_ = lean_ctor_get(v___x_1487_, 1);
lean_inc(v_a_1489_);
lean_dec_ref_known(v___x_1487_, 2);
v___x_1490_ = l_Lake_Job_await___redArg(v_a_1488_, v_a_1489_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v_a_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
v_a_1492_ = lean_ctor_get(v___x_1490_, 1);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1490_, 2);
v___x_1493_ = lean_unsigned_to_nat(0u);
v___x_1494_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_1495_ = lean_array_get_size(v_a_1491_);
v___x_1496_ = lean_nat_dec_lt(v___x_1493_, v___x_1495_);
if (v___x_1496_ == 0)
{
lean_dec(v_a_1491_);
lean_dec_ref(v___f_1414_);
v_a_1443_ = v___x_1494_;
v_a_1444_ = v_a_1492_;
goto v___jp_1442_;
}
else
{
size_t v___x_1497_; size_t v___x_1498_; lean_object* v___x_190051__overap_1499_; lean_object* v___x_1500_; 
v___x_1497_ = ((size_t)0ULL);
v___x_1498_ = lean_usize_of_nat(v___x_1495_);
lean_inc_ref(v___x_1409_);
v___x_190051__overap_1499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1409_, v___f_1414_, v_a_1491_, v___x_1497_, v___x_1498_, v___x_1494_);
lean_inc_ref(v___y_1419_);
lean_inc(v___y_1418_);
lean_inc(v___y_1417_);
lean_inc(v___x_1408_);
lean_inc_ref(v___y_1415_);
v___x_1500_ = lean_apply_7(v___x_190051__overap_1499_, v___y_1415_, v___x_1408_, v___y_1417_, v___y_1418_, v___y_1419_, v_a_1492_, lean_box(0));
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v_a_1502_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
v_a_1502_ = lean_ctor_get(v___x_1500_, 1);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1500_, 2);
v_a_1443_ = v_a_1501_;
v_a_1444_ = v_a_1502_;
goto v___jp_1442_;
}
else
{
lean_object* v_a_1503_; lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec_ref(v___y_1415_);
lean_dec_ref(v_self_1412_);
lean_dec_ref(v_dir_1411_);
lean_dec_ref(v___f_1410_);
lean_dec_ref(v___x_1409_);
lean_dec(v___x_1408_);
lean_dec(v___x_1407_);
lean_dec_ref(v___x_1406_);
lean_dec_ref(v_config_1402_);
v_a_1503_ = lean_ctor_get(v___x_1500_, 0);
v_a_1504_ = lean_ctor_get(v___x_1500_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1500_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_inc(v_a_1503_);
lean_dec(v___x_1500_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1503_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref(v___y_1415_);
lean_dec_ref(v___f_1414_);
lean_dec_ref(v_self_1412_);
lean_dec_ref(v_dir_1411_);
lean_dec_ref(v___f_1410_);
lean_dec_ref(v___x_1409_);
lean_dec(v___x_1408_);
lean_dec(v___x_1407_);
lean_dec_ref(v___x_1406_);
lean_dec_ref(v_config_1402_);
v_a_1512_ = lean_ctor_get(v___x_1490_, 0);
v_a_1513_ = lean_ctor_get(v___x_1490_, 1);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1490_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_inc(v_a_1512_);
lean_dec(v___x_1490_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1512_);
lean_ctor_set(v_reuseFailAlloc_1519_, 1, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec_ref(v___y_1415_);
lean_dec_ref(v___f_1414_);
lean_dec_ref(v_self_1412_);
lean_dec_ref(v_dir_1411_);
lean_dec_ref(v___f_1410_);
lean_dec_ref(v___x_1409_);
lean_dec(v___x_1408_);
lean_dec(v___x_1407_);
lean_dec_ref(v___x_1406_);
lean_dec_ref(v_config_1402_);
v_a_1521_ = lean_ctor_get(v___x_1487_, 0);
v_a_1522_ = lean_ctor_get(v___x_1487_, 1);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1487_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_inc(v_a_1521_);
lean_dec(v___x_1487_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1521_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
v___jp_1422_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___f_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1429_ = lean_box(v___y_1423_);
v___x_1430_ = lean_box(v_shouldExport_1404_);
v___x_1431_ = lean_box(v___x_1405_);
v___x_1432_ = lean_box_usize(v___y_1424_);
v___f_1433_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed), 14, 6);
lean_closure_set(v___f_1433_, 0, v___x_1429_);
lean_closure_set(v___f_1433_, 1, v___y_1428_);
lean_closure_set(v___f_1433_, 2, v___x_1430_);
lean_closure_set(v___f_1433_, 3, v___x_1431_);
lean_closure_set(v___f_1433_, 4, v___x_1406_);
lean_closure_set(v___f_1433_, 5, v___x_1432_);
v___x_1434_ = l_Array_append___redArg(v___y_1425_, v___y_1426_);
lean_dec_ref(v___y_1426_);
v___x_1435_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_1436_ = l_Lake_Job_collectArray___redArg(v___x_1434_, v___x_1435_);
lean_dec_ref(v___x_1434_);
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = 0;
v___x_1439_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_1440_ = l_Lake_Job_mapM___redArg(v___x_1407_, v___x_1436_, v___f_1433_, v___x_1437_, v___x_1438_, v___y_1415_, v___x_1408_, v___y_1417_, v___y_1418_, v___y_1419_, v___x_1439_);
lean_dec(v___x_1408_);
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
lean_ctor_set(v___x_1441_, 1, v___y_1427_);
return v___x_1441_;
}
v___jp_1442_:
{
lean_object* v_toLeanConfig_1445_; lean_object* v_toLeanConfig_1446_; uint8_t v_bootstrap_1447_; lean_object* v_buildDir_1448_; lean_object* v_nativeLibDir_1449_; lean_object* v_moreLinkObjs_1450_; lean_object* v_moreLinkObjs_1451_; lean_object* v___x_1452_; size_t v_sz_1453_; size_t v___x_1454_; lean_object* v___x_190009__overap_1455_; lean_object* v___x_1456_; 
v_toLeanConfig_1445_ = lean_ctor_get(v_config_1402_, 1);
lean_inc_ref(v_toLeanConfig_1445_);
v_toLeanConfig_1446_ = lean_ctor_get(v_config_1403_, 0);
v_bootstrap_1447_ = lean_ctor_get_uint8(v_config_1402_, sizeof(void*)*28);
v_buildDir_1448_ = lean_ctor_get(v_config_1402_, 5);
lean_inc_ref(v_buildDir_1448_);
v_nativeLibDir_1449_ = lean_ctor_get(v_config_1402_, 7);
lean_inc_ref(v_nativeLibDir_1449_);
lean_dec_ref(v_config_1402_);
v_moreLinkObjs_1450_ = lean_ctor_get(v_toLeanConfig_1445_, 6);
lean_inc_ref(v_moreLinkObjs_1450_);
lean_dec_ref(v_toLeanConfig_1445_);
v_moreLinkObjs_1451_ = lean_ctor_get(v_toLeanConfig_1446_, 6);
v___x_1452_ = l_Array_append___redArg(v_moreLinkObjs_1450_, v_moreLinkObjs_1451_);
v_sz_1453_ = lean_array_size(v___x_1452_);
v___x_1454_ = ((size_t)0ULL);
v___x_190009__overap_1455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1409_, v___f_1410_, v_sz_1453_, v___x_1454_, v___x_1452_);
lean_inc_ref(v___y_1419_);
lean_inc(v___y_1418_);
lean_inc(v___y_1417_);
lean_inc(v___x_1408_);
lean_inc_ref(v___y_1415_);
v___x_1456_ = lean_apply_7(v___x_190009__overap_1455_, v___y_1415_, v___x_1408_, v___y_1417_, v___y_1418_, v___y_1419_, v_a_1444_, lean_box(0));
if (lean_obj_tag(v___x_1456_) == 0)
{
if (v_shouldExport_1404_ == 0)
{
lean_object* v_a_1457_; lean_object* v_a_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
v_a_1458_ = lean_ctor_get(v___x_1456_, 1);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1456_, 2);
v___x_1459_ = l_System_FilePath_normalize(v_buildDir_1448_);
v___x_1460_ = l_Lake_joinRelative(v_dir_1411_, v___x_1459_);
v___x_1461_ = l_System_FilePath_normalize(v_nativeLibDir_1449_);
v___x_1462_ = l_Lake_joinRelative(v___x_1460_, v___x_1461_);
v___x_1463_ = l_Lake_LeanLib_libName(v_self_1412_);
v___x_1464_ = l_Lake_nameToStaticLib(v___x_1463_, v_shouldExport_1404_);
v___x_1465_ = l_Lake_joinRelative(v___x_1462_, v___x_1464_);
v___y_1423_ = v_bootstrap_1447_;
v___y_1424_ = v___x_1454_;
v___y_1425_ = v_a_1443_;
v___y_1426_ = v_a_1457_;
v___y_1427_ = v_a_1458_;
v___y_1428_ = v___x_1465_;
goto v___jp_1422_;
}
else
{
lean_object* v_a_1466_; lean_object* v_a_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_a_1466_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1466_);
v_a_1467_ = lean_ctor_get(v___x_1456_, 1);
lean_inc(v_a_1467_);
lean_dec_ref_known(v___x_1456_, 2);
v___x_1468_ = l_System_FilePath_normalize(v_buildDir_1448_);
v___x_1469_ = l_Lake_joinRelative(v_dir_1411_, v___x_1468_);
v___x_1470_ = l_System_FilePath_normalize(v_nativeLibDir_1449_);
v___x_1471_ = l_Lake_joinRelative(v___x_1469_, v___x_1470_);
v___x_1472_ = l_Lake_LeanLib_libName(v_self_1412_);
v___x_1473_ = 0;
v___x_1474_ = l_Lake_nameToStaticLib(v___x_1472_, v___x_1473_);
v___x_1475_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_1476_ = l_System_FilePath_addExtension(v___x_1474_, v___x_1475_);
v___x_1477_ = l_Lake_joinRelative(v___x_1471_, v___x_1476_);
v___y_1423_ = v_bootstrap_1447_;
v___y_1424_ = v___x_1454_;
v___y_1425_ = v_a_1443_;
v___y_1426_ = v_a_1466_;
v___y_1427_ = v_a_1467_;
v___y_1428_ = v___x_1477_;
goto v___jp_1422_;
}
}
else
{
lean_object* v_a_1478_; lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v_nativeLibDir_1449_);
lean_dec_ref(v_buildDir_1448_);
lean_dec_ref(v_a_1443_);
lean_dec_ref(v___y_1415_);
lean_dec_ref(v_self_1412_);
lean_dec_ref(v_dir_1411_);
lean_dec(v___x_1408_);
lean_dec(v___x_1407_);
lean_dec_ref(v___x_1406_);
v_a_1478_ = lean_ctor_get(v___x_1456_, 0);
v_a_1479_ = lean_ctor_get(v___x_1456_, 1);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1456_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_inc(v_a_1478_);
lean_dec(v___x_1456_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1478_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_1402_ = stack[0].m_obj;
lean_object* v_config_1403_ = stack[1].m_obj;
uint8_t v_shouldExport_1404_ = stack[2].m_num;
uint8_t v___x_1405_ = stack[3].m_num;
lean_object* v___x_1406_ = stack[4].m_obj;
lean_object* v___x_1407_ = stack[5].m_obj;
lean_object* v___x_1408_ = stack[6].m_obj;
lean_object* v___x_1409_ = stack[7].m_obj;
lean_object* v___f_1410_ = stack[8].m_obj;
lean_object* v_dir_1411_ = stack[9].m_obj;
lean_object* v_self_1412_ = stack[10].m_obj;
lean_object* v___x_1413_ = stack[11].m_obj;
lean_object* v___f_1414_ = stack[12].m_obj;
lean_object* v___y_1415_ = stack[13].m_obj;
lean_object* v___y_1416_ = stack[14].m_obj;
lean_object* v___y_1417_ = stack[15].m_obj;
lean_object* v___y_1418_ = stack[16].m_obj;
lean_object* v___y_1419_ = stack[17].m_obj;
lean_object* v___y_1420_ = stack[18].m_obj;
lean_object* v_res_1530_;
v_res_1530_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(v_config_1402_, v_config_1403_, v_shouldExport_1404_, v___x_1405_, v___x_1406_, v___x_1407_, v___x_1408_, v___x_1409_, v___f_1410_, v_dir_1411_, v_self_1412_, v___x_1413_, v___f_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
stack->m_obj
 = v_res_1530_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed(lean_object** _args){
lean_object* v_config_1531_ = _args[0];
lean_object* v_config_1532_ = _args[1];
lean_object* v_shouldExport_1533_ = _args[2];
lean_object* v___x_1534_ = _args[3];
lean_object* v___x_1535_ = _args[4];
lean_object* v___x_1536_ = _args[5];
lean_object* v___x_1537_ = _args[6];
lean_object* v___x_1538_ = _args[7];
lean_object* v___f_1539_ = _args[8];
lean_object* v_dir_1540_ = _args[9];
lean_object* v_self_1541_ = _args[10];
lean_object* v___x_1542_ = _args[11];
lean_object* v___f_1543_ = _args[12];
lean_object* v___y_1544_ = _args[13];
lean_object* v___y_1545_ = _args[14];
lean_object* v___y_1546_ = _args[15];
lean_object* v___y_1547_ = _args[16];
lean_object* v___y_1548_ = _args[17];
lean_object* v___y_1549_ = _args[18];
lean_object* v___y_1550_ = _args[19];
_start:
{
uint8_t v_shouldExport_boxed_1551_; uint8_t v___x_191192__boxed_1552_; lean_object* v_res_1553_; 
v_shouldExport_boxed_1551_ = lean_unbox(v_shouldExport_1533_);
v___x_191192__boxed_1552_ = lean_unbox(v___x_1534_);
v_res_1553_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(v_config_1531_, v_config_1532_, v_shouldExport_boxed_1551_, v___x_191192__boxed_1552_, v___x_1535_, v___x_1536_, v___x_1537_, v___x_1538_, v___f_1539_, v_dir_1540_, v_self_1541_, v___x_1542_, v___f_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec(v_config_1532_);
return v_res_1553_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object* v_self_1557_, uint8_t v_shouldExport_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v___x_1566_; lean_object* v_toApplicative_1567_; lean_object* v_toBind_1568_; lean_object* v_toFunctor_1569_; lean_object* v_toPure_1570_; lean_object* v___f_1571_; lean_object* v___f_1572_; lean_object* v___f_1573_; lean_object* v___f_1574_; lean_object* v___x_1575_; lean_object* v___f_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v_toBuildConfig_1584_; lean_object* v_registeredJobs_1585_; uint8_t v_verbosity_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___f_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; uint8_t v___x_1594_; lean_object* v___y_1596_; 
v___x_1566_ = l_instMonadBaseIO;
v_toApplicative_1567_ = lean_ctor_get(v___x_1566_, 0);
v_toBind_1568_ = lean_ctor_get(v___x_1566_, 1);
v_toFunctor_1569_ = lean_ctor_get(v_toApplicative_1567_, 0);
v_toPure_1570_ = lean_ctor_get(v_toApplicative_1567_, 1);
lean_inc_n(v_toBind_1568_, 3);
lean_inc_n(v_toPure_1570_, 5);
v___f_1571_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1571_, 0, v_toPure_1570_);
lean_closure_set(v___f_1571_, 1, v_toBind_1568_);
v___f_1572_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1572_, 0, v_toPure_1570_);
lean_closure_set(v___f_1572_, 1, v_toBind_1568_);
lean_inc_ref(v___f_1571_);
v___f_1573_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1573_, 0, v_toPure_1570_);
lean_closure_set(v___f_1573_, 1, v___f_1571_);
lean_inc_ref_n(v_toFunctor_1569_, 2);
v___f_1574_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1574_, 0, v_toFunctor_1569_);
lean_closure_set(v___f_1574_, 1, v_toPure_1570_);
lean_closure_set(v___f_1574_, 2, v_toBind_1568_);
v___x_1575_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1569_);
v___f_1576_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1576_, 0, v_toPure_1570_);
v___x_1577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___f_1576_);
lean_ctor_set(v___x_1577_, 2, v___f_1574_);
lean_ctor_set(v___x_1577_, 3, v___f_1573_);
lean_ctor_set(v___x_1577_, 4, v___f_1572_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v___f_1571_);
v___x_1579_ = l_ReaderT_instMonad___redArg(v___x_1578_);
v___x_1580_ = l_StateRefT_x27_instMonad___redArg(v___x_1579_);
v___x_1581_ = l_ReaderT_instMonad___redArg(v___x_1580_);
v___x_1582_ = l_ReaderT_instMonad___redArg(v___x_1581_);
v___x_1583_ = l_Lake_EquipT_instMonad___redArg(v___x_1582_);
v_toBuildConfig_1584_ = lean_ctor_get(v_a_1563_, 0);
v_registeredJobs_1585_ = lean_ctor_get(v_a_1563_, 4);
v_verbosity_1586_ = lean_ctor_get_uint8(v_toBuildConfig_1584_, sizeof(void*)*5 + 4);
v___x_1587_ = l_Lake_instDataKindFilePath;
v___x_1588_ = lean_box(v_shouldExport_1558_);
lean_inc_ref(v___x_1583_);
v___f_1589_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1589_, 0, v___x_1588_);
lean_closure_set(v___f_1589_, 1, v___x_1583_);
v___x_1590_ = lean_box(v_verbosity_1586_);
v___x_1591_ = lean_obj_tag_nat(v___x_1590_);
lean_dec(v___x_1590_);
v___x_1592_ = lean_unsigned_to_nat(2u);
v___x_1593_ = lean_nat_dec_eq(v___x_1591_, v___x_1592_);
v___x_1594_ = 1;
if (v___x_1593_ == 0)
{
lean_object* v___x_1642_; 
v___x_1642_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_1596_ = v___x_1642_;
goto v___jp_1595_;
}
else
{
if (v_shouldExport_1558_ == 0)
{
lean_object* v___x_1643_; 
v___x_1643_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___y_1596_ = v___x_1643_;
goto v___jp_1595_;
}
else
{
lean_object* v___x_1644_; 
v___x_1644_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_1596_ = v___x_1644_;
goto v___jp_1595_;
}
}
v___jp_1595_:
{
lean_object* v_pkg_1597_; lean_object* v_name_1598_; lean_object* v_config_1599_; lean_object* v_keyName_1600_; lean_object* v_dir_1601_; lean_object* v_config_1602_; lean_object* v___f_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___f_1615_; uint8_t v___x_1616_; lean_object* v___x_1617_; 
v_pkg_1597_ = lean_ctor_get(v_self_1557_, 0);
v_name_1598_ = lean_ctor_get(v_self_1557_, 1);
v_config_1599_ = lean_ctor_get(v_self_1557_, 2);
lean_inc(v_config_1599_);
v_keyName_1600_ = lean_ctor_get(v_pkg_1597_, 2);
v_dir_1601_ = lean_ctor_get(v_pkg_1597_, 4);
lean_inc_ref(v_dir_1601_);
v_config_1602_ = lean_ctor_get(v_pkg_1597_, 6);
lean_inc_ref(v_config_1602_);
lean_inc_ref_n(v_pkg_1597_, 2);
v___f_1603_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(v___f_1603_, 0, v___x_1587_);
lean_closure_set(v___f_1603_, 1, v_pkg_1597_);
lean_inc_n(v_name_1598_, 2);
v___x_1604_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1598_, v___x_1594_);
v___x_1605_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0));
v___x_1606_ = lean_string_append(v___x_1604_, v___x_1605_);
v___x_1607_ = lean_string_append(v___x_1606_, v___y_1596_);
v___x_1608_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_1600_);
v___x_1609_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1609_, 0, v_keyName_1600_);
lean_ctor_set(v___x_1609_, 1, v_name_1598_);
v___x_1610_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_1557_);
v___x_1611_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1609_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
lean_ctor_set(v___x_1611_, 2, v_self_1557_);
lean_ctor_set(v___x_1611_, 3, v___x_1608_);
v___x_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1612_, 0, v_pkg_1597_);
v___x_1613_ = lean_box(v_shouldExport_1558_);
v___x_1614_ = lean_box(v___x_1594_);
lean_inc_ref(v___x_1583_);
v___f_1615_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed), 20, 13);
lean_closure_set(v___f_1615_, 0, v_config_1602_);
lean_closure_set(v___f_1615_, 1, v_config_1599_);
lean_closure_set(v___f_1615_, 2, v___x_1613_);
lean_closure_set(v___f_1615_, 3, v___x_1614_);
lean_closure_set(v___f_1615_, 4, v___x_1583_);
lean_closure_set(v___f_1615_, 5, v___x_1587_);
lean_closure_set(v___f_1615_, 6, v___x_1612_);
lean_closure_set(v___f_1615_, 7, v___x_1583_);
lean_closure_set(v___f_1615_, 8, v___f_1603_);
lean_closure_set(v___f_1615_, 9, v_dir_1601_);
lean_closure_set(v___f_1615_, 10, v_self_1557_);
lean_closure_set(v___f_1615_, 11, v___x_1611_);
lean_closure_set(v___f_1615_, 12, v___f_1589_);
v___x_1616_ = 0;
v___x_1617_ = l_Lake_ensureJob___redArg(v___x_1587_, v___f_1615_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1641_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_a_1619_ = lean_ctor_get(v___x_1617_, 1);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1621_ = v___x_1617_;
v_isShared_1622_ = v_isSharedCheck_1641_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1641_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v_task_1623_; lean_object* v_kind_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1639_; 
v_task_1623_ = lean_ctor_get(v_a_1618_, 0);
v_kind_1624_ = lean_ctor_get(v_a_1618_, 1);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_a_1618_);
if (v_isSharedCheck_1639_ == 0)
{
lean_object* v_unused_1640_; 
v_unused_1640_ = lean_ctor_get(v_a_1618_, 2);
lean_dec(v_unused_1640_);
v___x_1626_ = v_a_1618_;
v_isShared_1627_ = v_isSharedCheck_1639_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_kind_1624_);
lean_inc(v_task_1623_);
lean_dec(v_a_1618_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1639_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v_job_1629_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 2, v___x_1607_);
v_job_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_task_1623_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_kind_1624_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v___x_1607_);
v_job_1629_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; 
lean_ctor_set_uint8(v_job_1629_, sizeof(void*)*3, v___x_1616_);
v___x_1630_ = lean_st_ref_take(v_registeredJobs_1585_);
lean_inc_ref(v_job_1629_);
v___x_1631_ = l_Lake_Job_toOpaque___redArg(v_job_1629_);
v___x_1632_ = lean_array_push(v___x_1630_, v___x_1631_);
v___x_1633_ = lean_st_ref_put(v_registeredJobs_1585_, v___x_1632_);
v___x_1634_ = l_Lake_Job_renew___redArg(v_job_1629_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1634_);
v___x_1636_ = v___x_1621_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_a_1619_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1607_);
return v___x_1617_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1557_ = stack[0].m_obj;
uint8_t v_shouldExport_1558_ = stack[1].m_num;
lean_object* v_a_1559_ = stack[2].m_obj;
lean_object* v_a_1560_ = stack[3].m_obj;
lean_object* v_a_1561_ = stack[4].m_obj;
lean_object* v_a_1562_ = stack[5].m_obj;
lean_object* v_a_1563_ = stack[6].m_obj;
lean_object* v_a_1564_ = stack[7].m_obj;
lean_object* v_res_1645_;
v_res_1645_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1557_, v_shouldExport_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
stack->m_obj
 = v_res_1645_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object* v_self_1646_, lean_object* v_shouldExport_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
uint8_t v_shouldExport_boxed_1655_; lean_object* v_res_1656_; 
v_shouldExport_boxed_1655_ = lean_unbox(v_shouldExport_1647_);
v_res_1656_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1646_, v_shouldExport_boxed_1655_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec(v_a_1649_);
return v_res_1656_;
}
}
lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t v_fmt_1657_, lean_object* v_a_1658_){
_start:
{
if (v_fmt_1657_ == 0)
{
return v_a_1658_;
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = l_Lake_mkRelPathString(v_a_1658_);
v___x_1660_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
v___x_1661_ = l_Lean_Json_compress(v___x_1660_);
return v___x_1661_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_1657_ = stack[0].m_num;
lean_object* v_a_1658_ = stack[1].m_obj;
lean_object* v_res_1662_;
v_res_1662_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_1657_, v_a_1658_);
stack->m_obj
 = v_res_1662_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object* v_fmt_1663_, lean_object* v_a_1664_){
_start:
{
uint8_t v_fmt_boxed_1665_; lean_object* v_res_1666_; 
v_fmt_boxed_1665_ = lean_unbox(v_fmt_1663_);
v_res_1666_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_boxed_1665_, v_a_1664_);
return v_res_1666_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2(void){
_start:
{
uint8_t v___x_1669_; lean_object* v_name_1670_; lean_object* v___x_1671_; 
v___x_1669_ = 1;
v_name_1670_ = l_Lake_instDataKindFilePath;
v___x_1671_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1670_, v___x_1669_);
return v___x_1671_;
}
}
lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* v_defaultPkg_1675_, lean_object* v_self_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_name_1684_; uint8_t v___x_1685_; lean_object* v___x_1686_; 
v_name_1684_ = l_Lake_instDataKindFilePath;
v___x_1685_ = 1;
lean_inc_ref_n(v_self_1676_, 2);
v___x_1686_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1675_, v_self_1676_, v_self_1676_, v___x_1685_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1728_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
v_a_1688_ = lean_ctor_get(v___x_1686_, 1);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1690_ = v___x_1686_;
v_isShared_1691_ = v_isSharedCheck_1728_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_inc(v_a_1687_);
lean_dec(v___x_1686_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1728_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___y_1693_; lean_object* v_snd_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1726_; 
v_snd_1711_ = lean_ctor_get(v_a_1687_, 1);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_a_1687_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v_a_1687_, 0);
lean_dec(v_unused_1727_);
v___x_1713_ = v_a_1687_;
v_isShared_1714_ = v_isSharedCheck_1726_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_snd_1711_);
lean_dec(v_a_1687_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1726_;
goto v_resetjp_1712_;
}
v___jp_1692_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1694_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1695_ = l_Lake_PartialBuildKey_toString(v_self_1676_);
v___x_1696_ = lean_string_append(v___x_1694_, v___x_1695_);
lean_dec_ref(v___x_1695_);
v___x_1697_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1698_ = lean_string_append(v___x_1696_, v___x_1697_);
v___x_1699_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
v___x_1700_ = lean_string_append(v___x_1698_, v___x_1699_);
v___x_1701_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1702_ = lean_string_append(v___x_1700_, v___x_1701_);
v___x_1703_ = lean_string_append(v___x_1702_, v___y_1693_);
lean_dec_ref(v___y_1693_);
v___x_1704_ = 3;
v___x_1705_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1705_, 0, v___x_1703_);
lean_ctor_set_uint8(v___x_1705_, sizeof(void*)*1, v___x_1704_);
v___x_1706_ = lean_array_get_size(v_a_1688_);
v___x_1707_ = lean_array_push(v_a_1688_, v___x_1705_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set_tag(v___x_1690_, 1);
lean_ctor_set(v___x_1690_, 1, v___x_1707_);
lean_ctor_set(v___x_1690_, 0, v___x_1706_);
v___x_1709_ = v___x_1690_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
v_resetjp_1712_:
{
lean_object* v_kind_1715_; uint8_t v___x_1716_; 
v_kind_1715_ = lean_ctor_get(v_snd_1711_, 1);
v___x_1716_ = lean_name_eq(v_kind_1715_, v_name_1684_);
if (v___x_1716_ == 0)
{
uint8_t v___x_1717_; 
lean_inc(v_kind_1715_);
lean_del_object(v___x_1713_);
lean_dec(v_snd_1711_);
v___x_1717_ = l_Lean_Name_isAnonymous(v_kind_1715_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1718_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1719_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1715_, v___x_1685_);
v___x_1720_ = lean_string_append(v___x_1718_, v___x_1719_);
lean_dec_ref(v___x_1719_);
v___x_1721_ = lean_string_append(v___x_1720_, v___x_1718_);
v___y_1693_ = v___x_1721_;
goto v___jp_1692_;
}
else
{
lean_object* v___x_1722_; 
lean_dec(v_kind_1715_);
v___x_1722_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1693_ = v___x_1722_;
goto v___jp_1692_;
}
}
else
{
lean_object* v___x_1724_; 
lean_del_object(v___x_1690_);
lean_dec_ref(v_self_1676_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 1, v_a_1688_);
lean_ctor_set(v___x_1713_, 0, v_snd_1711_);
v___x_1724_ = v___x_1713_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_snd_1711_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_a_1688_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
lean_dec_ref(v_self_1676_);
v_a_1729_ = lean_ctor_get(v___x_1686_, 0);
v_a_1730_ = lean_ctor_get(v___x_1686_, 1);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1686_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_inc(v_a_1729_);
lean_dec(v___x_1686_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1729_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_defaultPkg_1675_ = stack[0].m_obj;
lean_object* v_self_1676_ = stack[1].m_obj;
lean_object* v_a_1677_ = stack[2].m_obj;
lean_object* v_a_1678_ = stack[3].m_obj;
lean_object* v_a_1679_ = stack[4].m_obj;
lean_object* v_a_1680_ = stack[5].m_obj;
lean_object* v_a_1681_ = stack[6].m_obj;
lean_object* v_a_1682_ = stack[7].m_obj;
lean_object* v_res_1738_;
v_res_1738_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1675_, v_self_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
stack->m_obj
 = v_res_1738_;
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* v_defaultPkg_1739_, lean_object* v_self_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1739_, v_self_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
lean_dec_ref(v_a_1745_);
lean_dec(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec(v_a_1742_);
return v_res_1748_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* v___x_1749_, size_t v_sz_1750_, size_t v_i_1751_, lean_object* v_bs_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
uint8_t v___x_1760_; 
v___x_1760_ = lean_usize_dec_lt(v_i_1751_, v_sz_1750_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
lean_dec_ref(v___y_1753_);
lean_dec_ref(v___x_1749_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_bs_1752_);
lean_ctor_set(v___x_1761_, 1, v___y_1758_);
return v___x_1761_;
}
else
{
lean_object* v_v_1762_; lean_object* v___x_1763_; lean_object* v_bs_x27_1764_; lean_object* v___x_1765_; 
v_v_1762_ = lean_array_uget(v_bs_1752_, v_i_1751_);
v___x_1763_ = lean_unsigned_to_nat(0u);
v_bs_x27_1764_ = lean_array_uset(v_bs_1752_, v_i_1751_, v___x_1763_);
lean_inc_ref(v___y_1753_);
lean_inc_ref(v___x_1749_);
v___x_1765_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1749_, v_v_1762_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v_a_1767_; size_t v___x_1768_; size_t v___x_1769_; lean_object* v___x_1770_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
v_a_1767_ = lean_ctor_get(v___x_1765_, 1);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1765_, 2);
v___x_1768_ = ((size_t)1ULL);
v___x_1769_ = lean_usize_add(v_i_1751_, v___x_1768_);
v___x_1770_ = lean_array_uset(v_bs_x27_1764_, v_i_1751_, v_a_1766_);
v_i_1751_ = v___x_1769_;
v_bs_1752_ = v___x_1770_;
v___y_1758_ = v_a_1767_;
goto _start;
}
else
{
lean_object* v_a_1772_; lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec_ref(v_bs_x27_1764_);
lean_dec_ref(v___y_1753_);
lean_dec_ref(v___x_1749_);
v_a_1772_ = lean_ctor_get(v___x_1765_, 0);
v_a_1773_ = lean_ctor_get(v___x_1765_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1765_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_inc(v_a_1772_);
lean_dec(v___x_1765_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1772_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1749_ = stack[0].m_obj;
size_t v_sz_1750_ = stack[1].m_num;
size_t v_i_1751_ = stack[2].m_num;
lean_object* v_bs_1752_ = stack[3].m_obj;
lean_object* v___y_1753_ = stack[4].m_obj;
lean_object* v___y_1754_ = stack[5].m_obj;
lean_object* v___y_1755_ = stack[6].m_obj;
lean_object* v___y_1756_ = stack[7].m_obj;
lean_object* v___y_1757_ = stack[8].m_obj;
lean_object* v___y_1758_ = stack[9].m_obj;
lean_object* v_res_1781_;
v_res_1781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1749_, v_sz_1750_, v_i_1751_, v_bs_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
stack->m_obj
 = v_res_1781_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* v___x_1782_, lean_object* v_sz_1783_, lean_object* v_i_1784_, lean_object* v_bs_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
size_t v_sz_boxed_1793_; size_t v_i_boxed_1794_; lean_object* v_res_1795_; 
v_sz_boxed_1793_ = lean_unbox_usize(v_sz_1783_);
lean_dec(v_sz_1783_);
v_i_boxed_1794_ = lean_unbox_usize(v_i_1784_);
lean_dec(v_i_1784_);
v_res_1795_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1782_, v_sz_boxed_1793_, v_i_boxed_1794_, v_bs_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec(v___y_1787_);
return v_res_1795_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(lean_object* v_a_1796_, lean_object* v_as_1797_, size_t v_i_1798_, size_t v_stop_1799_, lean_object* v_b_1800_, lean_object* v___y_1801_){
_start:
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_usize_dec_eq(v_i_1798_, v_stop_1799_);
if (v___x_1803_ == 0)
{
lean_object* v_log_1804_; uint8_t v_action_1805_; uint8_t v_wantsRebuild_1806_; uint8_t v_canceled_1807_; lean_object* v_trace_1808_; lean_object* v_buildTime_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v_log_1804_ = lean_ctor_get(v___y_1801_, 0);
v_action_1805_ = lean_ctor_get_uint8(v___y_1801_, sizeof(void*)*3);
v_wantsRebuild_1806_ = lean_ctor_get_uint8(v___y_1801_, sizeof(void*)*3 + 1);
v_canceled_1807_ = lean_ctor_get_uint8(v___y_1801_, sizeof(void*)*3 + 2);
v_trace_1808_ = lean_ctor_get(v___y_1801_, 1);
v_buildTime_1809_ = lean_ctor_get(v___y_1801_, 2);
v___x_1810_ = lean_array_uget_borrowed(v_as_1797_, v_i_1798_);
v___x_1811_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
lean_inc(v___x_1810_);
v___x_1812_ = lean_string_append(v___x_1810_, v___x_1811_);
v___x_1813_ = lean_io_prim_handle_put_str(v_a_1796_, v___x_1812_);
lean_dec_ref(v___x_1812_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; size_t v___x_1815_; size_t v___x_1816_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref_known(v___x_1813_, 1);
v___x_1815_ = ((size_t)1ULL);
v___x_1816_ = lean_usize_add(v_i_1798_, v___x_1815_);
v_i_1798_ = v___x_1816_;
v_b_1800_ = v_a_1814_;
goto _start;
}
else
{
lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1831_; 
lean_inc(v_buildTime_1809_);
lean_inc_ref(v_trace_1808_);
lean_inc_ref(v_log_1804_);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___y_1801_);
if (v_isSharedCheck_1831_ == 0)
{
lean_object* v_unused_1832_; lean_object* v_unused_1833_; lean_object* v_unused_1834_; 
v_unused_1832_ = lean_ctor_get(v___y_1801_, 2);
lean_dec(v_unused_1832_);
v_unused_1833_ = lean_ctor_get(v___y_1801_, 1);
lean_dec(v_unused_1833_);
v_unused_1834_ = lean_ctor_get(v___y_1801_, 0);
lean_dec(v_unused_1834_);
v___x_1819_ = v___y_1801_;
v_isShared_1820_ = v_isSharedCheck_1831_;
goto v_resetjp_1818_;
}
else
{
lean_dec(v___y_1801_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1831_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_a_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v_a_1821_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___x_1813_, 1);
v___x_1822_ = lean_io_error_to_string(v_a_1821_);
v___x_1823_ = 3;
v___x_1824_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set_uint8(v___x_1824_, sizeof(void*)*1, v___x_1823_);
v___x_1825_ = lean_array_get_size(v_log_1804_);
v___x_1826_ = lean_array_push(v_log_1804_, v___x_1824_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1826_);
v___x_1828_ = v___x_1819_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_trace_1808_);
lean_ctor_set(v_reuseFailAlloc_1830_, 2, v_buildTime_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*3, v_action_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*3 + 1, v_wantsRebuild_1806_);
lean_ctor_set_uint8(v_reuseFailAlloc_1830_, sizeof(void*)*3 + 2, v_canceled_1807_);
v___x_1828_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; 
v___x_1829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1825_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
return v___x_1829_;
}
}
}
}
else
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1835_, 0, v_b_1800_);
lean_ctor_set(v___x_1835_, 1, v___y_1801_);
return v___x_1835_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1796_ = stack[0].m_obj;
lean_object* v_as_1797_ = stack[1].m_obj;
size_t v_i_1798_ = stack[2].m_num;
size_t v_stop_1799_ = stack[3].m_num;
lean_object* v_b_1800_ = stack[4].m_obj;
lean_object* v___y_1801_ = stack[5].m_obj;
lean_object* v_res_1836_;
v_res_1836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1796_, v_as_1797_, v_i_1798_, v_stop_1799_, v_b_1800_, v___y_1801_);
stack->m_obj
 = v_res_1836_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(lean_object* v_a_1837_, lean_object* v_as_1838_, lean_object* v_i_1839_, lean_object* v_stop_1840_, lean_object* v_b_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
size_t v_i_boxed_1844_; size_t v_stop_boxed_1845_; lean_object* v_res_1846_; 
v_i_boxed_1844_ = lean_unbox_usize(v_i_1839_);
lean_dec(v_i_1839_);
v_stop_boxed_1845_ = lean_unbox_usize(v_stop_1840_);
lean_dec(v_stop_1840_);
v_res_1846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1837_, v_as_1838_, v_i_boxed_1844_, v_stop_boxed_1845_, v_b_1841_, v___y_1842_);
lean_dec_ref(v_as_1838_);
lean_dec(v_a_1837_);
return v_res_1846_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(uint8_t v_bootstrap_1847_, lean_object* v___y_1848_, lean_object* v_oFiles_1849_, uint8_t v_shouldExport_1850_, uint8_t v___x_1851_, size_t v___x_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
if (v_bootstrap_1847_ == 0)
{
lean_object* v_toContext_1860_; lean_object* v_lakeEnv_1861_; lean_object* v_lean_1862_; lean_object* v_log_1863_; uint8_t v_action_1864_; uint8_t v_wantsRebuild_1865_; uint8_t v_canceled_1866_; lean_object* v_trace_1867_; lean_object* v_buildTime_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1898_; 
v_toContext_1860_ = lean_ctor_get(v___y_1857_, 1);
v_lakeEnv_1861_ = lean_ctor_get(v_toContext_1860_, 0);
v_lean_1862_ = lean_ctor_get(v_lakeEnv_1861_, 1);
v_log_1863_ = lean_ctor_get(v___y_1858_, 0);
v_action_1864_ = lean_ctor_get_uint8(v___y_1858_, sizeof(void*)*3);
v_wantsRebuild_1865_ = lean_ctor_get_uint8(v___y_1858_, sizeof(void*)*3 + 1);
v_canceled_1866_ = lean_ctor_get_uint8(v___y_1858_, sizeof(void*)*3 + 2);
v_trace_1867_ = lean_ctor_get(v___y_1858_, 1);
v_buildTime_1868_ = lean_ctor_get(v___y_1858_, 2);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___y_1858_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1870_ = v___y_1858_;
v_isShared_1871_ = v_isSharedCheck_1898_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_buildTime_1868_);
lean_inc(v_trace_1867_);
lean_inc(v_log_1863_);
lean_dec(v___y_1858_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1898_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v_ar_1872_; lean_object* v___x_1873_; 
v_ar_1872_ = lean_ctor_get(v_lean_1862_, 13);
lean_inc_ref(v_ar_1872_);
v___x_1873_ = l_Lake_compileStaticLib(v___y_1848_, v_oFiles_1849_, v_ar_1872_, v_bootstrap_1847_, v_log_1863_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1885_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_a_1875_ = lean_ctor_get(v___x_1873_, 1);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1877_ = v___x_1873_;
v_isShared_1878_ = v_isSharedCheck_1885_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1885_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v_a_1875_);
v___x_1880_ = v___x_1870_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1875_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_trace_1867_);
lean_ctor_set(v_reuseFailAlloc_1884_, 2, v_buildTime_1868_);
lean_ctor_set_uint8(v_reuseFailAlloc_1884_, sizeof(void*)*3, v_action_1864_);
lean_ctor_set_uint8(v_reuseFailAlloc_1884_, sizeof(void*)*3 + 1, v_wantsRebuild_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1884_, sizeof(void*)*3 + 2, v_canceled_1866_);
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
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_1886_; lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1897_; 
v_a_1886_ = lean_ctor_get(v___x_1873_, 0);
v_a_1887_ = lean_ctor_get(v___x_1873_, 1);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1889_ = v___x_1873_;
v_isShared_1890_ = v_isSharedCheck_1897_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_inc(v_a_1886_);
lean_dec(v___x_1873_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1897_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v_a_1887_);
v___x_1892_ = v___x_1870_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1887_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_trace_1867_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_buildTime_1868_);
lean_ctor_set_uint8(v_reuseFailAlloc_1896_, sizeof(void*)*3, v_action_1864_);
lean_ctor_set_uint8(v_reuseFailAlloc_1896_, sizeof(void*)*3 + 1, v_wantsRebuild_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1896_, sizeof(void*)*3 + 2, v_canceled_1866_);
v___x_1892_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1894_; 
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 1, v___x_1892_);
v___x_1894_ = v___x_1889_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1886_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
}
else
{
uint8_t v___x_1899_; 
v___x_1899_ = l_System_Platform_isOSX;
if (v___x_1899_ == 0)
{
uint8_t v___x_1900_; 
v___x_1900_ = l_System_Platform_isWindows;
if (v___x_1900_ == 0)
{
lean_object* v_toContext_1901_; lean_object* v_lakeEnv_1902_; lean_object* v_lean_1903_; lean_object* v_log_1904_; uint8_t v_action_1905_; uint8_t v_wantsRebuild_1906_; uint8_t v_canceled_1907_; lean_object* v_trace_1908_; lean_object* v_buildTime_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1939_; 
v_toContext_1901_ = lean_ctor_get(v___y_1857_, 1);
v_lakeEnv_1902_ = lean_ctor_get(v_toContext_1901_, 0);
v_lean_1903_ = lean_ctor_get(v_lakeEnv_1902_, 1);
v_log_1904_ = lean_ctor_get(v___y_1858_, 0);
v_action_1905_ = lean_ctor_get_uint8(v___y_1858_, sizeof(void*)*3);
v_wantsRebuild_1906_ = lean_ctor_get_uint8(v___y_1858_, sizeof(void*)*3 + 1);
v_canceled_1907_ = lean_ctor_get_uint8(v___y_1858_, sizeof(void*)*3 + 2);
v_trace_1908_ = lean_ctor_get(v___y_1858_, 1);
v_buildTime_1909_ = lean_ctor_get(v___y_1858_, 2);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___y_1858_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1911_ = v___y_1858_;
v_isShared_1912_ = v_isSharedCheck_1939_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_buildTime_1909_);
lean_inc(v_trace_1908_);
lean_inc(v_log_1904_);
lean_dec(v___y_1858_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1939_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v_ar_1913_; lean_object* v___x_1914_; 
v_ar_1913_ = lean_ctor_get(v_lean_1903_, 13);
lean_inc_ref(v_ar_1913_);
v___x_1914_ = l_Lake_compileStaticLib(v___y_1848_, v_oFiles_1849_, v_ar_1913_, v___x_1900_, v_log_1904_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1926_; 
v_a_1915_ = lean_ctor_get(v___x_1914_, 0);
v_a_1916_ = lean_ctor_get(v___x_1914_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1918_ = v___x_1914_;
v_isShared_1919_ = v_isSharedCheck_1926_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_inc(v_a_1915_);
lean_dec(v___x_1914_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1926_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v_a_1916_);
v___x_1921_ = v___x_1911_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1916_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_trace_1908_);
lean_ctor_set(v_reuseFailAlloc_1925_, 2, v_buildTime_1909_);
lean_ctor_set_uint8(v_reuseFailAlloc_1925_, sizeof(void*)*3, v_action_1905_);
lean_ctor_set_uint8(v_reuseFailAlloc_1925_, sizeof(void*)*3 + 1, v_wantsRebuild_1906_);
lean_ctor_set_uint8(v_reuseFailAlloc_1925_, sizeof(void*)*3 + 2, v_canceled_1907_);
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
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_1927_; lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1938_; 
v_a_1927_ = lean_ctor_get(v___x_1914_, 0);
v_a_1928_ = lean_ctor_get(v___x_1914_, 1);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1930_ = v___x_1914_;
v_isShared_1931_ = v_isSharedCheck_1938_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_inc(v_a_1927_);
lean_dec(v___x_1914_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1938_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v_a_1928_);
v___x_1933_ = v___x_1911_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1928_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_trace_1908_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_buildTime_1909_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*3, v_action_1905_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*3 + 1, v_wantsRebuild_1906_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*3 + 2, v_canceled_1907_);
v___x_1933_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1935_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v___x_1933_);
v___x_1935_ = v___x_1930_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1927_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___x_1933_);
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
}
else
{
lean_object* v_toContext_1940_; lean_object* v_lakeEnv_1941_; lean_object* v_lean_1942_; lean_object* v_log_1943_; uint8_t v_action_1944_; uint8_t v_wantsRebuild_1945_; uint8_t v_canceled_1946_; lean_object* v_trace_1947_; lean_object* v_buildTime_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1978_; 
v_toContext_1940_ = lean_ctor_get(v___y_1857_, 1);
v_lakeEnv_1941_ = lean_ctor_get(v_toContext_1940_, 0);
v_lean_1942_ = lean_ctor_get(v_lakeEnv_1941_, 1);
v_log_1943_ = lean_ctor_get(v___y_1858_, 0);
v_action_1944_ = lean_ctor_get_uint8(v___y_1858_, sizeof(void*)*3);
v_wantsRebuild_1945_ = lean_ctor_get_uint8(v___y_1858_, sizeof(void*)*3 + 1);
v_canceled_1946_ = lean_ctor_get_uint8(v___y_1858_, sizeof(void*)*3 + 2);
v_trace_1947_ = lean_ctor_get(v___y_1858_, 1);
v_buildTime_1948_ = lean_ctor_get(v___y_1858_, 2);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___y_1858_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1950_ = v___y_1858_;
v_isShared_1951_ = v_isSharedCheck_1978_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_buildTime_1948_);
lean_inc(v_trace_1947_);
lean_inc(v_log_1943_);
lean_dec(v___y_1858_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1978_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v_ar_1952_; lean_object* v___x_1953_; 
v_ar_1952_ = lean_ctor_get(v_lean_1942_, 13);
lean_inc_ref(v_ar_1952_);
v___x_1953_ = l_Lake_compileStaticLib(v___y_1848_, v_oFiles_1849_, v_ar_1952_, v_shouldExport_1850_, v_log_1943_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1965_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
v_a_1955_ = lean_ctor_get(v___x_1953_, 1);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1957_ = v___x_1953_;
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_inc(v_a_1954_);
lean_dec(v___x_1953_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v_a_1955_);
v___x_1960_ = v___x_1950_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1955_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_trace_1947_);
lean_ctor_set(v_reuseFailAlloc_1964_, 2, v_buildTime_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*3, v_action_1944_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*3 + 1, v_wantsRebuild_1945_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*3 + 2, v_canceled_1946_);
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
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_1966_; lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1977_; 
v_a_1966_ = lean_ctor_get(v___x_1953_, 0);
v_a_1967_ = lean_ctor_get(v___x_1953_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1969_ = v___x_1953_;
v_isShared_1970_ = v_isSharedCheck_1977_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_inc(v_a_1966_);
lean_dec(v___x_1953_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1977_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v_a_1967_);
v___x_1972_ = v___x_1950_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1967_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_trace_1947_);
lean_ctor_set(v_reuseFailAlloc_1976_, 2, v_buildTime_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*3, v_action_1944_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*3 + 1, v_wantsRebuild_1945_);
lean_ctor_set_uint8(v_reuseFailAlloc_1976_, sizeof(void*)*3 + 2, v_canceled_1946_);
v___x_1972_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1974_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 1, v___x_1972_);
v___x_1974_ = v___x_1969_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1966_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1979_; uint8_t v_action_1980_; uint8_t v_wantsRebuild_1981_; uint8_t v_canceled_1982_; lean_object* v_trace_1983_; lean_object* v_buildTime_1984_; lean_object* v___x_1985_; 
v_log_1979_ = lean_ctor_get(v___y_1858_, 0);
v_action_1980_ = lean_ctor_get_uint8(v___y_1858_, sizeof(void*)*3);
v_wantsRebuild_1981_ = lean_ctor_get_uint8(v___y_1858_, sizeof(void*)*3 + 1);
v_canceled_1982_ = lean_ctor_get_uint8(v___y_1858_, sizeof(void*)*3 + 2);
v_trace_1983_ = lean_ctor_get(v___y_1858_, 1);
v_buildTime_1984_ = lean_ctor_get(v___y_1858_, 2);
lean_inc_ref(v___y_1848_);
v___x_1985_ = l_Lake_createParentDirs(v___y_1848_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v_a_1989_; uint8_t v___x_2038_; lean_object* v___x_2039_; 
lean_dec_ref_known(v___x_1985_, 1);
v___x_1986_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1848_);
v___x_1987_ = l_System_FilePath_addExtension(v___y_1848_, v___x_1986_);
v___x_2038_ = 1;
v___x_2039_ = lean_io_prim_handle_mk(v___x_1987_, v___x_2038_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = lean_unsigned_to_nat(0u);
v___x_2042_ = lean_array_get_size(v_oFiles_1849_);
v___x_2043_ = lean_nat_dec_lt(v___x_2041_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_dec(v_a_2040_);
lean_dec_ref(v_oFiles_1849_);
v_a_1989_ = v___y_1858_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2044_; size_t v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_box(0);
v___x_2045_ = lean_usize_of_nat(v___x_2042_);
v___x_2046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2040_, v_oFiles_1849_, v___x_1852_, v___x_2045_, v___x_2044_, v___y_1858_);
lean_dec_ref(v_oFiles_1849_);
lean_dec(v_a_2040_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 1);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___x_2046_, 2);
v_a_1989_ = v_a_2047_;
goto v___jp_1988_;
}
else
{
lean_dec_ref(v___x_1987_);
lean_dec_ref(v___y_1848_);
return v___x_2046_;
}
}
}
else
{
lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2061_; 
lean_inc(v_buildTime_1984_);
lean_inc_ref(v_trace_1983_);
lean_inc_ref(v_log_1979_);
lean_dec_ref(v___x_1987_);
lean_dec_ref(v_oFiles_1849_);
lean_dec_ref(v___y_1848_);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___y_1858_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; lean_object* v_unused_2063_; lean_object* v_unused_2064_; 
v_unused_2062_ = lean_ctor_get(v___y_1858_, 2);
lean_dec(v_unused_2062_);
v_unused_2063_ = lean_ctor_get(v___y_1858_, 1);
lean_dec(v_unused_2063_);
v_unused_2064_ = lean_ctor_get(v___y_1858_, 0);
lean_dec(v_unused_2064_);
v___x_2049_ = v___y_1858_;
v_isShared_2050_ = v_isSharedCheck_2061_;
goto v_resetjp_2048_;
}
else
{
lean_dec(v___y_1858_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2061_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v_a_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v_a_2051_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2052_ = lean_io_error_to_string(v_a_2051_);
v___x_2053_ = 3;
v___x_2054_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2054_, 0, v___x_2052_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*1, v___x_2053_);
v___x_2055_ = lean_array_get_size(v_log_1979_);
v___x_2056_ = lean_array_push(v_log_1979_, v___x_2054_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2056_);
v___x_2058_ = v___x_2049_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_trace_1983_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v_buildTime_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*3, v_action_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*3 + 1, v_wantsRebuild_1981_);
lean_ctor_set_uint8(v_reuseFailAlloc_2060_, sizeof(void*)*3 + 2, v_canceled_1982_);
v___x_2058_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2055_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
return v___x_2059_;
}
}
}
v___jp_1988_:
{
lean_object* v___x_1990_; lean_object* v_log_1991_; uint8_t v_action_1992_; uint8_t v_wantsRebuild_1993_; uint8_t v_canceled_1994_; lean_object* v_trace_1995_; lean_object* v_buildTime_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2037_; 
v___x_1990_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1991_ = lean_ctor_get(v_a_1989_, 0);
v_action_1992_ = lean_ctor_get_uint8(v_a_1989_, sizeof(void*)*3);
v_wantsRebuild_1993_ = lean_ctor_get_uint8(v_a_1989_, sizeof(void*)*3 + 1);
v_canceled_1994_ = lean_ctor_get_uint8(v_a_1989_, sizeof(void*)*3 + 2);
v_trace_1995_ = lean_ctor_get(v_a_1989_, 1);
v_buildTime_1996_ = lean_ctor_get(v_a_1989_, 2);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_a_1989_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_1998_ = v_a_1989_;
v_isShared_1999_ = v_isSharedCheck_2037_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_buildTime_1996_);
lean_inc(v_trace_1995_);
lean_inc(v_log_1991_);
lean_dec(v_a_1989_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2037_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2000_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_2001_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_2002_ = lean_unsigned_to_nat(5u);
v___x_2003_ = lean_mk_empty_array_with_capacity(v___x_2002_);
lean_dec_ref(v___x_2003_);
v___x_2004_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_2005_ = lean_array_push(v___x_2004_, v___y_1848_);
v___x_2006_ = lean_array_push(v___x_2005_, v___x_2001_);
v___x_2007_ = lean_array_push(v___x_2006_, v___x_1987_);
v___x_2008_ = lean_box(0);
v___x_2009_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_2010_ = 0;
v___x_2011_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_2011_, 0, v___x_1990_);
lean_ctor_set(v___x_2011_, 1, v___x_2000_);
lean_ctor_set(v___x_2011_, 2, v___x_2007_);
lean_ctor_set(v___x_2011_, 3, v___x_2008_);
lean_ctor_set(v___x_2011_, 4, v___x_2009_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*5, v___x_1851_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*5 + 1, v___x_2010_);
v___x_2012_ = l_Lake_proc(v___x_2011_, v___x_2010_, v___x_2008_, v_log_1991_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2024_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_a_2014_ = lean_ctor_get(v___x_2012_, 1);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2016_ = v___x_2012_;
v_isShared_2017_ = v_isSharedCheck_2024_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2024_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v_a_2014_);
v___x_2019_ = v___x_1998_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2014_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_trace_1995_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_buildTime_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2023_, sizeof(void*)*3, v_action_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2023_, sizeof(void*)*3 + 1, v_wantsRebuild_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2023_, sizeof(void*)*3 + 2, v_canceled_1994_);
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
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_2025_; lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2036_; 
v_a_2025_ = lean_ctor_get(v___x_2012_, 0);
v_a_2026_ = lean_ctor_get(v___x_2012_, 1);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2028_ = v___x_2012_;
v_isShared_2029_ = v_isSharedCheck_2036_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_inc(v_a_2025_);
lean_dec(v___x_2012_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2036_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v_a_2026_);
v___x_2031_ = v___x_1998_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2026_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_trace_1995_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_buildTime_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2035_, sizeof(void*)*3, v_action_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2035_, sizeof(void*)*3 + 1, v_wantsRebuild_1993_);
lean_ctor_set_uint8(v_reuseFailAlloc_2035_, sizeof(void*)*3 + 2, v_canceled_1994_);
v___x_2031_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2033_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 1, v___x_2031_);
v___x_2033_ = v___x_2028_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2025_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2078_; 
lean_inc(v_buildTime_1984_);
lean_inc_ref(v_trace_1983_);
lean_inc_ref(v_log_1979_);
lean_dec_ref(v_oFiles_1849_);
lean_dec_ref(v___y_1848_);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___y_1858_);
if (v_isSharedCheck_2078_ == 0)
{
lean_object* v_unused_2079_; lean_object* v_unused_2080_; lean_object* v_unused_2081_; 
v_unused_2079_ = lean_ctor_get(v___y_1858_, 2);
lean_dec(v_unused_2079_);
v_unused_2080_ = lean_ctor_get(v___y_1858_, 1);
lean_dec(v_unused_2080_);
v_unused_2081_ = lean_ctor_get(v___y_1858_, 0);
lean_dec(v_unused_2081_);
v___x_2066_ = v___y_1858_;
v_isShared_2067_ = v_isSharedCheck_2078_;
goto v_resetjp_2065_;
}
else
{
lean_dec(v___y_1858_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2078_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v_a_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2075_; 
v_a_2068_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_1985_, 1);
v___x_2069_ = lean_io_error_to_string(v_a_2068_);
v___x_2070_ = 3;
v___x_2071_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set_uint8(v___x_2071_, sizeof(void*)*1, v___x_2070_);
v___x_2072_ = lean_array_get_size(v_log_1979_);
v___x_2073_ = lean_array_push(v_log_1979_, v___x_2071_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2073_);
v___x_2075_ = v___x_2066_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_trace_1983_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_buildTime_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2077_, sizeof(void*)*3, v_action_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_2077_, sizeof(void*)*3 + 1, v_wantsRebuild_1981_);
lean_ctor_set_uint8(v_reuseFailAlloc_2077_, sizeof(void*)*3 + 2, v_canceled_1982_);
v___x_2075_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2076_; 
v___x_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2072_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
return v___x_2076_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_bootstrap_1847_ = stack[0].m_num;
lean_object* v___y_1848_ = stack[1].m_obj;
lean_object* v_oFiles_1849_ = stack[2].m_obj;
uint8_t v_shouldExport_1850_ = stack[3].m_num;
uint8_t v___x_1851_ = stack[4].m_num;
size_t v___x_1852_ = stack[5].m_num;
lean_object* v___y_1853_ = stack[6].m_obj;
lean_object* v___y_1854_ = stack[7].m_obj;
lean_object* v___y_1855_ = stack[8].m_obj;
lean_object* v___y_1856_ = stack[9].m_obj;
lean_object* v___y_1857_ = stack[10].m_obj;
lean_object* v___y_1858_ = stack[11].m_obj;
lean_object* v_res_2082_;
v_res_2082_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_1847_, v___y_1848_, v_oFiles_1849_, v_shouldExport_1850_, v___x_1851_, v___x_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
stack->m_obj
 = v_res_2082_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object* v_bootstrap_2083_, lean_object* v___y_2084_, lean_object* v_oFiles_2085_, lean_object* v_shouldExport_2086_, lean_object* v___x_2087_, lean_object* v___x_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
uint8_t v_bootstrap_boxed_2096_; uint8_t v_shouldExport_boxed_2097_; uint8_t v___x_5969__boxed_2098_; size_t v___x_5970__boxed_2099_; lean_object* v_res_2100_; 
v_bootstrap_boxed_2096_ = lean_unbox(v_bootstrap_2083_);
v_shouldExport_boxed_2097_ = lean_unbox(v_shouldExport_2086_);
v___x_5969__boxed_2098_ = lean_unbox(v___x_2087_);
v___x_5970__boxed_2099_ = lean_unbox_usize(v___x_2088_);
lean_dec(v___x_2088_);
v_res_2100_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_boxed_2096_, v___y_2084_, v_oFiles_2085_, v_shouldExport_boxed_2097_, v___x_5969__boxed_2098_, v___x_5970__boxed_2099_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2100_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t v_bootstrap_2101_, lean_object* v___y_2102_, uint8_t v_shouldExport_2103_, uint8_t v___x_2104_, size_t v___x_2105_, lean_object* v_oFiles_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___y_2118_; uint8_t v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2114_ = lean_box(v_bootstrap_2101_);
v___x_2115_ = lean_box(v_shouldExport_2103_);
v___x_2116_ = lean_box(v___x_2104_);
v___x_2117_ = lean_box_usize(v___x_2105_);
lean_inc_ref(v___y_2102_);
v___y_2118_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed), 13, 6);
lean_closure_set(v___y_2118_, 0, v___x_2114_);
lean_closure_set(v___y_2118_, 1, v___y_2102_);
lean_closure_set(v___y_2118_, 2, v_oFiles_2106_);
lean_closure_set(v___y_2118_, 3, v___x_2115_);
lean_closure_set(v___y_2118_, 4, v___x_2116_);
lean_closure_set(v___y_2118_, 5, v___x_2117_);
v___x_2119_ = 0;
v___x_2120_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_2121_ = l_Lake_buildArtifactUnlessUpToDate(v___y_2102_, v___y_2118_, v___x_2119_, v___x_2120_, v___x_2104_, v___x_2119_, v___x_2119_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2131_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
v_a_2123_ = lean_ctor_get(v___x_2121_, 1);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2125_ = v___x_2121_;
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_inc(v_a_2122_);
lean_dec(v___x_2121_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2131_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v_path_2127_; lean_object* v___x_2129_; 
v_path_2127_ = lean_ctor_get(v_a_2122_, 1);
lean_inc_ref(v_path_2127_);
lean_dec(v_a_2122_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v_path_2127_);
v___x_2129_ = v___x_2125_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_path_2127_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_a_2123_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
v_a_2132_ = lean_ctor_get(v___x_2121_, 0);
v_a_2133_ = lean_ctor_get(v___x_2121_, 1);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2121_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_inc(v_a_2132_);
lean_dec(v___x_2121_);
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
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_bootstrap_2101_ = stack[0].m_num;
lean_object* v___y_2102_ = stack[1].m_obj;
uint8_t v_shouldExport_2103_ = stack[2].m_num;
uint8_t v___x_2104_ = stack[3].m_num;
size_t v___x_2105_ = stack[4].m_num;
lean_object* v_oFiles_2106_ = stack[5].m_obj;
lean_object* v___y_2107_ = stack[6].m_obj;
lean_object* v___y_2108_ = stack[7].m_obj;
lean_object* v___y_2109_ = stack[8].m_obj;
lean_object* v___y_2110_ = stack[9].m_obj;
lean_object* v___y_2111_ = stack[10].m_obj;
lean_object* v___y_2112_ = stack[11].m_obj;
lean_object* v_res_2141_;
v_res_2141_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_2101_, v___y_2102_, v_shouldExport_2103_, v___x_2104_, v___x_2105_, v_oFiles_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
stack->m_obj
 = v_res_2141_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* v_bootstrap_2142_, lean_object* v___y_2143_, lean_object* v_shouldExport_2144_, lean_object* v___x_2145_, lean_object* v___x_2146_, lean_object* v_oFiles_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
uint8_t v_bootstrap_boxed_2155_; uint8_t v_shouldExport_boxed_2156_; uint8_t v___x_6569__boxed_2157_; size_t v___x_6570__boxed_2158_; lean_object* v_res_2159_; 
v_bootstrap_boxed_2155_ = lean_unbox(v_bootstrap_2142_);
v_shouldExport_boxed_2156_ = lean_unbox(v_shouldExport_2144_);
v___x_6569__boxed_2157_ = lean_unbox(v___x_2145_);
v___x_6570__boxed_2158_ = lean_unbox_usize(v___x_2146_);
lean_dec(v___x_2146_);
v_res_2159_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_boxed_2155_, v___y_2143_, v_shouldExport_boxed_2156_, v___x_6569__boxed_2157_, v___x_6570__boxed_2158_, v_oFiles_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec(v___y_2149_);
return v_res_2159_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* v_a_2160_, size_t v_sz_2161_, size_t v_i_2162_, lean_object* v_bs_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
uint8_t v___x_2171_; 
v___x_2171_ = lean_usize_dec_lt(v_i_2162_, v_sz_2161_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; 
lean_dec_ref(v___y_2164_);
lean_dec_ref(v_a_2160_);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v_bs_2163_);
lean_ctor_set(v___x_2172_, 1, v___y_2169_);
return v___x_2172_;
}
else
{
lean_object* v_v_2173_; lean_object* v___x_2174_; lean_object* v_bs_x27_2175_; lean_object* v___x_2176_; 
v_v_2173_ = lean_array_uget(v_bs_2163_, v_i_2162_);
v___x_2174_ = lean_unsigned_to_nat(0u);
v_bs_x27_2175_ = lean_array_uset(v_bs_2163_, v_i_2162_, v___x_2174_);
lean_inc_ref(v___y_2164_);
lean_inc_ref(v_a_2160_);
v___x_2176_ = l_Lake_ModuleFacet_fetch___redArg(v_v_2173_, v_a_2160_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v_a_2178_; size_t v___x_2179_; size_t v___x_2180_; lean_object* v___x_2181_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
v_a_2178_ = lean_ctor_get(v___x_2176_, 1);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2176_, 2);
v___x_2179_ = ((size_t)1ULL);
v___x_2180_ = lean_usize_add(v_i_2162_, v___x_2179_);
v___x_2181_ = lean_array_uset(v_bs_x27_2175_, v_i_2162_, v_a_2177_);
v_i_2162_ = v___x_2180_;
v_bs_2163_ = v___x_2181_;
v___y_2169_ = v_a_2178_;
goto _start;
}
else
{
lean_object* v_a_2183_; lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref(v_bs_x27_2175_);
lean_dec_ref(v___y_2164_);
lean_dec_ref(v_a_2160_);
v_a_2183_ = lean_ctor_get(v___x_2176_, 0);
v_a_2184_ = lean_ctor_get(v___x_2176_, 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2176_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_inc(v_a_2183_);
lean_dec(v___x_2176_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2183_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2160_ = stack[0].m_obj;
size_t v_sz_2161_ = stack[1].m_num;
size_t v_i_2162_ = stack[2].m_num;
lean_object* v_bs_2163_ = stack[3].m_obj;
lean_object* v___y_2164_ = stack[4].m_obj;
lean_object* v___y_2165_ = stack[5].m_obj;
lean_object* v___y_2166_ = stack[6].m_obj;
lean_object* v___y_2167_ = stack[7].m_obj;
lean_object* v___y_2168_ = stack[8].m_obj;
lean_object* v___y_2169_ = stack[9].m_obj;
lean_object* v_res_2192_;
v_res_2192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_2160_, v_sz_2161_, v_i_2162_, v_bs_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
stack->m_obj
 = v_res_2192_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object* v_a_2193_, lean_object* v_sz_2194_, lean_object* v_i_2195_, lean_object* v_bs_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
size_t v_sz_boxed_2204_; size_t v_i_boxed_2205_; lean_object* v_res_2206_; 
v_sz_boxed_2204_ = lean_unbox_usize(v_sz_2194_);
lean_dec(v_sz_2194_);
v_i_boxed_2205_ = lean_unbox_usize(v_i_2195_);
lean_dec(v_i_2195_);
v_res_2206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_2193_, v_sz_boxed_2204_, v_i_boxed_2205_, v_bs_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec(v___y_2198_);
return v_res_2206_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(uint8_t v_shouldExport_2207_, lean_object* v_as_2208_, size_t v_i_2209_, size_t v_stop_2210_, lean_object* v_b_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
uint8_t v___x_2219_; 
v___x_2219_ = lean_usize_dec_eq(v_i_2209_, v_stop_2210_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v_lib_2221_; lean_object* v_config_2222_; lean_object* v_nativeFacets_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; size_t v_sz_2226_; size_t v___x_2227_; lean_object* v___x_2228_; 
v___x_2220_ = lean_array_uget_borrowed(v_as_2208_, v_i_2209_);
v_lib_2221_ = lean_ctor_get(v___x_2220_, 0);
v_config_2222_ = lean_ctor_get(v_lib_2221_, 2);
v_nativeFacets_2223_ = lean_ctor_get(v_config_2222_, 8);
v___x_2224_ = lean_box(v_shouldExport_2207_);
lean_inc_ref(v_nativeFacets_2223_);
v___x_2225_ = lean_apply_1(v_nativeFacets_2223_, v___x_2224_);
v_sz_2226_ = lean_array_size(v___x_2225_);
v___x_2227_ = ((size_t)0ULL);
lean_inc_ref(v___y_2212_);
lean_inc(v___x_2220_);
v___x_2228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2220_, v_sz_2226_, v___x_2227_, v___x_2225_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v_a_2230_; lean_object* v___x_2231_; size_t v___x_2232_; size_t v___x_2233_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
v_a_2230_ = lean_ctor_get(v___x_2228_, 1);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2228_, 2);
v___x_2231_ = l_Array_append___redArg(v_b_2211_, v_a_2229_);
lean_dec(v_a_2229_);
v___x_2232_ = ((size_t)1ULL);
v___x_2233_ = lean_usize_add(v_i_2209_, v___x_2232_);
v_i_2209_ = v___x_2233_;
v_b_2211_ = v___x_2231_;
v___y_2217_ = v_a_2230_;
goto _start;
}
else
{
lean_dec_ref(v___y_2212_);
lean_dec_ref(v_b_2211_);
return v___x_2228_;
}
}
else
{
lean_object* v___x_2235_; 
lean_dec_ref(v___y_2212_);
v___x_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2235_, 0, v_b_2211_);
lean_ctor_set(v___x_2235_, 1, v___y_2217_);
return v___x_2235_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_shouldExport_2207_ = stack[0].m_num;
lean_object* v_as_2208_ = stack[1].m_obj;
size_t v_i_2209_ = stack[2].m_num;
size_t v_stop_2210_ = stack[3].m_num;
lean_object* v_b_2211_ = stack[4].m_obj;
lean_object* v___y_2212_ = stack[5].m_obj;
lean_object* v___y_2213_ = stack[6].m_obj;
lean_object* v___y_2214_ = stack[7].m_obj;
lean_object* v___y_2215_ = stack[8].m_obj;
lean_object* v___y_2216_ = stack[9].m_obj;
lean_object* v___y_2217_ = stack[10].m_obj;
lean_object* v_res_2236_;
v_res_2236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2207_, v_as_2208_, v_i_2209_, v_stop_2210_, v_b_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
stack->m_obj
 = v_res_2236_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(lean_object* v_shouldExport_2237_, lean_object* v_as_2238_, lean_object* v_i_2239_, lean_object* v_stop_2240_, lean_object* v_b_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
uint8_t v_shouldExport_boxed_2249_; size_t v_i_boxed_2250_; size_t v_stop_boxed_2251_; lean_object* v_res_2252_; 
v_shouldExport_boxed_2249_ = lean_unbox(v_shouldExport_2237_);
v_i_boxed_2250_ = lean_unbox_usize(v_i_2239_);
lean_dec(v_i_2239_);
v_stop_boxed_2251_ = lean_unbox_usize(v_stop_2240_);
lean_dec(v_stop_2240_);
v_res_2252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_boxed_2249_, v_as_2238_, v_i_boxed_2250_, v_stop_boxed_2251_, v_b_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v_as_2238_);
return v_res_2252_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object* v_config_2253_, lean_object* v_config_2254_, uint8_t v_shouldExport_2255_, uint8_t v___x_2256_, lean_object* v___x_2257_, lean_object* v___x_2258_, lean_object* v_pkg_2259_, lean_object* v_dir_2260_, lean_object* v_self_2261_, lean_object* v___x_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
uint8_t v___y_2271_; size_t v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v_a_2291_; lean_object* v_a_2292_; lean_object* v___x_2334_; 
lean_inc_ref(v___y_2263_);
lean_inc_ref(v___y_2267_);
lean_inc(v___y_2266_);
lean_inc(v___y_2265_);
lean_inc(v___x_2258_);
v___x_2334_ = lean_apply_7(v___y_2263_, v___x_2262_, v___x_2258_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, lean_box(0));
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v_a_2336_; lean_object* v___x_2337_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
v_a_2336_ = lean_ctor_get(v___x_2334_, 1);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2334_, 2);
v___x_2337_ = l_Lake_Job_await___redArg(v_a_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v_a_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
v_a_2339_ = lean_ctor_get(v___x_2337_, 1);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2337_, 2);
v___x_2340_ = lean_unsigned_to_nat(0u);
v___x_2341_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_2342_ = lean_array_get_size(v_a_2338_);
v___x_2343_ = lean_nat_dec_lt(v___x_2340_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_dec(v_a_2338_);
v_a_2291_ = v___x_2341_;
v_a_2292_ = v_a_2339_;
goto v___jp_2290_;
}
else
{
size_t v___x_2344_; size_t v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = ((size_t)0ULL);
v___x_2345_ = lean_usize_of_nat(v___x_2342_);
lean_inc_ref(v___y_2263_);
v___x_2346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2255_, v_a_2338_, v___x_2344_, v___x_2345_, v___x_2341_, v___y_2263_, v___x_2258_, v___y_2265_, v___y_2266_, v___y_2267_, v_a_2339_);
lean_dec(v_a_2338_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v_a_2348_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
v_a_2348_ = lean_ctor_get(v___x_2346_, 1);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2346_, 2);
v_a_2291_ = v_a_2347_;
v_a_2292_ = v_a_2348_;
goto v___jp_2290_;
}
else
{
lean_object* v_a_2349_; lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v___y_2263_);
lean_dec_ref(v_self_2261_);
lean_dec_ref(v_dir_2260_);
lean_dec_ref(v_pkg_2259_);
lean_dec(v___x_2258_);
lean_dec(v___x_2257_);
lean_dec_ref(v_config_2253_);
v_a_2349_ = lean_ctor_get(v___x_2346_, 0);
v_a_2350_ = lean_ctor_get(v___x_2346_, 1);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2346_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_inc(v_a_2349_);
lean_dec(v___x_2346_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2349_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2366_; 
lean_dec_ref(v___y_2263_);
lean_dec_ref(v_self_2261_);
lean_dec_ref(v_dir_2260_);
lean_dec_ref(v_pkg_2259_);
lean_dec(v___x_2258_);
lean_dec(v___x_2257_);
lean_dec_ref(v_config_2253_);
v_a_2358_ = lean_ctor_get(v___x_2337_, 0);
v_a_2359_ = lean_ctor_get(v___x_2337_, 1);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2361_ = v___x_2337_;
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_inc(v_a_2358_);
lean_dec(v___x_2337_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2366_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2364_; 
if (v_isShared_2362_ == 0)
{
v___x_2364_ = v___x_2361_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_a_2358_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_a_2359_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec_ref(v___y_2263_);
lean_dec_ref(v_self_2261_);
lean_dec_ref(v_dir_2260_);
lean_dec_ref(v_pkg_2259_);
lean_dec(v___x_2258_);
lean_dec(v___x_2257_);
lean_dec_ref(v_config_2253_);
v_a_2367_ = lean_ctor_get(v___x_2334_, 0);
v_a_2368_ = lean_ctor_get(v___x_2334_, 1);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2334_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_inc(v_a_2367_);
lean_dec(v___x_2334_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2367_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
v___jp_2270_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___f_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2277_ = lean_box(v___y_2271_);
v___x_2278_ = lean_box(v_shouldExport_2255_);
v___x_2279_ = lean_box(v___x_2256_);
v___x_2280_ = lean_box_usize(v___y_2272_);
v___f_2281_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2281_, 0, v___x_2277_);
lean_closure_set(v___f_2281_, 1, v___y_2276_);
lean_closure_set(v___f_2281_, 2, v___x_2278_);
lean_closure_set(v___f_2281_, 3, v___x_2279_);
lean_closure_set(v___f_2281_, 4, v___x_2280_);
v___x_2282_ = l_Array_append___redArg(v___y_2273_, v___y_2274_);
lean_dec_ref(v___y_2274_);
v___x_2283_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_2284_ = l_Lake_Job_collectArray___redArg(v___x_2282_, v___x_2283_);
lean_dec_ref(v___x_2282_);
v___x_2285_ = lean_unsigned_to_nat(0u);
v___x_2286_ = 0;
v___x_2287_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_2288_ = l_Lake_Job_mapM___redArg(v___x_2257_, v___x_2284_, v___f_2281_, v___x_2285_, v___x_2286_, v___y_2263_, v___x_2258_, v___y_2265_, v___y_2266_, v___y_2267_, v___x_2287_);
lean_dec(v___x_2258_);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
lean_ctor_set(v___x_2289_, 1, v___y_2275_);
return v___x_2289_;
}
v___jp_2290_:
{
lean_object* v_toLeanConfig_2293_; lean_object* v_toLeanConfig_2294_; uint8_t v_bootstrap_2295_; lean_object* v_buildDir_2296_; lean_object* v_nativeLibDir_2297_; lean_object* v_moreLinkObjs_2298_; lean_object* v_moreLinkObjs_2299_; lean_object* v___x_2300_; size_t v_sz_2301_; size_t v___x_2302_; lean_object* v___x_2303_; 
v_toLeanConfig_2293_ = lean_ctor_get(v_config_2253_, 1);
lean_inc_ref(v_toLeanConfig_2293_);
v_toLeanConfig_2294_ = lean_ctor_get(v_config_2254_, 0);
v_bootstrap_2295_ = lean_ctor_get_uint8(v_config_2253_, sizeof(void*)*28);
v_buildDir_2296_ = lean_ctor_get(v_config_2253_, 5);
lean_inc_ref(v_buildDir_2296_);
v_nativeLibDir_2297_ = lean_ctor_get(v_config_2253_, 7);
lean_inc_ref(v_nativeLibDir_2297_);
lean_dec_ref(v_config_2253_);
v_moreLinkObjs_2298_ = lean_ctor_get(v_toLeanConfig_2293_, 6);
lean_inc_ref(v_moreLinkObjs_2298_);
lean_dec_ref(v_toLeanConfig_2293_);
v_moreLinkObjs_2299_ = lean_ctor_get(v_toLeanConfig_2294_, 6);
v___x_2300_ = l_Array_append___redArg(v_moreLinkObjs_2298_, v_moreLinkObjs_2299_);
v_sz_2301_ = lean_array_size(v___x_2300_);
v___x_2302_ = ((size_t)0ULL);
lean_inc_ref(v___y_2263_);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_2259_, v_sz_2301_, v___x_2302_, v___x_2300_, v___y_2263_, v___x_2258_, v___y_2265_, v___y_2266_, v___y_2267_, v_a_2292_);
if (lean_obj_tag(v___x_2303_) == 0)
{
if (v_shouldExport_2255_ == 0)
{
lean_object* v_a_2304_; lean_object* v_a_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
v_a_2305_ = lean_ctor_get(v___x_2303_, 1);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2303_, 2);
v___x_2306_ = l_System_FilePath_normalize(v_buildDir_2296_);
v___x_2307_ = l_Lake_joinRelative(v_dir_2260_, v___x_2306_);
v___x_2308_ = l_System_FilePath_normalize(v_nativeLibDir_2297_);
v___x_2309_ = l_Lake_joinRelative(v___x_2307_, v___x_2308_);
v___x_2310_ = l_Lake_LeanLib_libName(v_self_2261_);
v___x_2311_ = l_Lake_nameToStaticLib(v___x_2310_, v_shouldExport_2255_);
v___x_2312_ = l_Lake_joinRelative(v___x_2309_, v___x_2311_);
v___y_2271_ = v_bootstrap_2295_;
v___y_2272_ = v___x_2302_;
v___y_2273_ = v_a_2291_;
v___y_2274_ = v_a_2304_;
v___y_2275_ = v_a_2305_;
v___y_2276_ = v___x_2312_;
goto v___jp_2270_;
}
else
{
lean_object* v_a_2313_; lean_object* v_a_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_a_2313_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2313_);
v_a_2314_ = lean_ctor_get(v___x_2303_, 1);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2303_, 2);
v___x_2315_ = l_System_FilePath_normalize(v_buildDir_2296_);
v___x_2316_ = l_Lake_joinRelative(v_dir_2260_, v___x_2315_);
v___x_2317_ = l_System_FilePath_normalize(v_nativeLibDir_2297_);
v___x_2318_ = l_Lake_joinRelative(v___x_2316_, v___x_2317_);
v___x_2319_ = l_Lake_LeanLib_libName(v_self_2261_);
v___x_2320_ = 0;
v___x_2321_ = l_Lake_nameToStaticLib(v___x_2319_, v___x_2320_);
v___x_2322_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_2323_ = l_System_FilePath_addExtension(v___x_2321_, v___x_2322_);
v___x_2324_ = l_Lake_joinRelative(v___x_2318_, v___x_2323_);
v___y_2271_ = v_bootstrap_2295_;
v___y_2272_ = v___x_2302_;
v___y_2273_ = v_a_2291_;
v___y_2274_ = v_a_2313_;
v___y_2275_ = v_a_2314_;
v___y_2276_ = v___x_2324_;
goto v___jp_2270_;
}
}
else
{
lean_object* v_a_2325_; lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec_ref(v_nativeLibDir_2297_);
lean_dec_ref(v_buildDir_2296_);
lean_dec_ref(v_a_2291_);
lean_dec_ref(v___y_2263_);
lean_dec_ref(v_self_2261_);
lean_dec_ref(v_dir_2260_);
lean_dec(v___x_2258_);
lean_dec(v___x_2257_);
v_a_2325_ = lean_ctor_get(v___x_2303_, 0);
v_a_2326_ = lean_ctor_get(v___x_2303_, 1);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2303_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_inc(v_a_2325_);
lean_dec(v___x_2303_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2325_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_2253_ = stack[0].m_obj;
lean_object* v_config_2254_ = stack[1].m_obj;
uint8_t v_shouldExport_2255_ = stack[2].m_num;
uint8_t v___x_2256_ = stack[3].m_num;
lean_object* v___x_2257_ = stack[4].m_obj;
lean_object* v___x_2258_ = stack[5].m_obj;
lean_object* v_pkg_2259_ = stack[6].m_obj;
lean_object* v_dir_2260_ = stack[7].m_obj;
lean_object* v_self_2261_ = stack[8].m_obj;
lean_object* v___x_2262_ = stack[9].m_obj;
lean_object* v___y_2263_ = stack[10].m_obj;
lean_object* v___y_2264_ = stack[11].m_obj;
lean_object* v___y_2265_ = stack[12].m_obj;
lean_object* v___y_2266_ = stack[13].m_obj;
lean_object* v___y_2267_ = stack[14].m_obj;
lean_object* v___y_2268_ = stack[15].m_obj;
lean_object* v_res_2376_;
v_res_2376_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v_config_2253_, v_config_2254_, v_shouldExport_2255_, v___x_2256_, v___x_2257_, v___x_2258_, v_pkg_2259_, v_dir_2260_, v_self_2261_, v___x_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
stack->m_obj
 = v_res_2376_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(lean_object** _args){
lean_object* v_config_2377_ = _args[0];
lean_object* v_config_2378_ = _args[1];
lean_object* v_shouldExport_2379_ = _args[2];
lean_object* v___x_2380_ = _args[3];
lean_object* v___x_2381_ = _args[4];
lean_object* v___x_2382_ = _args[5];
lean_object* v_pkg_2383_ = _args[6];
lean_object* v_dir_2384_ = _args[7];
lean_object* v_self_2385_ = _args[8];
lean_object* v___x_2386_ = _args[9];
lean_object* v___y_2387_ = _args[10];
lean_object* v___y_2388_ = _args[11];
lean_object* v___y_2389_ = _args[12];
lean_object* v___y_2390_ = _args[13];
lean_object* v___y_2391_ = _args[14];
lean_object* v___y_2392_ = _args[15];
lean_object* v___y_2393_ = _args[16];
_start:
{
uint8_t v_shouldExport_boxed_2394_; uint8_t v___x_6873__boxed_2395_; lean_object* v_res_2396_; 
v_shouldExport_boxed_2394_ = lean_unbox(v_shouldExport_2379_);
v___x_6873__boxed_2395_ = lean_unbox(v___x_2380_);
v_res_2396_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v_config_2377_, v_config_2378_, v_shouldExport_boxed_2394_, v___x_6873__boxed_2395_, v___x_2381_, v___x_2382_, v_pkg_2383_, v_dir_2384_, v_self_2385_, v___x_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec(v_config_2378_);
return v_res_2396_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object* v___y_2397_, lean_object* v_self_2398_, uint8_t v_shouldExport_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_toBuildConfig_2406_; lean_object* v_registeredJobs_2407_; uint8_t v_verbosity_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; uint8_t v___x_2414_; lean_object* v___y_2416_; 
v_toBuildConfig_2406_ = lean_ctor_get(v_a_2403_, 0);
v_registeredJobs_2407_ = lean_ctor_get(v_a_2403_, 4);
v_verbosity_2408_ = lean_ctor_get_uint8(v_toBuildConfig_2406_, sizeof(void*)*5 + 4);
v___x_2409_ = l_Lake_instDataKindFilePath;
v___x_2410_ = lean_box(v_verbosity_2408_);
v___x_2411_ = lean_obj_tag_nat(v___x_2410_);
lean_dec(v___x_2410_);
v___x_2412_ = lean_unsigned_to_nat(2u);
v___x_2413_ = lean_nat_dec_eq(v___x_2411_, v___x_2412_);
v___x_2414_ = 1;
if (v___x_2413_ == 0)
{
lean_object* v___x_2461_; 
v___x_2461_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_2416_ = v___x_2461_;
goto v___jp_2415_;
}
else
{
if (v_shouldExport_2399_ == 0)
{
lean_object* v___x_2462_; 
v___x_2462_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___y_2416_ = v___x_2462_;
goto v___jp_2415_;
}
else
{
lean_object* v___x_2463_; 
v___x_2463_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_2416_ = v___x_2463_;
goto v___jp_2415_;
}
}
v___jp_2415_:
{
lean_object* v_pkg_2417_; lean_object* v_name_2418_; lean_object* v_config_2419_; lean_object* v_keyName_2420_; lean_object* v_dir_2421_; lean_object* v_config_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___f_2434_; uint8_t v___x_2435_; lean_object* v___x_2436_; 
v_pkg_2417_ = lean_ctor_get(v_self_2398_, 0);
lean_inc_ref_n(v_pkg_2417_, 2);
v_name_2418_ = lean_ctor_get(v_self_2398_, 1);
v_config_2419_ = lean_ctor_get(v_self_2398_, 2);
lean_inc(v_config_2419_);
v_keyName_2420_ = lean_ctor_get(v_pkg_2417_, 2);
v_dir_2421_ = lean_ctor_get(v_pkg_2417_, 4);
lean_inc_ref(v_dir_2421_);
v_config_2422_ = lean_ctor_get(v_pkg_2417_, 6);
lean_inc_ref(v_config_2422_);
lean_inc_n(v_name_2418_, 2);
v___x_2423_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2418_, v___x_2414_);
v___x_2424_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0));
v___x_2425_ = lean_string_append(v___x_2423_, v___x_2424_);
v___x_2426_ = lean_string_append(v___x_2425_, v___y_2416_);
v___x_2427_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_2420_);
v___x_2428_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2428_, 0, v_keyName_2420_);
lean_ctor_set(v___x_2428_, 1, v_name_2418_);
v___x_2429_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_2398_);
v___x_2430_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2428_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
lean_ctor_set(v___x_2430_, 2, v_self_2398_);
lean_ctor_set(v___x_2430_, 3, v___x_2427_);
v___x_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2431_, 0, v_pkg_2417_);
v___x_2432_ = lean_box(v_shouldExport_2399_);
v___x_2433_ = lean_box(v___x_2414_);
v___f_2434_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed), 17, 10);
lean_closure_set(v___f_2434_, 0, v_config_2422_);
lean_closure_set(v___f_2434_, 1, v_config_2419_);
lean_closure_set(v___f_2434_, 2, v___x_2432_);
lean_closure_set(v___f_2434_, 3, v___x_2433_);
lean_closure_set(v___f_2434_, 4, v___x_2409_);
lean_closure_set(v___f_2434_, 5, v___x_2431_);
lean_closure_set(v___f_2434_, 6, v_pkg_2417_);
lean_closure_set(v___f_2434_, 7, v_dir_2421_);
lean_closure_set(v___f_2434_, 8, v_self_2398_);
lean_closure_set(v___f_2434_, 9, v___x_2430_);
v___x_2435_ = 0;
v___x_2436_ = l_Lake_ensureJob___redArg(v___x_2409_, v___f_2434_, v___y_2397_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2460_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_a_2438_ = lean_ctor_get(v___x_2436_, 1);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2440_ = v___x_2436_;
v_isShared_2441_ = v_isSharedCheck_2460_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2460_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v_task_2442_; lean_object* v_kind_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2458_; 
v_task_2442_ = lean_ctor_get(v_a_2437_, 0);
v_kind_2443_ = lean_ctor_get(v_a_2437_, 1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_a_2437_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; 
v_unused_2459_ = lean_ctor_get(v_a_2437_, 2);
lean_dec(v_unused_2459_);
v___x_2445_ = v_a_2437_;
v_isShared_2446_ = v_isSharedCheck_2458_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_kind_2443_);
lean_inc(v_task_2442_);
lean_dec(v_a_2437_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2458_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v_job_2448_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 2, v___x_2426_);
v_job_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_task_2442_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_kind_2443_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v___x_2426_);
v_job_2448_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
lean_ctor_set_uint8(v_job_2448_, sizeof(void*)*3, v___x_2435_);
v___x_2449_ = lean_st_ref_take(v_registeredJobs_2407_);
lean_inc_ref(v_job_2448_);
v___x_2450_ = l_Lake_Job_toOpaque___redArg(v_job_2448_);
v___x_2451_ = lean_array_push(v___x_2449_, v___x_2450_);
v___x_2452_ = lean_st_ref_put(v_registeredJobs_2407_, v___x_2451_);
v___x_2453_ = l_Lake_Job_renew___redArg(v_job_2448_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v___x_2453_);
v___x_2455_ = v___x_2440_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_a_2438_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2426_);
return v___x_2436_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2397_ = stack[0].m_obj;
lean_object* v_self_2398_ = stack[1].m_obj;
uint8_t v_shouldExport_2399_ = stack[2].m_num;
lean_object* v_a_2400_ = stack[3].m_obj;
lean_object* v_a_2401_ = stack[4].m_obj;
lean_object* v_a_2402_ = stack[5].m_obj;
lean_object* v_a_2403_ = stack[6].m_obj;
lean_object* v_a_2404_ = stack[7].m_obj;
lean_object* v_res_2464_;
v_res_2464_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2397_, v_self_2398_, v_shouldExport_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
stack->m_obj
 = v_res_2464_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* v___y_2465_, lean_object* v_self_2466_, lean_object* v_shouldExport_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
uint8_t v_shouldExport_boxed_2474_; lean_object* v_res_2475_; 
v_shouldExport_boxed_2474_ = lean_unbox(v_shouldExport_2467_);
v_res_2475_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2465_, v_self_2466_, v_shouldExport_boxed_2474_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec(v_a_2469_);
lean_dec(v_a_2468_);
return v_res_2475_;
}
}
lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* v_x_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
uint8_t v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = 0;
v___x_2485_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2477_, v_x_2476_, v___x_2484_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
return v___x_2485_;
}
}
LEAN_EXPORT void l_Lake_LeanLib_staticFacetConfig___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2476_ = stack[0].m_obj;
lean_object* v___y_2477_ = stack[1].m_obj;
lean_object* v___y_2478_ = stack[2].m_obj;
lean_object* v___y_2479_ = stack[3].m_obj;
lean_object* v___y_2480_ = stack[4].m_obj;
lean_object* v___y_2481_ = stack[5].m_obj;
lean_object* v___y_2482_ = stack[6].m_obj;
lean_object* v_res_2486_;
v_res_2486_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
stack->m_obj
 = v_res_2486_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object* v_x_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec(v___y_2489_);
return v_res_2495_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2498_; uint8_t v___x_2499_; lean_object* v___x_2500_; lean_object* v___f_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___f_2498_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2499_ = 1;
v___x_2500_ = l_Lake_instDataKindFilePath;
v___f_2501_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__0));
v___x_2502_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2503_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
lean_ctor_set(v___x_2503_, 1, v___f_2501_);
lean_ctor_set(v___x_2503_, 2, v___x_2500_);
lean_ctor_set(v___x_2503_, 3, v___f_2498_);
lean_ctor_set_uint8(v___x_2503_, sizeof(void*)*4, v___x_2499_);
lean_ctor_set_uint8(v___x_2503_, sizeof(void*)*4 + 1, v___x_2499_);
return v___x_2503_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = lean_obj_once(&l_Lake_LeanLib_staticFacetConfig___closed__2, &l_Lake_LeanLib_staticFacetConfig___closed__2_once, _init_l_Lake_LeanLib_staticFacetConfig___closed__2);
return v___x_2504_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(lean_object* v_a_2505_, lean_object* v_as_2506_, size_t v_i_2507_, size_t v_stop_2508_, lean_object* v_b_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v___x_2517_; 
v___x_2517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2505_, v_as_2506_, v_i_2507_, v_stop_2508_, v_b_2509_, v___y_2515_);
return v___x_2517_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2505_ = stack[0].m_obj;
lean_object* v_as_2506_ = stack[1].m_obj;
size_t v_i_2507_ = stack[2].m_num;
size_t v_stop_2508_ = stack[3].m_num;
lean_object* v_b_2509_ = stack[4].m_obj;
lean_object* v___y_2510_ = stack[5].m_obj;
lean_object* v___y_2511_ = stack[6].m_obj;
lean_object* v___y_2512_ = stack[7].m_obj;
lean_object* v___y_2513_ = stack[8].m_obj;
lean_object* v___y_2514_ = stack[9].m_obj;
lean_object* v___y_2515_ = stack[10].m_obj;
lean_object* v_res_2518_;
v_res_2518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_2505_, v_as_2506_, v_i_2507_, v_stop_2508_, v_b_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
stack->m_obj
 = v_res_2518_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* v_a_2519_, lean_object* v_as_2520_, lean_object* v_i_2521_, lean_object* v_stop_2522_, lean_object* v_b_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
size_t v_i_boxed_2531_; size_t v_stop_boxed_2532_; lean_object* v_res_2533_; 
v_i_boxed_2531_ = lean_unbox_usize(v_i_2521_);
lean_dec(v_i_2521_);
v_stop_boxed_2532_ = lean_unbox_usize(v_stop_2522_);
lean_dec(v_stop_2522_);
v_res_2533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_2519_, v_as_2520_, v_i_boxed_2531_, v_stop_boxed_2532_, v_b_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v_as_2520_);
lean_dec(v_a_2519_);
return v_res_2533_;
}
}
lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* v_x_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
uint8_t v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = 1;
v___x_2543_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2535_, v_x_2534_, v___x_2542_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
return v___x_2543_;
}
}
LEAN_EXPORT void l_Lake_LeanLib_staticExportFacetConfig___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2534_ = stack[0].m_obj;
lean_object* v___y_2535_ = stack[1].m_obj;
lean_object* v___y_2536_ = stack[2].m_obj;
lean_object* v___y_2537_ = stack[3].m_obj;
lean_object* v___y_2538_ = stack[4].m_obj;
lean_object* v___y_2539_ = stack[5].m_obj;
lean_object* v___y_2540_ = stack[6].m_obj;
lean_object* v_res_2544_;
v_res_2544_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
stack->m_obj
 = v_res_2544_;
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object* v_x_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec(v___y_2547_);
return v_res_2553_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2555_; uint8_t v___x_2556_; lean_object* v___x_2557_; lean_object* v___f_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___f_2555_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2556_ = 1;
v___x_2557_ = l_Lake_instDataKindFilePath;
v___f_2558_ = ((lean_object*)(l_Lake_LeanLib_staticExportFacetConfig___closed__0));
v___x_2559_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2560_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
lean_ctor_set(v___x_2560_, 1, v___f_2558_);
lean_ctor_set(v___x_2560_, 2, v___x_2557_);
lean_ctor_set(v___x_2560_, 3, v___f_2555_);
lean_ctor_set_uint8(v___x_2560_, sizeof(void*)*4, v___x_2556_);
lean_ctor_set_uint8(v___x_2560_, sizeof(void*)*4 + 1, v___x_2556_);
return v___x_2560_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig(void){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_obj_once(&l_Lake_LeanLib_staticExportFacetConfig___closed__1, &l_Lake_LeanLib_staticExportFacetConfig___closed__1_once, _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1);
return v___x_2561_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0(void){
_start:
{
uint8_t v___x_2562_; lean_object* v_name_2563_; lean_object* v___x_2564_; 
v___x_2562_ = 1;
v_name_2563_ = l_Lake_instDataKindDynlib;
v___x_2564_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2563_, v___x_2562_);
return v___x_2564_;
}
}
lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object* v_defaultPkg_2565_, lean_object* v_self_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_name_2574_; uint8_t v___x_2575_; lean_object* v___x_2576_; 
v_name_2574_ = l_Lake_instDataKindDynlib;
v___x_2575_ = 1;
lean_inc_ref_n(v_self_2566_, 2);
v___x_2576_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_2565_, v_self_2566_, v_self_2566_, v___x_2575_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2618_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
v_a_2578_ = lean_ctor_get(v___x_2576_, 1);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2580_ = v___x_2576_;
v_isShared_2581_ = v_isSharedCheck_2618_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_inc(v_a_2577_);
lean_dec(v___x_2576_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2618_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___y_2583_; lean_object* v_snd_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2616_; 
v_snd_2601_ = lean_ctor_get(v_a_2577_, 1);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_a_2577_);
if (v_isSharedCheck_2616_ == 0)
{
lean_object* v_unused_2617_; 
v_unused_2617_ = lean_ctor_get(v_a_2577_, 0);
lean_dec(v_unused_2617_);
v___x_2603_ = v_a_2577_;
v_isShared_2604_ = v_isSharedCheck_2616_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_snd_2601_);
lean_dec(v_a_2577_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2616_;
goto v_resetjp_2602_;
}
v___jp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2599_; 
v___x_2584_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_2585_ = l_Lake_PartialBuildKey_toString(v_self_2566_);
v___x_2586_ = lean_string_append(v___x_2584_, v___x_2585_);
lean_dec_ref(v___x_2585_);
v___x_2587_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_2588_ = lean_string_append(v___x_2586_, v___x_2587_);
v___x_2589_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0);
v___x_2590_ = lean_string_append(v___x_2588_, v___x_2589_);
v___x_2591_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_2592_ = lean_string_append(v___x_2590_, v___x_2591_);
v___x_2593_ = lean_string_append(v___x_2592_, v___y_2583_);
lean_dec_ref(v___y_2583_);
v___x_2594_ = 3;
v___x_2595_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2595_, 0, v___x_2593_);
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*1, v___x_2594_);
v___x_2596_ = lean_array_get_size(v_a_2578_);
v___x_2597_ = lean_array_push(v_a_2578_, v___x_2595_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 1);
lean_ctor_set(v___x_2580_, 1, v___x_2597_);
lean_ctor_set(v___x_2580_, 0, v___x_2596_);
v___x_2599_ = v___x_2580_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2596_);
lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___x_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
v_resetjp_2602_:
{
lean_object* v_kind_2605_; uint8_t v___x_2606_; 
v_kind_2605_ = lean_ctor_get(v_snd_2601_, 1);
v___x_2606_ = lean_name_eq(v_kind_2605_, v_name_2574_);
if (v___x_2606_ == 0)
{
uint8_t v___x_2607_; 
lean_inc(v_kind_2605_);
lean_del_object(v___x_2603_);
lean_dec(v_snd_2601_);
v___x_2607_ = l_Lean_Name_isAnonymous(v_kind_2605_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2608_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_2609_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2605_, v___x_2575_);
v___x_2610_ = lean_string_append(v___x_2608_, v___x_2609_);
lean_dec_ref(v___x_2609_);
v___x_2611_ = lean_string_append(v___x_2610_, v___x_2608_);
v___y_2583_ = v___x_2611_;
goto v___jp_2582_;
}
else
{
lean_object* v___x_2612_; 
lean_dec(v_kind_2605_);
v___x_2612_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_2583_ = v___x_2612_;
goto v___jp_2582_;
}
}
else
{
lean_object* v___x_2614_; 
lean_del_object(v___x_2580_);
lean_dec_ref(v_self_2566_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 1, v_a_2578_);
lean_ctor_set(v___x_2603_, 0, v_snd_2601_);
v___x_2614_ = v___x_2603_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_snd_2601_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_a_2578_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec_ref(v_self_2566_);
v_a_2619_ = lean_ctor_get(v___x_2576_, 0);
v_a_2620_ = lean_ctor_get(v___x_2576_, 1);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2576_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_inc(v_a_2619_);
lean_dec(v___x_2576_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2619_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_defaultPkg_2565_ = stack[0].m_obj;
lean_object* v_self_2566_ = stack[1].m_obj;
lean_object* v_a_2567_ = stack[2].m_obj;
lean_object* v_a_2568_ = stack[3].m_obj;
lean_object* v_a_2569_ = stack[4].m_obj;
lean_object* v_a_2570_ = stack[5].m_obj;
lean_object* v_a_2571_ = stack[6].m_obj;
lean_object* v_a_2572_ = stack[7].m_obj;
lean_object* v_res_2628_;
v_res_2628_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_2565_, v_self_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
stack->m_obj
 = v_res_2628_;
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* v_defaultPkg_2629_, lean_object* v_self_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_2629_, v_self_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec(v_a_2632_);
return v_res_2638_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0));
v___x_2642_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2642_);
lean_ctor_set(v___x_2643_, 1, v___x_2641_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5(void){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
return v___x_2644_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object* v___x_2645_, lean_object* v_as_2646_, size_t v_i_2647_, size_t v_stop_2648_, lean_object* v_b_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
uint8_t v___x_2657_; 
v___x_2657_ = lean_usize_dec_eq(v_i_2647_, v_stop_2648_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = lean_array_uget_borrowed(v_as_2646_, v_i_2647_);
lean_inc_ref(v___y_2650_);
lean_inc(v___x_2658_);
lean_inc_ref(v___x_2645_);
v___x_2659_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_2645_, v___x_2658_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v_a_2661_; lean_object* v___x_2662_; size_t v___x_2663_; size_t v___x_2664_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
v_a_2661_ = lean_ctor_get(v___x_2659_, 1);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2659_, 2);
v___x_2662_ = lean_array_push(v_b_2649_, v_a_2660_);
v___x_2663_ = ((size_t)1ULL);
v___x_2664_ = lean_usize_add(v_i_2647_, v___x_2663_);
v_i_2647_ = v___x_2664_;
v_b_2649_ = v___x_2662_;
v___y_2655_ = v_a_2661_;
goto _start;
}
else
{
lean_object* v_a_2666_; lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec_ref(v___y_2650_);
lean_dec_ref(v_b_2649_);
lean_dec_ref(v___x_2645_);
v_a_2666_ = lean_ctor_get(v___x_2659_, 0);
v_a_2667_ = lean_ctor_get(v___x_2659_, 1);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2659_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_inc(v_a_2666_);
lean_dec(v___x_2659_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2666_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
lean_object* v___x_2675_; 
lean_dec_ref(v___y_2650_);
lean_dec_ref(v___x_2645_);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v_b_2649_);
lean_ctor_set(v___x_2675_, 1, v___y_2655_);
return v___x_2675_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2645_ = stack[0].m_obj;
lean_object* v_as_2646_ = stack[1].m_obj;
size_t v_i_2647_ = stack[2].m_num;
size_t v_stop_2648_ = stack[3].m_num;
lean_object* v_b_2649_ = stack[4].m_obj;
lean_object* v___y_2650_ = stack[5].m_obj;
lean_object* v___y_2651_ = stack[6].m_obj;
lean_object* v___y_2652_ = stack[7].m_obj;
lean_object* v___y_2653_ = stack[8].m_obj;
lean_object* v___y_2654_ = stack[9].m_obj;
lean_object* v___y_2655_ = stack[10].m_obj;
lean_object* v_res_2676_;
v_res_2676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_2645_, v_as_2646_, v_i_2647_, v_stop_2648_, v_b_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
stack->m_obj
 = v_res_2676_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* v___x_2677_, lean_object* v_as_2678_, lean_object* v_i_2679_, lean_object* v_stop_2680_, lean_object* v_b_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
size_t v_i_boxed_2689_; size_t v_stop_boxed_2690_; lean_object* v_res_2691_; 
v_i_boxed_2689_ = lean_unbox_usize(v_i_2679_);
lean_dec(v_i_2679_);
v_stop_boxed_2690_ = lean_unbox_usize(v_stop_2680_);
lean_dec(v_stop_2680_);
v_res_2691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_2677_, v_as_2678_, v_i_boxed_2689_, v_stop_boxed_2690_, v_b_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v_as_2678_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object* v_self_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v_toHashSet_2694_; lean_object* v_toArray_2695_; uint8_t v___x_2696_; 
v_toHashSet_2694_ = lean_ctor_get(v_self_2692_, 0);
v_toArray_2695_ = lean_ctor_get(v_self_2692_, 1);
v___x_2696_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_2694_, v_a_2693_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2706_; 
lean_inc_ref(v_toArray_2695_);
lean_inc_ref(v_toHashSet_2694_);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_self_2692_);
if (v_isSharedCheck_2706_ == 0)
{
lean_object* v_unused_2707_; lean_object* v_unused_2708_; 
v_unused_2707_ = lean_ctor_get(v_self_2692_, 1);
lean_dec(v_unused_2707_);
v_unused_2708_ = lean_ctor_get(v_self_2692_, 0);
lean_dec(v_unused_2708_);
v___x_2698_ = v_self_2692_;
v_isShared_2699_ = v_isSharedCheck_2706_;
goto v_resetjp_2697_;
}
else
{
lean_dec(v_self_2692_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2706_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2700_ = lean_box(0);
lean_inc_ref(v_a_2693_);
v___x_2701_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_toHashSet_2694_, v_a_2693_, v___x_2700_);
v___x_2702_ = lean_array_push(v_toArray_2695_, v_a_2693_);
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 1, v___x_2702_);
lean_ctor_set(v___x_2698_, 0, v___x_2701_);
v___x_2704_ = v___x_2698_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2701_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
else
{
lean_dec_ref(v_a_2693_);
return v_self_2692_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object* v_as_2709_, size_t v_i_2710_, size_t v_stop_2711_, lean_object* v_b_2712_){
_start:
{
uint8_t v___x_2713_; 
v___x_2713_ = lean_usize_dec_eq(v_i_2710_, v_stop_2711_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; lean_object* v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; 
v___x_2714_ = lean_array_uget_borrowed(v_as_2709_, v_i_2710_);
lean_inc(v___x_2714_);
v___x_2715_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_2712_, v___x_2714_);
v___x_2716_ = ((size_t)1ULL);
v___x_2717_ = lean_usize_add(v_i_2710_, v___x_2716_);
v_i_2710_ = v___x_2717_;
v_b_2712_ = v___x_2715_;
goto _start;
}
else
{
return v_b_2712_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2709_ = stack[0].m_obj;
size_t v_i_2710_ = stack[1].m_num;
size_t v_stop_2711_ = stack[2].m_num;
lean_object* v_b_2712_ = stack[3].m_obj;
lean_object* v_res_2719_;
v_res_2719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_2709_, v_i_2710_, v_stop_2711_, v_b_2712_);
stack->m_obj
 = v_res_2719_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object* v_as_2720_, lean_object* v_i_2721_, lean_object* v_stop_2722_, lean_object* v_b_2723_){
_start:
{
size_t v_i_boxed_2724_; size_t v_stop_boxed_2725_; lean_object* v_res_2726_; 
v_i_boxed_2724_ = lean_unbox_usize(v_i_2721_);
lean_dec(v_i_2721_);
v_stop_boxed_2725_ = lean_unbox_usize(v_stop_2722_);
lean_dec(v_stop_2722_);
v_res_2726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_2720_, v_i_boxed_2724_, v_stop_boxed_2725_, v_b_2723_);
lean_dec_ref(v_as_2720_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object* v_self_2727_, lean_object* v_arr_2728_){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2729_ = lean_unsigned_to_nat(0u);
v___x_2730_ = lean_array_get_size(v_arr_2728_);
v___x_2731_ = lean_nat_dec_lt(v___x_2729_, v___x_2730_);
if (v___x_2731_ == 0)
{
return v_self_2727_;
}
else
{
size_t v___x_2732_; size_t v___x_2733_; lean_object* v___x_2734_; 
v___x_2732_ = ((size_t)0ULL);
v___x_2733_ = lean_usize_of_nat(v___x_2730_);
v___x_2734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2728_, v___x_2732_, v___x_2733_, v_self_2727_);
return v___x_2734_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(lean_object* v_self_2735_, lean_object* v_arr_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_self_2735_, v_arr_2736_);
lean_dec_ref(v_arr_2736_);
return v_res_2737_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(lean_object* v_as_2738_, size_t v_i_2739_, size_t v_stop_2740_, lean_object* v_b_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
uint8_t v___x_2749_; 
v___x_2749_ = lean_usize_dec_eq(v_i_2739_, v_stop_2740_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; lean_object* v_lib_2751_; lean_object* v_pkg_2752_; lean_object* v_name_2753_; lean_object* v_keyName_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2750_ = lean_array_uget_borrowed(v_as_2738_, v_i_2739_);
v_lib_2751_ = lean_ctor_get(v___x_2750_, 0);
v_pkg_2752_ = lean_ctor_get(v_lib_2751_, 0);
v_name_2753_ = lean_ctor_get(v___x_2750_, 1);
v_keyName_2754_ = lean_ctor_get(v_pkg_2752_, 2);
v___x_2755_ = l_Lake_Module_transImportsFacet;
lean_inc(v_name_2753_);
lean_inc(v_keyName_2754_);
v___x_2756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2756_, 0, v_keyName_2754_);
lean_ctor_set(v___x_2756_, 1, v_name_2753_);
v___x_2757_ = l_Lake_Module_keyword;
lean_inc(v___x_2750_);
v___x_2758_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
lean_ctor_set(v___x_2758_, 2, v___x_2750_);
lean_ctor_set(v___x_2758_, 3, v___x_2755_);
lean_inc_ref(v___y_2742_);
lean_inc_ref(v___y_2746_);
lean_inc(v___y_2745_);
lean_inc(v___y_2744_);
lean_inc(v___y_2743_);
v___x_2759_ = lean_apply_7(v___y_2742_, v___x_2758_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, lean_box(0));
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v_a_2761_; lean_object* v___x_2762_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
v_a_2761_ = lean_ctor_get(v___x_2759_, 1);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2759_, 2);
v___x_2762_ = l_Lake_Job_await___redArg(v_a_2760_, v_a_2761_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v_a_2764_; lean_object* v___x_2765_; size_t v___x_2766_; size_t v___x_2767_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
v_a_2764_ = lean_ctor_get(v___x_2762_, 1);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2762_, 2);
v___x_2765_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_b_2741_, v_a_2763_);
lean_dec(v_a_2763_);
v___x_2766_ = ((size_t)1ULL);
v___x_2767_ = lean_usize_add(v_i_2739_, v___x_2766_);
v_i_2739_ = v___x_2767_;
v_b_2741_ = v___x_2765_;
v___y_2747_ = v_a_2764_;
goto _start;
}
else
{
lean_object* v_a_2769_; lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec_ref(v___y_2742_);
lean_dec_ref(v_b_2741_);
v_a_2769_ = lean_ctor_get(v___x_2762_, 0);
v_a_2770_ = lean_ctor_get(v___x_2762_, 1);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2762_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_inc(v_a_2769_);
lean_dec(v___x_2762_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2769_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec_ref(v___y_2742_);
lean_dec_ref(v_b_2741_);
v_a_2778_ = lean_ctor_get(v___x_2759_, 0);
v_a_2779_ = lean_ctor_get(v___x_2759_, 1);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2759_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_inc(v_a_2778_);
lean_dec(v___x_2759_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2778_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
else
{
lean_object* v___x_2787_; 
lean_dec_ref(v___y_2742_);
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v_b_2741_);
lean_ctor_set(v___x_2787_, 1, v___y_2747_);
return v___x_2787_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2738_ = stack[0].m_obj;
size_t v_i_2739_ = stack[1].m_num;
size_t v_stop_2740_ = stack[2].m_num;
lean_object* v_b_2741_ = stack[3].m_obj;
lean_object* v___y_2742_ = stack[4].m_obj;
lean_object* v___y_2743_ = stack[5].m_obj;
lean_object* v___y_2744_ = stack[6].m_obj;
lean_object* v___y_2745_ = stack[7].m_obj;
lean_object* v___y_2746_ = stack[8].m_obj;
lean_object* v___y_2747_ = stack[9].m_obj;
lean_object* v_res_2788_;
v_res_2788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_as_2738_, v_i_2739_, v_stop_2740_, v_b_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
stack->m_obj
 = v_res_2788_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object* v_as_2789_, lean_object* v_i_2790_, lean_object* v_stop_2791_, lean_object* v_b_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
size_t v_i_boxed_2800_; size_t v_stop_boxed_2801_; lean_object* v_res_2802_; 
v_i_boxed_2800_ = lean_unbox_usize(v_i_2790_);
lean_dec(v_i_2790_);
v_stop_boxed_2801_ = lean_unbox_usize(v_stop_2791_);
lean_dec(v_stop_2791_);
v_res_2802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_as_2789_, v_i_boxed_2800_, v_stop_boxed_2801_, v_b_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v_as_2789_);
return v_res_2802_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(lean_object* v_as_2803_, size_t v_i_2804_, size_t v_stop_2805_, lean_object* v_b_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
uint8_t v___x_2814_; 
v___x_2814_ = lean_usize_dec_eq(v_i_2804_, v_stop_2805_);
if (v___x_2814_ == 0)
{
lean_object* v___x_2815_; lean_object* v_pkg_2816_; lean_object* v_name_2817_; lean_object* v_keyName_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2815_ = lean_array_uget_borrowed(v_as_2803_, v_i_2804_);
v_pkg_2816_ = lean_ctor_get(v___x_2815_, 0);
v_name_2817_ = lean_ctor_get(v___x_2815_, 1);
v_keyName_2818_ = lean_ctor_get(v_pkg_2816_, 2);
v___x_2819_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_2817_);
lean_inc(v_keyName_2818_);
v___x_2820_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2820_, 0, v_keyName_2818_);
lean_ctor_set(v___x_2820_, 1, v_name_2817_);
v___x_2821_ = l_Lake_ExternLib_keyword;
lean_inc(v___x_2815_);
v___x_2822_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2820_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
lean_ctor_set(v___x_2822_, 2, v___x_2815_);
lean_ctor_set(v___x_2822_, 3, v___x_2819_);
lean_inc_ref(v___y_2807_);
lean_inc_ref(v___y_2811_);
lean_inc(v___y_2810_);
lean_inc(v___y_2809_);
lean_inc(v___y_2808_);
v___x_2823_ = lean_apply_7(v___y_2807_, v___x_2822_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, lean_box(0));
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v_a_2825_; lean_object* v___x_2826_; size_t v___x_2827_; size_t v___x_2828_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
v_a_2825_ = lean_ctor_get(v___x_2823_, 1);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2823_, 2);
v___x_2826_ = lean_array_push(v_b_2806_, v_a_2824_);
v___x_2827_ = ((size_t)1ULL);
v___x_2828_ = lean_usize_add(v_i_2804_, v___x_2827_);
v_i_2804_ = v___x_2828_;
v_b_2806_ = v___x_2826_;
v___y_2812_ = v_a_2825_;
goto _start;
}
else
{
lean_object* v_a_2830_; lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec_ref(v___y_2807_);
lean_dec_ref(v_b_2806_);
v_a_2830_ = lean_ctor_get(v___x_2823_, 0);
v_a_2831_ = lean_ctor_get(v___x_2823_, 1);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2823_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_inc(v_a_2830_);
lean_dec(v___x_2823_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2830_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
else
{
lean_object* v___x_2839_; 
lean_dec_ref(v___y_2807_);
v___x_2839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2839_, 0, v_b_2806_);
lean_ctor_set(v___x_2839_, 1, v___y_2812_);
return v___x_2839_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2803_ = stack[0].m_obj;
size_t v_i_2804_ = stack[1].m_num;
size_t v_stop_2805_ = stack[2].m_num;
lean_object* v_b_2806_ = stack[3].m_obj;
lean_object* v___y_2807_ = stack[4].m_obj;
lean_object* v___y_2808_ = stack[5].m_obj;
lean_object* v___y_2809_ = stack[6].m_obj;
lean_object* v___y_2810_ = stack[7].m_obj;
lean_object* v___y_2811_ = stack[8].m_obj;
lean_object* v___y_2812_ = stack[9].m_obj;
lean_object* v_res_2840_;
v_res_2840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v_as_2803_, v_i_2804_, v_stop_2805_, v_b_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_);
stack->m_obj
 = v_res_2840_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(lean_object* v_as_2841_, lean_object* v_i_2842_, lean_object* v_stop_2843_, lean_object* v_b_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
size_t v_i_boxed_2852_; size_t v_stop_boxed_2853_; lean_object* v_res_2854_; 
v_i_boxed_2852_ = lean_unbox_usize(v_i_2842_);
lean_dec(v_i_2842_);
v_stop_boxed_2853_ = lean_unbox_usize(v_stop_2843_);
lean_dec(v_stop_2843_);
v_res_2854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v_as_2841_, v_i_boxed_2852_, v_stop_boxed_2853_, v_b_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec(v___y_2847_);
lean_dec(v___y_2846_);
lean_dec_ref(v_as_2841_);
return v_res_2854_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(lean_object* v_as_2855_, size_t v_i_2856_, size_t v_stop_2857_, lean_object* v_b_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_a_2867_; lean_object* v_a_2868_; uint8_t v___x_2872_; 
v___x_2872_ = lean_usize_dec_eq(v_i_2856_, v_stop_2857_);
if (v___x_2872_ == 0)
{
lean_object* v_fst_2873_; lean_object* v_snd_2874_; lean_object* v___x_2875_; lean_object* v_lib_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2913_; 
v_fst_2873_ = lean_ctor_get(v_b_2858_, 0);
v_snd_2874_ = lean_ctor_get(v_b_2858_, 1);
v___x_2875_ = lean_array_uget(v_as_2855_, v_i_2856_);
v_lib_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; 
v_unused_2914_ = lean_ctor_get(v___x_2875_, 1);
lean_dec(v_unused_2914_);
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2913_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_lib_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2913_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v_pkg_2880_; lean_object* v_name_2881_; uint8_t v___x_2882_; 
v_pkg_2880_ = lean_ctor_get(v_lib_2876_, 0);
v_name_2881_ = lean_ctor_get(v_lib_2876_, 1);
lean_inc(v_name_2881_);
v___x_2882_ = l_Lean_NameSet_contains(v_fst_2873_, v_name_2881_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2910_; 
lean_inc(v_snd_2874_);
lean_inc(v_fst_2873_);
v_isSharedCheck_2910_ = !lean_is_exclusive(v_b_2858_);
if (v_isSharedCheck_2910_ == 0)
{
lean_object* v_unused_2911_; lean_object* v_unused_2912_; 
v_unused_2911_ = lean_ctor_get(v_b_2858_, 1);
lean_dec(v_unused_2911_);
v_unused_2912_ = lean_ctor_get(v_b_2858_, 0);
lean_dec(v_unused_2912_);
v___x_2884_ = v_b_2858_;
v_isShared_2885_ = v_isSharedCheck_2910_;
goto v_resetjp_2883_;
}
else
{
lean_dec(v_b_2858_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2910_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v_keyName_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
v_keyName_2886_ = lean_ctor_get(v_pkg_2880_, 2);
v___x_2887_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_2881_);
lean_inc(v_keyName_2886_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set_tag(v___x_2878_, 3);
lean_ctor_set(v___x_2878_, 1, v_name_2881_);
lean_ctor_set(v___x_2878_, 0, v_keyName_2886_);
v___x_2889_ = v___x_2878_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_keyName_2886_);
lean_ctor_set(v_reuseFailAlloc_2909_, 1, v_name_2881_);
v___x_2889_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2890_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2891_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
lean_ctor_set(v___x_2891_, 2, v_lib_2876_);
lean_ctor_set(v___x_2891_, 3, v___x_2887_);
lean_inc_ref(v___y_2859_);
lean_inc_ref(v___y_2863_);
lean_inc(v___y_2862_);
lean_inc(v___y_2861_);
lean_inc(v___y_2860_);
v___x_2892_ = lean_apply_7(v___y_2859_, v___x_2891_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, lean_box(0));
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2898_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
v_a_2894_ = lean_ctor_get(v___x_2892_, 1);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2892_, 2);
v___x_2895_ = lean_array_push(v_snd_2874_, v_a_2893_);
v___x_2896_ = l_Lean_NameSet_insert(v_fst_2873_, v_name_2881_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 1, v___x_2895_);
lean_ctor_set(v___x_2884_, 0, v___x_2896_);
v___x_2898_ = v___x_2884_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v___x_2895_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
v_a_2867_ = v___x_2898_;
v_a_2868_ = v_a_2894_;
goto v___jp_2866_;
}
}
else
{
lean_object* v_a_2900_; lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_del_object(v___x_2884_);
lean_dec(v_name_2881_);
lean_dec(v_snd_2874_);
lean_dec(v_fst_2873_);
lean_dec_ref(v___y_2859_);
v_a_2900_ = lean_ctor_get(v___x_2892_, 0);
v_a_2901_ = lean_ctor_get(v___x_2892_, 1);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2892_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_inc(v_a_2900_);
lean_dec(v___x_2892_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2900_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
}
else
{
lean_dec(v_name_2881_);
lean_del_object(v___x_2878_);
lean_dec_ref(v_lib_2876_);
v_a_2867_ = v_b_2858_;
v_a_2868_ = v___y_2864_;
goto v___jp_2866_;
}
}
}
else
{
lean_object* v___x_2915_; 
lean_dec_ref(v___y_2859_);
v___x_2915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2915_, 0, v_b_2858_);
lean_ctor_set(v___x_2915_, 1, v___y_2864_);
return v___x_2915_;
}
v___jp_2866_:
{
size_t v___x_2869_; size_t v___x_2870_; 
v___x_2869_ = ((size_t)1ULL);
v___x_2870_ = lean_usize_add(v_i_2856_, v___x_2869_);
v_i_2856_ = v___x_2870_;
v_b_2858_ = v_a_2867_;
v___y_2864_ = v_a_2868_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2855_ = stack[0].m_obj;
size_t v_i_2856_ = stack[1].m_num;
size_t v_stop_2857_ = stack[2].m_num;
lean_object* v_b_2858_ = stack[3].m_obj;
lean_object* v___y_2859_ = stack[4].m_obj;
lean_object* v___y_2860_ = stack[5].m_obj;
lean_object* v___y_2861_ = stack[6].m_obj;
lean_object* v___y_2862_ = stack[7].m_obj;
lean_object* v___y_2863_ = stack[8].m_obj;
lean_object* v___y_2864_ = stack[9].m_obj;
lean_object* v_res_2916_;
v_res_2916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_as_2855_, v_i_2856_, v_stop_2857_, v_b_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
stack->m_obj
 = v_res_2916_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object* v_as_2917_, lean_object* v_i_2918_, lean_object* v_stop_2919_, lean_object* v_b_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
size_t v_i_boxed_2928_; size_t v_stop_boxed_2929_; lean_object* v_res_2930_; 
v_i_boxed_2928_ = lean_unbox_usize(v_i_2918_);
lean_dec(v_i_2918_);
v_stop_boxed_2929_ = lean_unbox_usize(v_stop_2919_);
lean_dec(v_stop_2919_);
v_res_2930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_as_2917_, v_i_boxed_2928_, v_stop_boxed_2929_, v_b_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v_as_2917_);
return v_res_2930_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(lean_object* v___x_2931_, lean_object* v_as_2932_, size_t v_i_2933_, size_t v_stop_2934_, lean_object* v_b_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
uint8_t v___x_2943_; 
v___x_2943_ = lean_usize_dec_eq(v_i_2933_, v_stop_2934_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = lean_array_uget_borrowed(v_as_2932_, v_i_2933_);
lean_inc_ref(v___y_2936_);
lean_inc(v___x_2944_);
lean_inc_ref(v___x_2931_);
v___x_2945_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v___x_2931_, v___x_2944_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v_a_2947_; lean_object* v___x_2948_; size_t v___x_2949_; size_t v___x_2950_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
v_a_2947_ = lean_ctor_get(v___x_2945_, 1);
lean_inc(v_a_2947_);
lean_dec_ref_known(v___x_2945_, 2);
v___x_2948_ = lean_array_push(v_b_2935_, v_a_2946_);
v___x_2949_ = ((size_t)1ULL);
v___x_2950_ = lean_usize_add(v_i_2933_, v___x_2949_);
v_i_2933_ = v___x_2950_;
v_b_2935_ = v___x_2948_;
v___y_2941_ = v_a_2947_;
goto _start;
}
else
{
lean_object* v_a_2952_; lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec_ref(v___y_2936_);
lean_dec_ref(v_b_2935_);
lean_dec_ref(v___x_2931_);
v_a_2952_ = lean_ctor_get(v___x_2945_, 0);
v_a_2953_ = lean_ctor_get(v___x_2945_, 1);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2945_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_inc(v_a_2952_);
lean_dec(v___x_2945_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2952_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
else
{
lean_object* v___x_2961_; 
lean_dec_ref(v___y_2936_);
lean_dec_ref(v___x_2931_);
v___x_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2961_, 0, v_b_2935_);
lean_ctor_set(v___x_2961_, 1, v___y_2941_);
return v___x_2961_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2931_ = stack[0].m_obj;
lean_object* v_as_2932_ = stack[1].m_obj;
size_t v_i_2933_ = stack[2].m_num;
size_t v_stop_2934_ = stack[3].m_num;
lean_object* v_b_2935_ = stack[4].m_obj;
lean_object* v___y_2936_ = stack[5].m_obj;
lean_object* v___y_2937_ = stack[6].m_obj;
lean_object* v___y_2938_ = stack[7].m_obj;
lean_object* v___y_2939_ = stack[8].m_obj;
lean_object* v___y_2940_ = stack[9].m_obj;
lean_object* v___y_2941_ = stack[10].m_obj;
lean_object* v_res_2962_;
v_res_2962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v___x_2931_, v_as_2932_, v_i_2933_, v_stop_2934_, v_b_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
stack->m_obj
 = v_res_2962_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object* v___x_2963_, lean_object* v_as_2964_, lean_object* v_i_2965_, lean_object* v_stop_2966_, lean_object* v_b_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
size_t v_i_boxed_2975_; size_t v_stop_boxed_2976_; lean_object* v_res_2977_; 
v_i_boxed_2975_ = lean_unbox_usize(v_i_2965_);
lean_dec(v_i_2965_);
v_stop_boxed_2976_ = lean_unbox_usize(v_stop_2966_);
lean_dec(v_stop_2966_);
v_res_2977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v___x_2963_, v_as_2964_, v_i_boxed_2975_, v_stop_boxed_2976_, v_b_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v_as_2964_);
return v_res_2977_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(lean_object* v___x_2978_, lean_object* v_as_2979_, size_t v_i_2980_, size_t v_stop_2981_, lean_object* v_b_2982_){
_start:
{
lean_object* v___y_2984_; uint8_t v___x_2988_; 
v___x_2988_ = lean_usize_dec_eq(v_i_2980_, v_stop_2981_);
if (v___x_2988_ == 0)
{
lean_object* v_toConfigDecl_2989_; lean_object* v_name_2990_; lean_object* v_kind_2991_; lean_object* v_config_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; 
v_toConfigDecl_2989_ = lean_array_uget_borrowed(v_as_2979_, v_i_2980_);
v_name_2990_ = lean_ctor_get(v_toConfigDecl_2989_, 1);
v_kind_2991_ = lean_ctor_get(v_toConfigDecl_2989_, 2);
v_config_2992_ = lean_ctor_get(v_toConfigDecl_2989_, 3);
v___x_2993_ = l_Lake_ExternLib_keyword;
v___x_2994_ = lean_name_eq(v_kind_2991_, v___x_2993_);
if (v___x_2994_ == 0)
{
v___y_2984_ = v_b_2982_;
goto v___jp_2983_;
}
else
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
lean_inc(v_config_2992_);
lean_inc(v_name_2990_);
lean_inc_ref(v___x_2978_);
v___x_2995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2978_);
lean_ctor_set(v___x_2995_, 1, v_name_2990_);
lean_ctor_set(v___x_2995_, 2, v_config_2992_);
v___x_2996_ = lean_array_push(v_b_2982_, v___x_2995_);
v___y_2984_ = v___x_2996_;
goto v___jp_2983_;
}
}
else
{
lean_dec_ref(v___x_2978_);
return v_b_2982_;
}
v___jp_2983_:
{
size_t v___x_2985_; size_t v___x_2986_; 
v___x_2985_ = ((size_t)1ULL);
v___x_2986_ = lean_usize_add(v_i_2980_, v___x_2985_);
v_i_2980_ = v___x_2986_;
v_b_2982_ = v___y_2984_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2978_ = stack[0].m_obj;
lean_object* v_as_2979_ = stack[1].m_obj;
size_t v_i_2980_ = stack[2].m_num;
size_t v_stop_2981_ = stack[3].m_num;
lean_object* v_b_2982_ = stack[4].m_obj;
lean_object* v_res_2997_;
v_res_2997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v___x_2978_, v_as_2979_, v_i_2980_, v_stop_2981_, v_b_2982_);
stack->m_obj
 = v_res_2997_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(lean_object* v___x_2998_, lean_object* v_as_2999_, lean_object* v_i_3000_, lean_object* v_stop_3001_, lean_object* v_b_3002_){
_start:
{
size_t v_i_boxed_3003_; size_t v_stop_boxed_3004_; lean_object* v_res_3005_; 
v_i_boxed_3003_ = lean_unbox_usize(v_i_3000_);
lean_dec(v_i_3000_);
v_stop_boxed_3004_ = lean_unbox_usize(v_stop_3001_);
lean_dec(v_stop_3001_);
v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v___x_2998_, v_as_2999_, v_i_boxed_3003_, v_stop_boxed_3004_, v_b_3002_);
lean_dec_ref(v_as_2999_);
return v_res_3005_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(lean_object* v_as_3006_, size_t v_i_3007_, size_t v_stop_3008_, lean_object* v_b_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
uint8_t v___x_3017_; 
v___x_3017_ = lean_usize_dec_eq(v_i_3007_, v_stop_3008_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; lean_object* v_lib_3019_; lean_object* v_config_3020_; lean_object* v_nativeFacets_3021_; uint8_t v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; size_t v_sz_3025_; size_t v___x_3026_; lean_object* v___x_3027_; 
v___x_3018_ = lean_array_uget_borrowed(v_as_3006_, v_i_3007_);
v_lib_3019_ = lean_ctor_get(v___x_3018_, 0);
v_config_3020_ = lean_ctor_get(v_lib_3019_, 2);
v_nativeFacets_3021_ = lean_ctor_get(v_config_3020_, 8);
v___x_3022_ = 1;
v___x_3023_ = lean_box(v___x_3022_);
lean_inc_ref(v_nativeFacets_3021_);
v___x_3024_ = lean_apply_1(v_nativeFacets_3021_, v___x_3023_);
v_sz_3025_ = lean_array_size(v___x_3024_);
v___x_3026_ = ((size_t)0ULL);
lean_inc_ref(v___y_3010_);
lean_inc(v___x_3018_);
v___x_3027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_3018_, v_sz_3025_, v___x_3026_, v___x_3024_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v_a_3029_; lean_object* v___x_3030_; size_t v___x_3031_; size_t v___x_3032_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
v_a_3029_ = lean_ctor_get(v___x_3027_, 1);
lean_inc(v_a_3029_);
lean_dec_ref_known(v___x_3027_, 2);
v___x_3030_ = l_Array_append___redArg(v_b_3009_, v_a_3028_);
lean_dec(v_a_3028_);
v___x_3031_ = ((size_t)1ULL);
v___x_3032_ = lean_usize_add(v_i_3007_, v___x_3031_);
v_i_3007_ = v___x_3032_;
v_b_3009_ = v___x_3030_;
v___y_3015_ = v_a_3029_;
goto _start;
}
else
{
lean_dec_ref(v___y_3010_);
lean_dec_ref(v_b_3009_);
return v___x_3027_;
}
}
else
{
lean_object* v___x_3034_; 
lean_dec_ref(v___y_3010_);
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v_b_3009_);
lean_ctor_set(v___x_3034_, 1, v___y_3015_);
return v___x_3034_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3006_ = stack[0].m_obj;
size_t v_i_3007_ = stack[1].m_num;
size_t v_stop_3008_ = stack[2].m_num;
lean_object* v_b_3009_ = stack[3].m_obj;
lean_object* v___y_3010_ = stack[4].m_obj;
lean_object* v___y_3011_ = stack[5].m_obj;
lean_object* v___y_3012_ = stack[6].m_obj;
lean_object* v___y_3013_ = stack[7].m_obj;
lean_object* v___y_3014_ = stack[8].m_obj;
lean_object* v___y_3015_ = stack[9].m_obj;
lean_object* v_res_3035_;
v_res_3035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_as_3006_, v_i_3007_, v_stop_3008_, v_b_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
stack->m_obj
 = v_res_3035_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object* v_as_3036_, lean_object* v_i_3037_, lean_object* v_stop_3038_, lean_object* v_b_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
size_t v_i_boxed_3047_; size_t v_stop_boxed_3048_; lean_object* v_res_3049_; 
v_i_boxed_3047_ = lean_unbox_usize(v_i_3037_);
lean_dec(v_i_3037_);
v_stop_boxed_3048_ = lean_unbox_usize(v_stop_3038_);
lean_dec(v_stop_3038_);
v_res_3049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_as_3036_, v_i_boxed_3047_, v_stop_boxed_3048_, v_b_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v_as_3036_);
return v_res_3049_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(lean_object* v_self_3050_, lean_object* v_dir_3051_, lean_object* v___x_3052_, lean_object* v_targetDecls_3053_, lean_object* v_pkg_3054_, lean_object* v_name_3055_, lean_object* v___x_3056_, lean_object* v_config_3057_, lean_object* v_config_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_a_3067_; lean_object* v_a_3068_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v_a_3078_; lean_object* v_a_3079_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v_a_3139_; lean_object* v_a_3140_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v_snd_3172_; lean_object* v_a_3173_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v_a_3195_; lean_object* v_a_3196_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___x_3235_; 
lean_inc_ref(v___y_3059_);
lean_inc_ref(v___y_3063_);
lean_inc(v___y_3062_);
lean_inc(v___y_3061_);
lean_inc(v___x_3052_);
v___x_3235_ = lean_apply_7(v___y_3059_, v___x_3056_, v___x_3052_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, lean_box(0));
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v_a_3237_; lean_object* v___x_3238_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
v_a_3237_ = lean_ctor_get(v___x_3235_, 1);
lean_inc(v_a_3237_);
lean_dec_ref_known(v___x_3235_, 2);
v___x_3238_ = l_Lake_Job_await___redArg(v_a_3236_, v_a_3237_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v_a_3240_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v_a_3251_; lean_object* v_a_3252_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v_a_3286_; lean_object* v_a_3287_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
v_a_3240_ = lean_ctor_get(v___x_3238_, 1);
lean_inc(v_a_3240_);
lean_dec_ref_known(v___x_3238_, 2);
v___x_3311_ = lean_unsigned_to_nat(0u);
v___x_3312_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_3313_ = lean_array_get_size(v_a_3239_);
v___x_3314_ = lean_nat_dec_lt(v___x_3311_, v___x_3313_);
if (v___x_3314_ == 0)
{
v_a_3286_ = v___x_3312_;
v_a_3287_ = v_a_3240_;
goto v___jp_3285_;
}
else
{
size_t v___x_3315_; size_t v___x_3316_; lean_object* v___x_3317_; 
v___x_3315_ = ((size_t)0ULL);
v___x_3316_ = lean_usize_of_nat(v___x_3313_);
lean_inc_ref(v___y_3059_);
v___x_3317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3239_, v___x_3315_, v___x_3316_, v___x_3312_, v___y_3059_, v___x_3052_, v___y_3061_, v___y_3062_, v___y_3063_, v_a_3240_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v_a_3319_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3318_);
v_a_3319_ = lean_ctor_get(v___x_3317_, 1);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3317_, 2);
v_a_3286_ = v_a_3318_;
v_a_3287_ = v_a_3319_;
goto v___jp_3285_;
}
else
{
lean_object* v_a_3320_; lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_dec(v_a_3239_);
lean_dec_ref(v___y_3059_);
lean_dec_ref(v_config_3057_);
lean_dec(v_name_3055_);
lean_dec_ref(v_pkg_3054_);
lean_dec(v___x_3052_);
lean_dec_ref(v_dir_3051_);
lean_dec_ref(v_self_3050_);
v_a_3320_ = lean_ctor_get(v___x_3317_, 0);
v_a_3321_ = lean_ctor_get(v___x_3317_, 1);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3317_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_inc(v_a_3320_);
lean_dec(v___x_3317_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3320_);
lean_ctor_set(v_reuseFailAlloc_3327_, 1, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
v___jp_3241_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
v___x_3253_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
v___x_3254_ = lean_array_get_size(v_a_3239_);
v___x_3255_ = lean_nat_dec_lt(v___y_3245_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_dec(v_a_3239_);
v___y_3185_ = v___y_3242_;
v___y_3186_ = v___y_3243_;
v___y_3187_ = v___y_3244_;
v___y_3188_ = v___y_3245_;
v___y_3189_ = v___y_3246_;
v___y_3190_ = v___y_3247_;
v___y_3191_ = v___y_3248_;
v___y_3192_ = v___y_3249_;
v___y_3193_ = v_a_3251_;
v___y_3194_ = v___y_3250_;
v_a_3195_ = v___x_3253_;
v_a_3196_ = v_a_3252_;
goto v___jp_3184_;
}
else
{
uint8_t v___x_3256_; 
v___x_3256_ = lean_nat_dec_le(v___x_3254_, v___x_3254_);
if (v___x_3256_ == 0)
{
if (v___x_3255_ == 0)
{
lean_dec(v_a_3239_);
v___y_3185_ = v___y_3242_;
v___y_3186_ = v___y_3243_;
v___y_3187_ = v___y_3244_;
v___y_3188_ = v___y_3245_;
v___y_3189_ = v___y_3246_;
v___y_3190_ = v___y_3247_;
v___y_3191_ = v___y_3248_;
v___y_3192_ = v___y_3249_;
v___y_3193_ = v_a_3251_;
v___y_3194_ = v___y_3250_;
v_a_3195_ = v___x_3253_;
v_a_3196_ = v_a_3252_;
goto v___jp_3184_;
}
else
{
size_t v___x_3257_; size_t v___x_3258_; lean_object* v___x_3259_; 
v___x_3257_ = ((size_t)0ULL);
v___x_3258_ = lean_usize_of_nat(v___x_3254_);
lean_inc_ref(v___y_3059_);
v___x_3259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3239_, v___x_3257_, v___x_3258_, v___x_3253_, v___y_3059_, v___x_3052_, v___y_3061_, v___y_3062_, v___y_3063_, v_a_3252_);
lean_dec(v_a_3239_);
v___y_3220_ = v___y_3242_;
v___y_3221_ = v___y_3243_;
v___y_3222_ = v___y_3244_;
v___y_3223_ = v___y_3245_;
v___y_3224_ = v___y_3248_;
v___y_3225_ = v___y_3247_;
v___y_3226_ = v___y_3246_;
v___y_3227_ = v_a_3251_;
v___y_3228_ = v___y_3249_;
v___y_3229_ = v___y_3250_;
v___y_3230_ = v___x_3259_;
goto v___jp_3219_;
}
}
else
{
size_t v___x_3260_; size_t v___x_3261_; lean_object* v___x_3262_; 
v___x_3260_ = ((size_t)0ULL);
v___x_3261_ = lean_usize_of_nat(v___x_3254_);
lean_inc_ref(v___y_3059_);
v___x_3262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3239_, v___x_3260_, v___x_3261_, v___x_3253_, v___y_3059_, v___x_3052_, v___y_3061_, v___y_3062_, v___y_3063_, v_a_3252_);
lean_dec(v_a_3239_);
v___y_3220_ = v___y_3242_;
v___y_3221_ = v___y_3243_;
v___y_3222_ = v___y_3244_;
v___y_3223_ = v___y_3245_;
v___y_3224_ = v___y_3248_;
v___y_3225_ = v___y_3247_;
v___y_3226_ = v___y_3246_;
v___y_3227_ = v_a_3251_;
v___y_3228_ = v___y_3249_;
v___y_3229_ = v___y_3250_;
v___y_3230_ = v___x_3262_;
goto v___jp_3219_;
}
}
}
v___jp_3263_:
{
if (lean_obj_tag(v___y_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v_a_3275_; 
v_a_3274_ = lean_ctor_get(v___y_3273_, 0);
lean_inc(v_a_3274_);
v_a_3275_ = lean_ctor_get(v___y_3273_, 1);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___y_3273_, 2);
v___y_3242_ = v___y_3264_;
v___y_3243_ = v___y_3265_;
v___y_3244_ = v___y_3266_;
v___y_3245_ = v___y_3267_;
v___y_3246_ = v___y_3270_;
v___y_3247_ = v___y_3269_;
v___y_3248_ = v___y_3268_;
v___y_3249_ = v___y_3271_;
v___y_3250_ = v___y_3272_;
v_a_3251_ = v_a_3274_;
v_a_3252_ = v_a_3275_;
goto v___jp_3241_;
}
else
{
lean_object* v_a_3276_; lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec_ref(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec_ref(v___y_3268_);
lean_dec_ref(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v_a_3239_);
lean_dec_ref(v___y_3059_);
lean_dec(v_name_3055_);
lean_dec_ref(v_pkg_3054_);
lean_dec(v___x_3052_);
lean_dec_ref(v_dir_3051_);
lean_dec_ref(v_self_3050_);
v_a_3276_ = lean_ctor_get(v___y_3273_, 0);
v_a_3277_ = lean_ctor_get(v___y_3273_, 1);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___y_3273_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___y_3273_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_inc(v_a_3276_);
lean_dec(v___y_3273_);
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
v___jp_3285_:
{
lean_object* v_toLeanConfig_3288_; lean_object* v_toLeanConfig_3289_; lean_object* v_buildDir_3290_; lean_object* v_nativeLibDir_3291_; lean_object* v_moreLinkObjs_3292_; lean_object* v_moreLinkLibs_3293_; lean_object* v_moreLinkArgs_3294_; lean_object* v_weakLinkArgs_3295_; lean_object* v_moreLinkObjs_3296_; lean_object* v_moreLinkLibs_3297_; lean_object* v_moreLinkArgs_3298_; lean_object* v_weakLinkArgs_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; 
v_toLeanConfig_3288_ = lean_ctor_get(v_config_3057_, 1);
lean_inc_ref(v_toLeanConfig_3288_);
v_toLeanConfig_3289_ = lean_ctor_get(v_config_3058_, 0);
v_buildDir_3290_ = lean_ctor_get(v_config_3057_, 5);
lean_inc_ref(v_buildDir_3290_);
v_nativeLibDir_3291_ = lean_ctor_get(v_config_3057_, 7);
lean_inc_ref(v_nativeLibDir_3291_);
lean_dec_ref(v_config_3057_);
v_moreLinkObjs_3292_ = lean_ctor_get(v_toLeanConfig_3288_, 6);
lean_inc_ref(v_moreLinkObjs_3292_);
v_moreLinkLibs_3293_ = lean_ctor_get(v_toLeanConfig_3288_, 7);
lean_inc_ref(v_moreLinkLibs_3293_);
v_moreLinkArgs_3294_ = lean_ctor_get(v_toLeanConfig_3288_, 8);
lean_inc_ref(v_moreLinkArgs_3294_);
v_weakLinkArgs_3295_ = lean_ctor_get(v_toLeanConfig_3288_, 9);
lean_inc_ref(v_weakLinkArgs_3295_);
lean_dec_ref(v_toLeanConfig_3288_);
v_moreLinkObjs_3296_ = lean_ctor_get(v_toLeanConfig_3289_, 6);
v_moreLinkLibs_3297_ = lean_ctor_get(v_toLeanConfig_3289_, 7);
v_moreLinkArgs_3298_ = lean_ctor_get(v_toLeanConfig_3289_, 8);
v_weakLinkArgs_3299_ = lean_ctor_get(v_toLeanConfig_3289_, 9);
v___x_3300_ = l_Array_append___redArg(v_moreLinkObjs_3292_, v_moreLinkObjs_3296_);
v___x_3301_ = lean_unsigned_to_nat(0u);
v___x_3302_ = lean_array_get_size(v___x_3300_);
v___x_3303_ = lean_nat_dec_lt(v___x_3301_, v___x_3302_);
if (v___x_3303_ == 0)
{
lean_dec_ref(v___x_3300_);
v___y_3242_ = v_nativeLibDir_3291_;
v___y_3243_ = v_moreLinkArgs_3294_;
v___y_3244_ = v_weakLinkArgs_3299_;
v___y_3245_ = v___x_3301_;
v___y_3246_ = v_moreLinkLibs_3297_;
v___y_3247_ = v_moreLinkArgs_3298_;
v___y_3248_ = v_weakLinkArgs_3295_;
v___y_3249_ = v_moreLinkLibs_3293_;
v___y_3250_ = v_buildDir_3290_;
v_a_3251_ = v_a_3286_;
v_a_3252_ = v_a_3287_;
goto v___jp_3241_;
}
else
{
uint8_t v___x_3304_; 
v___x_3304_ = lean_nat_dec_le(v___x_3302_, v___x_3302_);
if (v___x_3304_ == 0)
{
if (v___x_3303_ == 0)
{
lean_dec_ref(v___x_3300_);
v___y_3242_ = v_nativeLibDir_3291_;
v___y_3243_ = v_moreLinkArgs_3294_;
v___y_3244_ = v_weakLinkArgs_3299_;
v___y_3245_ = v___x_3301_;
v___y_3246_ = v_moreLinkLibs_3297_;
v___y_3247_ = v_moreLinkArgs_3298_;
v___y_3248_ = v_weakLinkArgs_3295_;
v___y_3249_ = v_moreLinkLibs_3293_;
v___y_3250_ = v_buildDir_3290_;
v_a_3251_ = v_a_3286_;
v_a_3252_ = v_a_3287_;
goto v___jp_3241_;
}
else
{
size_t v___x_3305_; size_t v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = ((size_t)0ULL);
v___x_3306_ = lean_usize_of_nat(v___x_3302_);
lean_inc_ref(v___y_3059_);
lean_inc_ref(v_pkg_3054_);
v___x_3307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_3054_, v___x_3300_, v___x_3305_, v___x_3306_, v_a_3286_, v___y_3059_, v___x_3052_, v___y_3061_, v___y_3062_, v___y_3063_, v_a_3287_);
lean_dec_ref(v___x_3300_);
v___y_3264_ = v_nativeLibDir_3291_;
v___y_3265_ = v_moreLinkArgs_3294_;
v___y_3266_ = v_weakLinkArgs_3299_;
v___y_3267_ = v___x_3301_;
v___y_3268_ = v_weakLinkArgs_3295_;
v___y_3269_ = v_moreLinkArgs_3298_;
v___y_3270_ = v_moreLinkLibs_3297_;
v___y_3271_ = v_moreLinkLibs_3293_;
v___y_3272_ = v_buildDir_3290_;
v___y_3273_ = v___x_3307_;
goto v___jp_3263_;
}
}
else
{
size_t v___x_3308_; size_t v___x_3309_; lean_object* v___x_3310_; 
v___x_3308_ = ((size_t)0ULL);
v___x_3309_ = lean_usize_of_nat(v___x_3302_);
lean_inc_ref(v___y_3059_);
lean_inc_ref(v_pkg_3054_);
v___x_3310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_3054_, v___x_3300_, v___x_3308_, v___x_3309_, v_a_3286_, v___y_3059_, v___x_3052_, v___y_3061_, v___y_3062_, v___y_3063_, v_a_3287_);
lean_dec_ref(v___x_3300_);
v___y_3264_ = v_nativeLibDir_3291_;
v___y_3265_ = v_moreLinkArgs_3294_;
v___y_3266_ = v_weakLinkArgs_3299_;
v___y_3267_ = v___x_3301_;
v___y_3268_ = v_weakLinkArgs_3295_;
v___y_3269_ = v_moreLinkArgs_3298_;
v___y_3270_ = v_moreLinkLibs_3297_;
v___y_3271_ = v_moreLinkLibs_3293_;
v___y_3272_ = v_buildDir_3290_;
v___y_3273_ = v___x_3310_;
goto v___jp_3263_;
}
}
}
}
else
{
lean_object* v_a_3329_; lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec_ref(v___y_3059_);
lean_dec_ref(v_config_3057_);
lean_dec(v_name_3055_);
lean_dec_ref(v_pkg_3054_);
lean_dec(v___x_3052_);
lean_dec_ref(v_dir_3051_);
lean_dec_ref(v_self_3050_);
v_a_3329_ = lean_ctor_get(v___x_3238_, 0);
v_a_3330_ = lean_ctor_get(v___x_3238_, 1);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3238_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_inc(v_a_3329_);
lean_dec(v___x_3238_);
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
else
{
lean_object* v_a_3338_; lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_dec_ref(v___y_3059_);
lean_dec_ref(v_config_3057_);
lean_dec(v_name_3055_);
lean_dec_ref(v_pkg_3054_);
lean_dec(v___x_3052_);
lean_dec_ref(v_dir_3051_);
lean_dec_ref(v_self_3050_);
v_a_3338_ = lean_ctor_get(v___x_3235_, 0);
v_a_3339_ = lean_ctor_get(v___x_3235_, 1);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3235_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_inc(v_a_3338_);
lean_dec(v___x_3235_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3338_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
v___jp_3066_:
{
lean_object* v___x_3069_; 
v___x_3069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3069_, 0, v_a_3067_);
lean_ctor_set(v___x_3069_, 1, v_a_3068_);
return v___x_3069_;
}
v___jp_3070_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; uint8_t v___x_3090_; uint8_t v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_inc_ref(v_self_3050_);
v___x_3080_ = l_Lake_LeanLib_libName(v_self_3050_);
v___x_3081_ = l_System_FilePath_normalize(v___y_3077_);
v___x_3082_ = l_Lake_joinRelative(v_dir_3051_, v___x_3081_);
v___x_3083_ = l_System_FilePath_normalize(v___y_3071_);
v___x_3084_ = l_Lake_joinRelative(v___x_3082_, v___x_3083_);
v___x_3085_ = 0;
v___x_3086_ = l_Lake_nameToSharedLib(v___x_3080_, v___x_3085_);
v___x_3087_ = l_Lake_joinRelative(v___x_3084_, v___x_3086_);
v___x_3088_ = l_Array_append___redArg(v___y_3075_, v___y_3073_);
v___x_3089_ = l_Array_append___redArg(v___y_3072_, v___y_3074_);
v___x_3090_ = l_Lake_LeanLib_isPlugin(v_self_3050_);
v___x_3091_ = l_System_Platform_isWindows;
v___x_3092_ = lean_box(0);
v___x_3093_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___closed__1);
v___x_3094_ = l_Lake_buildLeanSharedLib(v___x_3080_, v___x_3087_, v___y_3076_, v_a_3078_, v___x_3088_, v___x_3089_, v___x_3090_, v___x_3091_, v___x_3092_, v___y_3059_, v___x_3052_, v___y_3061_, v___y_3062_, v___y_3063_, v___x_3093_);
lean_dec(v___x_3052_);
lean_dec_ref(v___y_3076_);
v___x_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
lean_ctor_set(v___x_3095_, 1, v_a_3079_);
return v___x_3095_;
}
v___jp_3096_:
{
if (lean_obj_tag(v___y_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v_a_3106_; 
v_a_3105_ = lean_ctor_get(v___y_3104_, 0);
lean_inc(v_a_3105_);
v_a_3106_ = lean_ctor_get(v___y_3104_, 1);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___y_3104_, 2);
v___y_3071_ = v___y_3097_;
v___y_3072_ = v___y_3098_;
v___y_3073_ = v___y_3099_;
v___y_3074_ = v___y_3101_;
v___y_3075_ = v___y_3100_;
v___y_3076_ = v___y_3102_;
v___y_3077_ = v___y_3103_;
v_a_3078_ = v_a_3105_;
v_a_3079_ = v_a_3106_;
goto v___jp_3070_;
}
else
{
lean_object* v_a_3107_; lean_object* v_a_3108_; 
lean_dec_ref(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec_ref(v___y_3100_);
lean_dec_ref(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec_ref(v___y_3059_);
lean_dec(v___x_3052_);
lean_dec_ref(v_dir_3051_);
lean_dec_ref(v_self_3050_);
v_a_3107_ = lean_ctor_get(v___y_3104_, 0);
lean_inc(v_a_3107_);
v_a_3108_ = lean_ctor_get(v___y_3104_, 1);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___y_3104_, 2);
v_a_3067_ = v_a_3107_;
v_a_3068_ = v_a_3108_;
goto v___jp_3066_;
}
}
v___jp_3109_:
{
lean_object* v___x_3121_; uint8_t v___x_3122_; 
v___x_3121_ = lean_array_get_size(v___y_3120_);
v___x_3122_ = lean_nat_dec_lt(v___y_3114_, v___x_3121_);
if (v___x_3122_ == 0)
{
lean_dec_ref(v___y_3120_);
v___y_3071_ = v___y_3110_;
v___y_3072_ = v___y_3111_;
v___y_3073_ = v___y_3113_;
v___y_3074_ = v___y_3116_;
v___y_3075_ = v___y_3115_;
v___y_3076_ = v___y_3118_;
v___y_3077_ = v___y_3119_;
v_a_3078_ = v___y_3117_;
v_a_3079_ = v___y_3112_;
goto v___jp_3070_;
}
else
{
uint8_t v___x_3123_; 
v___x_3123_ = lean_nat_dec_le(v___x_3121_, v___x_3121_);
if (v___x_3123_ == 0)
{
if (v___x_3122_ == 0)
{
lean_dec_ref(v___y_3120_);
v___y_3071_ = v___y_3110_;
v___y_3072_ = v___y_3111_;
v___y_3073_ = v___y_3113_;
v___y_3074_ = v___y_3116_;
v___y_3075_ = v___y_3115_;
v___y_3076_ = v___y_3118_;
v___y_3077_ = v___y_3119_;
v_a_3078_ = v___y_3117_;
v_a_3079_ = v___y_3112_;
goto v___jp_3070_;
}
else
{
size_t v___x_3124_; size_t v___x_3125_; lean_object* v___x_3126_; 
v___x_3124_ = ((size_t)0ULL);
v___x_3125_ = lean_usize_of_nat(v___x_3121_);
lean_inc_ref(v___y_3059_);
v___x_3126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_3120_, v___x_3124_, v___x_3125_, v___y_3117_, v___y_3059_, v___x_3052_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3112_);
lean_dec_ref(v___y_3120_);
v___y_3097_ = v___y_3110_;
v___y_3098_ = v___y_3111_;
v___y_3099_ = v___y_3113_;
v___y_3100_ = v___y_3115_;
v___y_3101_ = v___y_3116_;
v___y_3102_ = v___y_3118_;
v___y_3103_ = v___y_3119_;
v___y_3104_ = v___x_3126_;
goto v___jp_3096_;
}
}
else
{
size_t v___x_3127_; size_t v___x_3128_; lean_object* v___x_3129_; 
v___x_3127_ = ((size_t)0ULL);
v___x_3128_ = lean_usize_of_nat(v___x_3121_);
lean_inc_ref(v___y_3059_);
v___x_3129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_3120_, v___x_3127_, v___x_3128_, v___y_3117_, v___y_3059_, v___x_3052_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3112_);
lean_dec_ref(v___y_3120_);
v___y_3097_ = v___y_3110_;
v___y_3098_ = v___y_3111_;
v___y_3099_ = v___y_3113_;
v___y_3100_ = v___y_3115_;
v___y_3101_ = v___y_3116_;
v___y_3102_ = v___y_3118_;
v___y_3103_ = v___y_3119_;
v___y_3104_ = v___x_3129_;
goto v___jp_3096_;
}
}
}
v___jp_3130_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; uint8_t v___x_3143_; 
v___x_3141_ = lean_mk_empty_array_with_capacity(v___y_3134_);
v___x_3142_ = lean_array_get_size(v_targetDecls_3053_);
v___x_3143_ = lean_nat_dec_lt(v___y_3134_, v___x_3142_);
if (v___x_3143_ == 0)
{
lean_dec_ref(v_pkg_3054_);
v___y_3110_ = v___y_3131_;
v___y_3111_ = v___y_3132_;
v___y_3112_ = v_a_3140_;
v___y_3113_ = v___y_3133_;
v___y_3114_ = v___y_3134_;
v___y_3115_ = v___y_3136_;
v___y_3116_ = v___y_3135_;
v___y_3117_ = v_a_3139_;
v___y_3118_ = v___y_3137_;
v___y_3119_ = v___y_3138_;
v___y_3120_ = v___x_3141_;
goto v___jp_3109_;
}
else
{
size_t v___x_3144_; size_t v___x_3145_; lean_object* v___x_3146_; 
v___x_3144_ = ((size_t)0ULL);
v___x_3145_ = lean_usize_of_nat(v___x_3142_);
v___x_3146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_3054_, v_targetDecls_3053_, v___x_3144_, v___x_3145_, v___x_3141_);
v___y_3110_ = v___y_3131_;
v___y_3111_ = v___y_3132_;
v___y_3112_ = v_a_3140_;
v___y_3113_ = v___y_3133_;
v___y_3114_ = v___y_3134_;
v___y_3115_ = v___y_3136_;
v___y_3116_ = v___y_3135_;
v___y_3117_ = v_a_3139_;
v___y_3118_ = v___y_3137_;
v___y_3119_ = v___y_3138_;
v___y_3120_ = v___x_3146_;
goto v___jp_3109_;
}
}
v___jp_3147_:
{
if (lean_obj_tag(v___y_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v_a_3158_; 
v_a_3157_ = lean_ctor_get(v___y_3156_, 0);
lean_inc(v_a_3157_);
v_a_3158_ = lean_ctor_get(v___y_3156_, 1);
lean_inc(v_a_3158_);
lean_dec_ref_known(v___y_3156_, 2);
v___y_3131_ = v___y_3148_;
v___y_3132_ = v___y_3149_;
v___y_3133_ = v___y_3150_;
v___y_3134_ = v___y_3151_;
v___y_3135_ = v___y_3153_;
v___y_3136_ = v___y_3152_;
v___y_3137_ = v___y_3154_;
v___y_3138_ = v___y_3155_;
v_a_3139_ = v_a_3157_;
v_a_3140_ = v_a_3158_;
goto v___jp_3130_;
}
else
{
lean_object* v_a_3159_; lean_object* v_a_3160_; 
lean_dec_ref(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec_ref(v___y_3152_);
lean_dec_ref(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec_ref(v___y_3059_);
lean_dec_ref(v_pkg_3054_);
lean_dec(v___x_3052_);
lean_dec_ref(v_dir_3051_);
lean_dec_ref(v_self_3050_);
v_a_3159_ = lean_ctor_get(v___y_3156_, 0);
lean_inc(v_a_3159_);
v_a_3160_ = lean_ctor_get(v___y_3156_, 1);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___y_3156_, 2);
v_a_3067_ = v_a_3159_;
v_a_3068_ = v_a_3160_;
goto v___jp_3066_;
}
}
v___jp_3161_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; 
v___x_3174_ = l_Array_append___redArg(v___y_3170_, v___y_3168_);
v___x_3175_ = lean_array_get_size(v___x_3174_);
v___x_3176_ = lean_nat_dec_lt(v___y_3165_, v___x_3175_);
if (v___x_3176_ == 0)
{
lean_dec_ref(v___x_3174_);
v___y_3131_ = v___y_3162_;
v___y_3132_ = v___y_3163_;
v___y_3133_ = v___y_3164_;
v___y_3134_ = v___y_3165_;
v___y_3135_ = v___y_3167_;
v___y_3136_ = v___y_3166_;
v___y_3137_ = v___y_3169_;
v___y_3138_ = v___y_3171_;
v_a_3139_ = v_snd_3172_;
v_a_3140_ = v_a_3173_;
goto v___jp_3130_;
}
else
{
uint8_t v___x_3177_; 
v___x_3177_ = lean_nat_dec_le(v___x_3175_, v___x_3175_);
if (v___x_3177_ == 0)
{
if (v___x_3176_ == 0)
{
lean_dec_ref(v___x_3174_);
v___y_3131_ = v___y_3162_;
v___y_3132_ = v___y_3163_;
v___y_3133_ = v___y_3164_;
v___y_3134_ = v___y_3165_;
v___y_3135_ = v___y_3167_;
v___y_3136_ = v___y_3166_;
v___y_3137_ = v___y_3169_;
v___y_3138_ = v___y_3171_;
v_a_3139_ = v_snd_3172_;
v_a_3140_ = v_a_3173_;
goto v___jp_3130_;
}
else
{
size_t v___x_3178_; size_t v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = ((size_t)0ULL);
v___x_3179_ = lean_usize_of_nat(v___x_3175_);
lean_inc_ref(v___y_3059_);
lean_inc_ref(v_pkg_3054_);
v___x_3180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_3054_, v___x_3174_, v___x_3178_, v___x_3179_, v_snd_3172_, v___y_3059_, v___x_3052_, v___y_3061_, v___y_3062_, v___y_3063_, v_a_3173_);
lean_dec_ref(v___x_3174_);
v___y_3148_ = v___y_3162_;
v___y_3149_ = v___y_3163_;
v___y_3150_ = v___y_3164_;
v___y_3151_ = v___y_3165_;
v___y_3152_ = v___y_3166_;
v___y_3153_ = v___y_3167_;
v___y_3154_ = v___y_3169_;
v___y_3155_ = v___y_3171_;
v___y_3156_ = v___x_3180_;
goto v___jp_3147_;
}
}
else
{
size_t v___x_3181_; size_t v___x_3182_; lean_object* v___x_3183_; 
v___x_3181_ = ((size_t)0ULL);
v___x_3182_ = lean_usize_of_nat(v___x_3175_);
lean_inc_ref(v___y_3059_);
lean_inc_ref(v_pkg_3054_);
v___x_3183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_3054_, v___x_3174_, v___x_3181_, v___x_3182_, v_snd_3172_, v___y_3059_, v___x_3052_, v___y_3061_, v___y_3062_, v___y_3063_, v_a_3173_);
lean_dec_ref(v___x_3174_);
v___y_3148_ = v___y_3162_;
v___y_3149_ = v___y_3163_;
v___y_3150_ = v___y_3164_;
v___y_3151_ = v___y_3165_;
v___y_3152_ = v___y_3166_;
v___y_3153_ = v___y_3167_;
v___y_3154_ = v___y_3169_;
v___y_3155_ = v___y_3171_;
v___y_3156_ = v___x_3183_;
goto v___jp_3147_;
}
}
}
v___jp_3184_:
{
lean_object* v_toArray_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3217_; 
v_toArray_3197_ = lean_ctor_get(v_a_3195_, 1);
v_isSharedCheck_3217_ = !lean_is_exclusive(v_a_3195_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; 
v_unused_3218_ = lean_ctor_get(v_a_3195_, 0);
lean_dec(v_unused_3218_);
v___x_3199_ = v_a_3195_;
v_isShared_3200_ = v_isSharedCheck_3217_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_toArray_3197_);
lean_dec(v_a_3195_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3217_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; uint8_t v___x_3203_; 
v___x_3201_ = lean_mk_empty_array_with_capacity(v___y_3188_);
v___x_3202_ = lean_array_get_size(v_toArray_3197_);
v___x_3203_ = lean_nat_dec_lt(v___y_3188_, v___x_3202_);
if (v___x_3203_ == 0)
{
lean_del_object(v___x_3199_);
lean_dec_ref(v_toArray_3197_);
lean_dec(v_name_3055_);
v___y_3162_ = v___y_3185_;
v___y_3163_ = v___y_3186_;
v___y_3164_ = v___y_3187_;
v___y_3165_ = v___y_3188_;
v___y_3166_ = v___y_3191_;
v___y_3167_ = v___y_3190_;
v___y_3168_ = v___y_3189_;
v___y_3169_ = v___y_3193_;
v___y_3170_ = v___y_3192_;
v___y_3171_ = v___y_3194_;
v_snd_3172_ = v___x_3201_;
v_a_3173_ = v_a_3196_;
goto v___jp_3161_;
}
else
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3207_; 
v___x_3204_ = l_Lean_NameSet_empty;
v___x_3205_ = l_Lean_NameSet_insert(v___x_3204_, v_name_3055_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 1, v___x_3201_);
lean_ctor_set(v___x_3199_, 0, v___x_3205_);
v___x_3207_ = v___x_3199_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3205_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v___x_3201_);
v___x_3207_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
size_t v___x_3208_; size_t v___x_3209_; lean_object* v___x_3210_; 
v___x_3208_ = ((size_t)0ULL);
v___x_3209_ = lean_usize_of_nat(v___x_3202_);
lean_inc_ref(v___y_3059_);
v___x_3210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_3197_, v___x_3208_, v___x_3209_, v___x_3207_, v___y_3059_, v___x_3052_, v___y_3061_, v___y_3062_, v___y_3063_, v_a_3196_);
lean_dec_ref(v_toArray_3197_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v_a_3212_; lean_object* v_snd_3213_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
v_a_3212_ = lean_ctor_get(v___x_3210_, 1);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3210_, 2);
v_snd_3213_ = lean_ctor_get(v_a_3211_, 1);
lean_inc(v_snd_3213_);
lean_dec(v_a_3211_);
v___y_3162_ = v___y_3185_;
v___y_3163_ = v___y_3186_;
v___y_3164_ = v___y_3187_;
v___y_3165_ = v___y_3188_;
v___y_3166_ = v___y_3191_;
v___y_3167_ = v___y_3190_;
v___y_3168_ = v___y_3189_;
v___y_3169_ = v___y_3193_;
v___y_3170_ = v___y_3192_;
v___y_3171_ = v___y_3194_;
v_snd_3172_ = v_snd_3213_;
v_a_3173_ = v_a_3212_;
goto v___jp_3161_;
}
else
{
lean_object* v_a_3214_; lean_object* v_a_3215_; 
lean_dec_ref(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec_ref(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec_ref(v___y_3059_);
lean_dec_ref(v_pkg_3054_);
lean_dec(v___x_3052_);
lean_dec_ref(v_dir_3051_);
lean_dec_ref(v_self_3050_);
v_a_3214_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3214_);
v_a_3215_ = lean_ctor_get(v___x_3210_, 1);
lean_inc(v_a_3215_);
lean_dec_ref_known(v___x_3210_, 2);
v_a_3067_ = v_a_3214_;
v_a_3068_ = v_a_3215_;
goto v___jp_3066_;
}
}
}
}
}
v___jp_3219_:
{
if (lean_obj_tag(v___y_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v_a_3232_; 
v_a_3231_ = lean_ctor_get(v___y_3230_, 0);
lean_inc(v_a_3231_);
v_a_3232_ = lean_ctor_get(v___y_3230_, 1);
lean_inc(v_a_3232_);
lean_dec_ref_known(v___y_3230_, 2);
v___y_3185_ = v___y_3220_;
v___y_3186_ = v___y_3221_;
v___y_3187_ = v___y_3222_;
v___y_3188_ = v___y_3223_;
v___y_3189_ = v___y_3226_;
v___y_3190_ = v___y_3225_;
v___y_3191_ = v___y_3224_;
v___y_3192_ = v___y_3228_;
v___y_3193_ = v___y_3227_;
v___y_3194_ = v___y_3229_;
v_a_3195_ = v_a_3231_;
v_a_3196_ = v_a_3232_;
goto v___jp_3184_;
}
else
{
lean_object* v_a_3233_; lean_object* v_a_3234_; 
lean_dec_ref(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec_ref(v___y_3224_);
lean_dec_ref(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec_ref(v___y_3059_);
lean_dec(v_name_3055_);
lean_dec_ref(v_pkg_3054_);
lean_dec(v___x_3052_);
lean_dec_ref(v_dir_3051_);
lean_dec_ref(v_self_3050_);
v_a_3233_ = lean_ctor_get(v___y_3230_, 0);
lean_inc(v_a_3233_);
v_a_3234_ = lean_ctor_get(v___y_3230_, 1);
lean_inc(v_a_3234_);
lean_dec_ref_known(v___y_3230_, 2);
v_a_3067_ = v_a_3233_;
v_a_3068_ = v_a_3234_;
goto v___jp_3066_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3050_ = stack[0].m_obj;
lean_object* v_dir_3051_ = stack[1].m_obj;
lean_object* v___x_3052_ = stack[2].m_obj;
lean_object* v_targetDecls_3053_ = stack[3].m_obj;
lean_object* v_pkg_3054_ = stack[4].m_obj;
lean_object* v_name_3055_ = stack[5].m_obj;
lean_object* v___x_3056_ = stack[6].m_obj;
lean_object* v_config_3057_ = stack[7].m_obj;
lean_object* v_config_3058_ = stack[8].m_obj;
lean_object* v___y_3059_ = stack[9].m_obj;
lean_object* v___y_3060_ = stack[10].m_obj;
lean_object* v___y_3061_ = stack[11].m_obj;
lean_object* v___y_3062_ = stack[12].m_obj;
lean_object* v___y_3063_ = stack[13].m_obj;
lean_object* v___y_3064_ = stack[14].m_obj;
lean_object* v_res_3347_;
v_res_3347_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v_self_3050_, v_dir_3051_, v___x_3052_, v_targetDecls_3053_, v_pkg_3054_, v_name_3055_, v___x_3056_, v_config_3057_, v_config_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
stack->m_obj
 = v_res_3347_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* v_self_3348_, lean_object* v_dir_3349_, lean_object* v___x_3350_, lean_object* v_targetDecls_3351_, lean_object* v_pkg_3352_, lean_object* v_name_3353_, lean_object* v___x_3354_, lean_object* v_config_3355_, lean_object* v_config_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v_self_3348_, v_dir_3349_, v___x_3350_, v_targetDecls_3351_, v_pkg_3352_, v_name_3353_, v___x_3354_, v_config_3355_, v_config_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec(v_config_3356_);
lean_dec_ref(v_targetDecls_3351_);
return v_res_3364_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object* v_self_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_pkg_3374_; lean_object* v_name_3375_; lean_object* v_config_3376_; lean_object* v_keyName_3377_; lean_object* v_dir_3378_; lean_object* v_config_3379_; lean_object* v_targetDecls_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___f_3391_; uint8_t v___x_3392_; lean_object* v___x_3393_; 
v_pkg_3374_ = lean_ctor_get(v_self_3366_, 0);
lean_inc_ref_n(v_pkg_3374_, 2);
v_name_3375_ = lean_ctor_get(v_self_3366_, 1);
lean_inc_n(v_name_3375_, 3);
v_config_3376_ = lean_ctor_get(v_self_3366_, 2);
lean_inc(v_config_3376_);
v_keyName_3377_ = lean_ctor_get(v_pkg_3374_, 2);
v_dir_3378_ = lean_ctor_get(v_pkg_3374_, 4);
lean_inc_ref(v_dir_3378_);
v_config_3379_ = lean_ctor_get(v_pkg_3374_, 6);
lean_inc_ref(v_config_3379_);
v_targetDecls_3380_ = lean_ctor_get(v_pkg_3374_, 15);
lean_inc_ref(v_targetDecls_3380_);
v___x_3381_ = l_Lake_instDataKindDynlib;
v___x_3382_ = 1;
v___x_3383_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3375_, v___x_3382_);
v___x_3384_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0));
v___x_3385_ = lean_string_append(v___x_3383_, v___x_3384_);
v___x_3386_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_3377_);
v___x_3387_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3387_, 0, v_keyName_3377_);
lean_ctor_set(v___x_3387_, 1, v_name_3375_);
v___x_3388_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3366_);
v___x_3389_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3387_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
lean_ctor_set(v___x_3389_, 2, v_self_3366_);
lean_ctor_set(v___x_3389_, 3, v___x_3386_);
v___x_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3390_, 0, v_pkg_3374_);
v___f_3391_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3391_, 0, v_self_3366_);
lean_closure_set(v___f_3391_, 1, v_dir_3378_);
lean_closure_set(v___f_3391_, 2, v___x_3390_);
lean_closure_set(v___f_3391_, 3, v_targetDecls_3380_);
lean_closure_set(v___f_3391_, 4, v_pkg_3374_);
lean_closure_set(v___f_3391_, 5, v_name_3375_);
lean_closure_set(v___f_3391_, 6, v___x_3389_);
lean_closure_set(v___f_3391_, 7, v_config_3379_);
lean_closure_set(v___f_3391_, 8, v_config_3376_);
v___x_3392_ = 0;
v___x_3393_ = l_Lake_ensureJob___redArg(v___x_3381_, v___f_3391_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3418_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_a_3395_ = lean_ctor_get(v___x_3393_, 1);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3397_ = v___x_3393_;
v_isShared_3398_ = v_isSharedCheck_3418_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3418_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v_task_3399_; lean_object* v_kind_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3416_; 
v_task_3399_ = lean_ctor_get(v_a_3394_, 0);
v_kind_3400_ = lean_ctor_get(v_a_3394_, 1);
v_isSharedCheck_3416_ = !lean_is_exclusive(v_a_3394_);
if (v_isSharedCheck_3416_ == 0)
{
lean_object* v_unused_3417_; 
v_unused_3417_ = lean_ctor_get(v_a_3394_, 2);
lean_dec(v_unused_3417_);
v___x_3402_ = v_a_3394_;
v_isShared_3403_ = v_isSharedCheck_3416_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_kind_3400_);
lean_inc(v_task_3399_);
lean_dec(v_a_3394_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3416_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v_registeredJobs_3404_; lean_object* v_job_3406_; 
v_registeredJobs_3404_ = lean_ctor_get(v_a_3371_, 4);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 2, v___x_3385_);
v_job_3406_ = v___x_3402_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_task_3399_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_kind_3400_);
lean_ctor_set(v_reuseFailAlloc_3415_, 2, v___x_3385_);
v_job_3406_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3413_; 
lean_ctor_set_uint8(v_job_3406_, sizeof(void*)*3, v___x_3392_);
v___x_3407_ = lean_st_ref_take(v_registeredJobs_3404_);
lean_inc_ref(v_job_3406_);
v___x_3408_ = l_Lake_Job_toOpaque___redArg(v_job_3406_);
v___x_3409_ = lean_array_push(v___x_3407_, v___x_3408_);
v___x_3410_ = lean_st_ref_put(v_registeredJobs_3404_, v___x_3409_);
v___x_3411_ = l_Lake_Job_renew___redArg(v_job_3406_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3411_);
v___x_3413_ = v___x_3397_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_a_3395_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3385_);
return v___x_3393_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3366_ = stack[0].m_obj;
lean_object* v_a_3367_ = stack[1].m_obj;
lean_object* v_a_3368_ = stack[2].m_obj;
lean_object* v_a_3369_ = stack[3].m_obj;
lean_object* v_a_3370_ = stack[4].m_obj;
lean_object* v_a_3371_ = stack[5].m_obj;
lean_object* v_a_3372_ = stack[6].m_obj;
lean_object* v_res_3419_;
v_res_3419_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_);
stack->m_obj
 = v_res_3419_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object* v_self_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
lean_dec_ref(v_a_3425_);
lean_dec(v_a_3424_);
lean_dec(v_a_3423_);
lean_dec(v_a_3422_);
return v_res_3428_;
}
}
lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t v_fmt_3429_, lean_object* v_a_3430_){
_start:
{
if (v_fmt_3429_ == 0)
{
lean_object* v_path_3431_; 
v_path_3431_ = lean_ctor_get(v_a_3430_, 0);
lean_inc_ref(v_path_3431_);
return v_path_3431_;
}
else
{
lean_object* v_path_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v_path_3432_ = lean_ctor_get(v_a_3430_, 0);
lean_inc_ref(v_path_3432_);
v___x_3433_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3433_, 0, v_path_3432_);
v___x_3434_ = l_Lean_Json_compress(v___x_3433_);
return v___x_3434_;
}
}
}
LEAN_EXPORT void l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_fmt_3429_ = stack[0].m_num;
lean_object* v_a_3430_ = stack[1].m_obj;
lean_object* v_res_3435_;
v_res_3435_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_3429_, v_a_3430_);
stack->m_obj
 = v_res_3435_;
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* v_fmt_3436_, lean_object* v_a_3437_){
_start:
{
uint8_t v_fmt_boxed_3438_; lean_object* v_res_3439_; 
v_fmt_boxed_3438_ = lean_unbox(v_fmt_3436_);
v_res_3439_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_boxed_3438_, v_a_3437_);
lean_dec_ref(v_a_3437_);
return v_res_3439_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3442_; uint8_t v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___f_3442_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__0));
v___x_3443_ = 1;
v___x_3444_ = l_Lake_instDataKindDynlib;
v___x_3445_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__1));
v___x_3446_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3447_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3447_, 0, v___x_3446_);
lean_ctor_set(v___x_3447_, 1, v___x_3445_);
lean_ctor_set(v___x_3447_, 2, v___x_3444_);
lean_ctor_set(v___x_3447_, 3, v___f_3442_);
lean_ctor_set_uint8(v___x_3447_, sizeof(void*)*4, v___x_3443_);
lean_ctor_set_uint8(v___x_3447_, sizeof(void*)*4 + 1, v___x_3443_);
return v___x_3447_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_obj_once(&l_Lake_LeanLib_sharedFacetConfig___closed__2, &l_Lake_LeanLib_sharedFacetConfig___closed__2_once, _init_l_Lake_LeanLib_sharedFacetConfig___closed__2);
return v___x_3448_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* v___x_3449_, lean_object* v_as_3450_, size_t v_sz_3451_, size_t v_i_3452_, lean_object* v_b_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
uint8_t v___x_3461_; 
v___x_3461_ = lean_usize_dec_lt(v_i_3452_, v_sz_3451_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; 
lean_dec_ref(v___y_3454_);
lean_dec_ref(v___x_3449_);
v___x_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3462_, 0, v_b_3453_);
lean_ctor_set(v___x_3462_, 1, v___y_3459_);
return v___x_3462_;
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3464_; 
v_a_3463_ = lean_array_uget_borrowed(v_as_3450_, v_i_3452_);
lean_inc_ref(v___y_3454_);
lean_inc_n(v_a_3463_, 2);
lean_inc_ref(v___x_3449_);
v___x_3464_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v___x_3449_, v_a_3463_, v_a_3463_, v___x_3461_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v_a_3466_; lean_object* v_snd_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; size_t v___x_3470_; size_t v___x_3471_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3465_);
v_a_3466_ = lean_ctor_get(v___x_3464_, 1);
lean_inc(v_a_3466_);
lean_dec_ref_known(v___x_3464_, 2);
v_snd_3467_ = lean_ctor_get(v_a_3465_, 1);
lean_inc(v_snd_3467_);
lean_dec(v_a_3465_);
v___x_3468_ = l_Lake_Job_toOpaque___redArg(v_snd_3467_);
v___x_3469_ = l_Lake_Job_mix___redArg(v_b_3453_, v___x_3468_);
v___x_3470_ = ((size_t)1ULL);
v___x_3471_ = lean_usize_add(v_i_3452_, v___x_3470_);
v_i_3452_ = v___x_3471_;
v_b_3453_ = v___x_3469_;
v___y_3459_ = v_a_3466_;
goto _start;
}
else
{
lean_object* v_a_3473_; lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_dec_ref(v___y_3454_);
lean_dec_ref(v_b_3453_);
lean_dec_ref(v___x_3449_);
v_a_3473_ = lean_ctor_get(v___x_3464_, 0);
v_a_3474_ = lean_ctor_get(v___x_3464_, 1);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3464_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_inc(v_a_3473_);
lean_dec(v___x_3464_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3473_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3449_ = stack[0].m_obj;
lean_object* v_as_3450_ = stack[1].m_obj;
size_t v_sz_3451_ = stack[2].m_num;
size_t v_i_3452_ = stack[3].m_num;
lean_object* v_b_3453_ = stack[4].m_obj;
lean_object* v___y_3454_ = stack[5].m_obj;
lean_object* v___y_3455_ = stack[6].m_obj;
lean_object* v___y_3456_ = stack[7].m_obj;
lean_object* v___y_3457_ = stack[8].m_obj;
lean_object* v___y_3458_ = stack[9].m_obj;
lean_object* v___y_3459_ = stack[10].m_obj;
lean_object* v_res_3482_;
v_res_3482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_3449_, v_as_3450_, v_sz_3451_, v_i_3452_, v_b_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
stack->m_obj
 = v_res_3482_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* v___x_3483_, lean_object* v_as_3484_, lean_object* v_sz_3485_, lean_object* v_i_3486_, lean_object* v_b_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
size_t v_sz_boxed_3495_; size_t v_i_boxed_3496_; lean_object* v_res_3497_; 
v_sz_boxed_3495_ = lean_unbox_usize(v_sz_3485_);
lean_dec(v_sz_3485_);
v_i_boxed_3496_ = lean_unbox_usize(v_i_3486_);
lean_dec(v_i_3486_);
v_res_3497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_3483_, v_as_3484_, v_sz_boxed_3495_, v_i_boxed_3496_, v_b_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec_ref(v_as_3484_);
return v_res_3497_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* v___x_3498_, lean_object* v_as_3499_, size_t v_sz_3500_, size_t v_i_3501_, lean_object* v_b_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
uint8_t v___x_3510_; 
v___x_3510_ = lean_usize_dec_lt(v_i_3501_, v_sz_3500_);
if (v___x_3510_ == 0)
{
lean_object* v___x_3511_; 
lean_dec_ref(v___y_3503_);
lean_dec_ref(v___x_3498_);
v___x_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3511_, 0, v_b_3502_);
lean_ctor_set(v___x_3511_, 1, v___y_3508_);
return v___x_3511_;
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3513_; 
v_a_3512_ = lean_array_uget_borrowed(v_as_3499_, v_i_3501_);
lean_inc_ref(v___y_3503_);
lean_inc(v_a_3512_);
lean_inc_ref(v___x_3498_);
v___x_3513_ = l_Lake_Package_fetchTargetJob(v___x_3498_, v_a_3512_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v_a_3515_; lean_object* v___x_3516_; size_t v___x_3517_; size_t v___x_3518_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
v_a_3515_ = lean_ctor_get(v___x_3513_, 1);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3513_, 2);
v___x_3516_ = l_Lake_Job_mix___redArg(v_b_3502_, v_a_3514_);
v___x_3517_ = ((size_t)1ULL);
v___x_3518_ = lean_usize_add(v_i_3501_, v___x_3517_);
v_i_3501_ = v___x_3518_;
v_b_3502_ = v___x_3516_;
v___y_3508_ = v_a_3515_;
goto _start;
}
else
{
lean_object* v_a_3520_; lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec_ref(v___y_3503_);
lean_dec_ref(v_b_3502_);
lean_dec_ref(v___x_3498_);
v_a_3520_ = lean_ctor_get(v___x_3513_, 0);
v_a_3521_ = lean_ctor_get(v___x_3513_, 1);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3513_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_inc(v_a_3520_);
lean_dec(v___x_3513_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3520_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3498_ = stack[0].m_obj;
lean_object* v_as_3499_ = stack[1].m_obj;
size_t v_sz_3500_ = stack[2].m_num;
size_t v_i_3501_ = stack[3].m_num;
lean_object* v_b_3502_ = stack[4].m_obj;
lean_object* v___y_3503_ = stack[5].m_obj;
lean_object* v___y_3504_ = stack[6].m_obj;
lean_object* v___y_3505_ = stack[7].m_obj;
lean_object* v___y_3506_ = stack[8].m_obj;
lean_object* v___y_3507_ = stack[9].m_obj;
lean_object* v___y_3508_ = stack[10].m_obj;
lean_object* v_res_3529_;
v_res_3529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_3498_, v_as_3499_, v_sz_3500_, v_i_3501_, v_b_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
stack->m_obj
 = v_res_3529_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* v___x_3530_, lean_object* v_as_3531_, lean_object* v_sz_3532_, lean_object* v_i_3533_, lean_object* v_b_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
size_t v_sz_boxed_3542_; size_t v_i_boxed_3543_; lean_object* v_res_3544_; 
v_sz_boxed_3542_ = lean_unbox_usize(v_sz_3532_);
lean_dec(v_sz_3532_);
v_i_boxed_3543_ = lean_unbox_usize(v_i_3533_);
lean_dec(v_i_3533_);
v_res_3544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_3530_, v_as_3531_, v_sz_boxed_3542_, v_i_boxed_3543_, v_b_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v_as_3531_);
return v_res_3544_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object* v_self_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_pkg_3555_; lean_object* v_name_3556_; lean_object* v_config_3557_; lean_object* v_baseName_3558_; lean_object* v_keyName_3559_; uint8_t v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; uint8_t v___x_3572_; uint8_t v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v_job_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v_pkg_3555_ = lean_ctor_get(v_self_3547_, 0);
lean_inc_ref_n(v_pkg_3555_, 2);
v_name_3556_ = lean_ctor_get(v_self_3547_, 1);
lean_inc(v_name_3556_);
v_config_3557_ = lean_ctor_get(v_self_3547_, 2);
lean_inc(v_config_3557_);
lean_dec_ref(v_self_3547_);
v_baseName_3558_ = lean_ctor_get(v_pkg_3555_, 1);
v_keyName_3559_ = lean_ctor_get(v_pkg_3555_, 2);
v___x_3560_ = 1;
lean_inc(v_baseName_3558_);
v___x_3561_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3558_, v___x_3560_);
v___x_3562_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0));
v___x_3563_ = lean_string_append(v___x_3561_, v___x_3562_);
v___x_3564_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3556_, v___x_3560_);
v___x_3565_ = lean_string_append(v___x_3563_, v___x_3564_);
lean_dec_ref(v___x_3564_);
v___x_3566_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1));
v___x_3567_ = lean_string_append(v___x_3565_, v___x_3566_);
v___x_3568_ = lean_box(0);
v___x_3569_ = lean_box(0);
v___x_3570_ = lean_unsigned_to_nat(0u);
v___x_3571_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildElabArts___closed__0));
v___x_3572_ = 0;
v___x_3573_ = 0;
v___x_3574_ = l_Lake_BuildTrace_nil(v___x_3567_);
v___x_3575_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3575_, 0, v___x_3571_);
lean_ctor_set(v___x_3575_, 1, v___x_3574_);
lean_ctor_set(v___x_3575_, 2, v___x_3570_);
lean_ctor_set_uint8(v___x_3575_, sizeof(void*)*3, v___x_3572_);
lean_ctor_set_uint8(v___x_3575_, sizeof(void*)*3 + 1, v___x_3573_);
lean_ctor_set_uint8(v___x_3575_, sizeof(void*)*3 + 2, v___x_3573_);
v___x_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3568_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
v___x_3577_ = lean_task_pure(v___x_3576_);
v___x_3578_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v_job_3579_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_3579_, 0, v___x_3577_);
lean_ctor_set(v_job_3579_, 1, v___x_3569_);
lean_ctor_set(v_job_3579_, 2, v___x_3578_);
lean_ctor_set_uint8(v_job_3579_, sizeof(void*)*3, v___x_3573_);
v___x_3580_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_3559_);
v___x_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3581_, 0, v_keyName_3559_);
v___x_3582_ = l_Lake_Package_keyword;
v___x_3583_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3581_);
lean_ctor_set(v___x_3583_, 1, v___x_3582_);
lean_ctor_set(v___x_3583_, 2, v_pkg_3555_);
lean_ctor_set(v___x_3583_, 3, v___x_3580_);
lean_inc_ref(v_a_3548_);
lean_inc_ref(v_a_3552_);
lean_inc(v_a_3551_);
lean_inc(v_a_3550_);
lean_inc(v_a_3549_);
v___x_3584_ = lean_apply_7(v_a_3548_, v___x_3583_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, lean_box(0));
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; lean_object* v_a_3586_; lean_object* v_needs_3587_; lean_object* v_extraDepTargets_3588_; lean_object* v___x_3589_; size_t v_sz_3590_; size_t v___x_3591_; lean_object* v___x_3592_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_a_3585_);
v_a_3586_ = lean_ctor_get(v___x_3584_, 1);
lean_inc(v_a_3586_);
lean_dec_ref_known(v___x_3584_, 2);
v_needs_3587_ = lean_ctor_get(v_config_3557_, 5);
lean_inc_ref(v_needs_3587_);
v_extraDepTargets_3588_ = lean_ctor_get(v_config_3557_, 6);
lean_inc_ref(v_extraDepTargets_3588_);
lean_dec(v_config_3557_);
v___x_3589_ = l_Lake_Job_mix___redArg(v_job_3579_, v_a_3585_);
v_sz_3590_ = lean_array_size(v_extraDepTargets_3588_);
v___x_3591_ = ((size_t)0ULL);
lean_inc_ref(v_a_3548_);
lean_inc_ref(v_pkg_3555_);
v___x_3592_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_3555_, v_extraDepTargets_3588_, v_sz_3590_, v___x_3591_, v___x_3589_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3586_);
lean_dec_ref(v_extraDepTargets_3588_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3593_; lean_object* v_a_3594_; size_t v_sz_3595_; lean_object* v___x_3596_; 
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3593_);
v_a_3594_ = lean_ctor_get(v___x_3592_, 1);
lean_inc(v_a_3594_);
lean_dec_ref_known(v___x_3592_, 2);
v_sz_3595_ = lean_array_size(v_needs_3587_);
v___x_3596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_3555_, v_needs_3587_, v_sz_3595_, v___x_3591_, v_a_3593_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3594_);
lean_dec_ref(v_needs_3587_);
return v___x_3596_;
}
else
{
lean_dec_ref(v_needs_3587_);
lean_dec_ref(v_pkg_3555_);
lean_dec_ref(v_a_3548_);
return v___x_3592_;
}
}
else
{
lean_dec_ref_known(v_job_3579_, 3);
lean_dec(v_config_3557_);
lean_dec_ref(v_pkg_3555_);
lean_dec_ref(v_a_3548_);
return v___x_3584_;
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3547_ = stack[0].m_obj;
lean_object* v_a_3548_ = stack[1].m_obj;
lean_object* v_a_3549_ = stack[2].m_obj;
lean_object* v_a_3550_ = stack[3].m_obj;
lean_object* v_a_3551_ = stack[4].m_obj;
lean_object* v_a_3552_ = stack[5].m_obj;
lean_object* v_a_3553_ = stack[6].m_obj;
lean_object* v_res_3597_;
v_res_3597_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_);
stack->m_obj
 = v_res_3597_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object* v_self_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
lean_dec_ref(v_a_3603_);
lean_dec(v_a_3602_);
lean_dec(v_a_3601_);
lean_dec(v_a_3600_);
return v_res_3606_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3608_; uint8_t v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___f_3608_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_3609_ = 1;
v___x_3610_ = l_Lake_instDataKindUnit;
v___x_3611_ = ((lean_object*)(l_Lake_LeanLib_extraDepFacetConfig___closed__0));
v___x_3612_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3613_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
lean_ctor_set(v___x_3613_, 1, v___x_3611_);
lean_ctor_set(v___x_3613_, 2, v___x_3610_);
lean_ctor_set(v___x_3613_, 3, v___f_3608_);
lean_ctor_set_uint8(v___x_3613_, sizeof(void*)*4, v___x_3609_);
lean_ctor_set_uint8(v___x_3613_, sizeof(void*)*4 + 1, v___x_3609_);
return v___x_3613_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = lean_obj_once(&l_Lake_LeanLib_extraDepFacetConfig___closed__1, &l_Lake_LeanLib_extraDepFacetConfig___closed__1_once, _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1);
return v___x_3614_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* v_self_3615_, size_t v_sz_3616_, size_t v_i_3617_, lean_object* v_bs_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
uint8_t v___x_3626_; 
v___x_3626_ = lean_usize_dec_lt(v_i_3617_, v_sz_3616_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; 
lean_dec_ref(v___y_3619_);
lean_dec_ref(v_self_3615_);
v___x_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3627_, 0, v_bs_3618_);
lean_ctor_set(v___x_3627_, 1, v___y_3624_);
return v___x_3627_;
}
else
{
lean_object* v_pkg_3628_; lean_object* v_name_3629_; lean_object* v_keyName_3630_; lean_object* v_v_3631_; lean_object* v___x_3632_; lean_object* v_bs_x27_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v_pkg_3628_ = lean_ctor_get(v_self_3615_, 0);
v_name_3629_ = lean_ctor_get(v_self_3615_, 1);
v_keyName_3630_ = lean_ctor_get(v_pkg_3628_, 2);
v_v_3631_ = lean_array_uget(v_bs_3618_, v_i_3617_);
v___x_3632_ = lean_unsigned_to_nat(0u);
v_bs_x27_3633_ = lean_array_uset(v_bs_3618_, v_i_3617_, v___x_3632_);
lean_inc(v_name_3629_);
lean_inc(v_keyName_3630_);
v___x_3634_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3634_, 0, v_keyName_3630_);
lean_ctor_set(v___x_3634_, 1, v_name_3629_);
v___x_3635_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3615_);
v___x_3636_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3634_);
lean_ctor_set(v___x_3636_, 1, v___x_3635_);
lean_ctor_set(v___x_3636_, 2, v_self_3615_);
lean_ctor_set(v___x_3636_, 3, v_v_3631_);
lean_inc_ref(v___y_3619_);
lean_inc_ref(v___y_3623_);
lean_inc(v___y_3622_);
lean_inc(v___y_3621_);
lean_inc(v___y_3620_);
v___x_3637_ = lean_apply_7(v___y_3619_, v___x_3636_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, lean_box(0));
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v_a_3639_; lean_object* v___x_3640_; size_t v___x_3641_; size_t v___x_3642_; lean_object* v___x_3643_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
v_a_3639_ = lean_ctor_get(v___x_3637_, 1);
lean_inc(v_a_3639_);
lean_dec_ref_known(v___x_3637_, 2);
v___x_3640_ = l_Lake_Job_toOpaque___redArg(v_a_3638_);
v___x_3641_ = ((size_t)1ULL);
v___x_3642_ = lean_usize_add(v_i_3617_, v___x_3641_);
v___x_3643_ = lean_array_uset(v_bs_x27_3633_, v_i_3617_, v___x_3640_);
v_i_3617_ = v___x_3642_;
v_bs_3618_ = v___x_3643_;
v___y_3624_ = v_a_3639_;
goto _start;
}
else
{
lean_object* v_a_3645_; lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_dec_ref(v_bs_x27_3633_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v_self_3615_);
v_a_3645_ = lean_ctor_get(v___x_3637_, 0);
v_a_3646_ = lean_ctor_get(v___x_3637_, 1);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3637_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_inc(v_a_3645_);
lean_dec(v___x_3637_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3645_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3615_ = stack[0].m_obj;
size_t v_sz_3616_ = stack[1].m_num;
size_t v_i_3617_ = stack[2].m_num;
lean_object* v_bs_3618_ = stack[3].m_obj;
lean_object* v___y_3619_ = stack[4].m_obj;
lean_object* v___y_3620_ = stack[5].m_obj;
lean_object* v___y_3621_ = stack[6].m_obj;
lean_object* v___y_3622_ = stack[7].m_obj;
lean_object* v___y_3623_ = stack[8].m_obj;
lean_object* v___y_3624_ = stack[9].m_obj;
lean_object* v_res_3654_;
v_res_3654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3615_, v_sz_3616_, v_i_3617_, v_bs_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
stack->m_obj
 = v_res_3654_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* v_self_3655_, lean_object* v_sz_3656_, lean_object* v_i_3657_, lean_object* v_bs_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
size_t v_sz_boxed_3666_; size_t v_i_boxed_3667_; lean_object* v_res_3668_; 
v_sz_boxed_3666_ = lean_unbox_usize(v_sz_3656_);
lean_dec(v_sz_3656_);
v_i_boxed_3667_ = lean_unbox_usize(v_i_3657_);
lean_dec(v_i_3657_);
v_res_3668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3655_, v_sz_boxed_3666_, v_i_boxed_3667_, v_bs_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec(v___y_3661_);
lean_dec(v___y_3660_);
return v_res_3668_;
}
}
lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object* v_self_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_){
_start:
{
lean_object* v_config_3678_; lean_object* v_defaultFacets_3679_; size_t v_sz_3680_; size_t v___x_3681_; lean_object* v___x_3682_; 
v_config_3678_ = lean_ctor_get(v_self_3670_, 2);
v_defaultFacets_3679_ = lean_ctor_get(v_config_3678_, 7);
lean_inc_ref(v_defaultFacets_3679_);
v_sz_3680_ = lean_array_size(v_defaultFacets_3679_);
v___x_3681_ = ((size_t)0ULL);
v___x_3682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3670_, v_sz_3680_, v___x_3681_, v_defaultFacets_3679_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3693_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_a_3684_ = lean_ctor_get(v___x_3682_, 1);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3686_ = v___x_3682_;
v_isShared_3687_ = v_isSharedCheck_3693_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3693_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3691_; 
v___x_3688_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0));
v___x_3689_ = l_Lake_Job_mixArray___redArg(v_a_3683_, v___x_3688_);
lean_dec(v_a_3683_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 0, v___x_3689_);
v___x_3691_ = v___x_3686_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_a_3684_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
v_a_3694_ = lean_ctor_get(v___x_3682_, 0);
v_a_3695_ = lean_ctor_get(v___x_3682_, 1);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3682_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_inc(v_a_3694_);
lean_dec(v___x_3682_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3694_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_3670_ = stack[0].m_obj;
lean_object* v_a_3671_ = stack[1].m_obj;
lean_object* v_a_3672_ = stack[2].m_obj;
lean_object* v_a_3673_ = stack[3].m_obj;
lean_object* v_a_3674_ = stack[4].m_obj;
lean_object* v_a_3675_ = stack[5].m_obj;
lean_object* v_a_3676_ = stack[6].m_obj;
lean_object* v_res_3703_;
v_res_3703_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_);
stack->m_obj
 = v_res_3703_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object* v_self_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_);
lean_dec_ref(v_a_3709_);
lean_dec(v_a_3708_);
lean_dec(v_a_3707_);
lean_dec(v_a_3706_);
return v_res_3712_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3714_; uint8_t v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___f_3714_ = ((lean_object*)(l_Lake_LeanLib_elabArtsFacetConfig___closed__0));
v___x_3715_ = 1;
v___x_3716_ = l_Lake_instDataKindUnit;
v___x_3717_ = ((lean_object*)(l_Lake_LeanLib_defaultFacetConfig___closed__0));
v___x_3718_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3719_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3719_, 0, v___x_3718_);
lean_ctor_set(v___x_3719_, 1, v___x_3717_);
lean_ctor_set(v___x_3719_, 2, v___x_3716_);
lean_ctor_set(v___x_3719_, 3, v___f_3714_);
lean_ctor_set_uint8(v___x_3719_, sizeof(void*)*4, v___x_3715_);
lean_ctor_set_uint8(v___x_3719_, sizeof(void*)*4 + 1, v___x_3715_);
return v___x_3719_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_obj_once(&l_Lake_LeanLib_defaultFacetConfig___closed__1, &l_Lake_LeanLib_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanLib_defaultFacetConfig___closed__1);
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_3721_, lean_object* v_v_3722_, lean_object* v_t_3723_){
_start:
{
if (lean_obj_tag(v_t_3723_) == 0)
{
lean_object* v_size_3724_; lean_object* v_k_3725_; lean_object* v_v_3726_; lean_object* v_l_3727_; lean_object* v_r_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_4008_; 
v_size_3724_ = lean_ctor_get(v_t_3723_, 0);
v_k_3725_ = lean_ctor_get(v_t_3723_, 1);
v_v_3726_ = lean_ctor_get(v_t_3723_, 2);
v_l_3727_ = lean_ctor_get(v_t_3723_, 3);
v_r_3728_ = lean_ctor_get(v_t_3723_, 4);
v_isSharedCheck_4008_ = !lean_is_exclusive(v_t_3723_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_3730_ = v_t_3723_;
v_isShared_3731_ = v_isSharedCheck_4008_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_r_3728_);
lean_inc(v_l_3727_);
lean_inc(v_v_3726_);
lean_inc(v_k_3725_);
lean_inc(v_size_3724_);
lean_dec(v_t_3723_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_4008_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
uint8_t v___x_3732_; 
v___x_3732_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3721_, v_k_3725_);
switch(v___x_3732_)
{
case 0:
{
lean_object* v_impl_3733_; lean_object* v___x_3734_; 
lean_dec(v_size_3724_);
v_impl_3733_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3721_, v_v_3722_, v_l_3727_);
v___x_3734_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3728_) == 0)
{
lean_object* v_size_3735_; lean_object* v_size_3736_; lean_object* v_k_3737_; lean_object* v_v_3738_; lean_object* v_l_3739_; lean_object* v_r_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; uint8_t v___x_3743_; 
v_size_3735_ = lean_ctor_get(v_r_3728_, 0);
v_size_3736_ = lean_ctor_get(v_impl_3733_, 0);
v_k_3737_ = lean_ctor_get(v_impl_3733_, 1);
v_v_3738_ = lean_ctor_get(v_impl_3733_, 2);
v_l_3739_ = lean_ctor_get(v_impl_3733_, 3);
v_r_3740_ = lean_ctor_get(v_impl_3733_, 4);
lean_inc(v_r_3740_);
v___x_3741_ = lean_unsigned_to_nat(3u);
v___x_3742_ = lean_nat_mul(v___x_3741_, v_size_3735_);
v___x_3743_ = lean_nat_dec_lt(v___x_3742_, v_size_3736_);
lean_dec(v___x_3742_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
lean_dec(v_r_3740_);
v___x_3744_ = lean_nat_add(v___x_3734_, v_size_3736_);
v___x_3745_ = lean_nat_add(v___x_3744_, v_size_3735_);
lean_dec(v___x_3744_);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 3, v_impl_3733_);
lean_ctor_set(v___x_3730_, 0, v___x_3745_);
v___x_3747_ = v___x_3730_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3745_);
lean_ctor_set(v_reuseFailAlloc_3748_, 1, v_k_3725_);
lean_ctor_set(v_reuseFailAlloc_3748_, 2, v_v_3726_);
lean_ctor_set(v_reuseFailAlloc_3748_, 3, v_impl_3733_);
lean_ctor_set(v_reuseFailAlloc_3748_, 4, v_r_3728_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
else
{
lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3814_; 
lean_inc(v_l_3739_);
lean_inc(v_v_3738_);
lean_inc(v_k_3737_);
lean_inc(v_size_3736_);
v_isSharedCheck_3814_ = !lean_is_exclusive(v_impl_3733_);
if (v_isSharedCheck_3814_ == 0)
{
lean_object* v_unused_3815_; lean_object* v_unused_3816_; lean_object* v_unused_3817_; lean_object* v_unused_3818_; lean_object* v_unused_3819_; 
v_unused_3815_ = lean_ctor_get(v_impl_3733_, 4);
lean_dec(v_unused_3815_);
v_unused_3816_ = lean_ctor_get(v_impl_3733_, 3);
lean_dec(v_unused_3816_);
v_unused_3817_ = lean_ctor_get(v_impl_3733_, 2);
lean_dec(v_unused_3817_);
v_unused_3818_ = lean_ctor_get(v_impl_3733_, 1);
lean_dec(v_unused_3818_);
v_unused_3819_ = lean_ctor_get(v_impl_3733_, 0);
lean_dec(v_unused_3819_);
v___x_3750_ = v_impl_3733_;
v_isShared_3751_ = v_isSharedCheck_3814_;
goto v_resetjp_3749_;
}
else
{
lean_dec(v_impl_3733_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3814_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v_size_3752_; lean_object* v_size_3753_; lean_object* v_k_3754_; lean_object* v_v_3755_; lean_object* v_l_3756_; lean_object* v_r_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; uint8_t v___x_3760_; 
v_size_3752_ = lean_ctor_get(v_l_3739_, 0);
v_size_3753_ = lean_ctor_get(v_r_3740_, 0);
v_k_3754_ = lean_ctor_get(v_r_3740_, 1);
v_v_3755_ = lean_ctor_get(v_r_3740_, 2);
v_l_3756_ = lean_ctor_get(v_r_3740_, 3);
v_r_3757_ = lean_ctor_get(v_r_3740_, 4);
v___x_3758_ = lean_unsigned_to_nat(2u);
v___x_3759_ = lean_nat_mul(v___x_3758_, v_size_3752_);
v___x_3760_ = lean_nat_dec_lt(v_size_3753_, v___x_3759_);
lean_dec(v___x_3759_);
if (v___x_3760_ == 0)
{
lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3789_; 
lean_inc(v_r_3757_);
lean_inc(v_l_3756_);
lean_inc(v_v_3755_);
lean_inc(v_k_3754_);
v_isSharedCheck_3789_ = !lean_is_exclusive(v_r_3740_);
if (v_isSharedCheck_3789_ == 0)
{
lean_object* v_unused_3790_; lean_object* v_unused_3791_; lean_object* v_unused_3792_; lean_object* v_unused_3793_; lean_object* v_unused_3794_; 
v_unused_3790_ = lean_ctor_get(v_r_3740_, 4);
lean_dec(v_unused_3790_);
v_unused_3791_ = lean_ctor_get(v_r_3740_, 3);
lean_dec(v_unused_3791_);
v_unused_3792_ = lean_ctor_get(v_r_3740_, 2);
lean_dec(v_unused_3792_);
v_unused_3793_ = lean_ctor_get(v_r_3740_, 1);
lean_dec(v_unused_3793_);
v_unused_3794_ = lean_ctor_get(v_r_3740_, 0);
lean_dec(v_unused_3794_);
v___x_3762_ = v_r_3740_;
v_isShared_3763_ = v_isSharedCheck_3789_;
goto v_resetjp_3761_;
}
else
{
lean_dec(v_r_3740_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3789_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___x_3777_; lean_object* v___y_3779_; 
v___x_3764_ = lean_nat_add(v___x_3734_, v_size_3736_);
lean_dec(v_size_3736_);
v___x_3765_ = lean_nat_add(v___x_3764_, v_size_3735_);
lean_dec(v___x_3764_);
v___x_3777_ = lean_nat_add(v___x_3734_, v_size_3752_);
if (lean_obj_tag(v_l_3756_) == 0)
{
lean_object* v_size_3787_; 
v_size_3787_ = lean_ctor_get(v_l_3756_, 0);
lean_inc(v_size_3787_);
v___y_3779_ = v_size_3787_;
goto v___jp_3778_;
}
else
{
lean_object* v___x_3788_; 
v___x_3788_ = lean_unsigned_to_nat(0u);
v___y_3779_ = v___x_3788_;
goto v___jp_3778_;
}
v___jp_3766_:
{
lean_object* v___x_3770_; lean_object* v___x_3772_; 
v___x_3770_ = lean_nat_add(v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec(v___y_3768_);
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 4, v_r_3728_);
lean_ctor_set(v___x_3762_, 3, v_r_3757_);
lean_ctor_set(v___x_3762_, 2, v_v_3726_);
lean_ctor_set(v___x_3762_, 1, v_k_3725_);
lean_ctor_set(v___x_3762_, 0, v___x_3770_);
v___x_3772_ = v___x_3762_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3770_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v_k_3725_);
lean_ctor_set(v_reuseFailAlloc_3776_, 2, v_v_3726_);
lean_ctor_set(v_reuseFailAlloc_3776_, 3, v_r_3757_);
lean_ctor_set(v_reuseFailAlloc_3776_, 4, v_r_3728_);
v___x_3772_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3774_; 
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 4, v___x_3772_);
lean_ctor_set(v___x_3750_, 3, v___y_3767_);
lean_ctor_set(v___x_3750_, 2, v_v_3755_);
lean_ctor_set(v___x_3750_, 1, v_k_3754_);
lean_ctor_set(v___x_3750_, 0, v___x_3765_);
v___x_3774_ = v___x_3750_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3765_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v_k_3754_);
lean_ctor_set(v_reuseFailAlloc_3775_, 2, v_v_3755_);
lean_ctor_set(v_reuseFailAlloc_3775_, 3, v___y_3767_);
lean_ctor_set(v_reuseFailAlloc_3775_, 4, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
v___jp_3778_:
{
lean_object* v___x_3780_; lean_object* v___x_3782_; 
v___x_3780_ = lean_nat_add(v___x_3777_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec(v___x_3777_);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 4, v_l_3756_);
lean_ctor_set(v___x_3730_, 3, v_l_3739_);
lean_ctor_set(v___x_3730_, 2, v_v_3738_);
lean_ctor_set(v___x_3730_, 1, v_k_3737_);
lean_ctor_set(v___x_3730_, 0, v___x_3780_);
v___x_3782_ = v___x_3730_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3780_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_k_3737_);
lean_ctor_set(v_reuseFailAlloc_3786_, 2, v_v_3738_);
lean_ctor_set(v_reuseFailAlloc_3786_, 3, v_l_3739_);
lean_ctor_set(v_reuseFailAlloc_3786_, 4, v_l_3756_);
v___x_3782_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
lean_object* v___x_3783_; 
v___x_3783_ = lean_nat_add(v___x_3734_, v_size_3735_);
if (lean_obj_tag(v_r_3757_) == 0)
{
lean_object* v_size_3784_; 
v_size_3784_ = lean_ctor_get(v_r_3757_, 0);
lean_inc(v_size_3784_);
v___y_3767_ = v___x_3782_;
v___y_3768_ = v___x_3783_;
v___y_3769_ = v_size_3784_;
goto v___jp_3766_;
}
else
{
lean_object* v___x_3785_; 
v___x_3785_ = lean_unsigned_to_nat(0u);
v___y_3767_ = v___x_3782_;
v___y_3768_ = v___x_3783_;
v___y_3769_ = v___x_3785_;
goto v___jp_3766_;
}
}
}
}
}
else
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3800_; 
lean_del_object(v___x_3730_);
v___x_3795_ = lean_nat_add(v___x_3734_, v_size_3736_);
lean_dec(v_size_3736_);
v___x_3796_ = lean_nat_add(v___x_3795_, v_size_3735_);
lean_dec(v___x_3795_);
v___x_3797_ = lean_nat_add(v___x_3734_, v_size_3735_);
v___x_3798_ = lean_nat_add(v___x_3797_, v_size_3753_);
lean_dec(v___x_3797_);
lean_inc_ref(v_r_3728_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 4, v_r_3728_);
lean_ctor_set(v___x_3750_, 3, v_r_3740_);
lean_ctor_set(v___x_3750_, 2, v_v_3726_);
lean_ctor_set(v___x_3750_, 1, v_k_3725_);
lean_ctor_set(v___x_3750_, 0, v___x_3798_);
v___x_3800_ = v___x_3750_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3798_);
lean_ctor_set(v_reuseFailAlloc_3813_, 1, v_k_3725_);
lean_ctor_set(v_reuseFailAlloc_3813_, 2, v_v_3726_);
lean_ctor_set(v_reuseFailAlloc_3813_, 3, v_r_3740_);
lean_ctor_set(v_reuseFailAlloc_3813_, 4, v_r_3728_);
v___x_3800_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
v_isSharedCheck_3807_ = !lean_is_exclusive(v_r_3728_);
if (v_isSharedCheck_3807_ == 0)
{
lean_object* v_unused_3808_; lean_object* v_unused_3809_; lean_object* v_unused_3810_; lean_object* v_unused_3811_; lean_object* v_unused_3812_; 
v_unused_3808_ = lean_ctor_get(v_r_3728_, 4);
lean_dec(v_unused_3808_);
v_unused_3809_ = lean_ctor_get(v_r_3728_, 3);
lean_dec(v_unused_3809_);
v_unused_3810_ = lean_ctor_get(v_r_3728_, 2);
lean_dec(v_unused_3810_);
v_unused_3811_ = lean_ctor_get(v_r_3728_, 1);
lean_dec(v_unused_3811_);
v_unused_3812_ = lean_ctor_get(v_r_3728_, 0);
lean_dec(v_unused_3812_);
v___x_3802_ = v_r_3728_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_dec(v_r_3728_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 4, v___x_3800_);
lean_ctor_set(v___x_3802_, 3, v_l_3739_);
lean_ctor_set(v___x_3802_, 2, v_v_3738_);
lean_ctor_set(v___x_3802_, 1, v_k_3737_);
lean_ctor_set(v___x_3802_, 0, v___x_3796_);
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3796_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v_k_3737_);
lean_ctor_set(v_reuseFailAlloc_3806_, 2, v_v_3738_);
lean_ctor_set(v_reuseFailAlloc_3806_, 3, v_l_3739_);
lean_ctor_set(v_reuseFailAlloc_3806_, 4, v___x_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3820_; 
v_l_3820_ = lean_ctor_get(v_impl_3733_, 3);
if (lean_obj_tag(v_l_3820_) == 0)
{
lean_object* v_r_3821_; lean_object* v_k_3822_; lean_object* v_v_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3834_; 
lean_inc_ref(v_l_3820_);
v_r_3821_ = lean_ctor_get(v_impl_3733_, 4);
v_k_3822_ = lean_ctor_get(v_impl_3733_, 1);
v_v_3823_ = lean_ctor_get(v_impl_3733_, 2);
v_isSharedCheck_3834_ = !lean_is_exclusive(v_impl_3733_);
if (v_isSharedCheck_3834_ == 0)
{
lean_object* v_unused_3835_; lean_object* v_unused_3836_; 
v_unused_3835_ = lean_ctor_get(v_impl_3733_, 3);
lean_dec(v_unused_3835_);
v_unused_3836_ = lean_ctor_get(v_impl_3733_, 0);
lean_dec(v_unused_3836_);
v___x_3825_ = v_impl_3733_;
v_isShared_3826_ = v_isSharedCheck_3834_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_r_3821_);
lean_inc(v_v_3823_);
lean_inc(v_k_3822_);
lean_dec(v_impl_3733_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3834_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3827_; lean_object* v___x_3829_; 
v___x_3827_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3821_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 3, v_r_3821_);
lean_ctor_set(v___x_3825_, 2, v_v_3726_);
lean_ctor_set(v___x_3825_, 1, v_k_3725_);
lean_ctor_set(v___x_3825_, 0, v___x_3734_);
v___x_3829_ = v___x_3825_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3734_);
lean_ctor_set(v_reuseFailAlloc_3833_, 1, v_k_3725_);
lean_ctor_set(v_reuseFailAlloc_3833_, 2, v_v_3726_);
lean_ctor_set(v_reuseFailAlloc_3833_, 3, v_r_3821_);
lean_ctor_set(v_reuseFailAlloc_3833_, 4, v_r_3821_);
v___x_3829_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
lean_object* v___x_3831_; 
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 4, v___x_3829_);
lean_ctor_set(v___x_3730_, 3, v_l_3820_);
lean_ctor_set(v___x_3730_, 2, v_v_3823_);
lean_ctor_set(v___x_3730_, 1, v_k_3822_);
lean_ctor_set(v___x_3730_, 0, v___x_3827_);
v___x_3831_ = v___x_3730_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3827_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_k_3822_);
lean_ctor_set(v_reuseFailAlloc_3832_, 2, v_v_3823_);
lean_ctor_set(v_reuseFailAlloc_3832_, 3, v_l_3820_);
lean_ctor_set(v_reuseFailAlloc_3832_, 4, v___x_3829_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
else
{
lean_object* v_r_3837_; 
v_r_3837_ = lean_ctor_get(v_impl_3733_, 4);
lean_inc(v_r_3837_);
if (lean_obj_tag(v_r_3837_) == 0)
{
lean_object* v_k_3838_; lean_object* v_v_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3862_; 
lean_inc(v_l_3820_);
v_k_3838_ = lean_ctor_get(v_impl_3733_, 1);
v_v_3839_ = lean_ctor_get(v_impl_3733_, 2);
v_isSharedCheck_3862_ = !lean_is_exclusive(v_impl_3733_);
if (v_isSharedCheck_3862_ == 0)
{
lean_object* v_unused_3863_; lean_object* v_unused_3864_; lean_object* v_unused_3865_; 
v_unused_3863_ = lean_ctor_get(v_impl_3733_, 4);
lean_dec(v_unused_3863_);
v_unused_3864_ = lean_ctor_get(v_impl_3733_, 3);
lean_dec(v_unused_3864_);
v_unused_3865_ = lean_ctor_get(v_impl_3733_, 0);
lean_dec(v_unused_3865_);
v___x_3841_ = v_impl_3733_;
v_isShared_3842_ = v_isSharedCheck_3862_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_v_3839_);
lean_inc(v_k_3838_);
lean_dec(v_impl_3733_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3862_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v_k_3843_; lean_object* v_v_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3858_; 
v_k_3843_ = lean_ctor_get(v_r_3837_, 1);
v_v_3844_ = lean_ctor_get(v_r_3837_, 2);
v_isSharedCheck_3858_ = !lean_is_exclusive(v_r_3837_);
if (v_isSharedCheck_3858_ == 0)
{
lean_object* v_unused_3859_; lean_object* v_unused_3860_; lean_object* v_unused_3861_; 
v_unused_3859_ = lean_ctor_get(v_r_3837_, 4);
lean_dec(v_unused_3859_);
v_unused_3860_ = lean_ctor_get(v_r_3837_, 3);
lean_dec(v_unused_3860_);
v_unused_3861_ = lean_ctor_get(v_r_3837_, 0);
lean_dec(v_unused_3861_);
v___x_3846_ = v_r_3837_;
v_isShared_3847_ = v_isSharedCheck_3858_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_v_3844_);
lean_inc(v_k_3843_);
lean_dec(v_r_3837_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3858_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3848_; lean_object* v___x_3850_; 
v___x_3848_ = lean_unsigned_to_nat(3u);
if (v_isShared_3847_ == 0)
{
lean_ctor_set(v___x_3846_, 4, v_l_3820_);
lean_ctor_set(v___x_3846_, 3, v_l_3820_);
lean_ctor_set(v___x_3846_, 2, v_v_3839_);
lean_ctor_set(v___x_3846_, 1, v_k_3838_);
lean_ctor_set(v___x_3846_, 0, v___x_3734_);
v___x_3850_ = v___x_3846_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3734_);
lean_ctor_set(v_reuseFailAlloc_3857_, 1, v_k_3838_);
lean_ctor_set(v_reuseFailAlloc_3857_, 2, v_v_3839_);
lean_ctor_set(v_reuseFailAlloc_3857_, 3, v_l_3820_);
lean_ctor_set(v_reuseFailAlloc_3857_, 4, v_l_3820_);
v___x_3850_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
lean_object* v___x_3852_; 
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 4, v_l_3820_);
lean_ctor_set(v___x_3841_, 2, v_v_3726_);
lean_ctor_set(v___x_3841_, 1, v_k_3725_);
lean_ctor_set(v___x_3841_, 0, v___x_3734_);
v___x_3852_ = v___x_3841_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3734_);
lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_k_3725_);
lean_ctor_set(v_reuseFailAlloc_3856_, 2, v_v_3726_);
lean_ctor_set(v_reuseFailAlloc_3856_, 3, v_l_3820_);
lean_ctor_set(v_reuseFailAlloc_3856_, 4, v_l_3820_);
v___x_3852_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
lean_object* v___x_3854_; 
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 4, v___x_3852_);
lean_ctor_set(v___x_3730_, 3, v___x_3850_);
lean_ctor_set(v___x_3730_, 2, v_v_3844_);
lean_ctor_set(v___x_3730_, 1, v_k_3843_);
lean_ctor_set(v___x_3730_, 0, v___x_3848_);
v___x_3854_ = v___x_3730_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3848_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v_k_3843_);
lean_ctor_set(v_reuseFailAlloc_3855_, 2, v_v_3844_);
lean_ctor_set(v_reuseFailAlloc_3855_, 3, v___x_3850_);
lean_ctor_set(v_reuseFailAlloc_3855_, 4, v___x_3852_);
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
}
else
{
lean_object* v___x_3866_; lean_object* v___x_3868_; 
v___x_3866_ = lean_unsigned_to_nat(2u);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 4, v_r_3837_);
lean_ctor_set(v___x_3730_, 3, v_impl_3733_);
lean_ctor_set(v___x_3730_, 0, v___x_3866_);
v___x_3868_ = v___x_3730_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v_k_3725_);
lean_ctor_set(v_reuseFailAlloc_3869_, 2, v_v_3726_);
lean_ctor_set(v_reuseFailAlloc_3869_, 3, v_impl_3733_);
lean_ctor_set(v_reuseFailAlloc_3869_, 4, v_r_3837_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3871_; 
lean_dec(v_v_3726_);
lean_dec(v_k_3725_);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 2, v_v_3722_);
lean_ctor_set(v___x_3730_, 1, v_k_3721_);
v___x_3871_ = v___x_3730_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_size_3724_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_k_3721_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v_v_3722_);
lean_ctor_set(v_reuseFailAlloc_3872_, 3, v_l_3727_);
lean_ctor_set(v_reuseFailAlloc_3872_, 4, v_r_3728_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
default: 
{
lean_object* v_impl_3873_; lean_object* v___x_3874_; 
lean_dec(v_size_3724_);
v_impl_3873_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3721_, v_v_3722_, v_r_3728_);
v___x_3874_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3727_) == 0)
{
lean_object* v_size_3875_; lean_object* v_size_3876_; lean_object* v_k_3877_; lean_object* v_v_3878_; lean_object* v_l_3879_; lean_object* v_r_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; uint8_t v___x_3883_; 
v_size_3875_ = lean_ctor_get(v_l_3727_, 0);
v_size_3876_ = lean_ctor_get(v_impl_3873_, 0);
v_k_3877_ = lean_ctor_get(v_impl_3873_, 1);
v_v_3878_ = lean_ctor_get(v_impl_3873_, 2);
v_l_3879_ = lean_ctor_get(v_impl_3873_, 3);
lean_inc(v_l_3879_);
v_r_3880_ = lean_ctor_get(v_impl_3873_, 4);
v___x_3881_ = lean_unsigned_to_nat(3u);
v___x_3882_ = lean_nat_mul(v___x_3881_, v_size_3875_);
v___x_3883_ = lean_nat_dec_lt(v___x_3882_, v_size_3876_);
lean_dec(v___x_3882_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3887_; 
lean_dec(v_l_3879_);
v___x_3884_ = lean_nat_add(v___x_3874_, v_size_3875_);
v___x_3885_ = lean_nat_add(v___x_3884_, v_size_3876_);
lean_dec(v___x_3884_);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 4, v_impl_3873_);
lean_ctor_set(v___x_3730_, 0, v___x_3885_);
v___x_3887_ = v___x_3730_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_k_3725_);
lean_ctor_set(v_reuseFailAlloc_3888_, 2, v_v_3726_);
lean_ctor_set(v_reuseFailAlloc_3888_, 3, v_l_3727_);
lean_ctor_set(v_reuseFailAlloc_3888_, 4, v_impl_3873_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
else
{
lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3952_; 
lean_inc(v_r_3880_);
lean_inc(v_v_3878_);
lean_inc(v_k_3877_);
lean_inc(v_size_3876_);
v_isSharedCheck_3952_ = !lean_is_exclusive(v_impl_3873_);
if (v_isSharedCheck_3952_ == 0)
{
lean_object* v_unused_3953_; lean_object* v_unused_3954_; lean_object* v_unused_3955_; lean_object* v_unused_3956_; lean_object* v_unused_3957_; 
v_unused_3953_ = lean_ctor_get(v_impl_3873_, 4);
lean_dec(v_unused_3953_);
v_unused_3954_ = lean_ctor_get(v_impl_3873_, 3);
lean_dec(v_unused_3954_);
v_unused_3955_ = lean_ctor_get(v_impl_3873_, 2);
lean_dec(v_unused_3955_);
v_unused_3956_ = lean_ctor_get(v_impl_3873_, 1);
lean_dec(v_unused_3956_);
v_unused_3957_ = lean_ctor_get(v_impl_3873_, 0);
lean_dec(v_unused_3957_);
v___x_3890_ = v_impl_3873_;
v_isShared_3891_ = v_isSharedCheck_3952_;
goto v_resetjp_3889_;
}
else
{
lean_dec(v_impl_3873_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3952_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v_size_3892_; lean_object* v_k_3893_; lean_object* v_v_3894_; lean_object* v_l_3895_; lean_object* v_r_3896_; lean_object* v_size_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; 
v_size_3892_ = lean_ctor_get(v_l_3879_, 0);
v_k_3893_ = lean_ctor_get(v_l_3879_, 1);
v_v_3894_ = lean_ctor_get(v_l_3879_, 2);
v_l_3895_ = lean_ctor_get(v_l_3879_, 3);
v_r_3896_ = lean_ctor_get(v_l_3879_, 4);
v_size_3897_ = lean_ctor_get(v_r_3880_, 0);
v___x_3898_ = lean_unsigned_to_nat(2u);
v___x_3899_ = lean_nat_mul(v___x_3898_, v_size_3897_);
v___x_3900_ = lean_nat_dec_lt(v_size_3892_, v___x_3899_);
lean_dec(v___x_3899_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3928_; 
lean_inc(v_r_3896_);
lean_inc(v_l_3895_);
lean_inc(v_v_3894_);
lean_inc(v_k_3893_);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_l_3879_);
if (v_isSharedCheck_3928_ == 0)
{
lean_object* v_unused_3929_; lean_object* v_unused_3930_; lean_object* v_unused_3931_; lean_object* v_unused_3932_; lean_object* v_unused_3933_; 
v_unused_3929_ = lean_ctor_get(v_l_3879_, 4);
lean_dec(v_unused_3929_);
v_unused_3930_ = lean_ctor_get(v_l_3879_, 3);
lean_dec(v_unused_3930_);
v_unused_3931_ = lean_ctor_get(v_l_3879_, 2);
lean_dec(v_unused_3931_);
v_unused_3932_ = lean_ctor_get(v_l_3879_, 1);
lean_dec(v_unused_3932_);
v_unused_3933_ = lean_ctor_get(v_l_3879_, 0);
lean_dec(v_unused_3933_);
v___x_3902_ = v_l_3879_;
v_isShared_3903_ = v_isSharedCheck_3928_;
goto v_resetjp_3901_;
}
else
{
lean_dec(v_l_3879_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3928_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3918_; 
v___x_3904_ = lean_nat_add(v___x_3874_, v_size_3875_);
v___x_3905_ = lean_nat_add(v___x_3904_, v_size_3876_);
lean_dec(v_size_3876_);
if (lean_obj_tag(v_l_3895_) == 0)
{
lean_object* v_size_3926_; 
v_size_3926_ = lean_ctor_get(v_l_3895_, 0);
lean_inc(v_size_3926_);
v___y_3918_ = v_size_3926_;
goto v___jp_3917_;
}
else
{
lean_object* v___x_3927_; 
v___x_3927_ = lean_unsigned_to_nat(0u);
v___y_3918_ = v___x_3927_;
goto v___jp_3917_;
}
v___jp_3906_:
{
lean_object* v___x_3910_; lean_object* v___x_3912_; 
v___x_3910_ = lean_nat_add(v___y_3907_, v___y_3909_);
lean_dec(v___y_3909_);
lean_dec(v___y_3907_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 4, v_r_3880_);
lean_ctor_set(v___x_3902_, 3, v_r_3896_);
lean_ctor_set(v___x_3902_, 2, v_v_3878_);
lean_ctor_set(v___x_3902_, 1, v_k_3877_);
lean_ctor_set(v___x_3902_, 0, v___x_3910_);
v___x_3912_ = v___x_3902_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3910_);
lean_ctor_set(v_reuseFailAlloc_3916_, 1, v_k_3877_);
lean_ctor_set(v_reuseFailAlloc_3916_, 2, v_v_3878_);
lean_ctor_set(v_reuseFailAlloc_3916_, 3, v_r_3896_);
lean_ctor_set(v_reuseFailAlloc_3916_, 4, v_r_3880_);
v___x_3912_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
lean_object* v___x_3914_; 
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 4, v___x_3912_);
lean_ctor_set(v___x_3890_, 3, v___y_3908_);
lean_ctor_set(v___x_3890_, 2, v_v_3894_);
lean_ctor_set(v___x_3890_, 1, v_k_3893_);
lean_ctor_set(v___x_3890_, 0, v___x_3905_);
v___x_3914_ = v___x_3890_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_k_3893_);
lean_ctor_set(v_reuseFailAlloc_3915_, 2, v_v_3894_);
lean_ctor_set(v_reuseFailAlloc_3915_, 3, v___y_3908_);
lean_ctor_set(v_reuseFailAlloc_3915_, 4, v___x_3912_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
v___jp_3917_:
{
lean_object* v___x_3919_; lean_object* v___x_3921_; 
v___x_3919_ = lean_nat_add(v___x_3904_, v___y_3918_);
lean_dec(v___y_3918_);
lean_dec(v___x_3904_);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 4, v_l_3895_);
lean_ctor_set(v___x_3730_, 0, v___x_3919_);
v___x_3921_ = v___x_3730_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3919_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v_k_3725_);
lean_ctor_set(v_reuseFailAlloc_3925_, 2, v_v_3726_);
lean_ctor_set(v_reuseFailAlloc_3925_, 3, v_l_3727_);
lean_ctor_set(v_reuseFailAlloc_3925_, 4, v_l_3895_);
v___x_3921_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3922_; 
v___x_3922_ = lean_nat_add(v___x_3874_, v_size_3897_);
if (lean_obj_tag(v_r_3896_) == 0)
{
lean_object* v_size_3923_; 
v_size_3923_ = lean_ctor_get(v_r_3896_, 0);
lean_inc(v_size_3923_);
v___y_3907_ = v___x_3922_;
v___y_3908_ = v___x_3921_;
v___y_3909_ = v_size_3923_;
goto v___jp_3906_;
}
else
{
lean_object* v___x_3924_; 
v___x_3924_ = lean_unsigned_to_nat(0u);
v___y_3907_ = v___x_3922_;
v___y_3908_ = v___x_3921_;
v___y_3909_ = v___x_3924_;
goto v___jp_3906_;
}
}
}
}
}
else
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3938_; 
lean_del_object(v___x_3730_);
v___x_3934_ = lean_nat_add(v___x_3874_, v_size_3875_);
v___x_3935_ = lean_nat_add(v___x_3934_, v_size_3876_);
lean_dec(v_size_3876_);
v___x_3936_ = lean_nat_add(v___x_3934_, v_size_3892_);
lean_dec(v___x_3934_);
lean_inc_ref(v_l_3727_);
if (v_isShared_3891_ == 0)
{
lean_ctor_set(v___x_3890_, 4, v_l_3879_);
lean_ctor_set(v___x_3890_, 3, v_l_3727_);
lean_ctor_set(v___x_3890_, 2, v_v_3726_);
lean_ctor_set(v___x_3890_, 1, v_k_3725_);
lean_ctor_set(v___x_3890_, 0, v___x_3936_);
v___x_3938_ = v___x_3890_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3936_);
lean_ctor_set(v_reuseFailAlloc_3951_, 1, v_k_3725_);
lean_ctor_set(v_reuseFailAlloc_3951_, 2, v_v_3726_);
lean_ctor_set(v_reuseFailAlloc_3951_, 3, v_l_3727_);
lean_ctor_set(v_reuseFailAlloc_3951_, 4, v_l_3879_);
v___x_3938_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
v_isSharedCheck_3945_ = !lean_is_exclusive(v_l_3727_);
if (v_isSharedCheck_3945_ == 0)
{
lean_object* v_unused_3946_; lean_object* v_unused_3947_; lean_object* v_unused_3948_; lean_object* v_unused_3949_; lean_object* v_unused_3950_; 
v_unused_3946_ = lean_ctor_get(v_l_3727_, 4);
lean_dec(v_unused_3946_);
v_unused_3947_ = lean_ctor_get(v_l_3727_, 3);
lean_dec(v_unused_3947_);
v_unused_3948_ = lean_ctor_get(v_l_3727_, 2);
lean_dec(v_unused_3948_);
v_unused_3949_ = lean_ctor_get(v_l_3727_, 1);
lean_dec(v_unused_3949_);
v_unused_3950_ = lean_ctor_get(v_l_3727_, 0);
lean_dec(v_unused_3950_);
v___x_3940_ = v_l_3727_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_dec(v_l_3727_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 4, v_r_3880_);
lean_ctor_set(v___x_3940_, 3, v___x_3938_);
lean_ctor_set(v___x_3940_, 2, v_v_3878_);
lean_ctor_set(v___x_3940_, 1, v_k_3877_);
lean_ctor_set(v___x_3940_, 0, v___x_3935_);
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3935_);
lean_ctor_set(v_reuseFailAlloc_3944_, 1, v_k_3877_);
lean_ctor_set(v_reuseFailAlloc_3944_, 2, v_v_3878_);
lean_ctor_set(v_reuseFailAlloc_3944_, 3, v___x_3938_);
lean_ctor_set(v_reuseFailAlloc_3944_, 4, v_r_3880_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3958_; 
v_l_3958_ = lean_ctor_get(v_impl_3873_, 3);
lean_inc(v_l_3958_);
if (lean_obj_tag(v_l_3958_) == 0)
{
lean_object* v_r_3959_; lean_object* v_k_3960_; lean_object* v_v_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3984_; 
v_r_3959_ = lean_ctor_get(v_impl_3873_, 4);
v_k_3960_ = lean_ctor_get(v_impl_3873_, 1);
v_v_3961_ = lean_ctor_get(v_impl_3873_, 2);
v_isSharedCheck_3984_ = !lean_is_exclusive(v_impl_3873_);
if (v_isSharedCheck_3984_ == 0)
{
lean_object* v_unused_3985_; lean_object* v_unused_3986_; 
v_unused_3985_ = lean_ctor_get(v_impl_3873_, 3);
lean_dec(v_unused_3985_);
v_unused_3986_ = lean_ctor_get(v_impl_3873_, 0);
lean_dec(v_unused_3986_);
v___x_3963_ = v_impl_3873_;
v_isShared_3964_ = v_isSharedCheck_3984_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_r_3959_);
lean_inc(v_v_3961_);
lean_inc(v_k_3960_);
lean_dec(v_impl_3873_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3984_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v_k_3965_; lean_object* v_v_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3980_; 
v_k_3965_ = lean_ctor_get(v_l_3958_, 1);
v_v_3966_ = lean_ctor_get(v_l_3958_, 2);
v_isSharedCheck_3980_ = !lean_is_exclusive(v_l_3958_);
if (v_isSharedCheck_3980_ == 0)
{
lean_object* v_unused_3981_; lean_object* v_unused_3982_; lean_object* v_unused_3983_; 
v_unused_3981_ = lean_ctor_get(v_l_3958_, 4);
lean_dec(v_unused_3981_);
v_unused_3982_ = lean_ctor_get(v_l_3958_, 3);
lean_dec(v_unused_3982_);
v_unused_3983_ = lean_ctor_get(v_l_3958_, 0);
lean_dec(v_unused_3983_);
v___x_3968_ = v_l_3958_;
v_isShared_3969_ = v_isSharedCheck_3980_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_v_3966_);
lean_inc(v_k_3965_);
lean_dec(v_l_3958_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3980_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3970_; lean_object* v___x_3972_; 
v___x_3970_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3959_, 2);
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 4, v_r_3959_);
lean_ctor_set(v___x_3968_, 3, v_r_3959_);
lean_ctor_set(v___x_3968_, 2, v_v_3726_);
lean_ctor_set(v___x_3968_, 1, v_k_3725_);
lean_ctor_set(v___x_3968_, 0, v___x_3874_);
v___x_3972_ = v___x_3968_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3874_);
lean_ctor_set(v_reuseFailAlloc_3979_, 1, v_k_3725_);
lean_ctor_set(v_reuseFailAlloc_3979_, 2, v_v_3726_);
lean_ctor_set(v_reuseFailAlloc_3979_, 3, v_r_3959_);
lean_ctor_set(v_reuseFailAlloc_3979_, 4, v_r_3959_);
v___x_3972_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
lean_object* v___x_3974_; 
lean_inc(v_r_3959_);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 3, v_r_3959_);
lean_ctor_set(v___x_3963_, 0, v___x_3874_);
v___x_3974_ = v___x_3963_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3874_);
lean_ctor_set(v_reuseFailAlloc_3978_, 1, v_k_3960_);
lean_ctor_set(v_reuseFailAlloc_3978_, 2, v_v_3961_);
lean_ctor_set(v_reuseFailAlloc_3978_, 3, v_r_3959_);
lean_ctor_set(v_reuseFailAlloc_3978_, 4, v_r_3959_);
v___x_3974_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
lean_object* v___x_3976_; 
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 4, v___x_3974_);
lean_ctor_set(v___x_3730_, 3, v___x_3972_);
lean_ctor_set(v___x_3730_, 2, v_v_3966_);
lean_ctor_set(v___x_3730_, 1, v_k_3965_);
lean_ctor_set(v___x_3730_, 0, v___x_3970_);
v___x_3976_ = v___x_3730_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3970_);
lean_ctor_set(v_reuseFailAlloc_3977_, 1, v_k_3965_);
lean_ctor_set(v_reuseFailAlloc_3977_, 2, v_v_3966_);
lean_ctor_set(v_reuseFailAlloc_3977_, 3, v___x_3972_);
lean_ctor_set(v_reuseFailAlloc_3977_, 4, v___x_3974_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
}
}
else
{
lean_object* v_r_3987_; 
v_r_3987_ = lean_ctor_get(v_impl_3873_, 4);
lean_inc(v_r_3987_);
if (lean_obj_tag(v_r_3987_) == 0)
{
lean_object* v_k_3988_; lean_object* v_v_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_4000_; 
v_k_3988_ = lean_ctor_get(v_impl_3873_, 1);
v_v_3989_ = lean_ctor_get(v_impl_3873_, 2);
v_isSharedCheck_4000_ = !lean_is_exclusive(v_impl_3873_);
if (v_isSharedCheck_4000_ == 0)
{
lean_object* v_unused_4001_; lean_object* v_unused_4002_; lean_object* v_unused_4003_; 
v_unused_4001_ = lean_ctor_get(v_impl_3873_, 4);
lean_dec(v_unused_4001_);
v_unused_4002_ = lean_ctor_get(v_impl_3873_, 3);
lean_dec(v_unused_4002_);
v_unused_4003_ = lean_ctor_get(v_impl_3873_, 0);
lean_dec(v_unused_4003_);
v___x_3991_ = v_impl_3873_;
v_isShared_3992_ = v_isSharedCheck_4000_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_v_3989_);
lean_inc(v_k_3988_);
lean_dec(v_impl_3873_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_4000_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3993_; lean_object* v___x_3995_; 
v___x_3993_ = lean_unsigned_to_nat(3u);
if (v_isShared_3992_ == 0)
{
lean_ctor_set(v___x_3991_, 4, v_l_3958_);
lean_ctor_set(v___x_3991_, 2, v_v_3726_);
lean_ctor_set(v___x_3991_, 1, v_k_3725_);
lean_ctor_set(v___x_3991_, 0, v___x_3874_);
v___x_3995_ = v___x_3991_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3874_);
lean_ctor_set(v_reuseFailAlloc_3999_, 1, v_k_3725_);
lean_ctor_set(v_reuseFailAlloc_3999_, 2, v_v_3726_);
lean_ctor_set(v_reuseFailAlloc_3999_, 3, v_l_3958_);
lean_ctor_set(v_reuseFailAlloc_3999_, 4, v_l_3958_);
v___x_3995_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
lean_object* v___x_3997_; 
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 4, v_r_3987_);
lean_ctor_set(v___x_3730_, 3, v___x_3995_);
lean_ctor_set(v___x_3730_, 2, v_v_3989_);
lean_ctor_set(v___x_3730_, 1, v_k_3988_);
lean_ctor_set(v___x_3730_, 0, v___x_3993_);
v___x_3997_ = v___x_3730_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3993_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v_k_3988_);
lean_ctor_set(v_reuseFailAlloc_3998_, 2, v_v_3989_);
lean_ctor_set(v_reuseFailAlloc_3998_, 3, v___x_3995_);
lean_ctor_set(v_reuseFailAlloc_3998_, 4, v_r_3987_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
else
{
lean_object* v___x_4004_; lean_object* v___x_4006_; 
v___x_4004_ = lean_unsigned_to_nat(2u);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 4, v_impl_3873_);
lean_ctor_set(v___x_3730_, 3, v_r_3987_);
lean_ctor_set(v___x_3730_, 0, v___x_4004_);
v___x_4006_ = v___x_3730_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_4004_);
lean_ctor_set(v_reuseFailAlloc_4007_, 1, v_k_3725_);
lean_ctor_set(v_reuseFailAlloc_4007_, 2, v_v_3726_);
lean_ctor_set(v_reuseFailAlloc_4007_, 3, v_r_3987_);
lean_ctor_set(v_reuseFailAlloc_4007_, 4, v_impl_3873_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
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
lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4009_ = lean_unsigned_to_nat(1u);
v___x_4010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
lean_ctor_set(v___x_4010_, 1, v_k_3721_);
lean_ctor_set(v___x_4010_, 2, v_v_3722_);
lean_ctor_set(v___x_4010_, 3, v_t_3723_);
lean_ctor_set(v___x_4010_, 4, v_t_3723_);
return v___x_4010_;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4011_ = lean_box(1);
v___x_4012_ = l_Lake_LeanLib_defaultFacetConfig;
v___x_4013_ = l_Lake_LeanLib_defaultFacet;
v___x_4014_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4013_, v___x_4012_, v___x_4011_);
return v___x_4014_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4015_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__0, &l_Lake_LeanLib_initFacetConfigs___closed__0_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__0);
v___x_4016_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig));
v___x_4017_ = l_Lake_LeanLib_modulesFacet;
v___x_4018_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4017_, v___x_4016_, v___x_4015_);
return v___x_4018_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4019_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__1, &l_Lake_LeanLib_initFacetConfigs___closed__1_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__1);
v___x_4020_ = l_Lake_LeanLib_elabArtsFacetConfig;
v___x_4021_ = l_Lake_LeanLib_elabArtsFacet;
v___x_4022_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4021_, v___x_4020_, v___x_4019_);
return v___x_4022_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4023_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__2, &l_Lake_LeanLib_initFacetConfigs___closed__2_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__2);
v___x_4024_ = l_Lake_LeanLib_irArtsFacetConfig;
v___x_4025_ = l_Lake_LeanLib_irArtsFacet;
v___x_4026_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4025_, v___x_4024_, v___x_4023_);
return v___x_4026_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4027_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__3, &l_Lake_LeanLib_initFacetConfigs___closed__3_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__3);
v___x_4028_ = l_Lake_LeanLib_leanArtsFacetConfig;
v___x_4029_ = l_Lake_LeanLib_leanArtsFacet;
v___x_4030_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4029_, v___x_4028_, v___x_4027_);
return v___x_4030_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4031_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__4, &l_Lake_LeanLib_initFacetConfigs___closed__4_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__4);
v___x_4032_ = l_Lake_LeanLib_staticFacetConfig;
v___x_4033_ = l_Lake_LeanLib_staticFacet;
v___x_4034_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4033_, v___x_4032_, v___x_4031_);
return v___x_4034_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4035_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__5, &l_Lake_LeanLib_initFacetConfigs___closed__5_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__5);
v___x_4036_ = l_Lake_LeanLib_staticExportFacetConfig;
v___x_4037_ = l_Lake_LeanLib_staticExportFacet;
v___x_4038_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4037_, v___x_4036_, v___x_4035_);
return v___x_4038_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4039_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__6, &l_Lake_LeanLib_initFacetConfigs___closed__6_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__6);
v___x_4040_ = l_Lake_LeanLib_sharedFacetConfig;
v___x_4041_ = l_Lake_LeanLib_sharedFacet;
v___x_4042_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4041_, v___x_4040_, v___x_4039_);
return v___x_4042_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4043_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__7, &l_Lake_LeanLib_initFacetConfigs___closed__7_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__7);
v___x_4044_ = l_Lake_LeanLib_extraDepFacetConfig;
v___x_4045_ = l_Lake_LeanLib_extraDepFacet;
v___x_4046_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_4045_, v___x_4044_, v___x_4043_);
return v___x_4046_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__8, &l_Lake_LeanLib_initFacetConfigs___closed__8_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__8);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_4048_, lean_object* v_k_4049_, lean_object* v_v_4050_, lean_object* v_t_4051_, lean_object* v_hl_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_4049_, v_v_4050_, v_t_4051_);
return v___x_4053_;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs(void){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Lake_LeanLib_initFacetConfigs;
return v___x_4054_;
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
