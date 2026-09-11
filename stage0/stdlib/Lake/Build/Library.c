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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(lean_object* v_self_140_, lean_object* v_root_141_, lean_object* v_col_142_, uint8_t v_viaImport_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_col_152_; lean_object* v___y_153_; lean_object* v_mods_155_; lean_object* v_modSet_156_; uint8_t v_hasErrors_157_; uint8_t v___x_158_; 
v_mods_155_ = lean_ctor_get(v_col_142_, 0);
v_modSet_156_ = lean_ctor_get(v_col_142_, 1);
v_hasErrors_157_ = lean_ctor_get_uint8(v_col_142_, sizeof(void*)*2);
v___x_158_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_modSet_156_, v_root_141_);
if (v___x_158_ == 0)
{
lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_223_; 
lean_inc_ref(v_modSet_156_);
lean_inc_ref(v_mods_155_);
v_isSharedCheck_223_ = !lean_is_exclusive(v_col_142_);
if (v_isSharedCheck_223_ == 0)
{
lean_object* v_unused_224_; lean_object* v_unused_225_; 
v_unused_224_ = lean_ctor_get(v_col_142_, 1);
lean_dec(v_unused_224_);
v_unused_225_ = lean_ctor_get(v_col_142_, 0);
lean_dec(v_unused_225_);
v___x_160_ = v_col_142_;
v_isShared_161_ = v_isSharedCheck_223_;
goto v_resetjp_159_;
}
else
{
lean_dec(v_col_142_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_223_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_lib_162_; lean_object* v_pkg_163_; lean_object* v_name_164_; lean_object* v_keyName_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_lib_162_ = lean_ctor_get(v_root_141_, 0);
v_pkg_163_ = lean_ctor_get(v_lib_162_, 0);
v_name_164_ = lean_ctor_get(v_root_141_, 1);
v_keyName_165_ = lean_ctor_get(v_pkg_163_, 2);
v___x_166_ = lean_box(0);
lean_inc_ref_n(v_root_141_, 2);
v___x_167_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_modSet_156_, v_root_141_, v___x_166_);
v___x_168_ = l_Lake_Module_importsFacet;
lean_inc(v_name_164_);
lean_inc(v_keyName_165_);
v___x_169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_169_, 0, v_keyName_165_);
lean_ctor_set(v___x_169_, 1, v_name_164_);
v___x_170_ = l_Lake_Module_keyword;
v___x_171_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
lean_ctor_set(v___x_171_, 2, v_root_141_);
lean_ctor_set(v___x_171_, 3, v___x_168_);
lean_inc_ref(v_a_144_);
lean_inc_ref(v_a_148_);
lean_inc(v_a_147_);
lean_inc(v_a_146_);
lean_inc(v_a_145_);
v___x_172_ = lean_apply_7(v_a_144_, v___x_171_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, lean_box(0));
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_213_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_a_174_ = lean_ctor_get(v___x_172_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_213_ == 0)
{
v___x_176_ = v___x_172_;
v_isShared_177_ = v_isSharedCheck_213_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_213_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_task_178_; lean_object* v___x_179_; lean_object* v___y_181_; 
v_task_178_ = lean_ctor_get(v_a_173_, 0);
lean_inc_ref(v_task_178_);
lean_dec(v_a_173_);
v___x_179_ = lean_io_wait(v_task_178_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_185_; lean_object* v_col_187_; 
lean_del_object(v___x_176_);
v_a_185_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_179_, 2);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_167_);
v_col_187_ = v___x_160_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_mods_155_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___x_167_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*2, v_hasErrors_157_);
v_col_187_ = v_reuseFailAlloc_204_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
size_t v_sz_188_; size_t v___x_189_; lean_object* v___x_190_; 
v_sz_188_ = lean_array_size(v_a_185_);
v___x_189_ = ((size_t)0ULL);
v___x_190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_140_, v_a_185_, v_sz_188_, v___x_189_, v_col_187_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_174_);
lean_dec(v_a_185_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v_a_192_; lean_object* v_mods_193_; lean_object* v_modSet_194_; uint8_t v_hasErrors_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_203_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
v_a_192_ = lean_ctor_get(v___x_190_, 1);
lean_inc(v_a_192_);
lean_dec_ref_known(v___x_190_, 2);
v_mods_193_ = lean_ctor_get(v_a_191_, 0);
v_modSet_194_ = lean_ctor_get(v_a_191_, 1);
v_hasErrors_195_ = lean_ctor_get_uint8(v_a_191_, sizeof(void*)*2);
v_isSharedCheck_203_ = !lean_is_exclusive(v_a_191_);
if (v_isSharedCheck_203_ == 0)
{
v___x_197_ = v_a_191_;
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_modSet_194_);
lean_inc(v_mods_193_);
lean_dec(v_a_191_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = lean_array_push(v_mods_193_, v_root_141_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_modSet_194_);
lean_ctor_set_uint8(v_reuseFailAlloc_202_, sizeof(void*)*2, v_hasErrors_195_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
v_col_152_ = v___x_201_;
v___y_153_ = v_a_192_;
goto v___jp_151_;
}
}
}
else
{
lean_dec_ref(v_root_141_);
return v___x_190_;
}
}
}
else
{
uint8_t v___x_205_; 
lean_dec_ref_known(v___x_179_, 2);
lean_dec_ref(v_a_144_);
v___x_205_ = 1;
if (v_viaImport_143_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_206_ = lean_array_push(v_mods_155_, v_root_141_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_167_);
lean_ctor_set(v___x_160_, 0, v___x_206_);
v___x_208_ = v___x_160_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___x_167_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_ctor_set_uint8(v___x_208_, sizeof(void*)*2, v___x_205_);
v___y_181_ = v___x_208_;
goto v___jp_180_;
}
}
else
{
lean_object* v___x_211_; 
lean_dec_ref(v_root_141_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_167_);
v___x_211_ = v___x_160_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_mods_155_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_167_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_ctor_set_uint8(v___x_211_, sizeof(void*)*2, v___x_205_);
v___y_181_ = v___x_211_;
goto v___jp_180_;
}
}
}
v___jp_180_:
{
lean_object* v___x_183_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___y_181_);
v___x_183_ = v___x_176_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___y_181_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_a_174_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
else
{
lean_object* v_a_214_; lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec_ref(v___x_167_);
lean_del_object(v___x_160_);
lean_dec_ref(v_mods_155_);
lean_dec_ref(v_a_144_);
lean_dec_ref(v_root_141_);
v_a_214_ = lean_ctor_get(v___x_172_, 0);
v_a_215_ = lean_ctor_get(v___x_172_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_172_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_inc(v_a_214_);
lean_dec(v___x_172_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_214_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_144_);
lean_dec_ref(v_root_141_);
v_col_152_ = v_col_142_;
v___y_153_ = v_a_149_;
goto v___jp_151_;
}
v___jp_151_:
{
lean_object* v___x_154_; 
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v_col_152_);
lean_ctor_set(v___x_154_, 1, v___y_153_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(lean_object* v_self_226_, lean_object* v_as_227_, size_t v_sz_228_, size_t v_i_229_, lean_object* v_b_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_a_239_; lean_object* v_a_240_; uint8_t v___x_244_; 
v___x_244_ = lean_usize_dec_lt(v_i_229_, v_sz_228_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; 
lean_dec_ref(v___y_231_);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v_b_230_);
lean_ctor_set(v___x_245_, 1, v___y_236_);
return v___x_245_;
}
else
{
lean_object* v_a_246_; lean_object* v_lib_247_; lean_object* v_name_248_; lean_object* v_name_249_; uint8_t v___x_250_; 
v_a_246_ = lean_array_uget_borrowed(v_as_227_, v_i_229_);
v_lib_247_ = lean_ctor_get(v_a_246_, 0);
v_name_248_ = lean_ctor_get(v_lib_247_, 1);
v_name_249_ = lean_ctor_get(v_self_226_, 1);
v___x_250_ = lean_name_eq(v_name_248_, v_name_249_);
if (v___x_250_ == 0)
{
v_a_239_ = v_b_230_;
v_a_240_ = v___y_236_;
goto v___jp_238_;
}
else
{
lean_object* v___x_251_; 
lean_inc_ref(v___y_231_);
lean_inc(v_a_246_);
v___x_251_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_226_, v_a_246_, v_b_230_, v___x_250_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v_a_253_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_a_252_);
v_a_253_ = lean_ctor_get(v___x_251_, 1);
lean_inc(v_a_253_);
lean_dec_ref_known(v___x_251_, 2);
v_a_239_ = v_a_252_;
v_a_240_ = v_a_253_;
goto v___jp_238_;
}
else
{
lean_dec_ref(v___y_231_);
return v___x_251_;
}
}
}
v___jp_238_:
{
size_t v___x_241_; size_t v___x_242_; 
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_add(v_i_229_, v___x_241_);
v_i_229_ = v___x_242_;
v_b_230_ = v_a_239_;
v___y_236_ = v_a_240_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(lean_object* v_self_254_, lean_object* v_as_255_, lean_object* v_sz_256_, lean_object* v_i_257_, lean_object* v_b_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
size_t v_sz_boxed_266_; size_t v_i_boxed_267_; lean_object* v_res_268_; 
v_sz_boxed_266_ = lean_unbox_usize(v_sz_256_);
lean_dec(v_sz_256_);
v_i_boxed_267_ = lean_unbox_usize(v_i_257_);
lean_dec(v_i_257_);
v_res_268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_254_, v_as_255_, v_sz_boxed_266_, v_i_boxed_267_, v_b_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v_as_255_);
lean_dec_ref(v_self_254_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object* v_self_269_, lean_object* v_root_270_, lean_object* v_col_271_, lean_object* v_viaImport_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
uint8_t v_viaImport_boxed_280_; lean_object* v_res_281_; 
v_viaImport_boxed_280_ = lean_unbox(v_viaImport_272_);
v_res_281_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_269_, v_root_270_, v_col_271_, v_viaImport_boxed_280_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_self_269_);
return v_res_281_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_object* v_00_u03b2_282_, lean_object* v_m_283_, lean_object* v_a_284_){
_start:
{
uint8_t v___x_285_; 
v___x_285_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_283_, v_a_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(lean_object* v_00_u03b2_286_, lean_object* v_m_287_, lean_object* v_a_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(v_00_u03b2_286_, v_m_287_, v_a_288_);
lean_dec_ref(v_a_288_);
lean_dec_ref(v_m_287_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1(lean_object* v_00_u03b2_291_, lean_object* v_m_292_, lean_object* v_a_293_, lean_object* v_b_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_m_292_, v_a_293_, v_b_294_);
return v___x_295_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(lean_object* v_00_u03b2_296_, lean_object* v_a_297_, lean_object* v_x_298_){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_297_, v_x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_300_, lean_object* v_a_301_, lean_object* v_x_302_){
_start:
{
uint8_t v_res_303_; lean_object* v_r_304_; 
v_res_303_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(v_00_u03b2_300_, v_a_301_, v_x_302_);
lean_dec(v_x_302_);
lean_dec_ref(v_a_301_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2(lean_object* v_00_u03b2_305_, lean_object* v_data_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(v_data_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_308_, lean_object* v_i_309_, lean_object* v_source_310_, lean_object* v_target_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(v_i_309_, v_source_310_, v_target_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(v_x_314_, v_x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(lean_object* v_self_317_, lean_object* v_as_318_, size_t v_sz_319_, size_t v_i_320_, lean_object* v_b_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_lt(v_i_320_, v_sz_319_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
lean_dec_ref(v___y_322_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v_b_321_);
lean_ctor_set(v___x_330_, 1, v___y_327_);
return v___x_330_;
}
else
{
uint8_t v___x_331_; lean_object* v_a_332_; lean_object* v___x_333_; 
v___x_331_ = 0;
v_a_332_ = lean_array_uget_borrowed(v_as_318_, v_i_320_);
lean_inc_ref(v___y_322_);
lean_inc(v_a_332_);
v___x_333_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_317_, v_a_332_, v_b_321_, v___x_331_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v_a_335_; size_t v___x_336_; size_t v___x_337_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
v_a_335_ = lean_ctor_get(v___x_333_, 1);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_333_, 2);
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_add(v_i_320_, v___x_336_);
v_i_320_ = v___x_337_;
v_b_321_ = v_a_334_;
v___y_327_ = v_a_335_;
goto _start;
}
else
{
lean_dec_ref(v___y_322_);
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0___boxed(lean_object* v_self_339_, lean_object* v_as_340_, lean_object* v_sz_341_, lean_object* v_i_342_, lean_object* v_b_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
size_t v_sz_boxed_351_; size_t v_i_boxed_352_; lean_object* v_res_353_; 
v_sz_boxed_351_ = lean_unbox_usize(v_sz_341_);
lean_dec(v_sz_341_);
v_i_boxed_352_ = lean_unbox_usize(v_i_342_);
lean_dec(v_i_342_);
v_res_353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_339_, v_as_340_, v_sz_boxed_351_, v_i_boxed_352_, v_b_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v_as_340_);
lean_dec_ref(v_self_339_);
return v_res_353_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1));
v___x_357_ = l_Lake_BuildTrace_nil(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(lean_object* v_self_359_, lean_object* v_col_360_, lean_object* v___x_361_, uint8_t v___x_362_, lean_object* v___x_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; 
lean_inc_ref(v_self_359_);
v___x_371_ = l_Lake_LeanLib_getModuleArray(v_self_359_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; size_t v_sz_373_; size_t v___x_374_; lean_object* v___x_375_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_371_, 1);
v_sz_373_ = lean_array_size(v_a_372_);
v___x_374_ = ((size_t)0ULL);
v___x_375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_359_, v_a_372_, v_sz_373_, v___x_374_, v_col_360_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v_a_372_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_object* v_a_376_; lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_403_; 
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_a_377_ = lean_ctor_get(v___x_375_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_403_ == 0)
{
v___x_379_ = v___x_375_;
v_isShared_380_ = v_isSharedCheck_403_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_403_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_mods_381_; uint8_t v_hasErrors_382_; lean_object* v___y_384_; 
v_mods_381_ = lean_ctor_get(v_a_376_, 0);
lean_inc_ref(v_mods_381_);
v_hasErrors_382_ = lean_ctor_get_uint8(v_a_376_, sizeof(void*)*2);
lean_dec(v_a_376_);
if (v_hasErrors_382_ == 0)
{
lean_dec_ref(v_self_359_);
v___y_384_ = v_a_377_;
goto v___jp_383_;
}
else
{
lean_object* v_name_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_name_396_ = lean_ctor_get(v_self_359_, 1);
lean_inc(v_name_396_);
lean_dec_ref(v_self_359_);
v___x_397_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_396_, v_hasErrors_382_);
v___x_398_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__3));
v___x_399_ = lean_string_append(v___x_397_, v___x_398_);
v___x_400_ = 3;
v___x_401_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set_uint8(v___x_401_, sizeof(void*)*1, v___x_400_);
v___x_402_ = lean_array_push(v_a_377_, v___x_401_);
v___y_384_ = v___x_402_;
goto v___jp_383_;
}
v___jp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_385_ = lean_mk_empty_array_with_capacity(v___x_361_);
v___x_386_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_387_ = 0;
v___x_388_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_389_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_389_, 0, v___x_385_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
lean_ctor_set(v___x_389_, 2, v___x_361_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*3, v___x_387_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*3 + 1, v___x_362_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 1, v___x_389_);
lean_ctor_set(v___x_379_, 0, v_mods_381_);
v___x_391_ = v___x_379_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_mods_381_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___x_389_);
v___x_391_ = v_reuseFailAlloc_395_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_task_pure(v___x_391_);
v___x_393_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___x_363_);
lean_ctor_set(v___x_393_, 2, v___x_386_);
lean_ctor_set_uint8(v___x_393_, sizeof(void*)*3, v___x_362_);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___y_384_);
return v___x_394_;
}
}
}
}
else
{
lean_object* v_a_404_; lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v___x_363_);
lean_dec(v___x_361_);
lean_dec_ref(v_self_359_);
v_a_404_ = lean_ctor_get(v___x_375_, 0);
v_a_405_ = lean_ctor_get(v___x_375_, 1);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_375_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_inc(v_a_404_);
lean_dec(v___x_375_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_404_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_414_; uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec_ref(v___y_364_);
lean_dec(v___x_363_);
lean_dec(v___x_361_);
lean_dec_ref(v_col_360_);
lean_dec_ref(v_self_359_);
v_a_413_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_371_, 1);
v___x_414_ = lean_io_error_to_string(v_a_413_);
v___x_415_ = 3;
v___x_416_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*1, v___x_415_);
v___x_417_ = lean_array_get_size(v___y_369_);
v___x_418_ = lean_array_push(v___y_369_, v___x_416_);
v___x_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
return v___x_419_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed(lean_object* v_self_420_, lean_object* v_col_421_, lean_object* v___x_422_, lean_object* v___x_423_, lean_object* v___x_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
uint8_t v___x_7361__boxed_432_; lean_object* v_res_433_; 
v___x_7361__boxed_432_ = lean_unbox(v___x_423_);
v_res_433_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(v_self_420_, v_col_421_, v___x_422_, v___x_7361__boxed_432_, v___x_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec(v___y_427_);
lean_dec(v___y_426_);
return v_res_433_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_box(0);
v___x_437_ = lean_unsigned_to_nat(16u);
v___x_438_ = lean_mk_array(v___x_437_, v___x_436_);
return v___x_438_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1);
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
return v___x_441_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3(void){
_start:
{
uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_col_445_; 
v___x_442_ = 0;
v___x_443_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_444_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0));
v_col_445_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_col_445_, 0, v___x_444_);
lean_ctor_set(v_col_445_, 1, v___x_443_);
lean_ctor_set_uint8(v_col_445_, sizeof(void*)*2, v___x_442_);
return v_col_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(lean_object* v_self_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; lean_object* v_col_457_; lean_object* v___x_458_; lean_object* v___f_459_; lean_object* v___x_460_; 
v___x_454_ = lean_box(0);
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = 0;
v_col_457_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3);
v___x_458_ = lean_box(v___x_456_);
v___f_459_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed), 12, 5);
lean_closure_set(v___f_459_, 0, v_self_446_);
lean_closure_set(v___f_459_, 1, v_col_457_);
lean_closure_set(v___f_459_, 2, v___x_455_);
lean_closure_set(v___f_459_, 3, v___x_458_);
lean_closure_set(v___f_459_, 4, v___x_454_);
v___x_460_ = l_Lake_ensureJob___redArg(v___x_454_, v___f_459_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___boxed(lean_object* v_self_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(v_self_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec(v_a_464_);
lean_dec(v_a_463_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(lean_object* v_as_471_, size_t v_i_472_, size_t v_stop_473_, lean_object* v_b_474_){
_start:
{
uint8_t v___x_475_; 
v___x_475_ = lean_usize_dec_eq(v_i_472_, v_stop_473_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; lean_object* v_name_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; size_t v___x_483_; size_t v___x_484_; 
v___x_476_ = lean_array_uget_borrowed(v_as_471_, v_i_472_);
v_name_477_ = lean_ctor_get(v___x_476_, 1);
v___x_478_ = 1;
lean_inc(v_name_477_);
v___x_479_ = l_Lean_Name_toString(v_name_477_, v___x_478_);
v___x_480_ = lean_string_append(v_b_474_, v___x_479_);
lean_dec_ref(v___x_479_);
v___x_481_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_482_ = lean_string_append(v___x_480_, v___x_481_);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_add(v_i_472_, v___x_483_);
v_i_472_ = v___x_484_;
v_b_474_ = v___x_482_;
goto _start;
}
else
{
return v_b_474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_486_, lean_object* v_i_487_, lean_object* v_stop_488_, lean_object* v_b_489_){
_start:
{
size_t v_i_boxed_490_; size_t v_stop_boxed_491_; lean_object* v_res_492_; 
v_i_boxed_490_ = lean_unbox_usize(v_i_487_);
lean_dec(v_i_487_);
v_stop_boxed_491_ = lean_unbox_usize(v_stop_488_);
lean_dec(v_stop_488_);
v_res_492_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_as_486_, v_i_boxed_490_, v_stop_boxed_491_, v_b_489_);
lean_dec_ref(v_as_486_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(size_t v_sz_493_, size_t v_i_494_, lean_object* v_bs_495_){
_start:
{
uint8_t v___x_496_; 
v___x_496_ = lean_usize_dec_lt(v_i_494_, v_sz_493_);
if (v___x_496_ == 0)
{
return v_bs_495_;
}
else
{
lean_object* v_v_497_; lean_object* v_name_498_; lean_object* v___x_499_; lean_object* v_bs_x27_500_; lean_object* v___x_501_; lean_object* v___x_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; 
v_v_497_ = lean_array_uget_borrowed(v_bs_495_, v_i_494_);
v_name_498_ = lean_ctor_get(v_v_497_, 1);
lean_inc(v_name_498_);
v___x_499_ = lean_unsigned_to_nat(0u);
v_bs_x27_500_ = lean_array_uset(v_bs_495_, v_i_494_, v___x_499_);
v___x_501_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_498_, v___x_496_);
v___x_502_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
v___x_503_ = ((size_t)1ULL);
v___x_504_ = lean_usize_add(v_i_494_, v___x_503_);
v___x_505_ = lean_array_uset(v_bs_x27_500_, v_i_494_, v___x_502_);
v_i_494_ = v___x_504_;
v_bs_495_ = v___x_505_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_507_, lean_object* v_i_508_, lean_object* v_bs_509_){
_start:
{
size_t v_sz_boxed_510_; size_t v_i_boxed_511_; lean_object* v_res_512_; 
v_sz_boxed_510_ = lean_unbox_usize(v_sz_507_);
lean_dec(v_sz_507_);
v_i_boxed_511_ = lean_unbox_usize(v_i_508_);
lean_dec(v_i_508_);
v_res_512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_510_, v_i_boxed_511_, v_bs_509_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(lean_object* v_a_513_){
_start:
{
size_t v_sz_514_; size_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_sz_514_ = lean_array_size(v_a_513_);
v___x_515_ = ((size_t)0ULL);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_514_, v___x_515_, v_a_513_);
v___x_517_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(uint8_t v_fmt_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___y_521_; 
if (v_fmt_518_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_528_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_array_get_size(v_a_519_);
v___x_531_ = lean_nat_dec_lt(v___x_529_, v___x_530_);
if (v___x_531_ == 0)
{
lean_dec_ref(v_a_519_);
v___y_521_ = v___x_528_;
goto v___jp_520_;
}
else
{
size_t v___x_532_; size_t v___x_533_; lean_object* v___x_534_; 
v___x_532_ = ((size_t)0ULL);
v___x_533_ = lean_usize_of_nat(v___x_530_);
v___x_534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_519_, v___x_532_, v___x_533_, v___x_528_);
lean_dec_ref(v_a_519_);
v___y_521_ = v___x_534_;
goto v___jp_520_;
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(v_a_519_);
v___x_536_ = l_Lean_Json_compress(v___x_535_);
return v___x_536_;
}
v___jp_520_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = lean_string_utf8_byte_size(v___y_521_);
lean_inc_ref(v___y_521_);
v___x_525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_525_, 0, v___y_521_);
lean_ctor_set(v___x_525_, 1, v___x_523_);
lean_ctor_set(v___x_525_, 2, v___x_524_);
v___x_526_ = l_String_Slice_Pos_prevn(v___x_525_, v___x_524_, v___x_522_);
lean_dec_ref_known(v___x_525_, 3);
v___x_527_ = lean_string_utf8_extract_fast(v___y_521_, v___x_523_, v___x_526_);
lean_dec(v___x_526_);
lean_dec_ref(v___y_521_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0___boxed(lean_object* v_fmt_537_, lean_object* v_a_538_){
_start:
{
uint8_t v_fmt_boxed_539_; lean_object* v_res_540_; 
v_fmt_boxed_539_ = lean_unbox(v_fmt_537_);
v_res_540_ = l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(v_fmt_boxed_539_, v_a_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(lean_object* v_as_554_, size_t v_i_555_, size_t v_stop_556_, lean_object* v_b_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
uint8_t v___x_565_; 
v___x_565_ = lean_usize_dec_eq(v_i_555_, v_stop_556_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v_lib_567_; lean_object* v_pkg_568_; lean_object* v_name_569_; lean_object* v_keyName_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_566_ = lean_array_uget_borrowed(v_as_554_, v_i_555_);
v_lib_567_ = lean_ctor_get(v___x_566_, 0);
v_pkg_568_ = lean_ctor_get(v_lib_567_, 0);
v_name_569_ = lean_ctor_get(v___x_566_, 1);
v_keyName_570_ = lean_ctor_get(v_pkg_568_, 2);
v___x_571_ = l_Lake_Module_leanArtsFacet;
lean_inc(v_name_569_);
lean_inc(v_keyName_570_);
v___x_572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_572_, 0, v_keyName_570_);
lean_ctor_set(v___x_572_, 1, v_name_569_);
v___x_573_ = l_Lake_Module_keyword;
lean_inc(v___x_566_);
v___x_574_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
lean_ctor_set(v___x_574_, 2, v___x_566_);
lean_ctor_set(v___x_574_, 3, v___x_571_);
lean_inc_ref(v___y_558_);
lean_inc_ref(v___y_562_);
lean_inc(v___y_561_);
lean_inc(v___y_560_);
lean_inc(v___y_559_);
v___x_575_ = lean_apply_7(v___y_558_, v___x_574_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, lean_box(0));
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v_a_577_; lean_object* v___x_578_; size_t v___x_579_; size_t v___x_580_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
v_a_577_ = lean_ctor_get(v___x_575_, 1);
lean_inc(v_a_577_);
lean_dec_ref_known(v___x_575_, 2);
v___x_578_ = l_Lake_Job_mix___redArg(v_b_557_, v_a_576_);
v___x_579_ = ((size_t)1ULL);
v___x_580_ = lean_usize_add(v_i_555_, v___x_579_);
v_i_555_ = v___x_580_;
v_b_557_ = v___x_578_;
v___y_563_ = v_a_577_;
goto _start;
}
else
{
lean_object* v_a_582_; lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec_ref(v___y_558_);
lean_dec_ref(v_b_557_);
v_a_582_ = lean_ctor_get(v___x_575_, 0);
v_a_583_ = lean_ctor_get(v___x_575_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_575_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_inc(v_a_582_);
lean_dec(v___x_575_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_582_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v___x_591_; 
lean_dec_ref(v___y_558_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v_b_557_);
lean_ctor_set(v___x_591_, 1, v___y_563_);
return v___x_591_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0___boxed(lean_object* v_as_592_, lean_object* v_i_593_, lean_object* v_stop_594_, lean_object* v_b_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
size_t v_i_boxed_603_; size_t v_stop_boxed_604_; lean_object* v_res_605_; 
v_i_boxed_603_ = lean_unbox_usize(v_i_593_);
lean_dec(v_i_593_);
v_stop_boxed_604_ = lean_unbox_usize(v_stop_594_);
lean_dec(v_stop_594_);
v_res_605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_as_592_, v_i_boxed_603_, v_stop_boxed_604_, v_b_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v_as_592_);
return v_res_605_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; uint8_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_610_ = 0;
v___x_611_ = 0;
v___x_612_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v___x_613_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_609_);
lean_ctor_set(v___x_613_, 2, v___x_608_);
lean_ctor_set_uint8(v___x_613_, sizeof(void*)*3, v___x_611_);
lean_ctor_set_uint8(v___x_613_, sizeof(void*)*3 + 1, v___x_610_);
return v___x_613_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1);
v___x_615_ = lean_box(0);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v___x_614_);
return v___x_616_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2);
v___x_618_ = lean_task_pure(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4(void){
_start:
{
uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_619_ = 0;
v___x_620_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_621_ = lean_box(0);
v___x_622_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3);
v___x_623_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v___x_621_);
lean_ctor_set(v___x_623_, 2, v___x_620_);
lean_ctor_set_uint8(v___x_623_, sizeof(void*)*3, v___x_619_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(lean_object* v_self_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_pkg_632_; lean_object* v_name_633_; lean_object* v_keyName_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_pkg_632_ = lean_ctor_get(v_self_624_, 0);
v_name_633_ = lean_ctor_get(v_self_624_, 1);
v_keyName_634_ = lean_ctor_get(v_pkg_632_, 2);
v___x_635_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_633_);
lean_inc(v_keyName_634_);
v___x_636_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_636_, 0, v_keyName_634_);
lean_ctor_set(v___x_636_, 1, v_name_633_);
v___x_637_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_638_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
lean_ctor_set(v___x_638_, 2, v_self_624_);
lean_ctor_set(v___x_638_, 3, v___x_635_);
lean_inc_ref(v_a_625_);
lean_inc_ref(v_a_629_);
lean_inc(v_a_628_);
lean_inc(v_a_627_);
lean_inc(v_a_626_);
v___x_639_ = lean_apply_7(v_a_625_, v___x_638_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, lean_box(0));
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v_a_641_; lean_object* v___x_642_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
v_a_641_ = lean_ctor_get(v___x_639_, 1);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_639_, 2);
v___x_642_ = l_Lake_Job_await___redArg(v_a_640_, v_a_641_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_665_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
v_a_644_ = lean_ctor_get(v___x_642_, 1);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_665_ == 0)
{
v___x_646_ = v___x_642_;
v_isShared_647_ = v_isSharedCheck_665_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_inc(v_a_643_);
lean_dec(v___x_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_665_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4);
v___x_650_ = lean_array_get_size(v_a_643_);
v___x_651_ = lean_nat_dec_lt(v___x_648_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_653_; 
lean_dec(v_a_643_);
lean_dec_ref(v_a_625_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_649_);
v___x_653_ = v___x_646_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_a_644_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
else
{
uint8_t v___x_655_; 
v___x_655_ = lean_nat_dec_le(v___x_650_, v___x_650_);
if (v___x_655_ == 0)
{
if (v___x_651_ == 0)
{
lean_object* v___x_657_; 
lean_dec(v_a_643_);
lean_dec_ref(v_a_625_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_649_);
v___x_657_ = v___x_646_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_a_644_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
else
{
size_t v___x_659_; size_t v___x_660_; lean_object* v___x_661_; 
lean_del_object(v___x_646_);
v___x_659_ = ((size_t)0ULL);
v___x_660_ = lean_usize_of_nat(v___x_650_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_643_, v___x_659_, v___x_660_, v___x_649_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_644_);
lean_dec(v_a_643_);
return v___x_661_;
}
}
else
{
size_t v___x_662_; size_t v___x_663_; lean_object* v___x_664_; 
lean_del_object(v___x_646_);
v___x_662_ = ((size_t)0ULL);
v___x_663_ = lean_usize_of_nat(v___x_650_);
v___x_664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_643_, v___x_662_, v___x_663_, v___x_649_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_644_);
lean_dec(v_a_643_);
return v___x_664_;
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v_a_625_);
v_a_666_ = lean_ctor_get(v___x_642_, 0);
v_a_667_ = lean_ctor_get(v___x_642_, 1);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_642_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_inc(v_a_666_);
lean_dec(v___x_642_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_666_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v_a_675_; lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v_a_625_);
v_a_675_ = lean_ctor_get(v___x_639_, 0);
v_a_676_ = lean_ctor_get(v___x_639_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_639_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_inc(v_a_675_);
lean_dec(v___x_639_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_675_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___boxed(lean_object* v_self_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(v_self_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec(v_a_687_);
lean_dec(v_a_686_);
return v_res_692_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_box(0);
v___x_694_ = l_Lean_Json_compress(v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(uint8_t v_fmt_695_){
_start:
{
if (v_fmt_695_ == 0)
{
lean_object* v___x_696_; 
v___x_696_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
return v___x_696_;
}
else
{
lean_object* v___x_697_; 
v___x_697_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_698_){
_start:
{
uint8_t v_fmt_boxed_699_; lean_object* v_res_700_; 
v_fmt_boxed_699_ = lean_unbox(v_fmt_698_);
v_res_700_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_boxed_699_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(uint8_t v_fmt_701_, lean_object* v_a_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_701_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___boxed(lean_object* v_fmt_704_, lean_object* v_a_705_){
_start:
{
uint8_t v_fmt_boxed_706_; lean_object* v_res_707_; 
v_fmt_boxed_706_ = lean_unbox(v_fmt_704_);
v_res_707_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(v_fmt_boxed_706_, v_a_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0(uint8_t v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v___y_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
uint8_t v___y_68__boxed_713_; lean_object* v_res_714_; 
v___y_68__boxed_713_ = lean_unbox(v___y_711_);
v_res_714_ = l_Lake_LeanLib_leanArtsFacetConfig___lam__0(v___y_68__boxed_713_, v___y_712_);
return v_res_714_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_717_; uint8_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___f_717_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_718_ = 1;
v___x_719_ = l_Lake_instDataKindUnit;
v___x_720_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__1));
v___x_721_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_722_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_722_, 0, v___x_721_);
lean_ctor_set(v___x_722_, 1, v___x_720_);
lean_ctor_set(v___x_722_, 2, v___x_719_);
lean_ctor_set(v___x_722_, 3, v___f_717_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*4, v___x_718_);
lean_ctor_set_uint8(v___x_722_, sizeof(void*)*4 + 1, v___x_718_);
return v___x_722_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig(void){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = lean_obj_once(&l_Lake_LeanLib_leanArtsFacetConfig___closed__2, &l_Lake_LeanLib_leanArtsFacetConfig___closed__2_once, _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(lean_object* v_a_724_, lean_object* v_x_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lake_ModuleFacet_fetch___redArg(v_x_725_, v_a_724_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object* v_a_734_, lean_object* v_x_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(v_a_734_, v_x_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec(v___y_738_);
lean_dec(v___y_737_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(uint8_t v_shouldExport_744_, lean_object* v___x_745_, lean_object* v_bs_746_, lean_object* v_a_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_lib_755_; lean_object* v_config_756_; lean_object* v_nativeFacets_757_; lean_object* v___f_758_; lean_object* v___x_759_; lean_object* v___x_760_; size_t v_sz_761_; size_t v___x_762_; lean_object* v___x_187444__overap_763_; lean_object* v___x_764_; 
v_lib_755_ = lean_ctor_get(v_a_747_, 0);
v_config_756_ = lean_ctor_get(v_lib_755_, 2);
v_nativeFacets_757_ = lean_ctor_get(v_config_756_, 8);
lean_inc_ref(v_nativeFacets_757_);
v___f_758_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed), 9, 1);
lean_closure_set(v___f_758_, 0, v_a_747_);
v___x_759_ = lean_box(v_shouldExport_744_);
v___x_760_ = lean_apply_1(v_nativeFacets_757_, v___x_759_);
v_sz_761_ = lean_array_size(v___x_760_);
v___x_762_ = ((size_t)0ULL);
v___x_187444__overap_763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_745_, v___f_758_, v_sz_761_, v___x_762_, v___x_760_);
lean_inc_ref(v___y_752_);
lean_inc(v___y_751_);
lean_inc(v___y_750_);
lean_inc(v___y_749_);
v___x_764_ = lean_apply_7(v___x_187444__overap_763_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, lean_box(0));
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_774_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_a_766_ = lean_ctor_get(v___x_764_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_774_ == 0)
{
v___x_768_ = v___x_764_;
v_isShared_769_ = v_isSharedCheck_774_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_inc(v_a_765_);
lean_dec(v___x_764_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_774_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_770_ = l_Array_append___redArg(v_bs_746_, v_a_765_);
lean_dec(v_a_765_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_770_);
v___x_772_ = v___x_768_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_a_766_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
else
{
lean_dec_ref(v_bs_746_);
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed(lean_object* v_shouldExport_775_, lean_object* v___x_776_, lean_object* v_bs_777_, lean_object* v_a_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
uint8_t v_shouldExport_boxed_786_; lean_object* v_res_787_; 
v_shouldExport_boxed_786_ = lean_unbox(v_shouldExport_775_);
v_res_787_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(v_shouldExport_boxed_786_, v___x_776_, v_bs_777_, v_a_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec(v___y_781_);
lean_dec(v___y_780_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(lean_object* v___x_788_, lean_object* v_pkg_789_, lean_object* v_x_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lake_Target_fetchIn___redArg(v___x_788_, v_pkg_789_, v_x_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object* v___x_799_, lean_object* v_pkg_800_, lean_object* v_x_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(v___x_799_, v_pkg_800_, v_x_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec(v___y_804_);
lean_dec(v___y_803_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object* v_a_810_, lean_object* v_x_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_log_820_; uint8_t v_action_821_; uint8_t v_wantsRebuild_822_; lean_object* v_trace_823_; lean_object* v_buildTime_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_log_820_ = lean_ctor_get(v___y_818_, 0);
v_action_821_ = lean_ctor_get_uint8(v___y_818_, sizeof(void*)*3);
v_wantsRebuild_822_ = lean_ctor_get_uint8(v___y_818_, sizeof(void*)*3 + 1);
v_trace_823_ = lean_ctor_get(v___y_818_, 1);
v_buildTime_824_ = lean_ctor_get(v___y_818_, 2);
v___x_825_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_826_ = lean_string_append(v___y_812_, v___x_825_);
v___x_827_ = lean_io_prim_handle_put_str(v_a_810_, v___x_826_);
lean_dec_ref(v___x_826_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_829_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v_a_828_);
lean_ctor_set(v___x_829_, 1, v___y_818_);
return v___x_829_;
}
else
{
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_843_; 
lean_inc(v_buildTime_824_);
lean_inc_ref(v_trace_823_);
lean_inc_ref(v_log_820_);
v_isSharedCheck_843_ = !lean_is_exclusive(v___y_818_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; lean_object* v_unused_845_; lean_object* v_unused_846_; 
v_unused_844_ = lean_ctor_get(v___y_818_, 2);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v___y_818_, 1);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v___y_818_, 0);
lean_dec(v_unused_846_);
v___x_831_ = v___y_818_;
v_isShared_832_ = v_isSharedCheck_843_;
goto v_resetjp_830_;
}
else
{
lean_dec(v___y_818_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_843_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_a_833_; lean_object* v___x_834_; uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v_a_833_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_827_, 1);
v___x_834_ = lean_io_error_to_string(v_a_833_);
v___x_835_ = 3;
v___x_836_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set_uint8(v___x_836_, sizeof(void*)*1, v___x_835_);
v___x_837_ = lean_array_get_size(v_log_820_);
v___x_838_ = lean_array_push(v_log_820_, v___x_836_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_838_);
v___x_840_ = v___x_831_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_trace_823_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_buildTime_824_);
lean_ctor_set_uint8(v_reuseFailAlloc_842_, sizeof(void*)*3, v_action_821_);
lean_ctor_set_uint8(v_reuseFailAlloc_842_, sizeof(void*)*3 + 1, v_wantsRebuild_822_);
v___x_840_ = v_reuseFailAlloc_842_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; 
v___x_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_837_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
return v___x_841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object* v_a_847_, lean_object* v_x_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(v_a_847_, v_x_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v_a_847_);
return v_res_857_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_865_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3));
v___x_866_ = lean_unsigned_to_nat(5u);
v___x_867_ = lean_mk_empty_array_with_capacity(v___x_866_);
v___x_868_ = lean_array_push(v___x_867_, v___x_865_);
return v___x_868_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_869_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4));
v___x_870_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6);
v___x_871_ = lean_array_push(v___x_870_, v___x_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(uint8_t v_bootstrap_874_, lean_object* v___y_875_, lean_object* v_oFiles_876_, uint8_t v_shouldExport_877_, uint8_t v___x_878_, lean_object* v___x_879_, size_t v___x_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
if (v_bootstrap_874_ == 0)
{
lean_object* v_toContext_888_; lean_object* v_lakeEnv_889_; lean_object* v_lean_890_; lean_object* v_log_891_; uint8_t v_action_892_; uint8_t v_wantsRebuild_893_; lean_object* v_trace_894_; lean_object* v_buildTime_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_925_; 
lean_dec_ref(v___y_881_);
lean_dec_ref(v___x_879_);
v_toContext_888_ = lean_ctor_get(v___y_885_, 1);
v_lakeEnv_889_ = lean_ctor_get(v_toContext_888_, 0);
v_lean_890_ = lean_ctor_get(v_lakeEnv_889_, 1);
v_log_891_ = lean_ctor_get(v___y_886_, 0);
v_action_892_ = lean_ctor_get_uint8(v___y_886_, sizeof(void*)*3);
v_wantsRebuild_893_ = lean_ctor_get_uint8(v___y_886_, sizeof(void*)*3 + 1);
v_trace_894_ = lean_ctor_get(v___y_886_, 1);
v_buildTime_895_ = lean_ctor_get(v___y_886_, 2);
v_isSharedCheck_925_ = !lean_is_exclusive(v___y_886_);
if (v_isSharedCheck_925_ == 0)
{
v___x_897_ = v___y_886_;
v_isShared_898_ = v_isSharedCheck_925_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_buildTime_895_);
lean_inc(v_trace_894_);
lean_inc(v_log_891_);
lean_dec(v___y_886_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_925_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_ar_899_; lean_object* v___x_900_; 
v_ar_899_ = lean_ctor_get(v_lean_890_, 13);
lean_inc_ref(v_ar_899_);
v___x_900_ = l_Lake_compileStaticLib(v___y_875_, v_oFiles_876_, v_ar_899_, v_bootstrap_874_, v_log_891_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_912_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_a_902_ = lean_ctor_get(v___x_900_, 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_912_ == 0)
{
v___x_904_ = v___x_900_;
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v_a_902_);
v___x_907_ = v___x_897_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_902_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_trace_894_);
lean_ctor_set(v_reuseFailAlloc_911_, 2, v_buildTime_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, sizeof(void*)*3, v_action_892_);
lean_ctor_set_uint8(v_reuseFailAlloc_911_, sizeof(void*)*3 + 1, v_wantsRebuild_893_);
v___x_907_ = v_reuseFailAlloc_911_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
lean_object* v___x_909_; 
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v___x_907_);
v___x_909_ = v___x_904_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_901_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_924_; 
v_a_913_ = lean_ctor_get(v___x_900_, 0);
v_a_914_ = lean_ctor_get(v___x_900_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_924_ == 0)
{
v___x_916_ = v___x_900_;
v_isShared_917_ = v_isSharedCheck_924_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_inc(v_a_913_);
lean_dec(v___x_900_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_924_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v_a_914_);
v___x_919_ = v___x_897_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_914_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_trace_894_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_buildTime_895_);
lean_ctor_set_uint8(v_reuseFailAlloc_923_, sizeof(void*)*3, v_action_892_);
lean_ctor_set_uint8(v_reuseFailAlloc_923_, sizeof(void*)*3 + 1, v_wantsRebuild_893_);
v___x_919_ = v_reuseFailAlloc_923_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_921_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 1, v___x_919_);
v___x_921_ = v___x_916_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_913_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
else
{
uint8_t v___x_926_; 
v___x_926_ = l_System_Platform_isOSX;
if (v___x_926_ == 0)
{
uint8_t v___x_927_; 
lean_dec_ref(v___y_881_);
lean_dec_ref(v___x_879_);
v___x_927_ = l_System_Platform_isWindows;
if (v___x_927_ == 0)
{
lean_object* v_toContext_928_; lean_object* v_lakeEnv_929_; lean_object* v_lean_930_; lean_object* v_log_931_; uint8_t v_action_932_; uint8_t v_wantsRebuild_933_; lean_object* v_trace_934_; lean_object* v_buildTime_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_965_; 
v_toContext_928_ = lean_ctor_get(v___y_885_, 1);
v_lakeEnv_929_ = lean_ctor_get(v_toContext_928_, 0);
v_lean_930_ = lean_ctor_get(v_lakeEnv_929_, 1);
v_log_931_ = lean_ctor_get(v___y_886_, 0);
v_action_932_ = lean_ctor_get_uint8(v___y_886_, sizeof(void*)*3);
v_wantsRebuild_933_ = lean_ctor_get_uint8(v___y_886_, sizeof(void*)*3 + 1);
v_trace_934_ = lean_ctor_get(v___y_886_, 1);
v_buildTime_935_ = lean_ctor_get(v___y_886_, 2);
v_isSharedCheck_965_ = !lean_is_exclusive(v___y_886_);
if (v_isSharedCheck_965_ == 0)
{
v___x_937_ = v___y_886_;
v_isShared_938_ = v_isSharedCheck_965_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_buildTime_935_);
lean_inc(v_trace_934_);
lean_inc(v_log_931_);
lean_dec(v___y_886_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_965_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v_ar_939_; lean_object* v___x_940_; 
v_ar_939_ = lean_ctor_get(v_lean_930_, 13);
lean_inc_ref(v_ar_939_);
v___x_940_ = l_Lake_compileStaticLib(v___y_875_, v_oFiles_876_, v_ar_939_, v___x_927_, v_log_931_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_952_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
v_a_942_ = lean_ctor_get(v___x_940_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_952_ == 0)
{
v___x_944_ = v___x_940_;
v_isShared_945_ = v_isSharedCheck_952_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_inc(v_a_941_);
lean_dec(v___x_940_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_952_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v_a_942_);
v___x_947_ = v___x_937_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_942_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_trace_934_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_buildTime_935_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*3, v_action_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_951_, sizeof(void*)*3 + 1, v_wantsRebuild_933_);
v___x_947_ = v_reuseFailAlloc_951_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_949_; 
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v___x_947_);
v___x_949_ = v___x_944_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_941_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_964_; 
v_a_953_ = lean_ctor_get(v___x_940_, 0);
v_a_954_ = lean_ctor_get(v___x_940_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_964_ == 0)
{
v___x_956_ = v___x_940_;
v_isShared_957_ = v_isSharedCheck_964_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_inc(v_a_953_);
lean_dec(v___x_940_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_964_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v_a_954_);
v___x_959_ = v___x_937_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_954_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_trace_934_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_buildTime_935_);
lean_ctor_set_uint8(v_reuseFailAlloc_963_, sizeof(void*)*3, v_action_932_);
lean_ctor_set_uint8(v_reuseFailAlloc_963_, sizeof(void*)*3 + 1, v_wantsRebuild_933_);
v___x_959_ = v_reuseFailAlloc_963_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v___x_959_);
v___x_961_ = v___x_956_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_953_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_966_; lean_object* v_lakeEnv_967_; lean_object* v_lean_968_; lean_object* v_log_969_; uint8_t v_action_970_; uint8_t v_wantsRebuild_971_; lean_object* v_trace_972_; lean_object* v_buildTime_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1003_; 
v_toContext_966_ = lean_ctor_get(v___y_885_, 1);
v_lakeEnv_967_ = lean_ctor_get(v_toContext_966_, 0);
v_lean_968_ = lean_ctor_get(v_lakeEnv_967_, 1);
v_log_969_ = lean_ctor_get(v___y_886_, 0);
v_action_970_ = lean_ctor_get_uint8(v___y_886_, sizeof(void*)*3);
v_wantsRebuild_971_ = lean_ctor_get_uint8(v___y_886_, sizeof(void*)*3 + 1);
v_trace_972_ = lean_ctor_get(v___y_886_, 1);
v_buildTime_973_ = lean_ctor_get(v___y_886_, 2);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___y_886_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_975_ = v___y_886_;
v_isShared_976_ = v_isSharedCheck_1003_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_buildTime_973_);
lean_inc(v_trace_972_);
lean_inc(v_log_969_);
lean_dec(v___y_886_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1003_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_ar_977_; lean_object* v___x_978_; 
v_ar_977_ = lean_ctor_get(v_lean_968_, 13);
lean_inc_ref(v_ar_977_);
v___x_978_ = l_Lake_compileStaticLib(v___y_875_, v_oFiles_876_, v_ar_977_, v_shouldExport_877_, v_log_969_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_990_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_a_980_ = lean_ctor_get(v___x_978_, 1);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_990_ == 0)
{
v___x_982_ = v___x_978_;
v_isShared_983_ = v_isSharedCheck_990_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_990_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_a_980_);
v___x_985_ = v___x_975_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_trace_972_);
lean_ctor_set(v_reuseFailAlloc_989_, 2, v_buildTime_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_989_, sizeof(void*)*3, v_action_970_);
lean_ctor_set_uint8(v_reuseFailAlloc_989_, sizeof(void*)*3 + 1, v_wantsRebuild_971_);
v___x_985_ = v_reuseFailAlloc_989_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_987_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v___x_985_);
v___x_987_ = v___x_982_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_979_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1002_; 
v_a_991_ = lean_ctor_get(v___x_978_, 0);
v_a_992_ = lean_ctor_get(v___x_978_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_994_ = v___x_978_;
v_isShared_995_ = v_isSharedCheck_1002_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_inc(v_a_991_);
lean_dec(v___x_978_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1002_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_a_992_);
v___x_997_ = v___x_975_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_992_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_trace_972_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_buildTime_973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, sizeof(void*)*3, v_action_970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1001_, sizeof(void*)*3 + 1, v_wantsRebuild_971_);
v___x_997_ = v_reuseFailAlloc_1001_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_999_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v___x_997_);
v___x_999_ = v___x_994_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_991_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1004_; uint8_t v_action_1005_; uint8_t v_wantsRebuild_1006_; lean_object* v_trace_1007_; lean_object* v_buildTime_1008_; lean_object* v___x_1009_; 
v_log_1004_ = lean_ctor_get(v___y_886_, 0);
v_action_1005_ = lean_ctor_get_uint8(v___y_886_, sizeof(void*)*3);
v_wantsRebuild_1006_ = lean_ctor_get_uint8(v___y_886_, sizeof(void*)*3 + 1);
v_trace_1007_ = lean_ctor_get(v___y_886_, 1);
v_buildTime_1008_ = lean_ctor_get(v___y_886_, 2);
lean_inc_ref(v___y_875_);
v___x_1009_ = l_Lake_createParentDirs(v___y_875_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v_a_1013_; lean_object* v___y_1060_; uint8_t v___x_1062_; lean_object* v___x_1063_; 
lean_dec_ref_known(v___x_1009_, 1);
v___x_1010_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_875_);
v___x_1011_ = l_System_FilePath_addExtension(v___y_875_, v___x_1010_);
v___x_1062_ = 1;
v___x_1063_ = lean_io_prim_handle_mk(v___x_1011_, v___x_1062_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = lean_array_get_size(v_oFiles_876_);
v___x_1067_ = lean_nat_dec_lt(v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_dec(v_a_1064_);
lean_dec_ref(v___y_881_);
lean_dec_ref(v___x_879_);
lean_dec_ref(v_oFiles_876_);
v_a_1013_ = v___y_886_;
goto v___jp_1012_;
}
else
{
lean_object* v___f_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___f_1068_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1068_, 0, v_a_1064_);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_nat_dec_le(v___x_1066_, v___x_1066_);
if (v___x_1070_ == 0)
{
if (v___x_1067_ == 0)
{
lean_dec_ref(v___f_1068_);
lean_dec_ref(v___y_881_);
lean_dec_ref(v___x_879_);
lean_dec_ref(v_oFiles_876_);
v_a_1013_ = v___y_886_;
goto v___jp_1012_;
}
else
{
size_t v___x_1071_; lean_object* v___x_187602__overap_1072_; lean_object* v___x_1073_; 
v___x_1071_ = lean_usize_of_nat(v___x_1066_);
v___x_187602__overap_1072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_879_, v___f_1068_, v_oFiles_876_, v___x_880_, v___x_1071_, v___x_1069_);
lean_inc_ref(v___y_885_);
lean_inc(v___y_884_);
lean_inc(v___y_883_);
lean_inc(v___y_882_);
v___x_1073_ = lean_apply_7(v___x_187602__overap_1072_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, lean_box(0));
v___y_1060_ = v___x_1073_;
goto v___jp_1059_;
}
}
else
{
size_t v___x_1074_; lean_object* v___x_187604__overap_1075_; lean_object* v___x_1076_; 
v___x_1074_ = lean_usize_of_nat(v___x_1066_);
v___x_187604__overap_1075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_879_, v___f_1068_, v_oFiles_876_, v___x_880_, v___x_1074_, v___x_1069_);
lean_inc_ref(v___y_885_);
lean_inc(v___y_884_);
lean_inc(v___y_883_);
lean_inc(v___y_882_);
v___x_1076_ = lean_apply_7(v___x_187604__overap_1075_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, lean_box(0));
v___y_1060_ = v___x_1076_;
goto v___jp_1059_;
}
}
}
else
{
lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1090_; 
lean_inc(v_buildTime_1008_);
lean_inc_ref(v_trace_1007_);
lean_inc_ref(v_log_1004_);
lean_dec_ref(v___x_1011_);
lean_dec_ref(v___y_881_);
lean_dec_ref(v___x_879_);
lean_dec_ref(v_oFiles_876_);
lean_dec_ref(v___y_875_);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___y_886_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; lean_object* v_unused_1092_; lean_object* v_unused_1093_; 
v_unused_1091_ = lean_ctor_get(v___y_886_, 2);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v___y_886_, 1);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v___y_886_, 0);
lean_dec(v_unused_1093_);
v___x_1078_ = v___y_886_;
v_isShared_1079_ = v_isSharedCheck_1090_;
goto v_resetjp_1077_;
}
else
{
lean_dec(v___y_886_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1090_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v_a_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v_a_1080_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1081_ = lean_io_error_to_string(v_a_1080_);
v___x_1082_ = 3;
v___x_1083_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*1, v___x_1082_);
v___x_1084_ = lean_array_get_size(v_log_1004_);
v___x_1085_ = lean_array_push(v_log_1004_, v___x_1083_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1085_);
v___x_1087_ = v___x_1078_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_trace_1007_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_buildTime_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1089_, sizeof(void*)*3, v_action_1005_);
lean_ctor_set_uint8(v_reuseFailAlloc_1089_, sizeof(void*)*3 + 1, v_wantsRebuild_1006_);
v___x_1087_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1084_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
return v___x_1088_;
}
}
}
v___jp_1012_:
{
lean_object* v___x_1014_; lean_object* v_log_1015_; uint8_t v_action_1016_; uint8_t v_wantsRebuild_1017_; lean_object* v_trace_1018_; lean_object* v_buildTime_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1058_; 
v___x_1014_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1015_ = lean_ctor_get(v_a_1013_, 0);
v_action_1016_ = lean_ctor_get_uint8(v_a_1013_, sizeof(void*)*3);
v_wantsRebuild_1017_ = lean_ctor_get_uint8(v_a_1013_, sizeof(void*)*3 + 1);
v_trace_1018_ = lean_ctor_get(v_a_1013_, 1);
v_buildTime_1019_ = lean_ctor_get(v_a_1013_, 2);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_a_1013_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1021_ = v_a_1013_;
v_isShared_1022_ = v_isSharedCheck_1058_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_buildTime_1019_);
lean_inc(v_trace_1018_);
lean_inc(v_log_1015_);
lean_dec(v_a_1013_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1058_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1023_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1024_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1025_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1026_ = lean_array_push(v___x_1025_, v___y_875_);
v___x_1027_ = lean_array_push(v___x_1026_, v___x_1024_);
v___x_1028_ = lean_array_push(v___x_1027_, v___x_1011_);
v___x_1029_ = lean_box(0);
v___x_1030_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1031_ = 0;
v___x_1032_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1032_, 0, v___x_1014_);
lean_ctor_set(v___x_1032_, 1, v___x_1023_);
lean_ctor_set(v___x_1032_, 2, v___x_1028_);
lean_ctor_set(v___x_1032_, 3, v___x_1029_);
lean_ctor_set(v___x_1032_, 4, v___x_1030_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*5, v___x_878_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*5 + 1, v___x_1031_);
v___x_1033_ = l_Lake_proc(v___x_1032_, v___x_1031_, v___x_1029_, v_log_1015_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1045_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_a_1035_ = lean_ctor_get(v___x_1033_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1037_ = v___x_1033_;
v_isShared_1038_ = v_isSharedCheck_1045_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1045_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v_a_1035_);
v___x_1040_ = v___x_1021_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1035_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_trace_1018_);
lean_ctor_set(v_reuseFailAlloc_1044_, 2, v_buildTime_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1044_, sizeof(void*)*3, v_action_1016_);
lean_ctor_set_uint8(v_reuseFailAlloc_1044_, sizeof(void*)*3 + 1, v_wantsRebuild_1017_);
v___x_1040_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1042_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v___x_1040_);
v___x_1042_ = v___x_1037_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1034_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1057_; 
v_a_1046_ = lean_ctor_get(v___x_1033_, 0);
v_a_1047_ = lean_ctor_get(v___x_1033_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1049_ = v___x_1033_;
v_isShared_1050_ = v_isSharedCheck_1057_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_inc(v_a_1046_);
lean_dec(v___x_1033_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1057_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v_a_1047_);
v___x_1052_ = v___x_1021_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1047_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_trace_1018_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_buildTime_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*3, v_action_1016_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*3 + 1, v_wantsRebuild_1017_);
v___x_1052_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1054_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 1, v___x_1052_);
v___x_1054_ = v___x_1049_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1046_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
}
v___jp_1059_:
{
if (lean_obj_tag(v___y_1060_) == 0)
{
lean_object* v_a_1061_; 
v_a_1061_ = lean_ctor_get(v___y_1060_, 1);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___y_1060_, 2);
v_a_1013_ = v_a_1061_;
goto v___jp_1012_;
}
else
{
lean_dec_ref(v___x_1011_);
lean_dec_ref(v___y_875_);
return v___y_1060_;
}
}
}
else
{
lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1107_; 
lean_inc(v_buildTime_1008_);
lean_inc_ref(v_trace_1007_);
lean_inc_ref(v_log_1004_);
lean_dec_ref(v___y_881_);
lean_dec_ref(v___x_879_);
lean_dec_ref(v_oFiles_876_);
lean_dec_ref(v___y_875_);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___y_886_);
if (v_isSharedCheck_1107_ == 0)
{
lean_object* v_unused_1108_; lean_object* v_unused_1109_; lean_object* v_unused_1110_; 
v_unused_1108_ = lean_ctor_get(v___y_886_, 2);
lean_dec(v_unused_1108_);
v_unused_1109_ = lean_ctor_get(v___y_886_, 1);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v___y_886_, 0);
lean_dec(v_unused_1110_);
v___x_1095_ = v___y_886_;
v_isShared_1096_ = v_isSharedCheck_1107_;
goto v_resetjp_1094_;
}
else
{
lean_dec(v___y_886_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1107_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v_a_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v_a_1097_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1009_, 1);
v___x_1098_ = lean_io_error_to_string(v_a_1097_);
v___x_1099_ = 3;
v___x_1100_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*1, v___x_1099_);
v___x_1101_ = lean_array_get_size(v_log_1004_);
v___x_1102_ = lean_array_push(v_log_1004_, v___x_1100_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1102_);
v___x_1104_ = v___x_1095_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_trace_1007_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_buildTime_1008_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*3, v_action_1005_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*3 + 1, v_wantsRebuild_1006_);
v___x_1104_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1101_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
return v___x_1105_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object* v_bootstrap_1111_, lean_object* v___y_1112_, lean_object* v_oFiles_1113_, lean_object* v_shouldExport_1114_, lean_object* v___x_1115_, lean_object* v___x_1116_, lean_object* v___x_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
uint8_t v_bootstrap_boxed_1125_; uint8_t v_shouldExport_boxed_1126_; uint8_t v___x_187970__boxed_1127_; size_t v___x_187972__boxed_1128_; lean_object* v_res_1129_; 
v_bootstrap_boxed_1125_ = lean_unbox(v_bootstrap_1111_);
v_shouldExport_boxed_1126_ = lean_unbox(v_shouldExport_1114_);
v___x_187970__boxed_1127_ = lean_unbox(v___x_1115_);
v___x_187972__boxed_1128_ = lean_unbox_usize(v___x_1117_);
lean_dec(v___x_1117_);
v_res_1129_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(v_bootstrap_boxed_1125_, v___y_1112_, v_oFiles_1113_, v_shouldExport_boxed_1126_, v___x_187970__boxed_1127_, v___x_1116_, v___x_187972__boxed_1128_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec(v___y_1119_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(uint8_t v_bootstrap_1131_, lean_object* v___y_1132_, uint8_t v_shouldExport_1133_, uint8_t v___x_1134_, lean_object* v___x_1135_, size_t v___x_1136_, lean_object* v_oFiles_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___y_1149_; uint8_t v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1145_ = lean_box(v_bootstrap_1131_);
v___x_1146_ = lean_box(v_shouldExport_1133_);
v___x_1147_ = lean_box(v___x_1134_);
v___x_1148_ = lean_box_usize(v___x_1136_);
lean_inc_ref(v___y_1132_);
v___y_1149_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed), 14, 7);
lean_closure_set(v___y_1149_, 0, v___x_1145_);
lean_closure_set(v___y_1149_, 1, v___y_1132_);
lean_closure_set(v___y_1149_, 2, v_oFiles_1137_);
lean_closure_set(v___y_1149_, 3, v___x_1146_);
lean_closure_set(v___y_1149_, 4, v___x_1147_);
lean_closure_set(v___y_1149_, 5, v___x_1135_);
lean_closure_set(v___y_1149_, 6, v___x_1148_);
v___x_1150_ = 0;
v___x_1151_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1152_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1132_, v___y_1149_, v___x_1150_, v___x_1151_, v___x_1134_, v___x_1150_, v___x_1150_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1162_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_a_1154_ = lean_ctor_get(v___x_1152_, 1);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1156_ = v___x_1152_;
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v_path_1158_; lean_object* v___x_1160_; 
v_path_1158_ = lean_ctor_get(v_a_1153_, 1);
lean_inc_ref(v_path_1158_);
lean_dec(v_a_1153_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 0, v_path_1158_);
v___x_1160_ = v___x_1156_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_path_1158_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_a_1154_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
v_a_1163_ = lean_ctor_get(v___x_1152_, 0);
v_a_1164_ = lean_ctor_get(v___x_1152_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1152_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_inc(v_a_1163_);
lean_dec(v___x_1152_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1163_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object* v_bootstrap_1172_, lean_object* v___y_1173_, lean_object* v_shouldExport_1174_, lean_object* v___x_1175_, lean_object* v___x_1176_, lean_object* v___x_1177_, lean_object* v_oFiles_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
uint8_t v_bootstrap_boxed_1186_; uint8_t v_shouldExport_boxed_1187_; uint8_t v___x_188393__boxed_1188_; size_t v___x_188395__boxed_1189_; lean_object* v_res_1190_; 
v_bootstrap_boxed_1186_ = lean_unbox(v_bootstrap_1172_);
v_shouldExport_boxed_1187_ = lean_unbox(v_shouldExport_1174_);
v___x_188393__boxed_1188_ = lean_unbox(v___x_1175_);
v___x_188395__boxed_1189_ = lean_unbox_usize(v___x_1177_);
lean_dec(v___x_1177_);
v_res_1190_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(v_bootstrap_boxed_1186_, v___y_1173_, v_shouldExport_boxed_1187_, v___x_188393__boxed_1188_, v___x_1176_, v___x_188395__boxed_1189_, v_oFiles_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec(v___y_1180_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object* v___x_1195_, lean_object* v___x_1196_, lean_object* v_config_1197_, lean_object* v_config_1198_, lean_object* v___x_1199_, lean_object* v___f_1200_, uint8_t v_shouldExport_1201_, uint8_t v___x_1202_, lean_object* v___x_1203_, lean_object* v___x_1204_, lean_object* v_dir_1205_, lean_object* v_self_1206_, lean_object* v___f_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___y_1216_; lean_object* v___y_1217_; size_t v___y_1218_; uint8_t v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v_a_1236_; lean_object* v_a_1237_; lean_object* v___x_1280_; 
lean_inc_ref(v___y_1208_);
lean_inc_ref(v___y_1212_);
lean_inc(v___y_1211_);
lean_inc(v___y_1210_);
lean_inc(v___x_1196_);
v___x_1280_ = lean_apply_7(v___y_1208_, v___x_1195_, v___x_1196_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, lean_box(0));
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v_a_1282_; lean_object* v___x_1283_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
v_a_1282_ = lean_ctor_get(v___x_1280_, 1);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1280_, 2);
v___x_1283_ = l_Lake_Job_await___redArg(v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v_a_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
v_a_1285_ = lean_ctor_get(v___x_1283_, 1);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1283_, 2);
v___x_1286_ = lean_unsigned_to_nat(0u);
v___x_1287_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_1288_ = lean_array_get_size(v_a_1284_);
v___x_1289_ = lean_nat_dec_lt(v___x_1286_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_dec(v_a_1284_);
lean_dec_ref(v___f_1207_);
v_a_1236_ = v___x_1287_;
v_a_1237_ = v_a_1285_;
goto v___jp_1235_;
}
else
{
size_t v___x_1290_; size_t v___x_1291_; lean_object* v___x_187730__overap_1292_; lean_object* v___x_1293_; 
v___x_1290_ = ((size_t)0ULL);
v___x_1291_ = lean_usize_of_nat(v___x_1288_);
lean_inc_ref(v___x_1199_);
v___x_187730__overap_1292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1199_, v___f_1207_, v_a_1284_, v___x_1290_, v___x_1291_, v___x_1287_);
lean_inc_ref(v___y_1212_);
lean_inc(v___y_1211_);
lean_inc(v___y_1210_);
lean_inc(v___x_1196_);
lean_inc_ref(v___y_1208_);
v___x_1293_ = lean_apply_7(v___x_187730__overap_1292_, v___y_1208_, v___x_1196_, v___y_1210_, v___y_1211_, v___y_1212_, v_a_1285_, lean_box(0));
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v_a_1295_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
v_a_1295_ = lean_ctor_get(v___x_1293_, 1);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1293_, 2);
v_a_1236_ = v_a_1294_;
v_a_1237_ = v_a_1295_;
goto v___jp_1235_;
}
else
{
lean_object* v_a_1296_; lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec_ref(v___y_1208_);
lean_dec_ref(v_self_1206_);
lean_dec_ref(v_dir_1205_);
lean_dec(v___x_1204_);
lean_dec_ref(v___x_1203_);
lean_dec_ref(v___f_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v_config_1197_);
lean_dec(v___x_1196_);
v_a_1296_ = lean_ctor_get(v___x_1293_, 0);
v_a_1297_ = lean_ctor_get(v___x_1293_, 1);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1293_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_inc(v_a_1296_);
lean_dec(v___x_1293_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1296_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v___y_1208_);
lean_dec_ref(v___f_1207_);
lean_dec_ref(v_self_1206_);
lean_dec_ref(v_dir_1205_);
lean_dec(v___x_1204_);
lean_dec_ref(v___x_1203_);
lean_dec_ref(v___f_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v_config_1197_);
lean_dec(v___x_1196_);
v_a_1305_ = lean_ctor_get(v___x_1283_, 0);
v_a_1306_ = lean_ctor_get(v___x_1283_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1283_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_inc(v_a_1305_);
lean_dec(v___x_1283_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1305_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v___y_1208_);
lean_dec_ref(v___f_1207_);
lean_dec_ref(v_self_1206_);
lean_dec_ref(v_dir_1205_);
lean_dec(v___x_1204_);
lean_dec_ref(v___x_1203_);
lean_dec_ref(v___f_1200_);
lean_dec_ref(v___x_1199_);
lean_dec_ref(v_config_1197_);
lean_dec(v___x_1196_);
v_a_1314_ = lean_ctor_get(v___x_1280_, 0);
v_a_1315_ = lean_ctor_get(v___x_1280_, 1);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1280_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_inc(v_a_1314_);
lean_dec(v___x_1280_);
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
v___jp_1215_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___f_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1222_ = lean_box(v___y_1219_);
v___x_1223_ = lean_box(v_shouldExport_1201_);
v___x_1224_ = lean_box(v___x_1202_);
v___x_1225_ = lean_box_usize(v___y_1218_);
v___f_1226_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed), 14, 6);
lean_closure_set(v___f_1226_, 0, v___x_1222_);
lean_closure_set(v___f_1226_, 1, v___y_1221_);
lean_closure_set(v___f_1226_, 2, v___x_1223_);
lean_closure_set(v___f_1226_, 3, v___x_1224_);
lean_closure_set(v___f_1226_, 4, v___x_1203_);
lean_closure_set(v___f_1226_, 5, v___x_1225_);
v___x_1227_ = l_Array_append___redArg(v___y_1220_, v___y_1216_);
lean_dec_ref(v___y_1216_);
v___x_1228_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_1229_ = l_Lake_Job_collectArray___redArg(v___x_1227_, v___x_1228_);
lean_dec_ref(v___x_1227_);
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = 0;
v___x_1232_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_1233_ = l_Lake_Job_mapM___redArg(v___x_1204_, v___x_1229_, v___f_1226_, v___x_1230_, v___x_1231_, v___y_1208_, v___x_1196_, v___y_1210_, v___y_1211_, v___y_1212_, v___x_1232_);
lean_dec(v___x_1196_);
v___x_1234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v___y_1217_);
return v___x_1234_;
}
v___jp_1235_:
{
lean_object* v_toLeanConfig_1238_; lean_object* v_toLeanConfig_1239_; uint8_t v_bootstrap_1240_; lean_object* v_buildDir_1241_; lean_object* v_nativeLibDir_1242_; lean_object* v_moreLinkObjs_1243_; lean_object* v_moreLinkObjs_1244_; lean_object* v___x_1245_; size_t v_sz_1246_; size_t v___x_1247_; lean_object* v___x_187681__overap_1248_; lean_object* v___x_1249_; 
v_toLeanConfig_1238_ = lean_ctor_get(v_config_1197_, 1);
lean_inc_ref(v_toLeanConfig_1238_);
v_toLeanConfig_1239_ = lean_ctor_get(v_config_1198_, 0);
v_bootstrap_1240_ = lean_ctor_get_uint8(v_config_1197_, sizeof(void*)*28);
v_buildDir_1241_ = lean_ctor_get(v_config_1197_, 5);
lean_inc_ref(v_buildDir_1241_);
v_nativeLibDir_1242_ = lean_ctor_get(v_config_1197_, 7);
lean_inc_ref(v_nativeLibDir_1242_);
lean_dec_ref(v_config_1197_);
v_moreLinkObjs_1243_ = lean_ctor_get(v_toLeanConfig_1238_, 6);
lean_inc_ref(v_moreLinkObjs_1243_);
lean_dec_ref(v_toLeanConfig_1238_);
v_moreLinkObjs_1244_ = lean_ctor_get(v_toLeanConfig_1239_, 6);
v___x_1245_ = l_Array_append___redArg(v_moreLinkObjs_1243_, v_moreLinkObjs_1244_);
v_sz_1246_ = lean_array_size(v___x_1245_);
v___x_1247_ = ((size_t)0ULL);
v___x_187681__overap_1248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1199_, v___f_1200_, v_sz_1246_, v___x_1247_, v___x_1245_);
lean_inc_ref(v___y_1212_);
lean_inc(v___y_1211_);
lean_inc(v___y_1210_);
lean_inc(v___x_1196_);
lean_inc_ref(v___y_1208_);
v___x_1249_ = lean_apply_7(v___x_187681__overap_1248_, v___y_1208_, v___x_1196_, v___y_1210_, v___y_1211_, v___y_1212_, v_a_1237_, lean_box(0));
if (lean_obj_tag(v___x_1249_) == 0)
{
if (v_shouldExport_1201_ == 0)
{
lean_object* v_a_1250_; lean_object* v_a_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
v_a_1251_ = lean_ctor_get(v___x_1249_, 1);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1249_, 2);
v___x_1252_ = l_System_FilePath_normalize(v_buildDir_1241_);
v___x_1253_ = l_Lake_joinRelative(v_dir_1205_, v___x_1252_);
v___x_1254_ = l_System_FilePath_normalize(v_nativeLibDir_1242_);
v___x_1255_ = l_Lake_joinRelative(v___x_1253_, v___x_1254_);
v___x_1256_ = l_Lake_LeanLib_libName(v_self_1206_);
v___x_1257_ = l_Lake_nameToStaticLib(v___x_1256_, v_shouldExport_1201_);
v___x_1258_ = l_Lake_joinRelative(v___x_1255_, v___x_1257_);
v___y_1216_ = v_a_1250_;
v___y_1217_ = v_a_1251_;
v___y_1218_ = v___x_1247_;
v___y_1219_ = v_bootstrap_1240_;
v___y_1220_ = v_a_1236_;
v___y_1221_ = v___x_1258_;
goto v___jp_1215_;
}
else
{
lean_object* v_a_1259_; lean_object* v_a_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_a_1259_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1259_);
v_a_1260_ = lean_ctor_get(v___x_1249_, 1);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1249_, 2);
v___x_1261_ = l_System_FilePath_normalize(v_buildDir_1241_);
v___x_1262_ = l_Lake_joinRelative(v_dir_1205_, v___x_1261_);
v___x_1263_ = l_System_FilePath_normalize(v_nativeLibDir_1242_);
v___x_1264_ = l_Lake_joinRelative(v___x_1262_, v___x_1263_);
v___x_1265_ = l_Lake_LeanLib_libName(v_self_1206_);
v___x_1266_ = 0;
v___x_1267_ = l_Lake_nameToStaticLib(v___x_1265_, v___x_1266_);
v___x_1268_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_1269_ = l_System_FilePath_addExtension(v___x_1267_, v___x_1268_);
v___x_1270_ = l_Lake_joinRelative(v___x_1264_, v___x_1269_);
v___y_1216_ = v_a_1259_;
v___y_1217_ = v_a_1260_;
v___y_1218_ = v___x_1247_;
v___y_1219_ = v_bootstrap_1240_;
v___y_1220_ = v_a_1236_;
v___y_1221_ = v___x_1270_;
goto v___jp_1215_;
}
}
else
{
lean_object* v_a_1271_; lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref(v_nativeLibDir_1242_);
lean_dec_ref(v_buildDir_1241_);
lean_dec_ref(v_a_1236_);
lean_dec_ref(v___y_1208_);
lean_dec_ref(v_self_1206_);
lean_dec_ref(v_dir_1205_);
lean_dec(v___x_1204_);
lean_dec_ref(v___x_1203_);
lean_dec(v___x_1196_);
v_a_1271_ = lean_ctor_get(v___x_1249_, 0);
v_a_1272_ = lean_ctor_get(v___x_1249_, 1);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1249_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_inc(v_a_1271_);
lean_dec(v___x_1249_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1271_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed(lean_object** _args){
lean_object* v___x_1323_ = _args[0];
lean_object* v___x_1324_ = _args[1];
lean_object* v_config_1325_ = _args[2];
lean_object* v_config_1326_ = _args[3];
lean_object* v___x_1327_ = _args[4];
lean_object* v___f_1328_ = _args[5];
lean_object* v_shouldExport_1329_ = _args[6];
lean_object* v___x_1330_ = _args[7];
lean_object* v___x_1331_ = _args[8];
lean_object* v___x_1332_ = _args[9];
lean_object* v_dir_1333_ = _args[10];
lean_object* v_self_1334_ = _args[11];
lean_object* v___f_1335_ = _args[12];
lean_object* v___y_1336_ = _args[13];
lean_object* v___y_1337_ = _args[14];
lean_object* v___y_1338_ = _args[15];
lean_object* v___y_1339_ = _args[16];
lean_object* v___y_1340_ = _args[17];
lean_object* v___y_1341_ = _args[18];
lean_object* v___y_1342_ = _args[19];
_start:
{
uint8_t v_shouldExport_boxed_1343_; uint8_t v___x_188497__boxed_1344_; lean_object* v_res_1345_; 
v_shouldExport_boxed_1343_ = lean_unbox(v_shouldExport_1329_);
v___x_188497__boxed_1344_ = lean_unbox(v___x_1330_);
v_res_1345_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(v___x_1323_, v___x_1324_, v_config_1325_, v_config_1326_, v___x_1327_, v___f_1328_, v_shouldExport_boxed_1343_, v___x_188497__boxed_1344_, v___x_1331_, v___x_1332_, v_dir_1333_, v_self_1334_, v___f_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v_config_1326_);
return v_res_1345_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0(void){
_start:
{
uint8_t v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = 2;
v___x_1347_ = l_Lake_Verbosity_ctorIdx(v___x_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object* v_self_1351_, uint8_t v_shouldExport_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v___x_1360_; lean_object* v_toApplicative_1361_; lean_object* v_toBind_1362_; lean_object* v_toFunctor_1363_; lean_object* v_toPure_1364_; lean_object* v___f_1365_; lean_object* v___f_1366_; lean_object* v___f_1367_; lean_object* v___f_1368_; lean_object* v___x_1369_; lean_object* v___f_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_toBuildConfig_1378_; lean_object* v_registeredJobs_1379_; uint8_t v_verbosity_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___f_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; uint8_t v___x_1387_; lean_object* v___y_1389_; 
v___x_1360_ = l_instMonadBaseIO;
v_toApplicative_1361_ = lean_ctor_get(v___x_1360_, 0);
v_toBind_1362_ = lean_ctor_get(v___x_1360_, 1);
v_toFunctor_1363_ = lean_ctor_get(v_toApplicative_1361_, 0);
v_toPure_1364_ = lean_ctor_get(v_toApplicative_1361_, 1);
lean_inc_n(v_toBind_1362_, 3);
lean_inc_n(v_toPure_1364_, 5);
v___f_1365_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1365_, 0, v_toPure_1364_);
lean_closure_set(v___f_1365_, 1, v_toBind_1362_);
v___f_1366_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1366_, 0, v_toPure_1364_);
lean_closure_set(v___f_1366_, 1, v_toBind_1362_);
lean_inc_ref(v___f_1365_);
v___f_1367_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1367_, 0, v_toPure_1364_);
lean_closure_set(v___f_1367_, 1, v___f_1365_);
lean_inc_ref_n(v_toFunctor_1363_, 2);
v___f_1368_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1368_, 0, v_toFunctor_1363_);
lean_closure_set(v___f_1368_, 1, v_toPure_1364_);
lean_closure_set(v___f_1368_, 2, v_toBind_1362_);
v___x_1369_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1363_);
v___f_1370_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1370_, 0, v_toPure_1364_);
v___x_1371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set(v___x_1371_, 1, v___f_1370_);
lean_ctor_set(v___x_1371_, 2, v___f_1368_);
lean_ctor_set(v___x_1371_, 3, v___f_1367_);
lean_ctor_set(v___x_1371_, 4, v___f_1366_);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
lean_ctor_set(v___x_1372_, 1, v___f_1365_);
v___x_1373_ = l_ReaderT_instMonad___redArg(v___x_1372_);
v___x_1374_ = l_StateRefT_x27_instMonad___redArg(v___x_1373_);
v___x_1375_ = l_ReaderT_instMonad___redArg(v___x_1374_);
v___x_1376_ = l_ReaderT_instMonad___redArg(v___x_1375_);
v___x_1377_ = l_Lake_EquipT_instMonad___redArg(v___x_1376_);
v_toBuildConfig_1378_ = lean_ctor_get(v_a_1357_, 0);
v_registeredJobs_1379_ = lean_ctor_get(v_a_1357_, 4);
v_verbosity_1380_ = lean_ctor_get_uint8(v_toBuildConfig_1378_, sizeof(void*)*4 + 4);
v___x_1381_ = l_Lake_instDataKindFilePath;
v___x_1382_ = lean_box(v_shouldExport_1352_);
lean_inc_ref(v___x_1377_);
v___f_1383_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1383_, 0, v___x_1382_);
lean_closure_set(v___f_1383_, 1, v___x_1377_);
v___x_1384_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1380_);
v___x_1385_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0);
v___x_1386_ = lean_nat_dec_eq(v___x_1384_, v___x_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = 1;
if (v___x_1386_ == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_1389_ = v___x_1435_;
goto v___jp_1388_;
}
else
{
if (v_shouldExport_1352_ == 0)
{
lean_object* v___x_1436_; 
v___x_1436_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_1389_ = v___x_1436_;
goto v___jp_1388_;
}
else
{
lean_object* v___x_1437_; 
v___x_1437_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3));
v___y_1389_ = v___x_1437_;
goto v___jp_1388_;
}
}
v___jp_1388_:
{
lean_object* v_pkg_1390_; lean_object* v_name_1391_; lean_object* v_config_1392_; lean_object* v_keyName_1393_; lean_object* v_dir_1394_; lean_object* v_config_1395_; lean_object* v___f_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___f_1404_; lean_object* v___x_1405_; 
v_pkg_1390_ = lean_ctor_get(v_self_1351_, 0);
v_name_1391_ = lean_ctor_get(v_self_1351_, 1);
lean_inc_n(v_name_1391_, 2);
v_config_1392_ = lean_ctor_get(v_self_1351_, 2);
lean_inc(v_config_1392_);
v_keyName_1393_ = lean_ctor_get(v_pkg_1390_, 2);
v_dir_1394_ = lean_ctor_get(v_pkg_1390_, 4);
lean_inc_ref(v_dir_1394_);
v_config_1395_ = lean_ctor_get(v_pkg_1390_, 6);
lean_inc_ref(v_config_1395_);
lean_inc_ref_n(v_pkg_1390_, 2);
v___f_1396_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(v___f_1396_, 0, v___x_1381_);
lean_closure_set(v___f_1396_, 1, v_pkg_1390_);
v___x_1397_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_1393_);
v___x_1398_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1398_, 0, v_keyName_1393_);
lean_ctor_set(v___x_1398_, 1, v_name_1391_);
v___x_1399_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_1351_);
v___x_1400_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1398_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
lean_ctor_set(v___x_1400_, 2, v_self_1351_);
lean_ctor_set(v___x_1400_, 3, v___x_1397_);
v___x_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1401_, 0, v_pkg_1390_);
v___x_1402_ = lean_box(v_shouldExport_1352_);
v___x_1403_ = lean_box(v___x_1387_);
lean_inc_ref(v___x_1377_);
v___f_1404_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed), 20, 13);
lean_closure_set(v___f_1404_, 0, v___x_1400_);
lean_closure_set(v___f_1404_, 1, v___x_1401_);
lean_closure_set(v___f_1404_, 2, v_config_1395_);
lean_closure_set(v___f_1404_, 3, v_config_1392_);
lean_closure_set(v___f_1404_, 4, v___x_1377_);
lean_closure_set(v___f_1404_, 5, v___f_1396_);
lean_closure_set(v___f_1404_, 6, v___x_1402_);
lean_closure_set(v___f_1404_, 7, v___x_1403_);
lean_closure_set(v___f_1404_, 8, v___x_1377_);
lean_closure_set(v___f_1404_, 9, v___x_1381_);
lean_closure_set(v___f_1404_, 10, v_dir_1394_);
lean_closure_set(v___f_1404_, 11, v_self_1351_);
lean_closure_set(v___f_1404_, 12, v___f_1383_);
v___x_1405_ = l_Lake_ensureJob___redArg(v___x_1381_, v___f_1404_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1434_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_a_1407_ = lean_ctor_get(v___x_1405_, 1);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1409_ = v___x_1405_;
v_isShared_1410_ = v_isSharedCheck_1434_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1434_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_task_1411_; lean_object* v_kind_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1432_; 
v_task_1411_ = lean_ctor_get(v_a_1406_, 0);
v_kind_1412_ = lean_ctor_get(v_a_1406_, 1);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_a_1406_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v_a_1406_, 2);
lean_dec(v_unused_1433_);
v___x_1414_ = v_a_1406_;
v_isShared_1415_ = v_isSharedCheck_1432_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_kind_1412_);
lean_inc(v_task_1411_);
lean_dec(v_a_1406_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1432_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; lean_object* v_job_1423_; 
v___x_1416_ = lean_st_ref_take(v_registeredJobs_1379_);
v___x_1417_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1391_, v___x_1387_);
v___x_1418_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___x_1419_ = lean_string_append(v___x_1417_, v___x_1418_);
v___x_1420_ = lean_string_append(v___x_1419_, v___y_1389_);
v___x_1421_ = 0;
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 2, v___x_1420_);
v_job_1423_ = v___x_1414_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_task_1411_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_kind_1412_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v___x_1420_);
v_job_1423_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
lean_ctor_set_uint8(v_job_1423_, sizeof(void*)*3, v___x_1421_);
lean_inc_ref(v_job_1423_);
v___x_1424_ = l_Lake_Job_toOpaque___redArg(v_job_1423_);
v___x_1425_ = lean_array_push(v___x_1416_, v___x_1424_);
v___x_1426_ = lean_st_ref_put(v_registeredJobs_1379_, v___x_1425_);
v___x_1427_ = l_Lake_Job_renew___redArg(v_job_1423_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1427_);
v___x_1429_ = v___x_1409_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_a_1407_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
else
{
lean_dec(v_name_1391_);
return v___x_1405_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object* v_self_1438_, lean_object* v_shouldExport_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
uint8_t v_shouldExport_boxed_1447_; lean_object* v_res_1448_; 
v_shouldExport_boxed_1447_ = lean_unbox(v_shouldExport_1439_);
v_res_1448_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1438_, v_shouldExport_boxed_1447_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec(v_a_1441_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t v_fmt_1449_, lean_object* v_a_1450_){
_start:
{
if (v_fmt_1449_ == 0)
{
return v_a_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = l_Lake_mkRelPathString(v_a_1450_);
v___x_1452_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
v___x_1453_ = l_Lean_Json_compress(v___x_1452_);
return v___x_1453_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object* v_fmt_1454_, lean_object* v_a_1455_){
_start:
{
uint8_t v_fmt_boxed_1456_; lean_object* v_res_1457_; 
v_fmt_boxed_1456_ = lean_unbox(v_fmt_1454_);
v_res_1457_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_boxed_1456_, v_a_1455_);
return v_res_1457_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2(void){
_start:
{
uint8_t v___x_1460_; lean_object* v_name_1461_; lean_object* v___x_1462_; 
v___x_1460_ = 1;
v_name_1461_ = l_Lake_instDataKindFilePath;
v___x_1462_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1461_, v___x_1460_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* v_defaultPkg_1466_, lean_object* v_self_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_){
_start:
{
uint8_t v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = 1;
lean_inc_ref_n(v_self_1467_, 2);
v___x_1476_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1466_, v_self_1467_, v_self_1467_, v___x_1475_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v_snd_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1519_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
v_snd_1478_ = lean_ctor_get(v_a_1477_, 1);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_a_1477_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v_a_1477_, 0);
lean_dec(v_unused_1520_);
v___x_1480_ = v_a_1477_;
v_isShared_1481_ = v_isSharedCheck_1519_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_snd_1478_);
lean_dec(v_a_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1519_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1517_; 
v_a_1482_ = lean_ctor_get(v___x_1476_, 1);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v___x_1476_, 0);
lean_dec(v_unused_1518_);
v___x_1484_ = v___x_1476_;
v_isShared_1485_ = v_isSharedCheck_1517_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1476_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1517_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_kind_1486_; lean_object* v_name_1487_; lean_object* v___y_1489_; uint8_t v___x_1507_; 
v_kind_1486_ = lean_ctor_get(v_snd_1478_, 1);
v_name_1487_ = l_Lake_instDataKindFilePath;
v___x_1507_ = lean_name_eq(v_kind_1486_, v_name_1487_);
if (v___x_1507_ == 0)
{
uint8_t v___x_1508_; 
lean_inc(v_kind_1486_);
lean_del_object(v___x_1480_);
lean_dec(v_snd_1478_);
v___x_1508_ = l_Lean_Name_isAnonymous(v_kind_1486_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1509_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1510_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1486_, v___x_1475_);
v___x_1511_ = lean_string_append(v___x_1509_, v___x_1510_);
lean_dec_ref(v___x_1510_);
v___x_1512_ = lean_string_append(v___x_1511_, v___x_1509_);
v___y_1489_ = v___x_1512_;
goto v___jp_1488_;
}
else
{
lean_object* v___x_1513_; 
lean_dec(v_kind_1486_);
v___x_1513_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1489_ = v___x_1513_;
goto v___jp_1488_;
}
}
else
{
lean_object* v___x_1515_; 
lean_del_object(v___x_1484_);
lean_dec_ref(v_self_1467_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 1, v_a_1482_);
lean_ctor_set(v___x_1480_, 0, v_snd_1478_);
v___x_1515_ = v___x_1480_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_snd_1478_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_a_1482_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
v___jp_1488_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1490_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1491_ = l_Lake_PartialBuildKey_toString(v_self_1467_);
v___x_1492_ = lean_string_append(v___x_1490_, v___x_1491_);
lean_dec_ref(v___x_1491_);
v___x_1493_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1494_ = lean_string_append(v___x_1492_, v___x_1493_);
v___x_1495_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
v___x_1496_ = lean_string_append(v___x_1494_, v___x_1495_);
v___x_1497_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1498_ = lean_string_append(v___x_1496_, v___x_1497_);
v___x_1499_ = lean_string_append(v___x_1498_, v___y_1489_);
lean_dec_ref(v___y_1489_);
v___x_1500_ = 3;
v___x_1501_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1501_, 0, v___x_1499_);
lean_ctor_set_uint8(v___x_1501_, sizeof(void*)*1, v___x_1500_);
v___x_1502_ = lean_array_get_size(v_a_1482_);
v___x_1503_ = lean_array_push(v_a_1482_, v___x_1501_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set_tag(v___x_1484_, 1);
lean_ctor_set(v___x_1484_, 1, v___x_1503_);
lean_ctor_set(v___x_1484_, 0, v___x_1502_);
v___x_1505_ = v___x_1484_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec_ref(v_self_1467_);
v_a_1521_ = lean_ctor_get(v___x_1476_, 0);
v_a_1522_ = lean_ctor_get(v___x_1476_, 1);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1476_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_inc(v_a_1521_);
lean_dec(v___x_1476_);
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
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* v_defaultPkg_1530_, lean_object* v_self_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1530_, v_self_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec(v_a_1533_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* v___x_1540_, size_t v_sz_1541_, size_t v_i_1542_, lean_object* v_bs_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
uint8_t v___x_1551_; 
v___x_1551_ = lean_usize_dec_lt(v_i_1542_, v_sz_1541_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_dec_ref(v___y_1544_);
lean_dec_ref(v___x_1540_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v_bs_1543_);
lean_ctor_set(v___x_1552_, 1, v___y_1549_);
return v___x_1552_;
}
else
{
lean_object* v_v_1553_; lean_object* v___x_1554_; 
v_v_1553_ = lean_array_uget_borrowed(v_bs_1543_, v_i_1542_);
lean_inc_ref(v___y_1544_);
lean_inc(v_v_1553_);
lean_inc_ref(v___x_1540_);
v___x_1554_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1540_, v_v_1553_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v_a_1556_; lean_object* v___x_1557_; lean_object* v_bs_x27_1558_; size_t v___x_1559_; size_t v___x_1560_; lean_object* v___x_1561_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
v_a_1556_ = lean_ctor_get(v___x_1554_, 1);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1554_, 2);
v___x_1557_ = lean_unsigned_to_nat(0u);
v_bs_x27_1558_ = lean_array_uset(v_bs_1543_, v_i_1542_, v___x_1557_);
v___x_1559_ = ((size_t)1ULL);
v___x_1560_ = lean_usize_add(v_i_1542_, v___x_1559_);
v___x_1561_ = lean_array_uset(v_bs_x27_1558_, v_i_1542_, v_a_1555_);
v_i_1542_ = v___x_1560_;
v_bs_1543_ = v___x_1561_;
v___y_1549_ = v_a_1556_;
goto _start;
}
else
{
lean_object* v_a_1563_; lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref(v___y_1544_);
lean_dec_ref(v_bs_1543_);
lean_dec_ref(v___x_1540_);
v_a_1563_ = lean_ctor_get(v___x_1554_, 0);
v_a_1564_ = lean_ctor_get(v___x_1554_, 1);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1554_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_inc(v_a_1563_);
lean_dec(v___x_1554_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1563_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* v___x_1572_, lean_object* v_sz_1573_, lean_object* v_i_1574_, lean_object* v_bs_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
size_t v_sz_boxed_1583_; size_t v_i_boxed_1584_; lean_object* v_res_1585_; 
v_sz_boxed_1583_ = lean_unbox_usize(v_sz_1573_);
lean_dec(v_sz_1573_);
v_i_boxed_1584_ = lean_unbox_usize(v_i_1574_);
lean_dec(v_i_1574_);
v_res_1585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1572_, v_sz_boxed_1583_, v_i_boxed_1584_, v_bs_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec(v___y_1577_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(lean_object* v_a_1586_, lean_object* v_as_1587_, size_t v_i_1588_, size_t v_stop_1589_, lean_object* v_b_1590_, lean_object* v___y_1591_){
_start:
{
uint8_t v___x_1593_; 
v___x_1593_ = lean_usize_dec_eq(v_i_1588_, v_stop_1589_);
if (v___x_1593_ == 0)
{
lean_object* v_log_1594_; uint8_t v_action_1595_; uint8_t v_wantsRebuild_1596_; lean_object* v_trace_1597_; lean_object* v_buildTime_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_log_1594_ = lean_ctor_get(v___y_1591_, 0);
v_action_1595_ = lean_ctor_get_uint8(v___y_1591_, sizeof(void*)*3);
v_wantsRebuild_1596_ = lean_ctor_get_uint8(v___y_1591_, sizeof(void*)*3 + 1);
v_trace_1597_ = lean_ctor_get(v___y_1591_, 1);
v_buildTime_1598_ = lean_ctor_get(v___y_1591_, 2);
v___x_1599_ = lean_array_uget_borrowed(v_as_1587_, v_i_1588_);
v___x_1600_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
lean_inc(v___x_1599_);
v___x_1601_ = lean_string_append(v___x_1599_, v___x_1600_);
v___x_1602_ = lean_io_prim_handle_put_str(v_a_1586_, v___x_1601_);
lean_dec_ref(v___x_1601_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; size_t v___x_1604_; size_t v___x_1605_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
lean_dec_ref_known(v___x_1602_, 1);
v___x_1604_ = ((size_t)1ULL);
v___x_1605_ = lean_usize_add(v_i_1588_, v___x_1604_);
v_i_1588_ = v___x_1605_;
v_b_1590_ = v_a_1603_;
goto _start;
}
else
{
lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1620_; 
lean_inc(v_buildTime_1598_);
lean_inc_ref(v_trace_1597_);
lean_inc_ref(v_log_1594_);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___y_1591_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; lean_object* v_unused_1622_; lean_object* v_unused_1623_; 
v_unused_1621_ = lean_ctor_get(v___y_1591_, 2);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v___y_1591_, 1);
lean_dec(v_unused_1622_);
v_unused_1623_ = lean_ctor_get(v___y_1591_, 0);
lean_dec(v_unused_1623_);
v___x_1608_ = v___y_1591_;
v_isShared_1609_ = v_isSharedCheck_1620_;
goto v_resetjp_1607_;
}
else
{
lean_dec(v___y_1591_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1620_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v_a_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
v_a_1610_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1610_);
lean_dec_ref_known(v___x_1602_, 1);
v___x_1611_ = lean_io_error_to_string(v_a_1610_);
v___x_1612_ = 3;
v___x_1613_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*1, v___x_1612_);
v___x_1614_ = lean_array_get_size(v_log_1594_);
v___x_1615_ = lean_array_push(v_log_1594_, v___x_1613_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v___x_1615_);
v___x_1617_ = v___x_1608_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_trace_1597_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_buildTime_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1619_, sizeof(void*)*3, v_action_1595_);
lean_ctor_set_uint8(v_reuseFailAlloc_1619_, sizeof(void*)*3 + 1, v_wantsRebuild_1596_);
v___x_1617_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1614_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
return v___x_1618_;
}
}
}
}
else
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v_b_1590_);
lean_ctor_set(v___x_1624_, 1, v___y_1591_);
return v___x_1624_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(lean_object* v_a_1625_, lean_object* v_as_1626_, lean_object* v_i_1627_, lean_object* v_stop_1628_, lean_object* v_b_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
size_t v_i_boxed_1632_; size_t v_stop_boxed_1633_; lean_object* v_res_1634_; 
v_i_boxed_1632_ = lean_unbox_usize(v_i_1627_);
lean_dec(v_i_1627_);
v_stop_boxed_1633_ = lean_unbox_usize(v_stop_1628_);
lean_dec(v_stop_1628_);
v_res_1634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1625_, v_as_1626_, v_i_boxed_1632_, v_stop_boxed_1633_, v_b_1629_, v___y_1630_);
lean_dec_ref(v_as_1626_);
lean_dec(v_a_1625_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(uint8_t v_bootstrap_1635_, lean_object* v___y_1636_, lean_object* v_oFiles_1637_, uint8_t v_shouldExport_1638_, uint8_t v___x_1639_, size_t v___x_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
if (v_bootstrap_1635_ == 0)
{
lean_object* v_toContext_1648_; lean_object* v_lakeEnv_1649_; lean_object* v_lean_1650_; lean_object* v_log_1651_; uint8_t v_action_1652_; uint8_t v_wantsRebuild_1653_; lean_object* v_trace_1654_; lean_object* v_buildTime_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1685_; 
v_toContext_1648_ = lean_ctor_get(v___y_1645_, 1);
v_lakeEnv_1649_ = lean_ctor_get(v_toContext_1648_, 0);
v_lean_1650_ = lean_ctor_get(v_lakeEnv_1649_, 1);
v_log_1651_ = lean_ctor_get(v___y_1646_, 0);
v_action_1652_ = lean_ctor_get_uint8(v___y_1646_, sizeof(void*)*3);
v_wantsRebuild_1653_ = lean_ctor_get_uint8(v___y_1646_, sizeof(void*)*3 + 1);
v_trace_1654_ = lean_ctor_get(v___y_1646_, 1);
v_buildTime_1655_ = lean_ctor_get(v___y_1646_, 2);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___y_1646_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1657_ = v___y_1646_;
v_isShared_1658_ = v_isSharedCheck_1685_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_buildTime_1655_);
lean_inc(v_trace_1654_);
lean_inc(v_log_1651_);
lean_dec(v___y_1646_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1685_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v_ar_1659_; lean_object* v___x_1660_; 
v_ar_1659_ = lean_ctor_get(v_lean_1650_, 13);
lean_inc_ref(v_ar_1659_);
v___x_1660_ = l_Lake_compileStaticLib(v___y_1636_, v_oFiles_1637_, v_ar_1659_, v_bootstrap_1635_, v_log_1651_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1672_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_a_1662_ = lean_ctor_get(v___x_1660_, 1);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1664_ = v___x_1660_;
v_isShared_1665_ = v_isSharedCheck_1672_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1672_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v_a_1662_);
v___x_1667_ = v___x_1657_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1662_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_trace_1654_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_buildTime_1655_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*3, v_action_1652_);
lean_ctor_set_uint8(v_reuseFailAlloc_1671_, sizeof(void*)*3 + 1, v_wantsRebuild_1653_);
v___x_1667_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1669_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 1, v___x_1667_);
v___x_1669_ = v___x_1664_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1661_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_a_1673_; lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1684_; 
v_a_1673_ = lean_ctor_get(v___x_1660_, 0);
v_a_1674_ = lean_ctor_get(v___x_1660_, 1);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1676_ = v___x_1660_;
v_isShared_1677_ = v_isSharedCheck_1684_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_inc(v_a_1673_);
lean_dec(v___x_1660_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1684_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v_a_1674_);
v___x_1679_ = v___x_1657_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1674_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_trace_1654_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_buildTime_1655_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*3, v_action_1652_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*3 + 1, v_wantsRebuild_1653_);
v___x_1679_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1681_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v___x_1679_);
v___x_1681_ = v___x_1676_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1673_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
}
else
{
uint8_t v___x_1686_; 
v___x_1686_ = l_System_Platform_isOSX;
if (v___x_1686_ == 0)
{
uint8_t v___x_1687_; 
v___x_1687_ = l_System_Platform_isWindows;
if (v___x_1687_ == 0)
{
lean_object* v_toContext_1688_; lean_object* v_lakeEnv_1689_; lean_object* v_lean_1690_; lean_object* v_log_1691_; uint8_t v_action_1692_; uint8_t v_wantsRebuild_1693_; lean_object* v_trace_1694_; lean_object* v_buildTime_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1725_; 
v_toContext_1688_ = lean_ctor_get(v___y_1645_, 1);
v_lakeEnv_1689_ = lean_ctor_get(v_toContext_1688_, 0);
v_lean_1690_ = lean_ctor_get(v_lakeEnv_1689_, 1);
v_log_1691_ = lean_ctor_get(v___y_1646_, 0);
v_action_1692_ = lean_ctor_get_uint8(v___y_1646_, sizeof(void*)*3);
v_wantsRebuild_1693_ = lean_ctor_get_uint8(v___y_1646_, sizeof(void*)*3 + 1);
v_trace_1694_ = lean_ctor_get(v___y_1646_, 1);
v_buildTime_1695_ = lean_ctor_get(v___y_1646_, 2);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___y_1646_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1697_ = v___y_1646_;
v_isShared_1698_ = v_isSharedCheck_1725_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_buildTime_1695_);
lean_inc(v_trace_1694_);
lean_inc(v_log_1691_);
lean_dec(v___y_1646_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1725_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v_ar_1699_; lean_object* v___x_1700_; 
v_ar_1699_ = lean_ctor_get(v_lean_1690_, 13);
lean_inc_ref(v_ar_1699_);
v___x_1700_ = l_Lake_compileStaticLib(v___y_1636_, v_oFiles_1637_, v_ar_1699_, v___x_1687_, v_log_1691_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1712_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_a_1702_ = lean_ctor_get(v___x_1700_, 1);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1704_ = v___x_1700_;
v_isShared_1705_ = v_isSharedCheck_1712_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1712_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v_a_1702_);
v___x_1707_ = v___x_1697_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1702_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_trace_1694_);
lean_ctor_set(v_reuseFailAlloc_1711_, 2, v_buildTime_1695_);
lean_ctor_set_uint8(v_reuseFailAlloc_1711_, sizeof(void*)*3, v_action_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1711_, sizeof(void*)*3 + 1, v_wantsRebuild_1693_);
v___x_1707_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1709_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v___x_1707_);
v___x_1709_ = v___x_1704_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1701_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1724_; 
v_a_1713_ = lean_ctor_get(v___x_1700_, 0);
v_a_1714_ = lean_ctor_get(v___x_1700_, 1);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1716_ = v___x_1700_;
v_isShared_1717_ = v_isSharedCheck_1724_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_inc(v_a_1713_);
lean_dec(v___x_1700_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1724_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 0, v_a_1714_);
v___x_1719_ = v___x_1697_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1714_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_trace_1694_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_buildTime_1695_);
lean_ctor_set_uint8(v_reuseFailAlloc_1723_, sizeof(void*)*3, v_action_1692_);
lean_ctor_set_uint8(v_reuseFailAlloc_1723_, sizeof(void*)*3 + 1, v_wantsRebuild_1693_);
v___x_1719_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1721_; 
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 1, v___x_1719_);
v___x_1721_ = v___x_1716_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1713_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1726_; lean_object* v_lakeEnv_1727_; lean_object* v_lean_1728_; lean_object* v_log_1729_; uint8_t v_action_1730_; uint8_t v_wantsRebuild_1731_; lean_object* v_trace_1732_; lean_object* v_buildTime_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1763_; 
v_toContext_1726_ = lean_ctor_get(v___y_1645_, 1);
v_lakeEnv_1727_ = lean_ctor_get(v_toContext_1726_, 0);
v_lean_1728_ = lean_ctor_get(v_lakeEnv_1727_, 1);
v_log_1729_ = lean_ctor_get(v___y_1646_, 0);
v_action_1730_ = lean_ctor_get_uint8(v___y_1646_, sizeof(void*)*3);
v_wantsRebuild_1731_ = lean_ctor_get_uint8(v___y_1646_, sizeof(void*)*3 + 1);
v_trace_1732_ = lean_ctor_get(v___y_1646_, 1);
v_buildTime_1733_ = lean_ctor_get(v___y_1646_, 2);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___y_1646_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1735_ = v___y_1646_;
v_isShared_1736_ = v_isSharedCheck_1763_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_buildTime_1733_);
lean_inc(v_trace_1732_);
lean_inc(v_log_1729_);
lean_dec(v___y_1646_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1763_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v_ar_1737_; lean_object* v___x_1738_; 
v_ar_1737_ = lean_ctor_get(v_lean_1728_, 13);
lean_inc_ref(v_ar_1737_);
v___x_1738_ = l_Lake_compileStaticLib(v___y_1636_, v_oFiles_1637_, v_ar_1737_, v_shouldExport_1638_, v_log_1729_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1750_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_a_1740_ = lean_ctor_get(v___x_1738_, 1);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1742_ = v___x_1738_;
v_isShared_1743_ = v_isSharedCheck_1750_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1750_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v_a_1740_);
v___x_1745_ = v___x_1735_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1740_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_trace_1732_);
lean_ctor_set(v_reuseFailAlloc_1749_, 2, v_buildTime_1733_);
lean_ctor_set_uint8(v_reuseFailAlloc_1749_, sizeof(void*)*3, v_action_1730_);
lean_ctor_set_uint8(v_reuseFailAlloc_1749_, sizeof(void*)*3 + 1, v_wantsRebuild_1731_);
v___x_1745_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1747_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v___x_1745_);
v___x_1747_ = v___x_1742_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1739_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v_a_1751_; lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1762_; 
v_a_1751_ = lean_ctor_get(v___x_1738_, 0);
v_a_1752_ = lean_ctor_get(v___x_1738_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1754_ = v___x_1738_;
v_isShared_1755_ = v_isSharedCheck_1762_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_inc(v_a_1751_);
lean_dec(v___x_1738_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1762_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v_a_1752_);
v___x_1757_ = v___x_1735_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1752_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_trace_1732_);
lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_buildTime_1733_);
lean_ctor_set_uint8(v_reuseFailAlloc_1761_, sizeof(void*)*3, v_action_1730_);
lean_ctor_set_uint8(v_reuseFailAlloc_1761_, sizeof(void*)*3 + 1, v_wantsRebuild_1731_);
v___x_1757_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1759_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 1, v___x_1757_);
v___x_1759_ = v___x_1754_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1751_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1764_; uint8_t v_action_1765_; uint8_t v_wantsRebuild_1766_; lean_object* v_trace_1767_; lean_object* v_buildTime_1768_; lean_object* v___x_1769_; 
v_log_1764_ = lean_ctor_get(v___y_1646_, 0);
v_action_1765_ = lean_ctor_get_uint8(v___y_1646_, sizeof(void*)*3);
v_wantsRebuild_1766_ = lean_ctor_get_uint8(v___y_1646_, sizeof(void*)*3 + 1);
v_trace_1767_ = lean_ctor_get(v___y_1646_, 1);
v_buildTime_1768_ = lean_ctor_get(v___y_1646_, 2);
lean_inc_ref(v___y_1636_);
v___x_1769_ = l_Lake_createParentDirs(v___y_1636_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v_a_1773_; uint8_t v___x_1821_; lean_object* v___x_1822_; 
lean_dec_ref_known(v___x_1769_, 1);
v___x_1770_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1636_);
v___x_1771_ = l_System_FilePath_addExtension(v___y_1636_, v___x_1770_);
v___x_1821_ = 1;
v___x_1822_ = lean_io_prim_handle_mk(v___x_1771_, v___x_1821_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1822_, 1);
v___x_1824_ = lean_unsigned_to_nat(0u);
v___x_1825_ = lean_array_get_size(v_oFiles_1637_);
v___x_1826_ = lean_nat_dec_lt(v___x_1824_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_dec(v_a_1823_);
lean_dec_ref(v_oFiles_1637_);
v_a_1773_ = v___y_1646_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1827_; size_t v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = lean_box(0);
v___x_1828_ = lean_usize_of_nat(v___x_1825_);
v___x_1829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1823_, v_oFiles_1637_, v___x_1640_, v___x_1828_, v___x_1827_, v___y_1646_);
lean_dec_ref(v_oFiles_1637_);
lean_dec(v_a_1823_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 1);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1829_, 2);
v_a_1773_ = v_a_1830_;
goto v___jp_1772_;
}
else
{
lean_dec_ref(v___x_1771_);
lean_dec_ref(v___y_1636_);
return v___x_1829_;
}
}
}
else
{
lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1844_; 
lean_inc(v_buildTime_1768_);
lean_inc_ref(v_trace_1767_);
lean_inc_ref(v_log_1764_);
lean_dec_ref(v___x_1771_);
lean_dec_ref(v_oFiles_1637_);
lean_dec_ref(v___y_1636_);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___y_1646_);
if (v_isSharedCheck_1844_ == 0)
{
lean_object* v_unused_1845_; lean_object* v_unused_1846_; lean_object* v_unused_1847_; 
v_unused_1845_ = lean_ctor_get(v___y_1646_, 2);
lean_dec(v_unused_1845_);
v_unused_1846_ = lean_ctor_get(v___y_1646_, 1);
lean_dec(v_unused_1846_);
v_unused_1847_ = lean_ctor_get(v___y_1646_, 0);
lean_dec(v_unused_1847_);
v___x_1832_ = v___y_1646_;
v_isShared_1833_ = v_isSharedCheck_1844_;
goto v_resetjp_1831_;
}
else
{
lean_dec(v___y_1646_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1844_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_a_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
v_a_1834_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1822_, 1);
v___x_1835_ = lean_io_error_to_string(v_a_1834_);
v___x_1836_ = 3;
v___x_1837_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1837_, 0, v___x_1835_);
lean_ctor_set_uint8(v___x_1837_, sizeof(void*)*1, v___x_1836_);
v___x_1838_ = lean_array_get_size(v_log_1764_);
v___x_1839_ = lean_array_push(v_log_1764_, v___x_1837_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1839_);
v___x_1841_ = v___x_1832_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_trace_1767_);
lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_buildTime_1768_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, sizeof(void*)*3, v_action_1765_);
lean_ctor_set_uint8(v_reuseFailAlloc_1843_, sizeof(void*)*3 + 1, v_wantsRebuild_1766_);
v___x_1841_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1838_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
return v___x_1842_;
}
}
}
v___jp_1772_:
{
lean_object* v___x_1774_; lean_object* v_log_1775_; uint8_t v_action_1776_; uint8_t v_wantsRebuild_1777_; lean_object* v_trace_1778_; lean_object* v_buildTime_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1820_; 
v___x_1774_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1775_ = lean_ctor_get(v_a_1773_, 0);
v_action_1776_ = lean_ctor_get_uint8(v_a_1773_, sizeof(void*)*3);
v_wantsRebuild_1777_ = lean_ctor_get_uint8(v_a_1773_, sizeof(void*)*3 + 1);
v_trace_1778_ = lean_ctor_get(v_a_1773_, 1);
v_buildTime_1779_ = lean_ctor_get(v_a_1773_, 2);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_a_1773_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1781_ = v_a_1773_;
v_isShared_1782_ = v_isSharedCheck_1820_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_buildTime_1779_);
lean_inc(v_trace_1778_);
lean_inc(v_log_1775_);
lean_dec(v_a_1773_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1820_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1783_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1784_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1785_ = lean_unsigned_to_nat(5u);
v___x_1786_ = lean_mk_empty_array_with_capacity(v___x_1785_);
lean_dec_ref(v___x_1786_);
v___x_1787_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1788_ = lean_array_push(v___x_1787_, v___y_1636_);
v___x_1789_ = lean_array_push(v___x_1788_, v___x_1784_);
v___x_1790_ = lean_array_push(v___x_1789_, v___x_1771_);
v___x_1791_ = lean_box(0);
v___x_1792_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1793_ = 0;
v___x_1794_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1794_, 0, v___x_1774_);
lean_ctor_set(v___x_1794_, 1, v___x_1783_);
lean_ctor_set(v___x_1794_, 2, v___x_1790_);
lean_ctor_set(v___x_1794_, 3, v___x_1791_);
lean_ctor_set(v___x_1794_, 4, v___x_1792_);
lean_ctor_set_uint8(v___x_1794_, sizeof(void*)*5, v___x_1639_);
lean_ctor_set_uint8(v___x_1794_, sizeof(void*)*5 + 1, v___x_1793_);
v___x_1795_ = l_Lake_proc(v___x_1794_, v___x_1793_, v___x_1791_, v_log_1775_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1807_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
v_a_1797_ = lean_ctor_get(v___x_1795_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1799_ = v___x_1795_;
v_isShared_1800_ = v_isSharedCheck_1807_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_inc(v_a_1796_);
lean_dec(v___x_1795_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1807_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v_a_1797_);
v___x_1802_ = v___x_1781_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1797_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_trace_1778_);
lean_ctor_set(v_reuseFailAlloc_1806_, 2, v_buildTime_1779_);
lean_ctor_set_uint8(v_reuseFailAlloc_1806_, sizeof(void*)*3, v_action_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1806_, sizeof(void*)*3 + 1, v_wantsRebuild_1777_);
v___x_1802_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1804_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v___x_1802_);
v___x_1804_ = v___x_1799_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1796_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
else
{
lean_object* v_a_1808_; lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1819_; 
v_a_1808_ = lean_ctor_get(v___x_1795_, 0);
v_a_1809_ = lean_ctor_get(v___x_1795_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1795_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1811_ = v___x_1795_;
v_isShared_1812_ = v_isSharedCheck_1819_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_inc(v_a_1808_);
lean_dec(v___x_1795_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1819_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v_a_1809_);
v___x_1814_ = v___x_1781_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1809_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_trace_1778_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_buildTime_1779_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*3, v_action_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*3 + 1, v_wantsRebuild_1777_);
v___x_1814_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1816_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 1, v___x_1814_);
v___x_1816_ = v___x_1811_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1808_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1861_; 
lean_inc(v_buildTime_1768_);
lean_inc_ref(v_trace_1767_);
lean_inc_ref(v_log_1764_);
lean_dec_ref(v_oFiles_1637_);
lean_dec_ref(v___y_1636_);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___y_1646_);
if (v_isSharedCheck_1861_ == 0)
{
lean_object* v_unused_1862_; lean_object* v_unused_1863_; lean_object* v_unused_1864_; 
v_unused_1862_ = lean_ctor_get(v___y_1646_, 2);
lean_dec(v_unused_1862_);
v_unused_1863_ = lean_ctor_get(v___y_1646_, 1);
lean_dec(v_unused_1863_);
v_unused_1864_ = lean_ctor_get(v___y_1646_, 0);
lean_dec(v_unused_1864_);
v___x_1849_ = v___y_1646_;
v_isShared_1850_ = v_isSharedCheck_1861_;
goto v_resetjp_1848_;
}
else
{
lean_dec(v___y_1646_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1861_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v_a_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1858_; 
v_a_1851_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1769_, 1);
v___x_1852_ = lean_io_error_to_string(v_a_1851_);
v___x_1853_ = 3;
v___x_1854_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set_uint8(v___x_1854_, sizeof(void*)*1, v___x_1853_);
v___x_1855_ = lean_array_get_size(v_log_1764_);
v___x_1856_ = lean_array_push(v_log_1764_, v___x_1854_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1856_);
v___x_1858_ = v___x_1849_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_trace_1767_);
lean_ctor_set(v_reuseFailAlloc_1860_, 2, v_buildTime_1768_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*3, v_action_1765_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*3 + 1, v_wantsRebuild_1766_);
v___x_1858_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1855_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
return v___x_1859_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object* v_bootstrap_1865_, lean_object* v___y_1866_, lean_object* v_oFiles_1867_, lean_object* v_shouldExport_1868_, lean_object* v___x_1869_, lean_object* v___x_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
uint8_t v_bootstrap_boxed_1878_; uint8_t v_shouldExport_boxed_1879_; uint8_t v___x_5803__boxed_1880_; size_t v___x_5804__boxed_1881_; lean_object* v_res_1882_; 
v_bootstrap_boxed_1878_ = lean_unbox(v_bootstrap_1865_);
v_shouldExport_boxed_1879_ = lean_unbox(v_shouldExport_1868_);
v___x_5803__boxed_1880_ = lean_unbox(v___x_1869_);
v___x_5804__boxed_1881_ = lean_unbox_usize(v___x_1870_);
lean_dec(v___x_1870_);
v_res_1882_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_boxed_1878_, v___y_1866_, v_oFiles_1867_, v_shouldExport_boxed_1879_, v___x_5803__boxed_1880_, v___x_5804__boxed_1881_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t v_bootstrap_1883_, lean_object* v___y_1884_, uint8_t v_shouldExport_1885_, uint8_t v___x_1886_, size_t v___x_1887_, lean_object* v_oFiles_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___y_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1896_ = lean_box(v_bootstrap_1883_);
v___x_1897_ = lean_box(v_shouldExport_1885_);
v___x_1898_ = lean_box(v___x_1886_);
v___x_1899_ = lean_box_usize(v___x_1887_);
lean_inc_ref(v___y_1884_);
v___y_1900_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed), 13, 6);
lean_closure_set(v___y_1900_, 0, v___x_1896_);
lean_closure_set(v___y_1900_, 1, v___y_1884_);
lean_closure_set(v___y_1900_, 2, v_oFiles_1888_);
lean_closure_set(v___y_1900_, 3, v___x_1897_);
lean_closure_set(v___y_1900_, 4, v___x_1898_);
lean_closure_set(v___y_1900_, 5, v___x_1899_);
v___x_1901_ = 0;
v___x_1902_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1903_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1884_, v___y_1900_, v___x_1901_, v___x_1902_, v___x_1886_, v___x_1901_, v___x_1901_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1913_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
v_a_1905_ = lean_ctor_get(v___x_1903_, 1);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1907_ = v___x_1903_;
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_inc(v_a_1904_);
lean_dec(v___x_1903_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_path_1909_; lean_object* v___x_1911_; 
v_path_1909_ = lean_ctor_get(v_a_1904_, 1);
lean_inc_ref(v_path_1909_);
lean_dec(v_a_1904_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v_path_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_path_1909_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_a_1905_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1914_ = lean_ctor_get(v___x_1903_, 0);
v_a_1915_ = lean_ctor_get(v___x_1903_, 1);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1903_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_inc(v_a_1914_);
lean_dec(v___x_1903_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1914_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* v_bootstrap_1923_, lean_object* v___y_1924_, lean_object* v_shouldExport_1925_, lean_object* v___x_1926_, lean_object* v___x_1927_, lean_object* v_oFiles_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
uint8_t v_bootstrap_boxed_1936_; uint8_t v_shouldExport_boxed_1937_; uint8_t v___x_6203__boxed_1938_; size_t v___x_6204__boxed_1939_; lean_object* v_res_1940_; 
v_bootstrap_boxed_1936_ = lean_unbox(v_bootstrap_1923_);
v_shouldExport_boxed_1937_ = lean_unbox(v_shouldExport_1925_);
v___x_6203__boxed_1938_ = lean_unbox(v___x_1926_);
v___x_6204__boxed_1939_ = lean_unbox_usize(v___x_1927_);
lean_dec(v___x_1927_);
v_res_1940_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_boxed_1936_, v___y_1924_, v_shouldExport_boxed_1937_, v___x_6203__boxed_1938_, v___x_6204__boxed_1939_, v_oFiles_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec(v___y_1930_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* v_a_1941_, size_t v_sz_1942_, size_t v_i_1943_, lean_object* v_bs_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
uint8_t v___x_1952_; 
v___x_1952_ = lean_usize_dec_lt(v_i_1943_, v_sz_1942_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; 
lean_dec_ref(v___y_1945_);
lean_dec_ref(v_a_1941_);
v___x_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1953_, 0, v_bs_1944_);
lean_ctor_set(v___x_1953_, 1, v___y_1950_);
return v___x_1953_;
}
else
{
lean_object* v_v_1954_; lean_object* v___x_1955_; 
v_v_1954_ = lean_array_uget_borrowed(v_bs_1944_, v_i_1943_);
lean_inc_ref(v___y_1945_);
lean_inc_ref(v_a_1941_);
lean_inc(v_v_1954_);
v___x_1955_ = l_Lake_ModuleFacet_fetch___redArg(v_v_1954_, v_a_1941_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v_a_1957_; lean_object* v___x_1958_; lean_object* v_bs_x27_1959_; size_t v___x_1960_; size_t v___x_1961_; lean_object* v___x_1962_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
v_a_1957_ = lean_ctor_get(v___x_1955_, 1);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1955_, 2);
v___x_1958_ = lean_unsigned_to_nat(0u);
v_bs_x27_1959_ = lean_array_uset(v_bs_1944_, v_i_1943_, v___x_1958_);
v___x_1960_ = ((size_t)1ULL);
v___x_1961_ = lean_usize_add(v_i_1943_, v___x_1960_);
v___x_1962_ = lean_array_uset(v_bs_x27_1959_, v_i_1943_, v_a_1956_);
v_i_1943_ = v___x_1961_;
v_bs_1944_ = v___x_1962_;
v___y_1950_ = v_a_1957_;
goto _start;
}
else
{
lean_object* v_a_1964_; lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec_ref(v___y_1945_);
lean_dec_ref(v_bs_1944_);
lean_dec_ref(v_a_1941_);
v_a_1964_ = lean_ctor_get(v___x_1955_, 0);
v_a_1965_ = lean_ctor_get(v___x_1955_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1955_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_inc(v_a_1964_);
lean_dec(v___x_1955_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1964_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object* v_a_1973_, lean_object* v_sz_1974_, lean_object* v_i_1975_, lean_object* v_bs_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
size_t v_sz_boxed_1984_; size_t v_i_boxed_1985_; lean_object* v_res_1986_; 
v_sz_boxed_1984_ = lean_unbox_usize(v_sz_1974_);
lean_dec(v_sz_1974_);
v_i_boxed_1985_ = lean_unbox_usize(v_i_1975_);
lean_dec(v_i_1975_);
v_res_1986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_1973_, v_sz_boxed_1984_, v_i_boxed_1985_, v_bs_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec(v___y_1978_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(uint8_t v_shouldExport_1987_, lean_object* v_as_1988_, size_t v_i_1989_, size_t v_stop_1990_, lean_object* v_b_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_usize_dec_eq(v_i_1989_, v_stop_1990_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; lean_object* v_lib_2001_; lean_object* v_config_2002_; lean_object* v_nativeFacets_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; size_t v_sz_2006_; size_t v___x_2007_; lean_object* v___x_2008_; 
v___x_2000_ = lean_array_uget_borrowed(v_as_1988_, v_i_1989_);
v_lib_2001_ = lean_ctor_get(v___x_2000_, 0);
v_config_2002_ = lean_ctor_get(v_lib_2001_, 2);
v_nativeFacets_2003_ = lean_ctor_get(v_config_2002_, 8);
v___x_2004_ = lean_box(v_shouldExport_1987_);
lean_inc_ref(v_nativeFacets_2003_);
v___x_2005_ = lean_apply_1(v_nativeFacets_2003_, v___x_2004_);
v_sz_2006_ = lean_array_size(v___x_2005_);
v___x_2007_ = ((size_t)0ULL);
lean_inc_ref(v___y_1992_);
lean_inc(v___x_2000_);
v___x_2008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2000_, v_sz_2006_, v___x_2007_, v___x_2005_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v_a_2010_; lean_object* v___x_2011_; size_t v___x_2012_; size_t v___x_2013_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
v_a_2010_ = lean_ctor_get(v___x_2008_, 1);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2008_, 2);
v___x_2011_ = l_Array_append___redArg(v_b_1991_, v_a_2009_);
lean_dec(v_a_2009_);
v___x_2012_ = ((size_t)1ULL);
v___x_2013_ = lean_usize_add(v_i_1989_, v___x_2012_);
v_i_1989_ = v___x_2013_;
v_b_1991_ = v___x_2011_;
v___y_1997_ = v_a_2010_;
goto _start;
}
else
{
lean_dec_ref(v___y_1992_);
lean_dec_ref(v_b_1991_);
return v___x_2008_;
}
}
else
{
lean_object* v___x_2015_; 
lean_dec_ref(v___y_1992_);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v_b_1991_);
lean_ctor_set(v___x_2015_, 1, v___y_1997_);
return v___x_2015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(lean_object* v_shouldExport_2016_, lean_object* v_as_2017_, lean_object* v_i_2018_, lean_object* v_stop_2019_, lean_object* v_b_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
uint8_t v_shouldExport_boxed_2028_; size_t v_i_boxed_2029_; size_t v_stop_boxed_2030_; lean_object* v_res_2031_; 
v_shouldExport_boxed_2028_ = lean_unbox(v_shouldExport_2016_);
v_i_boxed_2029_ = lean_unbox_usize(v_i_2018_);
lean_dec(v_i_2018_);
v_stop_boxed_2030_ = lean_unbox_usize(v_stop_2019_);
lean_dec(v_stop_2019_);
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_boxed_2028_, v_as_2017_, v_i_boxed_2029_, v_stop_boxed_2030_, v_b_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v_as_2017_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object* v___x_2032_, lean_object* v___x_2033_, lean_object* v_config_2034_, lean_object* v_config_2035_, lean_object* v_pkg_2036_, uint8_t v_shouldExport_2037_, uint8_t v___x_2038_, lean_object* v___x_2039_, lean_object* v_dir_2040_, lean_object* v_self_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
size_t v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v_a_2070_; lean_object* v_a_2071_; lean_object* v___x_2113_; 
lean_inc_ref(v___y_2042_);
lean_inc_ref(v___y_2046_);
lean_inc(v___y_2045_);
lean_inc(v___y_2044_);
lean_inc(v___x_2033_);
v___x_2113_ = lean_apply_7(v___y_2042_, v___x_2032_, v___x_2033_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, lean_box(0));
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v_a_2115_; lean_object* v___x_2116_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
v_a_2115_ = lean_ctor_get(v___x_2113_, 1);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2113_, 2);
v___x_2116_ = l_Lake_Job_await___redArg(v_a_2114_, v_a_2115_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v_a_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
v_a_2118_ = lean_ctor_get(v___x_2116_, 1);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2116_, 2);
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2120_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_2121_ = lean_array_get_size(v_a_2117_);
v___x_2122_ = lean_nat_dec_lt(v___x_2119_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_dec(v_a_2117_);
v_a_2070_ = v___x_2120_;
v_a_2071_ = v_a_2118_;
goto v___jp_2069_;
}
else
{
size_t v___x_2123_; size_t v___x_2124_; lean_object* v___x_2125_; 
v___x_2123_ = ((size_t)0ULL);
v___x_2124_ = lean_usize_of_nat(v___x_2121_);
lean_inc_ref(v___y_2042_);
v___x_2125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2037_, v_a_2117_, v___x_2123_, v___x_2124_, v___x_2120_, v___y_2042_, v___x_2033_, v___y_2044_, v___y_2045_, v___y_2046_, v_a_2118_);
lean_dec(v_a_2117_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v_a_2127_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
v_a_2127_ = lean_ctor_get(v___x_2125_, 1);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2125_, 2);
v_a_2070_ = v_a_2126_;
v_a_2071_ = v_a_2127_;
goto v___jp_2069_;
}
else
{
lean_object* v_a_2128_; lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec_ref(v___y_2042_);
lean_dec_ref(v_self_2041_);
lean_dec_ref(v_dir_2040_);
lean_dec(v___x_2039_);
lean_dec_ref(v_pkg_2036_);
lean_dec_ref(v_config_2034_);
lean_dec(v___x_2033_);
v_a_2128_ = lean_ctor_get(v___x_2125_, 0);
v_a_2129_ = lean_ctor_get(v___x_2125_, 1);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2125_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_inc(v_a_2128_);
lean_dec(v___x_2125_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2128_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v___y_2042_);
lean_dec_ref(v_self_2041_);
lean_dec_ref(v_dir_2040_);
lean_dec(v___x_2039_);
lean_dec_ref(v_pkg_2036_);
lean_dec_ref(v_config_2034_);
lean_dec(v___x_2033_);
v_a_2137_ = lean_ctor_get(v___x_2116_, 0);
v_a_2138_ = lean_ctor_get(v___x_2116_, 1);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2116_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_inc(v_a_2137_);
lean_dec(v___x_2116_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2137_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec_ref(v___y_2042_);
lean_dec_ref(v_self_2041_);
lean_dec_ref(v_dir_2040_);
lean_dec(v___x_2039_);
lean_dec_ref(v_pkg_2036_);
lean_dec_ref(v_config_2034_);
lean_dec(v___x_2033_);
v_a_2146_ = lean_ctor_get(v___x_2113_, 0);
v_a_2147_ = lean_ctor_get(v___x_2113_, 1);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2113_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_inc(v_a_2146_);
lean_dec(v___x_2113_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2146_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
v___jp_2049_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2056_ = lean_box(v___y_2051_);
v___x_2057_ = lean_box(v_shouldExport_2037_);
v___x_2058_ = lean_box(v___x_2038_);
v___x_2059_ = lean_box_usize(v___y_2050_);
v___f_2060_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2060_, 0, v___x_2056_);
lean_closure_set(v___f_2060_, 1, v___y_2055_);
lean_closure_set(v___f_2060_, 2, v___x_2057_);
lean_closure_set(v___f_2060_, 3, v___x_2058_);
lean_closure_set(v___f_2060_, 4, v___x_2059_);
v___x_2061_ = l_Array_append___redArg(v___y_2054_, v___y_2053_);
lean_dec_ref(v___y_2053_);
v___x_2062_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_2063_ = l_Lake_Job_collectArray___redArg(v___x_2061_, v___x_2062_);
lean_dec_ref(v___x_2061_);
v___x_2064_ = lean_unsigned_to_nat(0u);
v___x_2065_ = 0;
v___x_2066_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2067_ = l_Lake_Job_mapM___redArg(v___x_2039_, v___x_2063_, v___f_2060_, v___x_2064_, v___x_2065_, v___y_2042_, v___x_2033_, v___y_2044_, v___y_2045_, v___y_2046_, v___x_2066_);
lean_dec(v___x_2033_);
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v___y_2052_);
return v___x_2068_;
}
v___jp_2069_:
{
lean_object* v_toLeanConfig_2072_; lean_object* v_toLeanConfig_2073_; uint8_t v_bootstrap_2074_; lean_object* v_buildDir_2075_; lean_object* v_nativeLibDir_2076_; lean_object* v_moreLinkObjs_2077_; lean_object* v_moreLinkObjs_2078_; lean_object* v___x_2079_; size_t v_sz_2080_; size_t v___x_2081_; lean_object* v___x_2082_; 
v_toLeanConfig_2072_ = lean_ctor_get(v_config_2034_, 1);
lean_inc_ref(v_toLeanConfig_2072_);
v_toLeanConfig_2073_ = lean_ctor_get(v_config_2035_, 0);
v_bootstrap_2074_ = lean_ctor_get_uint8(v_config_2034_, sizeof(void*)*28);
v_buildDir_2075_ = lean_ctor_get(v_config_2034_, 5);
lean_inc_ref(v_buildDir_2075_);
v_nativeLibDir_2076_ = lean_ctor_get(v_config_2034_, 7);
lean_inc_ref(v_nativeLibDir_2076_);
lean_dec_ref(v_config_2034_);
v_moreLinkObjs_2077_ = lean_ctor_get(v_toLeanConfig_2072_, 6);
lean_inc_ref(v_moreLinkObjs_2077_);
lean_dec_ref(v_toLeanConfig_2072_);
v_moreLinkObjs_2078_ = lean_ctor_get(v_toLeanConfig_2073_, 6);
v___x_2079_ = l_Array_append___redArg(v_moreLinkObjs_2077_, v_moreLinkObjs_2078_);
v_sz_2080_ = lean_array_size(v___x_2079_);
v___x_2081_ = ((size_t)0ULL);
lean_inc_ref(v___y_2042_);
v___x_2082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_2036_, v_sz_2080_, v___x_2081_, v___x_2079_, v___y_2042_, v___x_2033_, v___y_2044_, v___y_2045_, v___y_2046_, v_a_2071_);
if (lean_obj_tag(v___x_2082_) == 0)
{
if (v_shouldExport_2037_ == 0)
{
lean_object* v_a_2083_; lean_object* v_a_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
v_a_2084_ = lean_ctor_get(v___x_2082_, 1);
lean_inc(v_a_2084_);
lean_dec_ref_known(v___x_2082_, 2);
v___x_2085_ = l_System_FilePath_normalize(v_buildDir_2075_);
v___x_2086_ = l_Lake_joinRelative(v_dir_2040_, v___x_2085_);
v___x_2087_ = l_System_FilePath_normalize(v_nativeLibDir_2076_);
v___x_2088_ = l_Lake_joinRelative(v___x_2086_, v___x_2087_);
v___x_2089_ = l_Lake_LeanLib_libName(v_self_2041_);
v___x_2090_ = l_Lake_nameToStaticLib(v___x_2089_, v_shouldExport_2037_);
v___x_2091_ = l_Lake_joinRelative(v___x_2088_, v___x_2090_);
v___y_2050_ = v___x_2081_;
v___y_2051_ = v_bootstrap_2074_;
v___y_2052_ = v_a_2084_;
v___y_2053_ = v_a_2083_;
v___y_2054_ = v_a_2070_;
v___y_2055_ = v___x_2091_;
goto v___jp_2049_;
}
else
{
lean_object* v_a_2092_; lean_object* v_a_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v_a_2092_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2092_);
v_a_2093_ = lean_ctor_get(v___x_2082_, 1);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2082_, 2);
v___x_2094_ = l_System_FilePath_normalize(v_buildDir_2075_);
v___x_2095_ = l_Lake_joinRelative(v_dir_2040_, v___x_2094_);
v___x_2096_ = l_System_FilePath_normalize(v_nativeLibDir_2076_);
v___x_2097_ = l_Lake_joinRelative(v___x_2095_, v___x_2096_);
v___x_2098_ = l_Lake_LeanLib_libName(v_self_2041_);
v___x_2099_ = 0;
v___x_2100_ = l_Lake_nameToStaticLib(v___x_2098_, v___x_2099_);
v___x_2101_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_2102_ = l_System_FilePath_addExtension(v___x_2100_, v___x_2101_);
v___x_2103_ = l_Lake_joinRelative(v___x_2097_, v___x_2102_);
v___y_2050_ = v___x_2081_;
v___y_2051_ = v_bootstrap_2074_;
v___y_2052_ = v_a_2093_;
v___y_2053_ = v_a_2092_;
v___y_2054_ = v_a_2070_;
v___y_2055_ = v___x_2103_;
goto v___jp_2049_;
}
}
else
{
lean_object* v_a_2104_; lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec_ref(v_nativeLibDir_2076_);
lean_dec_ref(v_buildDir_2075_);
lean_dec_ref(v_a_2070_);
lean_dec_ref(v___y_2042_);
lean_dec_ref(v_self_2041_);
lean_dec_ref(v_dir_2040_);
lean_dec(v___x_2039_);
lean_dec(v___x_2033_);
v_a_2104_ = lean_ctor_get(v___x_2082_, 0);
v_a_2105_ = lean_ctor_get(v___x_2082_, 1);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2082_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_inc(v_a_2104_);
lean_dec(v___x_2082_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2104_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(lean_object** _args){
lean_object* v___x_2155_ = _args[0];
lean_object* v___x_2156_ = _args[1];
lean_object* v_config_2157_ = _args[2];
lean_object* v_config_2158_ = _args[3];
lean_object* v_pkg_2159_ = _args[4];
lean_object* v_shouldExport_2160_ = _args[5];
lean_object* v___x_2161_ = _args[6];
lean_object* v___x_2162_ = _args[7];
lean_object* v_dir_2163_ = _args[8];
lean_object* v_self_2164_ = _args[9];
lean_object* v___y_2165_ = _args[10];
lean_object* v___y_2166_ = _args[11];
lean_object* v___y_2167_ = _args[12];
lean_object* v___y_2168_ = _args[13];
lean_object* v___y_2169_ = _args[14];
lean_object* v___y_2170_ = _args[15];
lean_object* v___y_2171_ = _args[16];
_start:
{
uint8_t v_shouldExport_boxed_2172_; uint8_t v___x_6405__boxed_2173_; lean_object* v_res_2174_; 
v_shouldExport_boxed_2172_ = lean_unbox(v_shouldExport_2160_);
v___x_6405__boxed_2173_ = lean_unbox(v___x_2161_);
v_res_2174_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v___x_2155_, v___x_2156_, v_config_2157_, v_config_2158_, v_pkg_2159_, v_shouldExport_boxed_2172_, v___x_6405__boxed_2173_, v___x_2162_, v_dir_2163_, v_self_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec(v_config_2158_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object* v___y_2175_, lean_object* v_self_2176_, uint8_t v_shouldExport_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_){
_start:
{
lean_object* v_toBuildConfig_2184_; lean_object* v_registeredJobs_2185_; uint8_t v_verbosity_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; uint8_t v___x_2191_; lean_object* v___y_2193_; 
v_toBuildConfig_2184_ = lean_ctor_get(v_a_2181_, 0);
v_registeredJobs_2185_ = lean_ctor_get(v_a_2181_, 4);
v_verbosity_2186_ = lean_ctor_get_uint8(v_toBuildConfig_2184_, sizeof(void*)*4 + 4);
v___x_2187_ = l_Lake_instDataKindFilePath;
v___x_2188_ = l_Lake_Verbosity_ctorIdx(v_verbosity_2186_);
v___x_2189_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0);
v___x_2190_ = lean_nat_dec_eq(v___x_2188_, v___x_2189_);
lean_dec(v___x_2188_);
v___x_2191_ = 1;
if (v___x_2190_ == 0)
{
lean_object* v___x_2238_; 
v___x_2238_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_2193_ = v___x_2238_;
goto v___jp_2192_;
}
else
{
if (v_shouldExport_2177_ == 0)
{
lean_object* v___x_2239_; 
v___x_2239_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_2193_ = v___x_2239_;
goto v___jp_2192_;
}
else
{
lean_object* v___x_2240_; 
v___x_2240_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3));
v___y_2193_ = v___x_2240_;
goto v___jp_2192_;
}
}
v___jp_2192_:
{
lean_object* v_pkg_2194_; lean_object* v_name_2195_; lean_object* v_config_2196_; lean_object* v_keyName_2197_; lean_object* v_dir_2198_; lean_object* v_config_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___f_2207_; lean_object* v___x_2208_; 
v_pkg_2194_ = lean_ctor_get(v_self_2176_, 0);
lean_inc_ref_n(v_pkg_2194_, 2);
v_name_2195_ = lean_ctor_get(v_self_2176_, 1);
lean_inc_n(v_name_2195_, 2);
v_config_2196_ = lean_ctor_get(v_self_2176_, 2);
lean_inc(v_config_2196_);
v_keyName_2197_ = lean_ctor_get(v_pkg_2194_, 2);
v_dir_2198_ = lean_ctor_get(v_pkg_2194_, 4);
lean_inc_ref(v_dir_2198_);
v_config_2199_ = lean_ctor_get(v_pkg_2194_, 6);
lean_inc_ref(v_config_2199_);
v___x_2200_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_2197_);
v___x_2201_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_keyName_2197_);
lean_ctor_set(v___x_2201_, 1, v_name_2195_);
v___x_2202_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_2176_);
v___x_2203_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2201_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
lean_ctor_set(v___x_2203_, 2, v_self_2176_);
lean_ctor_set(v___x_2203_, 3, v___x_2200_);
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v_pkg_2194_);
v___x_2205_ = lean_box(v_shouldExport_2177_);
v___x_2206_ = lean_box(v___x_2191_);
v___f_2207_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed), 17, 10);
lean_closure_set(v___f_2207_, 0, v___x_2203_);
lean_closure_set(v___f_2207_, 1, v___x_2204_);
lean_closure_set(v___f_2207_, 2, v_config_2199_);
lean_closure_set(v___f_2207_, 3, v_config_2196_);
lean_closure_set(v___f_2207_, 4, v_pkg_2194_);
lean_closure_set(v___f_2207_, 5, v___x_2205_);
lean_closure_set(v___f_2207_, 6, v___x_2206_);
lean_closure_set(v___f_2207_, 7, v___x_2187_);
lean_closure_set(v___f_2207_, 8, v_dir_2198_);
lean_closure_set(v___f_2207_, 9, v_self_2176_);
v___x_2208_ = l_Lake_ensureJob___redArg(v___x_2187_, v___f_2207_, v___y_2175_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2237_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
v_a_2210_ = lean_ctor_get(v___x_2208_, 1);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2212_ = v___x_2208_;
v_isShared_2213_ = v_isSharedCheck_2237_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_inc(v_a_2209_);
lean_dec(v___x_2208_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2237_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v_task_2214_; lean_object* v_kind_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2235_; 
v_task_2214_ = lean_ctor_get(v_a_2209_, 0);
v_kind_2215_ = lean_ctor_get(v_a_2209_, 1);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_a_2209_);
if (v_isSharedCheck_2235_ == 0)
{
lean_object* v_unused_2236_; 
v_unused_2236_ = lean_ctor_get(v_a_2209_, 2);
lean_dec(v_unused_2236_);
v___x_2217_ = v_a_2209_;
v_isShared_2218_ = v_isSharedCheck_2235_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_kind_2215_);
lean_inc(v_task_2214_);
lean_dec(v_a_2209_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2235_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; lean_object* v_job_2226_; 
v___x_2219_ = lean_st_ref_take(v_registeredJobs_2185_);
v___x_2220_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2195_, v___x_2191_);
v___x_2221_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___x_2222_ = lean_string_append(v___x_2220_, v___x_2221_);
v___x_2223_ = lean_string_append(v___x_2222_, v___y_2193_);
v___x_2224_ = 0;
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 2, v___x_2223_);
v_job_2226_ = v___x_2217_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_task_2214_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_kind_2215_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v___x_2223_);
v_job_2226_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
lean_ctor_set_uint8(v_job_2226_, sizeof(void*)*3, v___x_2224_);
lean_inc_ref(v_job_2226_);
v___x_2227_ = l_Lake_Job_toOpaque___redArg(v_job_2226_);
v___x_2228_ = lean_array_push(v___x_2219_, v___x_2227_);
v___x_2229_ = lean_st_ref_put(v_registeredJobs_2185_, v___x_2228_);
v___x_2230_ = l_Lake_Job_renew___redArg(v_job_2226_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2230_);
v___x_2232_ = v___x_2212_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v_a_2210_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
else
{
lean_dec(v_name_2195_);
return v___x_2208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* v___y_2241_, lean_object* v_self_2242_, lean_object* v_shouldExport_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
uint8_t v_shouldExport_boxed_2250_; lean_object* v_res_2251_; 
v_shouldExport_boxed_2250_ = lean_unbox(v_shouldExport_2243_);
v_res_2251_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2241_, v_self_2242_, v_shouldExport_boxed_2250_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec(v_a_2244_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* v_x_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
uint8_t v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = 0;
v___x_2261_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2253_, v_x_2252_, v___x_2260_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object* v_x_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec(v___y_2264_);
return v_res_2270_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2273_; uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___f_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___f_2273_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2274_ = 1;
v___x_2275_ = l_Lake_instDataKindFilePath;
v___f_2276_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__0));
v___x_2277_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2278_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v___f_2276_);
lean_ctor_set(v___x_2278_, 2, v___x_2275_);
lean_ctor_set(v___x_2278_, 3, v___f_2273_);
lean_ctor_set_uint8(v___x_2278_, sizeof(void*)*4, v___x_2274_);
lean_ctor_set_uint8(v___x_2278_, sizeof(void*)*4 + 1, v___x_2274_);
return v___x_2278_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_obj_once(&l_Lake_LeanLib_staticFacetConfig___closed__2, &l_Lake_LeanLib_staticFacetConfig___closed__2_once, _init_l_Lake_LeanLib_staticFacetConfig___closed__2);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(lean_object* v_a_2280_, lean_object* v_as_2281_, size_t v_i_2282_, size_t v_stop_2283_, lean_object* v_b_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2280_, v_as_2281_, v_i_2282_, v_stop_2283_, v_b_2284_, v___y_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* v_a_2293_, lean_object* v_as_2294_, lean_object* v_i_2295_, lean_object* v_stop_2296_, lean_object* v_b_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
size_t v_i_boxed_2305_; size_t v_stop_boxed_2306_; lean_object* v_res_2307_; 
v_i_boxed_2305_ = lean_unbox_usize(v_i_2295_);
lean_dec(v_i_2295_);
v_stop_boxed_2306_ = lean_unbox_usize(v_stop_2296_);
lean_dec(v_stop_2296_);
v_res_2307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_2293_, v_as_2294_, v_i_boxed_2305_, v_stop_boxed_2306_, v_b_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec_ref(v_as_2294_);
lean_dec(v_a_2293_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* v_x_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
uint8_t v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = 1;
v___x_2317_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2309_, v_x_2308_, v___x_2316_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object* v_x_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec(v___y_2320_);
return v_res_2326_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___f_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___f_2328_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2329_ = 1;
v___x_2330_ = l_Lake_instDataKindFilePath;
v___f_2331_ = ((lean_object*)(l_Lake_LeanLib_staticExportFacetConfig___closed__0));
v___x_2332_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2333_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_ctor_set(v___x_2333_, 1, v___f_2331_);
lean_ctor_set(v___x_2333_, 2, v___x_2330_);
lean_ctor_set(v___x_2333_, 3, v___f_2328_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*4, v___x_2329_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*4 + 1, v___x_2329_);
return v___x_2333_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig(void){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = lean_obj_once(&l_Lake_LeanLib_staticExportFacetConfig___closed__1, &l_Lake_LeanLib_staticExportFacetConfig___closed__1_once, _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1);
return v___x_2334_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0(void){
_start:
{
uint8_t v___x_2335_; lean_object* v_name_2336_; lean_object* v___x_2337_; 
v___x_2335_ = 1;
v_name_2336_ = l_Lake_instDataKindDynlib;
v___x_2337_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2336_, v___x_2335_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object* v_defaultPkg_2338_, lean_object* v_self_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
uint8_t v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = 1;
lean_inc_ref_n(v_self_2339_, 2);
v___x_2348_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_2338_, v_self_2339_, v_self_2339_, v___x_2347_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v_snd_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2391_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
v_snd_2350_ = lean_ctor_get(v_a_2349_, 1);
v_isSharedCheck_2391_ = !lean_is_exclusive(v_a_2349_);
if (v_isSharedCheck_2391_ == 0)
{
lean_object* v_unused_2392_; 
v_unused_2392_ = lean_ctor_get(v_a_2349_, 0);
lean_dec(v_unused_2392_);
v___x_2352_ = v_a_2349_;
v_isShared_2353_ = v_isSharedCheck_2391_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_snd_2350_);
lean_dec(v_a_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2391_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2389_; 
v_a_2354_ = lean_ctor_get(v___x_2348_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2389_ == 0)
{
lean_object* v_unused_2390_; 
v_unused_2390_ = lean_ctor_get(v___x_2348_, 0);
lean_dec(v_unused_2390_);
v___x_2356_ = v___x_2348_;
v_isShared_2357_ = v_isSharedCheck_2389_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2348_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2389_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v_kind_2358_; lean_object* v_name_2359_; lean_object* v___y_2361_; uint8_t v___x_2379_; 
v_kind_2358_ = lean_ctor_get(v_snd_2350_, 1);
v_name_2359_ = l_Lake_instDataKindDynlib;
v___x_2379_ = lean_name_eq(v_kind_2358_, v_name_2359_);
if (v___x_2379_ == 0)
{
uint8_t v___x_2380_; 
lean_inc(v_kind_2358_);
lean_del_object(v___x_2352_);
lean_dec(v_snd_2350_);
v___x_2380_ = l_Lean_Name_isAnonymous(v_kind_2358_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2381_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_2382_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2358_, v___x_2347_);
v___x_2383_ = lean_string_append(v___x_2381_, v___x_2382_);
lean_dec_ref(v___x_2382_);
v___x_2384_ = lean_string_append(v___x_2383_, v___x_2381_);
v___y_2361_ = v___x_2384_;
goto v___jp_2360_;
}
else
{
lean_object* v___x_2385_; 
lean_dec(v_kind_2358_);
v___x_2385_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_2361_ = v___x_2385_;
goto v___jp_2360_;
}
}
else
{
lean_object* v___x_2387_; 
lean_del_object(v___x_2356_);
lean_dec_ref(v_self_2339_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 1, v_a_2354_);
lean_ctor_set(v___x_2352_, 0, v_snd_2350_);
v___x_2387_ = v___x_2352_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_snd_2350_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_a_2354_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
v___jp_2360_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2362_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_2363_ = l_Lake_PartialBuildKey_toString(v_self_2339_);
v___x_2364_ = lean_string_append(v___x_2362_, v___x_2363_);
lean_dec_ref(v___x_2363_);
v___x_2365_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_2366_ = lean_string_append(v___x_2364_, v___x_2365_);
v___x_2367_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0);
v___x_2368_ = lean_string_append(v___x_2366_, v___x_2367_);
v___x_2369_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_2370_ = lean_string_append(v___x_2368_, v___x_2369_);
v___x_2371_ = lean_string_append(v___x_2370_, v___y_2361_);
lean_dec_ref(v___y_2361_);
v___x_2372_ = 3;
v___x_2373_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set_uint8(v___x_2373_, sizeof(void*)*1, v___x_2372_);
v___x_2374_ = lean_array_get_size(v_a_2354_);
v___x_2375_ = lean_array_push(v_a_2354_, v___x_2373_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set_tag(v___x_2356_, 1);
lean_ctor_set(v___x_2356_, 1, v___x_2375_);
lean_ctor_set(v___x_2356_, 0, v___x_2374_);
v___x_2377_ = v___x_2356_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec_ref(v_self_2339_);
v_a_2393_ = lean_ctor_get(v___x_2348_, 0);
v_a_2394_ = lean_ctor_get(v___x_2348_, 1);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2348_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_inc(v_a_2393_);
lean_dec(v___x_2348_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2393_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* v_defaultPkg_2402_, lean_object* v_self_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_2402_, v_self_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_);
lean_dec_ref(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec(v_a_2405_);
return v_res_2411_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0));
v___x_2415_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
lean_ctor_set(v___x_2416_, 1, v___x_2414_);
return v___x_2416_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5(void){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object* v___x_2418_, lean_object* v_as_2419_, size_t v_i_2420_, size_t v_stop_2421_, lean_object* v_b_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
uint8_t v___x_2430_; 
v___x_2430_ = lean_usize_dec_eq(v_i_2420_, v_stop_2421_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2431_ = lean_array_uget_borrowed(v_as_2419_, v_i_2420_);
lean_inc_ref(v___y_2423_);
lean_inc(v___x_2431_);
lean_inc_ref(v___x_2418_);
v___x_2432_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_2418_, v___x_2431_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v_a_2434_; lean_object* v___x_2435_; size_t v___x_2436_; size_t v___x_2437_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
v_a_2434_ = lean_ctor_get(v___x_2432_, 1);
lean_inc(v_a_2434_);
lean_dec_ref_known(v___x_2432_, 2);
v___x_2435_ = lean_array_push(v_b_2422_, v_a_2433_);
v___x_2436_ = ((size_t)1ULL);
v___x_2437_ = lean_usize_add(v_i_2420_, v___x_2436_);
v_i_2420_ = v___x_2437_;
v_b_2422_ = v___x_2435_;
v___y_2428_ = v_a_2434_;
goto _start;
}
else
{
lean_object* v_a_2439_; lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec_ref(v___y_2423_);
lean_dec_ref(v_b_2422_);
lean_dec_ref(v___x_2418_);
v_a_2439_ = lean_ctor_get(v___x_2432_, 0);
v_a_2440_ = lean_ctor_get(v___x_2432_, 1);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2432_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_inc(v_a_2439_);
lean_dec(v___x_2432_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2439_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
else
{
lean_object* v___x_2448_; 
lean_dec_ref(v___y_2423_);
lean_dec_ref(v___x_2418_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v_b_2422_);
lean_ctor_set(v___x_2448_, 1, v___y_2428_);
return v___x_2448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* v___x_2449_, lean_object* v_as_2450_, lean_object* v_i_2451_, lean_object* v_stop_2452_, lean_object* v_b_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
size_t v_i_boxed_2461_; size_t v_stop_boxed_2462_; lean_object* v_res_2463_; 
v_i_boxed_2461_ = lean_unbox_usize(v_i_2451_);
lean_dec(v_i_2451_);
v_stop_boxed_2462_ = lean_unbox_usize(v_stop_2452_);
lean_dec(v_stop_2452_);
v_res_2463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_2449_, v_as_2450_, v_i_boxed_2461_, v_stop_boxed_2462_, v_b_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v_as_2450_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object* v_self_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v_toHashSet_2466_; lean_object* v_toArray_2467_; uint8_t v___x_2468_; 
v_toHashSet_2466_ = lean_ctor_get(v_self_2464_, 0);
v_toArray_2467_ = lean_ctor_get(v_self_2464_, 1);
v___x_2468_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_2466_, v_a_2465_);
if (v___x_2468_ == 0)
{
lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2478_; 
lean_inc_ref(v_toArray_2467_);
lean_inc_ref(v_toHashSet_2466_);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_self_2464_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; lean_object* v_unused_2480_; 
v_unused_2479_ = lean_ctor_get(v_self_2464_, 1);
lean_dec(v_unused_2479_);
v_unused_2480_ = lean_ctor_get(v_self_2464_, 0);
lean_dec(v_unused_2480_);
v___x_2470_ = v_self_2464_;
v_isShared_2471_ = v_isSharedCheck_2478_;
goto v_resetjp_2469_;
}
else
{
lean_dec(v_self_2464_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2478_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2472_ = lean_box(0);
lean_inc_ref(v_a_2465_);
v___x_2473_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_toHashSet_2466_, v_a_2465_, v___x_2472_);
v___x_2474_ = lean_array_push(v_toArray_2467_, v_a_2465_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 1, v___x_2474_);
lean_ctor_set(v___x_2470_, 0, v___x_2473_);
v___x_2476_ = v___x_2470_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
else
{
lean_dec_ref(v_a_2465_);
return v_self_2464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object* v_as_2481_, size_t v_i_2482_, size_t v_stop_2483_, lean_object* v_b_2484_){
_start:
{
uint8_t v___x_2485_; 
v___x_2485_ = lean_usize_dec_eq(v_i_2482_, v_stop_2483_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; size_t v___x_2488_; size_t v___x_2489_; 
v___x_2486_ = lean_array_uget_borrowed(v_as_2481_, v_i_2482_);
lean_inc(v___x_2486_);
v___x_2487_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_2484_, v___x_2486_);
v___x_2488_ = ((size_t)1ULL);
v___x_2489_ = lean_usize_add(v_i_2482_, v___x_2488_);
v_i_2482_ = v___x_2489_;
v_b_2484_ = v___x_2487_;
goto _start;
}
else
{
return v_b_2484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object* v_as_2491_, lean_object* v_i_2492_, lean_object* v_stop_2493_, lean_object* v_b_2494_){
_start:
{
size_t v_i_boxed_2495_; size_t v_stop_boxed_2496_; lean_object* v_res_2497_; 
v_i_boxed_2495_ = lean_unbox_usize(v_i_2492_);
lean_dec(v_i_2492_);
v_stop_boxed_2496_ = lean_unbox_usize(v_stop_2493_);
lean_dec(v_stop_2493_);
v_res_2497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_2491_, v_i_boxed_2495_, v_stop_boxed_2496_, v_b_2494_);
lean_dec_ref(v_as_2491_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object* v_self_2498_, lean_object* v_arr_2499_){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; 
v___x_2500_ = lean_unsigned_to_nat(0u);
v___x_2501_ = lean_array_get_size(v_arr_2499_);
v___x_2502_ = lean_nat_dec_lt(v___x_2500_, v___x_2501_);
if (v___x_2502_ == 0)
{
return v_self_2498_;
}
else
{
size_t v___x_2503_; size_t v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = ((size_t)0ULL);
v___x_2504_ = lean_usize_of_nat(v___x_2501_);
v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2499_, v___x_2503_, v___x_2504_, v_self_2498_);
return v___x_2505_;
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
lean_dec_ref_known(v___x_2530_, 2);
v___x_2533_ = l_Lake_Job_await___redArg(v_a_2531_, v_a_2532_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v_a_2535_; lean_object* v___x_2536_; size_t v___x_2537_; size_t v___x_2538_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
v_a_2535_ = lean_ctor_get(v___x_2533_, 1);
lean_inc(v_a_2535_);
lean_dec_ref_known(v___x_2533_, 2);
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
lean_dec_ref_known(v___x_2593_, 2);
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
lean_dec_ref_known(v___x_2661_, 2);
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
lean_dec_ref_known(v___x_2713_, 2);
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
lean_dec_ref_known(v___x_2793_, 2);
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
lean_object* v_a_2832_; lean_object* v_a_2833_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v_a_2843_; lean_object* v_a_2844_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v_a_2904_; lean_object* v_a_2905_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v_snd_2937_; lean_object* v_a_2938_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v_a_2960_; lean_object* v_a_2961_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___x_3000_; 
lean_inc_ref(v___y_2824_);
lean_inc_ref(v___y_2828_);
lean_inc(v___y_2827_);
lean_inc(v___y_2826_);
lean_inc(v___x_2816_);
v___x_3000_ = lean_apply_7(v___y_2824_, v___x_2815_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, lean_box(0));
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v_a_3002_; lean_object* v___x_3003_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
v_a_3002_ = lean_ctor_get(v___x_3000_, 1);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3000_, 2);
v___x_3003_ = l_Lake_Job_await___redArg(v_a_3001_, v_a_3002_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v_a_3005_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v_a_3016_; lean_object* v_a_3017_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v_a_3051_; lean_object* v_a_3052_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
v_a_3005_ = lean_ctor_get(v___x_3003_, 1);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3003_, 2);
v___x_3076_ = lean_unsigned_to_nat(0u);
v___x_3077_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_3078_ = lean_array_get_size(v_a_3004_);
v___x_3079_ = lean_nat_dec_lt(v___x_3076_, v___x_3078_);
if (v___x_3079_ == 0)
{
v_a_3051_ = v___x_3077_;
v_a_3052_ = v_a_3005_;
goto v___jp_3050_;
}
else
{
size_t v___x_3080_; size_t v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = ((size_t)0ULL);
v___x_3081_ = lean_usize_of_nat(v___x_3078_);
lean_inc_ref(v___y_2824_);
v___x_3082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3004_, v___x_3080_, v___x_3081_, v___x_3077_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_3005_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v_a_3084_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
v_a_3084_ = lean_ctor_get(v___x_3082_, 1);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3082_, 2);
v_a_3051_ = v_a_3083_;
v_a_3052_ = v_a_3084_;
goto v___jp_3050_;
}
else
{
lean_object* v_a_3085_; lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v_a_3004_);
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_config_2822_);
lean_dec(v_name_2821_);
lean_dec_ref(v_pkg_2820_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_3085_ = lean_ctor_get(v___x_3082_, 0);
v_a_3086_ = lean_ctor_get(v___x_3082_, 1);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3082_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_inc(v_a_3085_);
lean_dec(v___x_3082_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3085_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
v___jp_3006_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v___x_3018_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
v___x_3019_ = lean_array_get_size(v_a_3004_);
v___x_3020_ = lean_nat_dec_lt(v___y_3015_, v___x_3019_);
if (v___x_3020_ == 0)
{
lean_dec(v_a_3004_);
v___y_2950_ = v___y_3007_;
v___y_2951_ = v___y_3008_;
v___y_2952_ = v___y_3009_;
v___y_2953_ = v___y_3010_;
v___y_2954_ = v_a_3016_;
v___y_2955_ = v___y_3011_;
v___y_2956_ = v___y_3012_;
v___y_2957_ = v___y_3013_;
v___y_2958_ = v___y_3014_;
v___y_2959_ = v___y_3015_;
v_a_2960_ = v___x_3018_;
v_a_2961_ = v_a_3017_;
goto v___jp_2949_;
}
else
{
uint8_t v___x_3021_; 
v___x_3021_ = lean_nat_dec_le(v___x_3019_, v___x_3019_);
if (v___x_3021_ == 0)
{
if (v___x_3020_ == 0)
{
lean_dec(v_a_3004_);
v___y_2950_ = v___y_3007_;
v___y_2951_ = v___y_3008_;
v___y_2952_ = v___y_3009_;
v___y_2953_ = v___y_3010_;
v___y_2954_ = v_a_3016_;
v___y_2955_ = v___y_3011_;
v___y_2956_ = v___y_3012_;
v___y_2957_ = v___y_3013_;
v___y_2958_ = v___y_3014_;
v___y_2959_ = v___y_3015_;
v_a_2960_ = v___x_3018_;
v_a_2961_ = v_a_3017_;
goto v___jp_2949_;
}
else
{
size_t v___x_3022_; size_t v___x_3023_; lean_object* v___x_3024_; 
v___x_3022_ = ((size_t)0ULL);
v___x_3023_ = lean_usize_of_nat(v___x_3019_);
lean_inc_ref(v___y_2824_);
v___x_3024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3004_, v___x_3022_, v___x_3023_, v___x_3018_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_3017_);
lean_dec(v_a_3004_);
v___y_2985_ = v___y_3007_;
v___y_2986_ = v___y_3009_;
v___y_2987_ = v___y_3008_;
v___y_2988_ = v___y_3010_;
v___y_2989_ = v___y_3011_;
v___y_2990_ = v_a_3016_;
v___y_2991_ = v___y_3012_;
v___y_2992_ = v___y_3015_;
v___y_2993_ = v___y_3014_;
v___y_2994_ = v___y_3013_;
v___y_2995_ = v___x_3024_;
goto v___jp_2984_;
}
}
else
{
size_t v___x_3025_; size_t v___x_3026_; lean_object* v___x_3027_; 
v___x_3025_ = ((size_t)0ULL);
v___x_3026_ = lean_usize_of_nat(v___x_3019_);
lean_inc_ref(v___y_2824_);
v___x_3027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3004_, v___x_3025_, v___x_3026_, v___x_3018_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_3017_);
lean_dec(v_a_3004_);
v___y_2985_ = v___y_3007_;
v___y_2986_ = v___y_3009_;
v___y_2987_ = v___y_3008_;
v___y_2988_ = v___y_3010_;
v___y_2989_ = v___y_3011_;
v___y_2990_ = v_a_3016_;
v___y_2991_ = v___y_3012_;
v___y_2992_ = v___y_3015_;
v___y_2993_ = v___y_3014_;
v___y_2994_ = v___y_3013_;
v___y_2995_ = v___x_3027_;
goto v___jp_2984_;
}
}
}
v___jp_3028_:
{
if (lean_obj_tag(v___y_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v_a_3040_; 
v_a_3039_ = lean_ctor_get(v___y_3038_, 0);
lean_inc(v_a_3039_);
v_a_3040_ = lean_ctor_get(v___y_3038_, 1);
lean_inc(v_a_3040_);
lean_dec_ref_known(v___y_3038_, 2);
v___y_3007_ = v___y_3029_;
v___y_3008_ = v___y_3031_;
v___y_3009_ = v___y_3030_;
v___y_3010_ = v___y_3032_;
v___y_3011_ = v___y_3033_;
v___y_3012_ = v___y_3034_;
v___y_3013_ = v___y_3037_;
v___y_3014_ = v___y_3036_;
v___y_3015_ = v___y_3035_;
v_a_3016_ = v_a_3039_;
v_a_3017_ = v_a_3040_;
goto v___jp_3006_;
}
else
{
lean_object* v_a_3041_; lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec_ref(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec_ref(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec_ref(v___y_3031_);
lean_dec(v_a_3004_);
lean_dec_ref(v___y_2824_);
lean_dec(v_name_2821_);
lean_dec_ref(v_pkg_2820_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_3041_ = lean_ctor_get(v___y_3038_, 0);
v_a_3042_ = lean_ctor_get(v___y_3038_, 1);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___y_3038_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___y_3038_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_inc(v_a_3041_);
lean_dec(v___y_3038_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3041_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
v___jp_3050_:
{
lean_object* v_toLeanConfig_3053_; lean_object* v_toLeanConfig_3054_; lean_object* v_buildDir_3055_; lean_object* v_nativeLibDir_3056_; lean_object* v_moreLinkObjs_3057_; lean_object* v_moreLinkLibs_3058_; lean_object* v_moreLinkArgs_3059_; lean_object* v_weakLinkArgs_3060_; lean_object* v_moreLinkObjs_3061_; lean_object* v_moreLinkLibs_3062_; lean_object* v_moreLinkArgs_3063_; lean_object* v_weakLinkArgs_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v_toLeanConfig_3053_ = lean_ctor_get(v_config_2822_, 1);
lean_inc_ref(v_toLeanConfig_3053_);
v_toLeanConfig_3054_ = lean_ctor_get(v_config_2823_, 0);
v_buildDir_3055_ = lean_ctor_get(v_config_2822_, 5);
lean_inc_ref(v_buildDir_3055_);
v_nativeLibDir_3056_ = lean_ctor_get(v_config_2822_, 7);
lean_inc_ref(v_nativeLibDir_3056_);
lean_dec_ref(v_config_2822_);
v_moreLinkObjs_3057_ = lean_ctor_get(v_toLeanConfig_3053_, 6);
lean_inc_ref(v_moreLinkObjs_3057_);
v_moreLinkLibs_3058_ = lean_ctor_get(v_toLeanConfig_3053_, 7);
lean_inc_ref(v_moreLinkLibs_3058_);
v_moreLinkArgs_3059_ = lean_ctor_get(v_toLeanConfig_3053_, 8);
lean_inc_ref(v_moreLinkArgs_3059_);
v_weakLinkArgs_3060_ = lean_ctor_get(v_toLeanConfig_3053_, 9);
lean_inc_ref(v_weakLinkArgs_3060_);
lean_dec_ref(v_toLeanConfig_3053_);
v_moreLinkObjs_3061_ = lean_ctor_get(v_toLeanConfig_3054_, 6);
v_moreLinkLibs_3062_ = lean_ctor_get(v_toLeanConfig_3054_, 7);
v_moreLinkArgs_3063_ = lean_ctor_get(v_toLeanConfig_3054_, 8);
v_weakLinkArgs_3064_ = lean_ctor_get(v_toLeanConfig_3054_, 9);
v___x_3065_ = l_Array_append___redArg(v_moreLinkObjs_3057_, v_moreLinkObjs_3061_);
v___x_3066_ = lean_unsigned_to_nat(0u);
v___x_3067_ = lean_array_get_size(v___x_3065_);
v___x_3068_ = lean_nat_dec_lt(v___x_3066_, v___x_3067_);
if (v___x_3068_ == 0)
{
lean_dec_ref(v___x_3065_);
v___y_3007_ = v_moreLinkArgs_3063_;
v___y_3008_ = v_moreLinkLibs_3058_;
v___y_3009_ = v_moreLinkLibs_3062_;
v___y_3010_ = v_weakLinkArgs_3064_;
v___y_3011_ = v_nativeLibDir_3056_;
v___y_3012_ = v_moreLinkArgs_3059_;
v___y_3013_ = v_weakLinkArgs_3060_;
v___y_3014_ = v_buildDir_3055_;
v___y_3015_ = v___x_3066_;
v_a_3016_ = v_a_3051_;
v_a_3017_ = v_a_3052_;
goto v___jp_3006_;
}
else
{
uint8_t v___x_3069_; 
v___x_3069_ = lean_nat_dec_le(v___x_3067_, v___x_3067_);
if (v___x_3069_ == 0)
{
if (v___x_3068_ == 0)
{
lean_dec_ref(v___x_3065_);
v___y_3007_ = v_moreLinkArgs_3063_;
v___y_3008_ = v_moreLinkLibs_3058_;
v___y_3009_ = v_moreLinkLibs_3062_;
v___y_3010_ = v_weakLinkArgs_3064_;
v___y_3011_ = v_nativeLibDir_3056_;
v___y_3012_ = v_moreLinkArgs_3059_;
v___y_3013_ = v_weakLinkArgs_3060_;
v___y_3014_ = v_buildDir_3055_;
v___y_3015_ = v___x_3066_;
v_a_3016_ = v_a_3051_;
v_a_3017_ = v_a_3052_;
goto v___jp_3006_;
}
else
{
size_t v___x_3070_; size_t v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = ((size_t)0ULL);
v___x_3071_ = lean_usize_of_nat(v___x_3067_);
lean_inc_ref(v___y_2824_);
lean_inc_ref(v_pkg_2820_);
v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2820_, v___x_3065_, v___x_3070_, v___x_3071_, v_a_3051_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_3052_);
lean_dec_ref(v___x_3065_);
v___y_3029_ = v_moreLinkArgs_3063_;
v___y_3030_ = v_moreLinkLibs_3062_;
v___y_3031_ = v_moreLinkLibs_3058_;
v___y_3032_ = v_weakLinkArgs_3064_;
v___y_3033_ = v_nativeLibDir_3056_;
v___y_3034_ = v_moreLinkArgs_3059_;
v___y_3035_ = v___x_3066_;
v___y_3036_ = v_buildDir_3055_;
v___y_3037_ = v_weakLinkArgs_3060_;
v___y_3038_ = v___x_3072_;
goto v___jp_3028_;
}
}
else
{
size_t v___x_3073_; size_t v___x_3074_; lean_object* v___x_3075_; 
v___x_3073_ = ((size_t)0ULL);
v___x_3074_ = lean_usize_of_nat(v___x_3067_);
lean_inc_ref(v___y_2824_);
lean_inc_ref(v_pkg_2820_);
v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2820_, v___x_3065_, v___x_3073_, v___x_3074_, v_a_3051_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_3052_);
lean_dec_ref(v___x_3065_);
v___y_3029_ = v_moreLinkArgs_3063_;
v___y_3030_ = v_moreLinkLibs_3062_;
v___y_3031_ = v_moreLinkLibs_3058_;
v___y_3032_ = v_weakLinkArgs_3064_;
v___y_3033_ = v_nativeLibDir_3056_;
v___y_3034_ = v_moreLinkArgs_3059_;
v___y_3035_ = v___x_3066_;
v___y_3036_ = v_buildDir_3055_;
v___y_3037_ = v_weakLinkArgs_3060_;
v___y_3038_ = v___x_3075_;
goto v___jp_3028_;
}
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_config_2822_);
lean_dec(v_name_2821_);
lean_dec_ref(v_pkg_2820_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_3094_ = lean_ctor_get(v___x_3003_, 0);
v_a_3095_ = lean_ctor_get(v___x_3003_, 1);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3003_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_inc(v_a_3094_);
lean_dec(v___x_3003_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3094_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_config_2822_);
lean_dec(v_name_2821_);
lean_dec_ref(v_pkg_2820_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_3103_ = lean_ctor_get(v___x_3000_, 0);
v_a_3104_ = lean_ctor_get(v___x_3000_, 1);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3000_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_inc(v_a_3103_);
lean_dec(v___x_3000_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3103_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
v___jp_2831_:
{
lean_object* v___x_2834_; 
v___x_2834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2834_, 0, v_a_2832_);
lean_ctor_set(v___x_2834_, 1, v_a_2833_);
return v___x_2834_;
}
v___jp_2835_:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; uint8_t v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
lean_inc_ref(v_self_2817_);
v___x_2845_ = l_Lake_LeanLib_libName(v_self_2817_);
v___x_2846_ = l_System_FilePath_normalize(v___y_2842_);
v___x_2847_ = l_Lake_joinRelative(v_dir_2818_, v___x_2846_);
v___x_2848_ = l_System_FilePath_normalize(v___y_2839_);
v___x_2849_ = l_Lake_joinRelative(v___x_2847_, v___x_2848_);
v___x_2850_ = 0;
v___x_2851_ = l_Lake_nameToSharedLib(v___x_2845_, v___x_2850_);
v___x_2852_ = l_Lake_joinRelative(v___x_2849_, v___x_2851_);
v___x_2853_ = l_Array_append___redArg(v___y_2841_, v___y_2837_);
v___x_2854_ = l_Array_append___redArg(v___y_2840_, v___y_2836_);
v___x_2855_ = l_Lake_LeanLib_isPlugin(v_self_2817_);
v___x_2856_ = l_System_Platform_isWindows;
v___x_2857_ = lean_box(0);
v___x_2858_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2859_ = l_Lake_buildLeanSharedLib(v___x_2845_, v___x_2852_, v___y_2838_, v_a_2843_, v___x_2853_, v___x_2854_, v___x_2855_, v___x_2856_, v___x_2857_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v___x_2858_);
lean_dec(v___x_2816_);
lean_dec_ref(v___y_2838_);
v___x_2860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
lean_ctor_set(v___x_2860_, 1, v_a_2844_);
return v___x_2860_;
}
v___jp_2861_:
{
if (lean_obj_tag(v___y_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v_a_2871_; 
v_a_2870_ = lean_ctor_get(v___y_2869_, 0);
lean_inc(v_a_2870_);
v_a_2871_ = lean_ctor_get(v___y_2869_, 1);
lean_inc(v_a_2871_);
lean_dec_ref_known(v___y_2869_, 2);
v___y_2836_ = v___y_2862_;
v___y_2837_ = v___y_2863_;
v___y_2838_ = v___y_2865_;
v___y_2839_ = v___y_2864_;
v___y_2840_ = v___y_2866_;
v___y_2841_ = v___y_2868_;
v___y_2842_ = v___y_2867_;
v_a_2843_ = v_a_2870_;
v_a_2844_ = v_a_2871_;
goto v___jp_2835_;
}
else
{
lean_object* v_a_2872_; lean_object* v_a_2873_; 
lean_dec_ref(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec_ref(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_2872_ = lean_ctor_get(v___y_2869_, 0);
lean_inc(v_a_2872_);
v_a_2873_ = lean_ctor_get(v___y_2869_, 1);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___y_2869_, 2);
v_a_2832_ = v_a_2872_;
v_a_2833_ = v_a_2873_;
goto v___jp_2831_;
}
}
v___jp_2874_:
{
lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = lean_array_get_size(v___y_2885_);
v___x_2887_ = lean_nat_dec_lt(v___y_2882_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_dec_ref(v___y_2885_);
v___y_2836_ = v___y_2875_;
v___y_2837_ = v___y_2877_;
v___y_2838_ = v___y_2879_;
v___y_2839_ = v___y_2878_;
v___y_2840_ = v___y_2880_;
v___y_2841_ = v___y_2884_;
v___y_2842_ = v___y_2883_;
v_a_2843_ = v___y_2881_;
v_a_2844_ = v___y_2876_;
goto v___jp_2835_;
}
else
{
uint8_t v___x_2888_; 
v___x_2888_ = lean_nat_dec_le(v___x_2886_, v___x_2886_);
if (v___x_2888_ == 0)
{
if (v___x_2887_ == 0)
{
lean_dec_ref(v___y_2885_);
v___y_2836_ = v___y_2875_;
v___y_2837_ = v___y_2877_;
v___y_2838_ = v___y_2879_;
v___y_2839_ = v___y_2878_;
v___y_2840_ = v___y_2880_;
v___y_2841_ = v___y_2884_;
v___y_2842_ = v___y_2883_;
v_a_2843_ = v___y_2881_;
v_a_2844_ = v___y_2876_;
goto v___jp_2835_;
}
else
{
size_t v___x_2889_; size_t v___x_2890_; lean_object* v___x_2891_; 
v___x_2889_ = ((size_t)0ULL);
v___x_2890_ = lean_usize_of_nat(v___x_2886_);
lean_inc_ref(v___y_2824_);
v___x_2891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2885_, v___x_2889_, v___x_2890_, v___y_2881_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2876_);
lean_dec_ref(v___y_2885_);
v___y_2862_ = v___y_2875_;
v___y_2863_ = v___y_2877_;
v___y_2864_ = v___y_2878_;
v___y_2865_ = v___y_2879_;
v___y_2866_ = v___y_2880_;
v___y_2867_ = v___y_2883_;
v___y_2868_ = v___y_2884_;
v___y_2869_ = v___x_2891_;
goto v___jp_2861_;
}
}
else
{
size_t v___x_2892_; size_t v___x_2893_; lean_object* v___x_2894_; 
v___x_2892_ = ((size_t)0ULL);
v___x_2893_ = lean_usize_of_nat(v___x_2886_);
lean_inc_ref(v___y_2824_);
v___x_2894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2885_, v___x_2892_, v___x_2893_, v___y_2881_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2876_);
lean_dec_ref(v___y_2885_);
v___y_2862_ = v___y_2875_;
v___y_2863_ = v___y_2877_;
v___y_2864_ = v___y_2878_;
v___y_2865_ = v___y_2879_;
v___y_2866_ = v___y_2880_;
v___y_2867_ = v___y_2883_;
v___y_2868_ = v___y_2884_;
v___y_2869_ = v___x_2894_;
goto v___jp_2861_;
}
}
}
v___jp_2895_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; 
v___x_2906_ = lean_mk_empty_array_with_capacity(v___y_2903_);
v___x_2907_ = lean_array_get_size(v_targetDecls_2819_);
v___x_2908_ = lean_nat_dec_lt(v___y_2903_, v___x_2907_);
if (v___x_2908_ == 0)
{
lean_dec_ref(v_pkg_2820_);
v___y_2875_ = v___y_2896_;
v___y_2876_ = v_a_2905_;
v___y_2877_ = v___y_2897_;
v___y_2878_ = v___y_2899_;
v___y_2879_ = v___y_2898_;
v___y_2880_ = v___y_2900_;
v___y_2881_ = v_a_2904_;
v___y_2882_ = v___y_2903_;
v___y_2883_ = v___y_2902_;
v___y_2884_ = v___y_2901_;
v___y_2885_ = v___x_2906_;
goto v___jp_2874_;
}
else
{
size_t v___x_2909_; size_t v___x_2910_; lean_object* v___x_2911_; 
v___x_2909_ = ((size_t)0ULL);
v___x_2910_ = lean_usize_of_nat(v___x_2907_);
v___x_2911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2820_, v_targetDecls_2819_, v___x_2909_, v___x_2910_, v___x_2906_);
v___y_2875_ = v___y_2896_;
v___y_2876_ = v_a_2905_;
v___y_2877_ = v___y_2897_;
v___y_2878_ = v___y_2899_;
v___y_2879_ = v___y_2898_;
v___y_2880_ = v___y_2900_;
v___y_2881_ = v_a_2904_;
v___y_2882_ = v___y_2903_;
v___y_2883_ = v___y_2902_;
v___y_2884_ = v___y_2901_;
v___y_2885_ = v___x_2911_;
goto v___jp_2874_;
}
}
v___jp_2912_:
{
if (lean_obj_tag(v___y_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v_a_2923_; 
v_a_2922_ = lean_ctor_get(v___y_2921_, 0);
lean_inc(v_a_2922_);
v_a_2923_ = lean_ctor_get(v___y_2921_, 1);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___y_2921_, 2);
v___y_2896_ = v___y_2913_;
v___y_2897_ = v___y_2914_;
v___y_2898_ = v___y_2916_;
v___y_2899_ = v___y_2915_;
v___y_2900_ = v___y_2917_;
v___y_2901_ = v___y_2920_;
v___y_2902_ = v___y_2919_;
v___y_2903_ = v___y_2918_;
v_a_2904_ = v_a_2922_;
v_a_2905_ = v_a_2923_;
goto v___jp_2895_;
}
else
{
lean_object* v_a_2924_; lean_object* v_a_2925_; 
lean_dec_ref(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec_ref(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_pkg_2820_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_2924_ = lean_ctor_get(v___y_2921_, 0);
lean_inc(v_a_2924_);
v_a_2925_ = lean_ctor_get(v___y_2921_, 1);
lean_inc(v_a_2925_);
lean_dec_ref_known(v___y_2921_, 2);
v_a_2832_ = v_a_2924_;
v_a_2833_ = v_a_2925_;
goto v___jp_2831_;
}
}
v___jp_2926_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2939_ = l_Array_append___redArg(v___y_2929_, v___y_2928_);
v___x_2940_ = lean_array_get_size(v___x_2939_);
v___x_2941_ = lean_nat_dec_lt(v___y_2934_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_dec_ref(v___x_2939_);
v___y_2896_ = v___y_2927_;
v___y_2897_ = v___y_2930_;
v___y_2898_ = v___y_2932_;
v___y_2899_ = v___y_2931_;
v___y_2900_ = v___y_2933_;
v___y_2901_ = v___y_2936_;
v___y_2902_ = v___y_2935_;
v___y_2903_ = v___y_2934_;
v_a_2904_ = v_snd_2937_;
v_a_2905_ = v_a_2938_;
goto v___jp_2895_;
}
else
{
uint8_t v___x_2942_; 
v___x_2942_ = lean_nat_dec_le(v___x_2940_, v___x_2940_);
if (v___x_2942_ == 0)
{
if (v___x_2941_ == 0)
{
lean_dec_ref(v___x_2939_);
v___y_2896_ = v___y_2927_;
v___y_2897_ = v___y_2930_;
v___y_2898_ = v___y_2932_;
v___y_2899_ = v___y_2931_;
v___y_2900_ = v___y_2933_;
v___y_2901_ = v___y_2936_;
v___y_2902_ = v___y_2935_;
v___y_2903_ = v___y_2934_;
v_a_2904_ = v_snd_2937_;
v_a_2905_ = v_a_2938_;
goto v___jp_2895_;
}
else
{
size_t v___x_2943_; size_t v___x_2944_; lean_object* v___x_2945_; 
v___x_2943_ = ((size_t)0ULL);
v___x_2944_ = lean_usize_of_nat(v___x_2940_);
lean_inc_ref(v___y_2824_);
lean_inc_ref(v_pkg_2820_);
v___x_2945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2820_, v___x_2939_, v___x_2943_, v___x_2944_, v_snd_2937_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_2938_);
lean_dec_ref(v___x_2939_);
v___y_2913_ = v___y_2927_;
v___y_2914_ = v___y_2930_;
v___y_2915_ = v___y_2931_;
v___y_2916_ = v___y_2932_;
v___y_2917_ = v___y_2933_;
v___y_2918_ = v___y_2934_;
v___y_2919_ = v___y_2935_;
v___y_2920_ = v___y_2936_;
v___y_2921_ = v___x_2945_;
goto v___jp_2912_;
}
}
else
{
size_t v___x_2946_; size_t v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = ((size_t)0ULL);
v___x_2947_ = lean_usize_of_nat(v___x_2940_);
lean_inc_ref(v___y_2824_);
lean_inc_ref(v_pkg_2820_);
v___x_2948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2820_, v___x_2939_, v___x_2946_, v___x_2947_, v_snd_2937_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_2938_);
lean_dec_ref(v___x_2939_);
v___y_2913_ = v___y_2927_;
v___y_2914_ = v___y_2930_;
v___y_2915_ = v___y_2931_;
v___y_2916_ = v___y_2932_;
v___y_2917_ = v___y_2933_;
v___y_2918_ = v___y_2934_;
v___y_2919_ = v___y_2935_;
v___y_2920_ = v___y_2936_;
v___y_2921_ = v___x_2948_;
goto v___jp_2912_;
}
}
}
v___jp_2949_:
{
lean_object* v_toArray_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2982_; 
v_toArray_2962_ = lean_ctor_get(v_a_2960_, 1);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_a_2960_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v_a_2960_, 0);
lean_dec(v_unused_2983_);
v___x_2964_ = v_a_2960_;
v_isShared_2965_ = v_isSharedCheck_2982_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_toArray_2962_);
lean_dec(v_a_2960_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2982_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; 
v___x_2966_ = lean_mk_empty_array_with_capacity(v___y_2959_);
v___x_2967_ = lean_array_get_size(v_toArray_2962_);
v___x_2968_ = lean_nat_dec_lt(v___y_2959_, v___x_2967_);
if (v___x_2968_ == 0)
{
lean_del_object(v___x_2964_);
lean_dec_ref(v_toArray_2962_);
lean_dec(v_name_2821_);
v___y_2927_ = v___y_2950_;
v___y_2928_ = v___y_2952_;
v___y_2929_ = v___y_2951_;
v___y_2930_ = v___y_2953_;
v___y_2931_ = v___y_2955_;
v___y_2932_ = v___y_2954_;
v___y_2933_ = v___y_2956_;
v___y_2934_ = v___y_2959_;
v___y_2935_ = v___y_2958_;
v___y_2936_ = v___y_2957_;
v_snd_2937_ = v___x_2966_;
v_a_2938_ = v_a_2961_;
goto v___jp_2926_;
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2969_ = l_Lean_NameSet_empty;
v___x_2970_ = l_Lean_NameSet_insert(v___x_2969_, v_name_2821_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 1, v___x_2966_);
lean_ctor_set(v___x_2964_, 0, v___x_2970_);
v___x_2972_ = v___x_2964_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2966_);
v___x_2972_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
size_t v___x_2973_; size_t v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = ((size_t)0ULL);
v___x_2974_ = lean_usize_of_nat(v___x_2967_);
lean_inc_ref(v___y_2824_);
v___x_2975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_2962_, v___x_2973_, v___x_2974_, v___x_2972_, v___y_2824_, v___x_2816_, v___y_2826_, v___y_2827_, v___y_2828_, v_a_2961_);
lean_dec_ref(v_toArray_2962_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v_a_2977_; lean_object* v_snd_2978_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2976_);
v_a_2977_ = lean_ctor_get(v___x_2975_, 1);
lean_inc(v_a_2977_);
lean_dec_ref_known(v___x_2975_, 2);
v_snd_2978_ = lean_ctor_get(v_a_2976_, 1);
lean_inc(v_snd_2978_);
lean_dec(v_a_2976_);
v___y_2927_ = v___y_2950_;
v___y_2928_ = v___y_2952_;
v___y_2929_ = v___y_2951_;
v___y_2930_ = v___y_2953_;
v___y_2931_ = v___y_2955_;
v___y_2932_ = v___y_2954_;
v___y_2933_ = v___y_2956_;
v___y_2934_ = v___y_2959_;
v___y_2935_ = v___y_2958_;
v___y_2936_ = v___y_2957_;
v_snd_2937_ = v_snd_2978_;
v_a_2938_ = v_a_2977_;
goto v___jp_2926_;
}
else
{
lean_object* v_a_2979_; lean_object* v_a_2980_; 
lean_dec_ref(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v___y_2824_);
lean_dec_ref(v_pkg_2820_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_2979_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2979_);
v_a_2980_ = lean_ctor_get(v___x_2975_, 1);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2975_, 2);
v_a_2832_ = v_a_2979_;
v_a_2833_ = v_a_2980_;
goto v___jp_2831_;
}
}
}
}
}
v___jp_2984_:
{
if (lean_obj_tag(v___y_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v_a_2997_; 
v_a_2996_ = lean_ctor_get(v___y_2995_, 0);
lean_inc(v_a_2996_);
v_a_2997_ = lean_ctor_get(v___y_2995_, 1);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___y_2995_, 2);
v___y_2950_ = v___y_2985_;
v___y_2951_ = v___y_2987_;
v___y_2952_ = v___y_2986_;
v___y_2953_ = v___y_2988_;
v___y_2954_ = v___y_2990_;
v___y_2955_ = v___y_2989_;
v___y_2956_ = v___y_2991_;
v___y_2957_ = v___y_2994_;
v___y_2958_ = v___y_2993_;
v___y_2959_ = v___y_2992_;
v_a_2960_ = v_a_2996_;
v_a_2961_ = v_a_2997_;
goto v___jp_2949_;
}
else
{
lean_object* v_a_2998_; lean_object* v_a_2999_; 
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec_ref(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec_ref(v___y_2987_);
lean_dec_ref(v___y_2824_);
lean_dec(v_name_2821_);
lean_dec_ref(v_pkg_2820_);
lean_dec_ref(v_dir_2818_);
lean_dec_ref(v_self_2817_);
lean_dec(v___x_2816_);
v_a_2998_ = lean_ctor_get(v___y_2995_, 0);
lean_inc(v_a_2998_);
v_a_2999_ = lean_ctor_get(v___y_2995_, 1);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___y_2995_, 2);
v_a_2832_ = v_a_2998_;
v_a_2833_ = v_a_2999_;
goto v___jp_2831_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* v___x_3112_, lean_object* v___x_3113_, lean_object* v_self_3114_, lean_object* v_dir_3115_, lean_object* v_targetDecls_3116_, lean_object* v_pkg_3117_, lean_object* v_name_3118_, lean_object* v_config_3119_, lean_object* v_config_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v___x_3112_, v___x_3113_, v_self_3114_, v_dir_3115_, v_targetDecls_3116_, v_pkg_3117_, v_name_3118_, v_config_3119_, v_config_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec(v_config_3120_);
lean_dec_ref(v_targetDecls_3116_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object* v_self_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v_pkg_3138_; lean_object* v_name_3139_; lean_object* v_config_3140_; lean_object* v_keyName_3141_; lean_object* v_dir_3142_; lean_object* v_config_3143_; lean_object* v_targetDecls_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___f_3151_; lean_object* v___x_3152_; 
v_pkg_3138_ = lean_ctor_get(v_self_3130_, 0);
lean_inc_ref_n(v_pkg_3138_, 2);
v_name_3139_ = lean_ctor_get(v_self_3130_, 1);
lean_inc_n(v_name_3139_, 3);
v_config_3140_ = lean_ctor_get(v_self_3130_, 2);
lean_inc(v_config_3140_);
v_keyName_3141_ = lean_ctor_get(v_pkg_3138_, 2);
v_dir_3142_ = lean_ctor_get(v_pkg_3138_, 4);
lean_inc_ref(v_dir_3142_);
v_config_3143_ = lean_ctor_get(v_pkg_3138_, 6);
lean_inc_ref(v_config_3143_);
v_targetDecls_3144_ = lean_ctor_get(v_pkg_3138_, 15);
lean_inc_ref(v_targetDecls_3144_);
v___x_3145_ = l_Lake_instDataKindDynlib;
v___x_3146_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_3141_);
v___x_3147_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3147_, 0, v_keyName_3141_);
lean_ctor_set(v___x_3147_, 1, v_name_3139_);
v___x_3148_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3130_);
v___x_3149_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3147_);
lean_ctor_set(v___x_3149_, 1, v___x_3148_);
lean_ctor_set(v___x_3149_, 2, v_self_3130_);
lean_ctor_set(v___x_3149_, 3, v___x_3146_);
v___x_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3150_, 0, v_pkg_3138_);
v___f_3151_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3151_, 0, v___x_3149_);
lean_closure_set(v___f_3151_, 1, v___x_3150_);
lean_closure_set(v___f_3151_, 2, v_self_3130_);
lean_closure_set(v___f_3151_, 3, v_dir_3142_);
lean_closure_set(v___f_3151_, 4, v_targetDecls_3144_);
lean_closure_set(v___f_3151_, 5, v_pkg_3138_);
lean_closure_set(v___f_3151_, 6, v_name_3139_);
lean_closure_set(v___f_3151_, 7, v_config_3143_);
lean_closure_set(v___f_3151_, 8, v_config_3140_);
v___x_3152_ = l_Lake_ensureJob___redArg(v___x_3145_, v___f_3151_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3182_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
v_a_3154_ = lean_ctor_get(v___x_3152_, 1);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3156_ = v___x_3152_;
v_isShared_3157_ = v_isSharedCheck_3182_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_inc(v_a_3153_);
lean_dec(v___x_3152_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3182_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v_task_3158_; lean_object* v_kind_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3180_; 
v_task_3158_ = lean_ctor_get(v_a_3153_, 0);
v_kind_3159_ = lean_ctor_get(v_a_3153_, 1);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_a_3153_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; 
v_unused_3181_ = lean_ctor_get(v_a_3153_, 2);
lean_dec(v_unused_3181_);
v___x_3161_ = v_a_3153_;
v_isShared_3162_ = v_isSharedCheck_3180_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_kind_3159_);
lean_inc(v_task_3158_);
lean_dec(v_a_3153_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3180_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v_registeredJobs_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; uint8_t v___x_3169_; lean_object* v_job_3171_; 
v_registeredJobs_3163_ = lean_ctor_get(v_a_3135_, 4);
v___x_3164_ = lean_st_ref_take(v_registeredJobs_3163_);
v___x_3165_ = 1;
v___x_3166_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3139_, v___x_3165_);
v___x_3167_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0));
v___x_3168_ = lean_string_append(v___x_3166_, v___x_3167_);
v___x_3169_ = 0;
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 2, v___x_3168_);
v_job_3171_ = v___x_3161_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_task_3158_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_kind_3159_);
lean_ctor_set(v_reuseFailAlloc_3179_, 2, v___x_3168_);
v_job_3171_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3177_; 
lean_ctor_set_uint8(v_job_3171_, sizeof(void*)*3, v___x_3169_);
lean_inc_ref(v_job_3171_);
v___x_3172_ = l_Lake_Job_toOpaque___redArg(v_job_3171_);
v___x_3173_ = lean_array_push(v___x_3164_, v___x_3172_);
v___x_3174_ = lean_st_ref_put(v_registeredJobs_3163_, v___x_3173_);
v___x_3175_ = l_Lake_Job_renew___redArg(v_job_3171_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 0, v___x_3175_);
v___x_3177_ = v___x_3156_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3175_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_a_3154_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
}
else
{
lean_dec(v_name_3139_);
return v___x_3152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object* v_self_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
lean_dec_ref(v_a_3188_);
lean_dec(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec(v_a_3185_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t v_fmt_3192_, lean_object* v_a_3193_){
_start:
{
if (v_fmt_3192_ == 0)
{
lean_object* v_path_3194_; 
v_path_3194_ = lean_ctor_get(v_a_3193_, 0);
lean_inc_ref(v_path_3194_);
return v_path_3194_;
}
else
{
lean_object* v_path_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v_path_3195_ = lean_ctor_get(v_a_3193_, 0);
lean_inc_ref(v_path_3195_);
v___x_3196_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3196_, 0, v_path_3195_);
v___x_3197_ = l_Lean_Json_compress(v___x_3196_);
return v___x_3197_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* v_fmt_3198_, lean_object* v_a_3199_){
_start:
{
uint8_t v_fmt_boxed_3200_; lean_object* v_res_3201_; 
v_fmt_boxed_3200_ = lean_unbox(v_fmt_3198_);
v_res_3201_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_boxed_3200_, v_a_3199_);
lean_dec_ref(v_a_3199_);
return v_res_3201_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3204_; uint8_t v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___f_3204_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__0));
v___x_3205_ = 1;
v___x_3206_ = l_Lake_instDataKindDynlib;
v___x_3207_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__1));
v___x_3208_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3209_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
lean_ctor_set(v___x_3209_, 1, v___x_3207_);
lean_ctor_set(v___x_3209_, 2, v___x_3206_);
lean_ctor_set(v___x_3209_, 3, v___f_3204_);
lean_ctor_set_uint8(v___x_3209_, sizeof(void*)*4, v___x_3205_);
lean_ctor_set_uint8(v___x_3209_, sizeof(void*)*4 + 1, v___x_3205_);
return v___x_3209_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = lean_obj_once(&l_Lake_LeanLib_sharedFacetConfig___closed__2, &l_Lake_LeanLib_sharedFacetConfig___closed__2_once, _init_l_Lake_LeanLib_sharedFacetConfig___closed__2);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* v___x_3211_, lean_object* v_as_3212_, size_t v_sz_3213_, size_t v_i_3214_, lean_object* v_b_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
uint8_t v___x_3223_; 
v___x_3223_ = lean_usize_dec_lt(v_i_3214_, v_sz_3213_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; 
lean_dec_ref(v___y_3216_);
lean_dec_ref(v___x_3211_);
v___x_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3224_, 0, v_b_3215_);
lean_ctor_set(v___x_3224_, 1, v___y_3221_);
return v___x_3224_;
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3226_; 
v_a_3225_ = lean_array_uget_borrowed(v_as_3212_, v_i_3214_);
lean_inc_ref(v___y_3216_);
lean_inc_n(v_a_3225_, 2);
lean_inc_ref(v___x_3211_);
v___x_3226_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v___x_3211_, v_a_3225_, v_a_3225_, v___x_3223_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v_a_3228_; lean_object* v_snd_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; size_t v___x_3232_; size_t v___x_3233_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
v_a_3228_ = lean_ctor_get(v___x_3226_, 1);
lean_inc(v_a_3228_);
lean_dec_ref_known(v___x_3226_, 2);
v_snd_3229_ = lean_ctor_get(v_a_3227_, 1);
lean_inc(v_snd_3229_);
lean_dec(v_a_3227_);
v___x_3230_ = l_Lake_Job_toOpaque___redArg(v_snd_3229_);
v___x_3231_ = l_Lake_Job_mix___redArg(v_b_3215_, v___x_3230_);
v___x_3232_ = ((size_t)1ULL);
v___x_3233_ = lean_usize_add(v_i_3214_, v___x_3232_);
v_i_3214_ = v___x_3233_;
v_b_3215_ = v___x_3231_;
v___y_3221_ = v_a_3228_;
goto _start;
}
else
{
lean_object* v_a_3235_; lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3243_; 
lean_dec_ref(v___y_3216_);
lean_dec_ref(v_b_3215_);
lean_dec_ref(v___x_3211_);
v_a_3235_ = lean_ctor_get(v___x_3226_, 0);
v_a_3236_ = lean_ctor_get(v___x_3226_, 1);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3238_ = v___x_3226_;
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_inc(v_a_3235_);
lean_dec(v___x_3226_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3243_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3241_; 
if (v_isShared_3239_ == 0)
{
v___x_3241_ = v___x_3238_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3235_);
lean_ctor_set(v_reuseFailAlloc_3242_, 1, v_a_3236_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* v___x_3244_, lean_object* v_as_3245_, lean_object* v_sz_3246_, lean_object* v_i_3247_, lean_object* v_b_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
size_t v_sz_boxed_3256_; size_t v_i_boxed_3257_; lean_object* v_res_3258_; 
v_sz_boxed_3256_ = lean_unbox_usize(v_sz_3246_);
lean_dec(v_sz_3246_);
v_i_boxed_3257_ = lean_unbox_usize(v_i_3247_);
lean_dec(v_i_3247_);
v_res_3258_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_3244_, v_as_3245_, v_sz_boxed_3256_, v_i_boxed_3257_, v_b_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v_as_3245_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* v___x_3259_, lean_object* v_as_3260_, size_t v_sz_3261_, size_t v_i_3262_, lean_object* v_b_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
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
lean_inc(v_a_3273_);
lean_inc_ref(v___x_3259_);
v___x_3274_ = l_Lake_Package_fetchTargetJob(v___x_3259_, v_a_3273_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v_a_3276_; lean_object* v___x_3277_; size_t v___x_3278_; size_t v___x_3279_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
v_a_3276_ = lean_ctor_get(v___x_3274_, 1);
lean_inc(v_a_3276_);
lean_dec_ref_known(v___x_3274_, 2);
v___x_3277_ = l_Lake_Job_mix___redArg(v_b_3263_, v_a_3275_);
v___x_3278_ = ((size_t)1ULL);
v___x_3279_ = lean_usize_add(v_i_3262_, v___x_3278_);
v_i_3262_ = v___x_3279_;
v_b_3263_ = v___x_3277_;
v___y_3269_ = v_a_3276_;
goto _start;
}
else
{
lean_object* v_a_3281_; lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_dec_ref(v___y_3264_);
lean_dec_ref(v_b_3263_);
lean_dec_ref(v___x_3259_);
v_a_3281_ = lean_ctor_get(v___x_3274_, 0);
v_a_3282_ = lean_ctor_get(v___x_3274_, 1);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3274_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_inc(v_a_3281_);
lean_dec(v___x_3274_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3281_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* v___x_3290_, lean_object* v_as_3291_, lean_object* v_sz_3292_, lean_object* v_i_3293_, lean_object* v_b_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
size_t v_sz_boxed_3302_; size_t v_i_boxed_3303_; lean_object* v_res_3304_; 
v_sz_boxed_3302_ = lean_unbox_usize(v_sz_3292_);
lean_dec(v_sz_3292_);
v_i_boxed_3303_ = lean_unbox_usize(v_i_3293_);
lean_dec(v_i_3293_);
v_res_3304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_3290_, v_as_3291_, v_sz_boxed_3302_, v_i_boxed_3303_, v_b_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v_as_3291_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object* v_self_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_pkg_3315_; lean_object* v_name_3316_; lean_object* v_config_3317_; lean_object* v_baseName_3318_; lean_object* v_keyName_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v_pkg_3315_ = lean_ctor_get(v_self_3307_, 0);
lean_inc_ref_n(v_pkg_3315_, 2);
v_name_3316_ = lean_ctor_get(v_self_3307_, 1);
lean_inc(v_name_3316_);
v_config_3317_ = lean_ctor_get(v_self_3307_, 2);
lean_inc(v_config_3317_);
lean_dec_ref(v_self_3307_);
v_baseName_3318_ = lean_ctor_get(v_pkg_3315_, 1);
v_keyName_3319_ = lean_ctor_get(v_pkg_3315_, 2);
v___x_3320_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_3319_);
v___x_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3321_, 0, v_keyName_3319_);
v___x_3322_ = l_Lake_Package_keyword;
v___x_3323_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3321_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
lean_ctor_set(v___x_3323_, 2, v_pkg_3315_);
lean_ctor_set(v___x_3323_, 3, v___x_3320_);
lean_inc_ref(v_a_3308_);
lean_inc_ref(v_a_3312_);
lean_inc(v_a_3311_);
lean_inc(v_a_3310_);
lean_inc(v_a_3309_);
v___x_3324_ = lean_apply_7(v_a_3308_, v___x_3323_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, lean_box(0));
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3362_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
v_a_3326_ = lean_ctor_get(v___x_3324_, 1);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3328_ = v___x_3324_;
v_isShared_3329_ = v_isSharedCheck_3362_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_inc(v_a_3325_);
lean_dec(v___x_3324_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3362_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
uint8_t v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v_needs_3334_; lean_object* v_extraDepTargets_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; uint8_t v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3349_; 
v___x_3330_ = 1;
lean_inc(v_baseName_3318_);
v___x_3331_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3318_, v___x_3330_);
v___x_3332_ = lean_unsigned_to_nat(0u);
v___x_3333_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v_needs_3334_ = lean_ctor_get(v_config_3317_, 5);
lean_inc_ref(v_needs_3334_);
v_extraDepTargets_3335_ = lean_ctor_get(v_config_3317_, 6);
lean_inc_ref(v_extraDepTargets_3335_);
lean_dec(v_config_3317_);
v___x_3336_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0));
v___x_3337_ = lean_string_append(v___x_3331_, v___x_3336_);
v___x_3338_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3316_, v___x_3330_);
v___x_3339_ = lean_string_append(v___x_3337_, v___x_3338_);
lean_dec_ref(v___x_3338_);
v___x_3340_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1));
v___x_3341_ = lean_string_append(v___x_3339_, v___x_3340_);
v___x_3342_ = 0;
v___x_3343_ = 0;
v___x_3344_ = l_Lake_BuildTrace_nil(v___x_3341_);
v___x_3345_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3345_, 0, v___x_3333_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
lean_ctor_set(v___x_3345_, 2, v___x_3332_);
lean_ctor_set_uint8(v___x_3345_, sizeof(void*)*3, v___x_3342_);
lean_ctor_set_uint8(v___x_3345_, sizeof(void*)*3 + 1, v___x_3343_);
v___x_3346_ = lean_box(0);
v___x_3347_ = lean_box(0);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 1, v___x_3345_);
lean_ctor_set(v___x_3328_, 0, v___x_3347_);
v___x_3349_ = v___x_3328_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3347_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v___x_3345_);
v___x_3349_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v_job_3352_; lean_object* v___x_3353_; size_t v_sz_3354_; size_t v___x_3355_; lean_object* v___x_3356_; 
v___x_3350_ = lean_task_pure(v___x_3349_);
v___x_3351_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v_job_3352_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_3352_, 0, v___x_3350_);
lean_ctor_set(v_job_3352_, 1, v___x_3346_);
lean_ctor_set(v_job_3352_, 2, v___x_3351_);
lean_ctor_set_uint8(v_job_3352_, sizeof(void*)*3, v___x_3343_);
v___x_3353_ = l_Lake_Job_mix___redArg(v_job_3352_, v_a_3325_);
v_sz_3354_ = lean_array_size(v_extraDepTargets_3335_);
v___x_3355_ = ((size_t)0ULL);
lean_inc_ref(v_a_3308_);
lean_inc_ref(v_pkg_3315_);
v___x_3356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_3315_, v_extraDepTargets_3335_, v_sz_3354_, v___x_3355_, v___x_3353_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3326_);
lean_dec_ref(v_extraDepTargets_3335_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v_a_3358_; size_t v_sz_3359_; lean_object* v___x_3360_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
v_a_3358_ = lean_ctor_get(v___x_3356_, 1);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3356_, 2);
v_sz_3359_ = lean_array_size(v_needs_3334_);
v___x_3360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_3315_, v_needs_3334_, v_sz_3359_, v___x_3355_, v_a_3357_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3358_);
lean_dec_ref(v_needs_3334_);
return v___x_3360_;
}
else
{
lean_dec_ref(v_needs_3334_);
lean_dec_ref(v_pkg_3315_);
lean_dec_ref(v_a_3308_);
return v___x_3356_;
}
}
}
}
else
{
lean_dec(v_config_3317_);
lean_dec(v_name_3316_);
lean_dec_ref(v_pkg_3315_);
lean_dec_ref(v_a_3308_);
return v___x_3324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object* v_self_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec(v_a_3365_);
return v_res_3371_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3373_; uint8_t v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___f_3373_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3374_ = 1;
v___x_3375_ = l_Lake_instDataKindUnit;
v___x_3376_ = ((lean_object*)(l_Lake_LeanLib_extraDepFacetConfig___closed__0));
v___x_3377_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3378_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
lean_ctor_set(v___x_3378_, 1, v___x_3376_);
lean_ctor_set(v___x_3378_, 2, v___x_3375_);
lean_ctor_set(v___x_3378_, 3, v___f_3373_);
lean_ctor_set_uint8(v___x_3378_, sizeof(void*)*4, v___x_3374_);
lean_ctor_set_uint8(v___x_3378_, sizeof(void*)*4 + 1, v___x_3374_);
return v___x_3378_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_obj_once(&l_Lake_LeanLib_extraDepFacetConfig___closed__1, &l_Lake_LeanLib_extraDepFacetConfig___closed__1_once, _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* v_self_3380_, size_t v_sz_3381_, size_t v_i_3382_, lean_object* v_bs_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
uint8_t v___x_3391_; 
v___x_3391_ = lean_usize_dec_lt(v_i_3382_, v_sz_3381_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; 
lean_dec_ref(v___y_3384_);
lean_dec_ref(v_self_3380_);
v___x_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3392_, 0, v_bs_3383_);
lean_ctor_set(v___x_3392_, 1, v___y_3389_);
return v___x_3392_;
}
else
{
lean_object* v_pkg_3393_; lean_object* v_name_3394_; lean_object* v_keyName_3395_; lean_object* v_v_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v_pkg_3393_ = lean_ctor_get(v_self_3380_, 0);
v_name_3394_ = lean_ctor_get(v_self_3380_, 1);
v_keyName_3395_ = lean_ctor_get(v_pkg_3393_, 2);
v_v_3396_ = lean_array_uget_borrowed(v_bs_3383_, v_i_3382_);
lean_inc(v_name_3394_);
lean_inc(v_keyName_3395_);
v___x_3397_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3397_, 0, v_keyName_3395_);
lean_ctor_set(v___x_3397_, 1, v_name_3394_);
v___x_3398_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc(v_v_3396_);
lean_inc_ref(v_self_3380_);
v___x_3399_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3397_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
lean_ctor_set(v___x_3399_, 2, v_self_3380_);
lean_ctor_set(v___x_3399_, 3, v_v_3396_);
lean_inc_ref(v___y_3384_);
lean_inc_ref(v___y_3388_);
lean_inc(v___y_3387_);
lean_inc(v___y_3386_);
lean_inc(v___y_3385_);
v___x_3400_ = lean_apply_7(v___y_3384_, v___x_3399_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, lean_box(0));
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v_a_3401_; lean_object* v_a_3402_; lean_object* v___x_3403_; lean_object* v_bs_x27_3404_; lean_object* v___x_3405_; size_t v___x_3406_; size_t v___x_3407_; lean_object* v___x_3408_; 
v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc(v_a_3401_);
v_a_3402_ = lean_ctor_get(v___x_3400_, 1);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3400_, 2);
v___x_3403_ = lean_unsigned_to_nat(0u);
v_bs_x27_3404_ = lean_array_uset(v_bs_3383_, v_i_3382_, v___x_3403_);
v___x_3405_ = l_Lake_Job_toOpaque___redArg(v_a_3401_);
v___x_3406_ = ((size_t)1ULL);
v___x_3407_ = lean_usize_add(v_i_3382_, v___x_3406_);
v___x_3408_ = lean_array_uset(v_bs_x27_3404_, v_i_3382_, v___x_3405_);
v_i_3382_ = v___x_3407_;
v_bs_3383_ = v___x_3408_;
v___y_3389_ = v_a_3402_;
goto _start;
}
else
{
lean_object* v_a_3410_; lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec_ref(v___y_3384_);
lean_dec_ref(v_bs_3383_);
lean_dec_ref(v_self_3380_);
v_a_3410_ = lean_ctor_get(v___x_3400_, 0);
v_a_3411_ = lean_ctor_get(v___x_3400_, 1);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3400_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_inc(v_a_3410_);
lean_dec(v___x_3400_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3410_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* v_self_3419_, lean_object* v_sz_3420_, lean_object* v_i_3421_, lean_object* v_bs_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
size_t v_sz_boxed_3430_; size_t v_i_boxed_3431_; lean_object* v_res_3432_; 
v_sz_boxed_3430_ = lean_unbox_usize(v_sz_3420_);
lean_dec(v_sz_3420_);
v_i_boxed_3431_ = lean_unbox_usize(v_i_3421_);
lean_dec(v_i_3421_);
v_res_3432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3419_, v_sz_boxed_3430_, v_i_boxed_3431_, v_bs_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec(v___y_3424_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object* v_self_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
lean_object* v_config_3442_; lean_object* v_defaultFacets_3443_; size_t v_sz_3444_; size_t v___x_3445_; lean_object* v___x_3446_; 
v_config_3442_ = lean_ctor_get(v_self_3434_, 2);
v_defaultFacets_3443_ = lean_ctor_get(v_config_3442_, 7);
lean_inc_ref(v_defaultFacets_3443_);
v_sz_3444_ = lean_array_size(v_defaultFacets_3443_);
v___x_3445_ = ((size_t)0ULL);
v___x_3446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3434_, v_sz_3444_, v___x_3445_, v_defaultFacets_3443_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3457_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
v_a_3448_ = lean_ctor_get(v___x_3446_, 1);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3450_ = v___x_3446_;
v_isShared_3451_ = v_isSharedCheck_3457_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_inc(v_a_3447_);
lean_dec(v___x_3446_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3457_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3455_; 
v___x_3452_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0));
v___x_3453_ = l_Lake_Job_mixArray___redArg(v_a_3447_, v___x_3452_);
lean_dec(v_a_3447_);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v___x_3453_);
v___x_3455_ = v___x_3450_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3456_, 1, v_a_3448_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
else
{
lean_object* v_a_3458_; lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
v_a_3458_ = lean_ctor_get(v___x_3446_, 0);
v_a_3459_ = lean_ctor_get(v___x_3446_, 1);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3446_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_inc(v_a_3458_);
lean_dec(v___x_3446_);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object* v_self_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
lean_object* v_res_3475_; 
v_res_3475_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_);
lean_dec_ref(v_a_3472_);
lean_dec(v_a_3471_);
lean_dec(v_a_3470_);
lean_dec(v_a_3469_);
return v_res_3475_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3477_; uint8_t v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___f_3477_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3478_ = 1;
v___x_3479_ = l_Lake_instDataKindUnit;
v___x_3480_ = ((lean_object*)(l_Lake_LeanLib_defaultFacetConfig___closed__0));
v___x_3481_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3482_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
lean_ctor_set(v___x_3482_, 1, v___x_3480_);
lean_ctor_set(v___x_3482_, 2, v___x_3479_);
lean_ctor_set(v___x_3482_, 3, v___f_3477_);
lean_ctor_set_uint8(v___x_3482_, sizeof(void*)*4, v___x_3478_);
lean_ctor_set_uint8(v___x_3482_, sizeof(void*)*4 + 1, v___x_3478_);
return v___x_3482_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = lean_obj_once(&l_Lake_LeanLib_defaultFacetConfig___closed__1, &l_Lake_LeanLib_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanLib_defaultFacetConfig___closed__1);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_3484_, lean_object* v_v_3485_, lean_object* v_t_3486_){
_start:
{
if (lean_obj_tag(v_t_3486_) == 0)
{
lean_object* v_size_3487_; lean_object* v_k_3488_; lean_object* v_v_3489_; lean_object* v_l_3490_; lean_object* v_r_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3771_; 
v_size_3487_ = lean_ctor_get(v_t_3486_, 0);
v_k_3488_ = lean_ctor_get(v_t_3486_, 1);
v_v_3489_ = lean_ctor_get(v_t_3486_, 2);
v_l_3490_ = lean_ctor_get(v_t_3486_, 3);
v_r_3491_ = lean_ctor_get(v_t_3486_, 4);
v_isSharedCheck_3771_ = !lean_is_exclusive(v_t_3486_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3493_ = v_t_3486_;
v_isShared_3494_ = v_isSharedCheck_3771_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_r_3491_);
lean_inc(v_l_3490_);
lean_inc(v_v_3489_);
lean_inc(v_k_3488_);
lean_inc(v_size_3487_);
lean_dec(v_t_3486_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3771_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
uint8_t v___x_3495_; 
v___x_3495_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3484_, v_k_3488_);
switch(v___x_3495_)
{
case 0:
{
lean_object* v_impl_3496_; lean_object* v___x_3497_; 
lean_dec(v_size_3487_);
v_impl_3496_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3484_, v_v_3485_, v_l_3490_);
v___x_3497_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3491_) == 0)
{
lean_object* v_size_3498_; lean_object* v_size_3499_; lean_object* v_k_3500_; lean_object* v_v_3501_; lean_object* v_l_3502_; lean_object* v_r_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v_size_3498_ = lean_ctor_get(v_r_3491_, 0);
v_size_3499_ = lean_ctor_get(v_impl_3496_, 0);
lean_inc(v_size_3499_);
v_k_3500_ = lean_ctor_get(v_impl_3496_, 1);
lean_inc(v_k_3500_);
v_v_3501_ = lean_ctor_get(v_impl_3496_, 2);
lean_inc(v_v_3501_);
v_l_3502_ = lean_ctor_get(v_impl_3496_, 3);
lean_inc(v_l_3502_);
v_r_3503_ = lean_ctor_get(v_impl_3496_, 4);
lean_inc(v_r_3503_);
v___x_3504_ = lean_unsigned_to_nat(3u);
v___x_3505_ = lean_nat_mul(v___x_3504_, v_size_3498_);
v___x_3506_ = lean_nat_dec_lt(v___x_3505_, v_size_3499_);
lean_dec(v___x_3505_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3510_; 
lean_dec(v_r_3503_);
lean_dec(v_l_3502_);
lean_dec(v_v_3501_);
lean_dec(v_k_3500_);
v___x_3507_ = lean_nat_add(v___x_3497_, v_size_3499_);
lean_dec(v_size_3499_);
v___x_3508_ = lean_nat_add(v___x_3507_, v_size_3498_);
lean_dec(v___x_3507_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 3, v_impl_3496_);
lean_ctor_set(v___x_3493_, 0, v___x_3508_);
v___x_3510_ = v___x_3493_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3508_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3511_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3511_, 3, v_impl_3496_);
lean_ctor_set(v_reuseFailAlloc_3511_, 4, v_r_3491_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
else
{
lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3577_; 
v_isSharedCheck_3577_ = !lean_is_exclusive(v_impl_3496_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; lean_object* v_unused_3579_; lean_object* v_unused_3580_; lean_object* v_unused_3581_; lean_object* v_unused_3582_; 
v_unused_3578_ = lean_ctor_get(v_impl_3496_, 4);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_impl_3496_, 3);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_impl_3496_, 2);
lean_dec(v_unused_3580_);
v_unused_3581_ = lean_ctor_get(v_impl_3496_, 1);
lean_dec(v_unused_3581_);
v_unused_3582_ = lean_ctor_get(v_impl_3496_, 0);
lean_dec(v_unused_3582_);
v___x_3513_ = v_impl_3496_;
v_isShared_3514_ = v_isSharedCheck_3577_;
goto v_resetjp_3512_;
}
else
{
lean_dec(v_impl_3496_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3577_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v_size_3515_; lean_object* v_size_3516_; lean_object* v_k_3517_; lean_object* v_v_3518_; lean_object* v_l_3519_; lean_object* v_r_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; uint8_t v___x_3523_; 
v_size_3515_ = lean_ctor_get(v_l_3502_, 0);
v_size_3516_ = lean_ctor_get(v_r_3503_, 0);
v_k_3517_ = lean_ctor_get(v_r_3503_, 1);
v_v_3518_ = lean_ctor_get(v_r_3503_, 2);
v_l_3519_ = lean_ctor_get(v_r_3503_, 3);
v_r_3520_ = lean_ctor_get(v_r_3503_, 4);
v___x_3521_ = lean_unsigned_to_nat(2u);
v___x_3522_ = lean_nat_mul(v___x_3521_, v_size_3515_);
v___x_3523_ = lean_nat_dec_lt(v_size_3516_, v___x_3522_);
lean_dec(v___x_3522_);
if (v___x_3523_ == 0)
{
lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3552_; 
lean_inc(v_r_3520_);
lean_inc(v_l_3519_);
lean_inc(v_v_3518_);
lean_inc(v_k_3517_);
v_isSharedCheck_3552_ = !lean_is_exclusive(v_r_3503_);
if (v_isSharedCheck_3552_ == 0)
{
lean_object* v_unused_3553_; lean_object* v_unused_3554_; lean_object* v_unused_3555_; lean_object* v_unused_3556_; lean_object* v_unused_3557_; 
v_unused_3553_ = lean_ctor_get(v_r_3503_, 4);
lean_dec(v_unused_3553_);
v_unused_3554_ = lean_ctor_get(v_r_3503_, 3);
lean_dec(v_unused_3554_);
v_unused_3555_ = lean_ctor_get(v_r_3503_, 2);
lean_dec(v_unused_3555_);
v_unused_3556_ = lean_ctor_get(v_r_3503_, 1);
lean_dec(v_unused_3556_);
v_unused_3557_ = lean_ctor_get(v_r_3503_, 0);
lean_dec(v_unused_3557_);
v___x_3525_ = v_r_3503_;
v_isShared_3526_ = v_isSharedCheck_3552_;
goto v_resetjp_3524_;
}
else
{
lean_dec(v_r_3503_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3552_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___x_3540_; lean_object* v___y_3542_; 
v___x_3527_ = lean_nat_add(v___x_3497_, v_size_3499_);
lean_dec(v_size_3499_);
v___x_3528_ = lean_nat_add(v___x_3527_, v_size_3498_);
lean_dec(v___x_3527_);
v___x_3540_ = lean_nat_add(v___x_3497_, v_size_3515_);
if (lean_obj_tag(v_l_3519_) == 0)
{
lean_object* v_size_3550_; 
v_size_3550_ = lean_ctor_get(v_l_3519_, 0);
lean_inc(v_size_3550_);
v___y_3542_ = v_size_3550_;
goto v___jp_3541_;
}
else
{
lean_object* v___x_3551_; 
v___x_3551_ = lean_unsigned_to_nat(0u);
v___y_3542_ = v___x_3551_;
goto v___jp_3541_;
}
v___jp_3529_:
{
lean_object* v___x_3533_; lean_object* v___x_3535_; 
v___x_3533_ = lean_nat_add(v___y_3530_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec(v___y_3530_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 4, v_r_3491_);
lean_ctor_set(v___x_3525_, 3, v_r_3520_);
lean_ctor_set(v___x_3525_, 2, v_v_3489_);
lean_ctor_set(v___x_3525_, 1, v_k_3488_);
lean_ctor_set(v___x_3525_, 0, v___x_3533_);
v___x_3535_ = v___x_3525_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3533_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3539_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3539_, 3, v_r_3520_);
lean_ctor_set(v_reuseFailAlloc_3539_, 4, v_r_3491_);
v___x_3535_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
lean_object* v___x_3537_; 
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 4, v___x_3535_);
lean_ctor_set(v___x_3513_, 3, v___y_3531_);
lean_ctor_set(v___x_3513_, 2, v_v_3518_);
lean_ctor_set(v___x_3513_, 1, v_k_3517_);
lean_ctor_set(v___x_3513_, 0, v___x_3528_);
v___x_3537_ = v___x_3513_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_k_3517_);
lean_ctor_set(v_reuseFailAlloc_3538_, 2, v_v_3518_);
lean_ctor_set(v_reuseFailAlloc_3538_, 3, v___y_3531_);
lean_ctor_set(v_reuseFailAlloc_3538_, 4, v___x_3535_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
v___jp_3541_:
{
lean_object* v___x_3543_; lean_object* v___x_3545_; 
v___x_3543_ = lean_nat_add(v___x_3540_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec(v___x_3540_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 4, v_l_3519_);
lean_ctor_set(v___x_3493_, 3, v_l_3502_);
lean_ctor_set(v___x_3493_, 2, v_v_3501_);
lean_ctor_set(v___x_3493_, 1, v_k_3500_);
lean_ctor_set(v___x_3493_, 0, v___x_3543_);
v___x_3545_ = v___x_3493_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3543_);
lean_ctor_set(v_reuseFailAlloc_3549_, 1, v_k_3500_);
lean_ctor_set(v_reuseFailAlloc_3549_, 2, v_v_3501_);
lean_ctor_set(v_reuseFailAlloc_3549_, 3, v_l_3502_);
lean_ctor_set(v_reuseFailAlloc_3549_, 4, v_l_3519_);
v___x_3545_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
lean_object* v___x_3546_; 
v___x_3546_ = lean_nat_add(v___x_3497_, v_size_3498_);
if (lean_obj_tag(v_r_3520_) == 0)
{
lean_object* v_size_3547_; 
v_size_3547_ = lean_ctor_get(v_r_3520_, 0);
lean_inc(v_size_3547_);
v___y_3530_ = v___x_3546_;
v___y_3531_ = v___x_3545_;
v___y_3532_ = v_size_3547_;
goto v___jp_3529_;
}
else
{
lean_object* v___x_3548_; 
v___x_3548_ = lean_unsigned_to_nat(0u);
v___y_3530_ = v___x_3546_;
v___y_3531_ = v___x_3545_;
v___y_3532_ = v___x_3548_;
goto v___jp_3529_;
}
}
}
}
}
else
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
lean_del_object(v___x_3493_);
v___x_3558_ = lean_nat_add(v___x_3497_, v_size_3499_);
lean_dec(v_size_3499_);
v___x_3559_ = lean_nat_add(v___x_3558_, v_size_3498_);
lean_dec(v___x_3558_);
v___x_3560_ = lean_nat_add(v___x_3497_, v_size_3498_);
v___x_3561_ = lean_nat_add(v___x_3560_, v_size_3516_);
lean_dec(v___x_3560_);
lean_inc_ref(v_r_3491_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 4, v_r_3491_);
lean_ctor_set(v___x_3513_, 3, v_r_3503_);
lean_ctor_set(v___x_3513_, 2, v_v_3489_);
lean_ctor_set(v___x_3513_, 1, v_k_3488_);
lean_ctor_set(v___x_3513_, 0, v___x_3561_);
v___x_3563_ = v___x_3513_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3561_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3576_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3576_, 3, v_r_3503_);
lean_ctor_set(v_reuseFailAlloc_3576_, 4, v_r_3491_);
v___x_3563_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
v_isSharedCheck_3570_ = !lean_is_exclusive(v_r_3491_);
if (v_isSharedCheck_3570_ == 0)
{
lean_object* v_unused_3571_; lean_object* v_unused_3572_; lean_object* v_unused_3573_; lean_object* v_unused_3574_; lean_object* v_unused_3575_; 
v_unused_3571_ = lean_ctor_get(v_r_3491_, 4);
lean_dec(v_unused_3571_);
v_unused_3572_ = lean_ctor_get(v_r_3491_, 3);
lean_dec(v_unused_3572_);
v_unused_3573_ = lean_ctor_get(v_r_3491_, 2);
lean_dec(v_unused_3573_);
v_unused_3574_ = lean_ctor_get(v_r_3491_, 1);
lean_dec(v_unused_3574_);
v_unused_3575_ = lean_ctor_get(v_r_3491_, 0);
lean_dec(v_unused_3575_);
v___x_3565_ = v_r_3491_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_dec(v_r_3491_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 4, v___x_3563_);
lean_ctor_set(v___x_3565_, 3, v_l_3502_);
lean_ctor_set(v___x_3565_, 2, v_v_3501_);
lean_ctor_set(v___x_3565_, 1, v_k_3500_);
lean_ctor_set(v___x_3565_, 0, v___x_3559_);
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3559_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_k_3500_);
lean_ctor_set(v_reuseFailAlloc_3569_, 2, v_v_3501_);
lean_ctor_set(v_reuseFailAlloc_3569_, 3, v_l_3502_);
lean_ctor_set(v_reuseFailAlloc_3569_, 4, v___x_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3583_; 
v_l_3583_ = lean_ctor_get(v_impl_3496_, 3);
lean_inc(v_l_3583_);
if (lean_obj_tag(v_l_3583_) == 0)
{
lean_object* v_r_3584_; lean_object* v_k_3585_; lean_object* v_v_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3597_; 
v_r_3584_ = lean_ctor_get(v_impl_3496_, 4);
v_k_3585_ = lean_ctor_get(v_impl_3496_, 1);
v_v_3586_ = lean_ctor_get(v_impl_3496_, 2);
v_isSharedCheck_3597_ = !lean_is_exclusive(v_impl_3496_);
if (v_isSharedCheck_3597_ == 0)
{
lean_object* v_unused_3598_; lean_object* v_unused_3599_; 
v_unused_3598_ = lean_ctor_get(v_impl_3496_, 3);
lean_dec(v_unused_3598_);
v_unused_3599_ = lean_ctor_get(v_impl_3496_, 0);
lean_dec(v_unused_3599_);
v___x_3588_ = v_impl_3496_;
v_isShared_3589_ = v_isSharedCheck_3597_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_r_3584_);
lean_inc(v_v_3586_);
lean_inc(v_k_3585_);
lean_dec(v_impl_3496_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3597_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3590_; lean_object* v___x_3592_; 
v___x_3590_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3584_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 3, v_r_3584_);
lean_ctor_set(v___x_3588_, 2, v_v_3489_);
lean_ctor_set(v___x_3588_, 1, v_k_3488_);
lean_ctor_set(v___x_3588_, 0, v___x_3497_);
v___x_3592_ = v___x_3588_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3596_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3596_, 3, v_r_3584_);
lean_ctor_set(v_reuseFailAlloc_3596_, 4, v_r_3584_);
v___x_3592_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3594_; 
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 4, v___x_3592_);
lean_ctor_set(v___x_3493_, 3, v_l_3583_);
lean_ctor_set(v___x_3493_, 2, v_v_3586_);
lean_ctor_set(v___x_3493_, 1, v_k_3585_);
lean_ctor_set(v___x_3493_, 0, v___x_3590_);
v___x_3594_ = v___x_3493_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3590_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_k_3585_);
lean_ctor_set(v_reuseFailAlloc_3595_, 2, v_v_3586_);
lean_ctor_set(v_reuseFailAlloc_3595_, 3, v_l_3583_);
lean_ctor_set(v_reuseFailAlloc_3595_, 4, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
else
{
lean_object* v_r_3600_; 
v_r_3600_ = lean_ctor_get(v_impl_3496_, 4);
lean_inc(v_r_3600_);
if (lean_obj_tag(v_r_3600_) == 0)
{
lean_object* v_k_3601_; lean_object* v_v_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3625_; 
v_k_3601_ = lean_ctor_get(v_impl_3496_, 1);
v_v_3602_ = lean_ctor_get(v_impl_3496_, 2);
v_isSharedCheck_3625_ = !lean_is_exclusive(v_impl_3496_);
if (v_isSharedCheck_3625_ == 0)
{
lean_object* v_unused_3626_; lean_object* v_unused_3627_; lean_object* v_unused_3628_; 
v_unused_3626_ = lean_ctor_get(v_impl_3496_, 4);
lean_dec(v_unused_3626_);
v_unused_3627_ = lean_ctor_get(v_impl_3496_, 3);
lean_dec(v_unused_3627_);
v_unused_3628_ = lean_ctor_get(v_impl_3496_, 0);
lean_dec(v_unused_3628_);
v___x_3604_ = v_impl_3496_;
v_isShared_3605_ = v_isSharedCheck_3625_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_v_3602_);
lean_inc(v_k_3601_);
lean_dec(v_impl_3496_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3625_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v_k_3606_; lean_object* v_v_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3621_; 
v_k_3606_ = lean_ctor_get(v_r_3600_, 1);
v_v_3607_ = lean_ctor_get(v_r_3600_, 2);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_r_3600_);
if (v_isSharedCheck_3621_ == 0)
{
lean_object* v_unused_3622_; lean_object* v_unused_3623_; lean_object* v_unused_3624_; 
v_unused_3622_ = lean_ctor_get(v_r_3600_, 4);
lean_dec(v_unused_3622_);
v_unused_3623_ = lean_ctor_get(v_r_3600_, 3);
lean_dec(v_unused_3623_);
v_unused_3624_ = lean_ctor_get(v_r_3600_, 0);
lean_dec(v_unused_3624_);
v___x_3609_ = v_r_3600_;
v_isShared_3610_ = v_isSharedCheck_3621_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_v_3607_);
lean_inc(v_k_3606_);
lean_dec(v_r_3600_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3621_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3611_ = lean_unsigned_to_nat(3u);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 4, v_l_3583_);
lean_ctor_set(v___x_3609_, 3, v_l_3583_);
lean_ctor_set(v___x_3609_, 2, v_v_3602_);
lean_ctor_set(v___x_3609_, 1, v_k_3601_);
lean_ctor_set(v___x_3609_, 0, v___x_3497_);
v___x_3613_ = v___x_3609_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_k_3601_);
lean_ctor_set(v_reuseFailAlloc_3620_, 2, v_v_3602_);
lean_ctor_set(v_reuseFailAlloc_3620_, 3, v_l_3583_);
lean_ctor_set(v_reuseFailAlloc_3620_, 4, v_l_3583_);
v___x_3613_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___x_3615_; 
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 4, v_l_3583_);
lean_ctor_set(v___x_3604_, 2, v_v_3489_);
lean_ctor_set(v___x_3604_, 1, v_k_3488_);
lean_ctor_set(v___x_3604_, 0, v___x_3497_);
v___x_3615_ = v___x_3604_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3497_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3619_, 3, v_l_3583_);
lean_ctor_set(v_reuseFailAlloc_3619_, 4, v_l_3583_);
v___x_3615_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
lean_object* v___x_3617_; 
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 4, v___x_3615_);
lean_ctor_set(v___x_3493_, 3, v___x_3613_);
lean_ctor_set(v___x_3493_, 2, v_v_3607_);
lean_ctor_set(v___x_3493_, 1, v_k_3606_);
lean_ctor_set(v___x_3493_, 0, v___x_3611_);
v___x_3617_ = v___x_3493_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v_k_3606_);
lean_ctor_set(v_reuseFailAlloc_3618_, 2, v_v_3607_);
lean_ctor_set(v_reuseFailAlloc_3618_, 3, v___x_3613_);
lean_ctor_set(v_reuseFailAlloc_3618_, 4, v___x_3615_);
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
else
{
lean_object* v___x_3629_; lean_object* v___x_3631_; 
v___x_3629_ = lean_unsigned_to_nat(2u);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 4, v_r_3600_);
lean_ctor_set(v___x_3493_, 3, v_impl_3496_);
lean_ctor_set(v___x_3493_, 0, v___x_3629_);
v___x_3631_ = v___x_3493_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3629_);
lean_ctor_set(v_reuseFailAlloc_3632_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3632_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3632_, 3, v_impl_3496_);
lean_ctor_set(v_reuseFailAlloc_3632_, 4, v_r_3600_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3634_; 
lean_dec(v_v_3489_);
lean_dec(v_k_3488_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 2, v_v_3485_);
lean_ctor_set(v___x_3493_, 1, v_k_3484_);
v___x_3634_ = v___x_3493_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_size_3487_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v_k_3484_);
lean_ctor_set(v_reuseFailAlloc_3635_, 2, v_v_3485_);
lean_ctor_set(v_reuseFailAlloc_3635_, 3, v_l_3490_);
lean_ctor_set(v_reuseFailAlloc_3635_, 4, v_r_3491_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
default: 
{
lean_object* v_impl_3636_; lean_object* v___x_3637_; 
lean_dec(v_size_3487_);
v_impl_3636_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3484_, v_v_3485_, v_r_3491_);
v___x_3637_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3490_) == 0)
{
lean_object* v_size_3638_; lean_object* v_size_3639_; lean_object* v_k_3640_; lean_object* v_v_3641_; lean_object* v_l_3642_; lean_object* v_r_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
v_size_3638_ = lean_ctor_get(v_l_3490_, 0);
v_size_3639_ = lean_ctor_get(v_impl_3636_, 0);
lean_inc(v_size_3639_);
v_k_3640_ = lean_ctor_get(v_impl_3636_, 1);
lean_inc(v_k_3640_);
v_v_3641_ = lean_ctor_get(v_impl_3636_, 2);
lean_inc(v_v_3641_);
v_l_3642_ = lean_ctor_get(v_impl_3636_, 3);
lean_inc(v_l_3642_);
v_r_3643_ = lean_ctor_get(v_impl_3636_, 4);
lean_inc(v_r_3643_);
v___x_3644_ = lean_unsigned_to_nat(3u);
v___x_3645_ = lean_nat_mul(v___x_3644_, v_size_3638_);
v___x_3646_ = lean_nat_dec_lt(v___x_3645_, v_size_3639_);
lean_dec(v___x_3645_);
if (v___x_3646_ == 0)
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
lean_dec(v_r_3643_);
lean_dec(v_l_3642_);
lean_dec(v_v_3641_);
lean_dec(v_k_3640_);
v___x_3647_ = lean_nat_add(v___x_3637_, v_size_3638_);
v___x_3648_ = lean_nat_add(v___x_3647_, v_size_3639_);
lean_dec(v_size_3639_);
lean_dec(v___x_3647_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 4, v_impl_3636_);
lean_ctor_set(v___x_3493_, 0, v___x_3648_);
v___x_3650_ = v___x_3493_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3651_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3651_, 3, v_l_3490_);
lean_ctor_set(v_reuseFailAlloc_3651_, 4, v_impl_3636_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
else
{
lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3715_; 
v_isSharedCheck_3715_ = !lean_is_exclusive(v_impl_3636_);
if (v_isSharedCheck_3715_ == 0)
{
lean_object* v_unused_3716_; lean_object* v_unused_3717_; lean_object* v_unused_3718_; lean_object* v_unused_3719_; lean_object* v_unused_3720_; 
v_unused_3716_ = lean_ctor_get(v_impl_3636_, 4);
lean_dec(v_unused_3716_);
v_unused_3717_ = lean_ctor_get(v_impl_3636_, 3);
lean_dec(v_unused_3717_);
v_unused_3718_ = lean_ctor_get(v_impl_3636_, 2);
lean_dec(v_unused_3718_);
v_unused_3719_ = lean_ctor_get(v_impl_3636_, 1);
lean_dec(v_unused_3719_);
v_unused_3720_ = lean_ctor_get(v_impl_3636_, 0);
lean_dec(v_unused_3720_);
v___x_3653_ = v_impl_3636_;
v_isShared_3654_ = v_isSharedCheck_3715_;
goto v_resetjp_3652_;
}
else
{
lean_dec(v_impl_3636_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3715_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v_size_3655_; lean_object* v_k_3656_; lean_object* v_v_3657_; lean_object* v_l_3658_; lean_object* v_r_3659_; lean_object* v_size_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; 
v_size_3655_ = lean_ctor_get(v_l_3642_, 0);
v_k_3656_ = lean_ctor_get(v_l_3642_, 1);
v_v_3657_ = lean_ctor_get(v_l_3642_, 2);
v_l_3658_ = lean_ctor_get(v_l_3642_, 3);
v_r_3659_ = lean_ctor_get(v_l_3642_, 4);
v_size_3660_ = lean_ctor_get(v_r_3643_, 0);
v___x_3661_ = lean_unsigned_to_nat(2u);
v___x_3662_ = lean_nat_mul(v___x_3661_, v_size_3660_);
v___x_3663_ = lean_nat_dec_lt(v_size_3655_, v___x_3662_);
lean_dec(v___x_3662_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3691_; 
lean_inc(v_r_3659_);
lean_inc(v_l_3658_);
lean_inc(v_v_3657_);
lean_inc(v_k_3656_);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_l_3642_);
if (v_isSharedCheck_3691_ == 0)
{
lean_object* v_unused_3692_; lean_object* v_unused_3693_; lean_object* v_unused_3694_; lean_object* v_unused_3695_; lean_object* v_unused_3696_; 
v_unused_3692_ = lean_ctor_get(v_l_3642_, 4);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_l_3642_, 3);
lean_dec(v_unused_3693_);
v_unused_3694_ = lean_ctor_get(v_l_3642_, 2);
lean_dec(v_unused_3694_);
v_unused_3695_ = lean_ctor_get(v_l_3642_, 1);
lean_dec(v_unused_3695_);
v_unused_3696_ = lean_ctor_get(v_l_3642_, 0);
lean_dec(v_unused_3696_);
v___x_3665_ = v_l_3642_;
v_isShared_3666_ = v_isSharedCheck_3691_;
goto v_resetjp_3664_;
}
else
{
lean_dec(v_l_3642_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3691_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3681_; 
v___x_3667_ = lean_nat_add(v___x_3637_, v_size_3638_);
v___x_3668_ = lean_nat_add(v___x_3667_, v_size_3639_);
lean_dec(v_size_3639_);
if (lean_obj_tag(v_l_3658_) == 0)
{
lean_object* v_size_3689_; 
v_size_3689_ = lean_ctor_get(v_l_3658_, 0);
lean_inc(v_size_3689_);
v___y_3681_ = v_size_3689_;
goto v___jp_3680_;
}
else
{
lean_object* v___x_3690_; 
v___x_3690_ = lean_unsigned_to_nat(0u);
v___y_3681_ = v___x_3690_;
goto v___jp_3680_;
}
v___jp_3669_:
{
lean_object* v___x_3673_; lean_object* v___x_3675_; 
v___x_3673_ = lean_nat_add(v___y_3670_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec(v___y_3670_);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 4, v_r_3643_);
lean_ctor_set(v___x_3665_, 3, v_r_3659_);
lean_ctor_set(v___x_3665_, 2, v_v_3641_);
lean_ctor_set(v___x_3665_, 1, v_k_3640_);
lean_ctor_set(v___x_3665_, 0, v___x_3673_);
v___x_3675_ = v___x_3665_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_k_3640_);
lean_ctor_set(v_reuseFailAlloc_3679_, 2, v_v_3641_);
lean_ctor_set(v_reuseFailAlloc_3679_, 3, v_r_3659_);
lean_ctor_set(v_reuseFailAlloc_3679_, 4, v_r_3643_);
v___x_3675_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3677_; 
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 4, v___x_3675_);
lean_ctor_set(v___x_3653_, 3, v___y_3671_);
lean_ctor_set(v___x_3653_, 2, v_v_3657_);
lean_ctor_set(v___x_3653_, 1, v_k_3656_);
lean_ctor_set(v___x_3653_, 0, v___x_3668_);
v___x_3677_ = v___x_3653_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3668_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v_k_3656_);
lean_ctor_set(v_reuseFailAlloc_3678_, 2, v_v_3657_);
lean_ctor_set(v_reuseFailAlloc_3678_, 3, v___y_3671_);
lean_ctor_set(v_reuseFailAlloc_3678_, 4, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
v___jp_3680_:
{
lean_object* v___x_3682_; lean_object* v___x_3684_; 
v___x_3682_ = lean_nat_add(v___x_3667_, v___y_3681_);
lean_dec(v___y_3681_);
lean_dec(v___x_3667_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 4, v_l_3658_);
lean_ctor_set(v___x_3493_, 0, v___x_3682_);
v___x_3684_ = v___x_3493_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3688_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3688_, 3, v_l_3490_);
lean_ctor_set(v_reuseFailAlloc_3688_, 4, v_l_3658_);
v___x_3684_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3685_; 
v___x_3685_ = lean_nat_add(v___x_3637_, v_size_3660_);
if (lean_obj_tag(v_r_3659_) == 0)
{
lean_object* v_size_3686_; 
v_size_3686_ = lean_ctor_get(v_r_3659_, 0);
lean_inc(v_size_3686_);
v___y_3670_ = v___x_3685_;
v___y_3671_ = v___x_3684_;
v___y_3672_ = v_size_3686_;
goto v___jp_3669_;
}
else
{
lean_object* v___x_3687_; 
v___x_3687_ = lean_unsigned_to_nat(0u);
v___y_3670_ = v___x_3685_;
v___y_3671_ = v___x_3684_;
v___y_3672_ = v___x_3687_;
goto v___jp_3669_;
}
}
}
}
}
else
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3701_; 
lean_del_object(v___x_3493_);
v___x_3697_ = lean_nat_add(v___x_3637_, v_size_3638_);
v___x_3698_ = lean_nat_add(v___x_3697_, v_size_3639_);
lean_dec(v_size_3639_);
v___x_3699_ = lean_nat_add(v___x_3697_, v_size_3655_);
lean_dec(v___x_3697_);
lean_inc_ref(v_l_3490_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 4, v_l_3642_);
lean_ctor_set(v___x_3653_, 3, v_l_3490_);
lean_ctor_set(v___x_3653_, 2, v_v_3489_);
lean_ctor_set(v___x_3653_, 1, v_k_3488_);
lean_ctor_set(v___x_3653_, 0, v___x_3699_);
v___x_3701_ = v___x_3653_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3699_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3714_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3714_, 3, v_l_3490_);
lean_ctor_set(v_reuseFailAlloc_3714_, 4, v_l_3642_);
v___x_3701_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
v_isSharedCheck_3708_ = !lean_is_exclusive(v_l_3490_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; lean_object* v_unused_3710_; lean_object* v_unused_3711_; lean_object* v_unused_3712_; lean_object* v_unused_3713_; 
v_unused_3709_ = lean_ctor_get(v_l_3490_, 4);
lean_dec(v_unused_3709_);
v_unused_3710_ = lean_ctor_get(v_l_3490_, 3);
lean_dec(v_unused_3710_);
v_unused_3711_ = lean_ctor_get(v_l_3490_, 2);
lean_dec(v_unused_3711_);
v_unused_3712_ = lean_ctor_get(v_l_3490_, 1);
lean_dec(v_unused_3712_);
v_unused_3713_ = lean_ctor_get(v_l_3490_, 0);
lean_dec(v_unused_3713_);
v___x_3703_ = v_l_3490_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_dec(v_l_3490_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 4, v_r_3643_);
lean_ctor_set(v___x_3703_, 3, v___x_3701_);
lean_ctor_set(v___x_3703_, 2, v_v_3641_);
lean_ctor_set(v___x_3703_, 1, v_k_3640_);
lean_ctor_set(v___x_3703_, 0, v___x_3698_);
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_k_3640_);
lean_ctor_set(v_reuseFailAlloc_3707_, 2, v_v_3641_);
lean_ctor_set(v_reuseFailAlloc_3707_, 3, v___x_3701_);
lean_ctor_set(v_reuseFailAlloc_3707_, 4, v_r_3643_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3721_; 
v_l_3721_ = lean_ctor_get(v_impl_3636_, 3);
lean_inc(v_l_3721_);
if (lean_obj_tag(v_l_3721_) == 0)
{
lean_object* v_r_3722_; lean_object* v_k_3723_; lean_object* v_v_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3747_; 
v_r_3722_ = lean_ctor_get(v_impl_3636_, 4);
v_k_3723_ = lean_ctor_get(v_impl_3636_, 1);
v_v_3724_ = lean_ctor_get(v_impl_3636_, 2);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_impl_3636_);
if (v_isSharedCheck_3747_ == 0)
{
lean_object* v_unused_3748_; lean_object* v_unused_3749_; 
v_unused_3748_ = lean_ctor_get(v_impl_3636_, 3);
lean_dec(v_unused_3748_);
v_unused_3749_ = lean_ctor_get(v_impl_3636_, 0);
lean_dec(v_unused_3749_);
v___x_3726_ = v_impl_3636_;
v_isShared_3727_ = v_isSharedCheck_3747_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_r_3722_);
lean_inc(v_v_3724_);
lean_inc(v_k_3723_);
lean_dec(v_impl_3636_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3747_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v_k_3728_; lean_object* v_v_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3743_; 
v_k_3728_ = lean_ctor_get(v_l_3721_, 1);
v_v_3729_ = lean_ctor_get(v_l_3721_, 2);
v_isSharedCheck_3743_ = !lean_is_exclusive(v_l_3721_);
if (v_isSharedCheck_3743_ == 0)
{
lean_object* v_unused_3744_; lean_object* v_unused_3745_; lean_object* v_unused_3746_; 
v_unused_3744_ = lean_ctor_get(v_l_3721_, 4);
lean_dec(v_unused_3744_);
v_unused_3745_ = lean_ctor_get(v_l_3721_, 3);
lean_dec(v_unused_3745_);
v_unused_3746_ = lean_ctor_get(v_l_3721_, 0);
lean_dec(v_unused_3746_);
v___x_3731_ = v_l_3721_;
v_isShared_3732_ = v_isSharedCheck_3743_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_v_3729_);
lean_inc(v_k_3728_);
lean_dec(v_l_3721_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3743_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3733_; lean_object* v___x_3735_; 
v___x_3733_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3722_, 2);
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 4, v_r_3722_);
lean_ctor_set(v___x_3731_, 3, v_r_3722_);
lean_ctor_set(v___x_3731_, 2, v_v_3489_);
lean_ctor_set(v___x_3731_, 1, v_k_3488_);
lean_ctor_set(v___x_3731_, 0, v___x_3637_);
v___x_3735_ = v___x_3731_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3637_);
lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3742_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3742_, 3, v_r_3722_);
lean_ctor_set(v_reuseFailAlloc_3742_, 4, v_r_3722_);
v___x_3735_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
lean_object* v___x_3737_; 
lean_inc(v_r_3722_);
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 3, v_r_3722_);
lean_ctor_set(v___x_3726_, 0, v___x_3637_);
v___x_3737_ = v___x_3726_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3637_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_k_3723_);
lean_ctor_set(v_reuseFailAlloc_3741_, 2, v_v_3724_);
lean_ctor_set(v_reuseFailAlloc_3741_, 3, v_r_3722_);
lean_ctor_set(v_reuseFailAlloc_3741_, 4, v_r_3722_);
v___x_3737_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
lean_object* v___x_3739_; 
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 4, v___x_3737_);
lean_ctor_set(v___x_3493_, 3, v___x_3735_);
lean_ctor_set(v___x_3493_, 2, v_v_3729_);
lean_ctor_set(v___x_3493_, 1, v_k_3728_);
lean_ctor_set(v___x_3493_, 0, v___x_3733_);
v___x_3739_ = v___x_3493_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3733_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_k_3728_);
lean_ctor_set(v_reuseFailAlloc_3740_, 2, v_v_3729_);
lean_ctor_set(v_reuseFailAlloc_3740_, 3, v___x_3735_);
lean_ctor_set(v_reuseFailAlloc_3740_, 4, v___x_3737_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
}
}
else
{
lean_object* v_r_3750_; 
v_r_3750_ = lean_ctor_get(v_impl_3636_, 4);
lean_inc(v_r_3750_);
if (lean_obj_tag(v_r_3750_) == 0)
{
lean_object* v_k_3751_; lean_object* v_v_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3763_; 
v_k_3751_ = lean_ctor_get(v_impl_3636_, 1);
v_v_3752_ = lean_ctor_get(v_impl_3636_, 2);
v_isSharedCheck_3763_ = !lean_is_exclusive(v_impl_3636_);
if (v_isSharedCheck_3763_ == 0)
{
lean_object* v_unused_3764_; lean_object* v_unused_3765_; lean_object* v_unused_3766_; 
v_unused_3764_ = lean_ctor_get(v_impl_3636_, 4);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_impl_3636_, 3);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_impl_3636_, 0);
lean_dec(v_unused_3766_);
v___x_3754_ = v_impl_3636_;
v_isShared_3755_ = v_isSharedCheck_3763_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_v_3752_);
lean_inc(v_k_3751_);
lean_dec(v_impl_3636_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3763_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3756_; lean_object* v___x_3758_; 
v___x_3756_ = lean_unsigned_to_nat(3u);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 4, v_l_3721_);
lean_ctor_set(v___x_3754_, 2, v_v_3489_);
lean_ctor_set(v___x_3754_, 1, v_k_3488_);
lean_ctor_set(v___x_3754_, 0, v___x_3637_);
v___x_3758_ = v___x_3754_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v___x_3637_);
lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3762_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3762_, 3, v_l_3721_);
lean_ctor_set(v_reuseFailAlloc_3762_, 4, v_l_3721_);
v___x_3758_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
lean_object* v___x_3760_; 
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 4, v_r_3750_);
lean_ctor_set(v___x_3493_, 3, v___x_3758_);
lean_ctor_set(v___x_3493_, 2, v_v_3752_);
lean_ctor_set(v___x_3493_, 1, v_k_3751_);
lean_ctor_set(v___x_3493_, 0, v___x_3756_);
v___x_3760_ = v___x_3493_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3756_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_k_3751_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v_v_3752_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v___x_3758_);
lean_ctor_set(v_reuseFailAlloc_3761_, 4, v_r_3750_);
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
else
{
lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3767_ = lean_unsigned_to_nat(2u);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 4, v_impl_3636_);
lean_ctor_set(v___x_3493_, 3, v_r_3750_);
lean_ctor_set(v___x_3493_, 0, v___x_3767_);
v___x_3769_ = v___x_3493_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3767_);
lean_ctor_set(v_reuseFailAlloc_3770_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3770_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3770_, 3, v_r_3750_);
lean_ctor_set(v_reuseFailAlloc_3770_, 4, v_impl_3636_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
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
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = lean_unsigned_to_nat(1u);
v___x_3773_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
lean_ctor_set(v___x_3773_, 1, v_k_3484_);
lean_ctor_set(v___x_3773_, 2, v_v_3485_);
lean_ctor_set(v___x_3773_, 3, v_t_3486_);
lean_ctor_set(v___x_3773_, 4, v_t_3486_);
return v___x_3773_;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3774_ = lean_box(1);
v___x_3775_ = l_Lake_LeanLib_defaultFacetConfig;
v___x_3776_ = l_Lake_LeanLib_defaultFacet;
v___x_3777_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3776_, v___x_3775_, v___x_3774_);
return v___x_3777_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3778_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__0, &l_Lake_LeanLib_initFacetConfigs___closed__0_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__0);
v___x_3779_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig));
v___x_3780_ = l_Lake_LeanLib_modulesFacet;
v___x_3781_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3780_, v___x_3779_, v___x_3778_);
return v___x_3781_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3782_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__1, &l_Lake_LeanLib_initFacetConfigs___closed__1_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__1);
v___x_3783_ = l_Lake_LeanLib_leanArtsFacetConfig;
v___x_3784_ = l_Lake_LeanLib_leanArtsFacet;
v___x_3785_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3784_, v___x_3783_, v___x_3782_);
return v___x_3785_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3786_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__2, &l_Lake_LeanLib_initFacetConfigs___closed__2_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__2);
v___x_3787_ = l_Lake_LeanLib_staticFacetConfig;
v___x_3788_ = l_Lake_LeanLib_staticFacet;
v___x_3789_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3788_, v___x_3787_, v___x_3786_);
return v___x_3789_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3790_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__3, &l_Lake_LeanLib_initFacetConfigs___closed__3_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__3);
v___x_3791_ = l_Lake_LeanLib_staticExportFacetConfig;
v___x_3792_ = l_Lake_LeanLib_staticExportFacet;
v___x_3793_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3792_, v___x_3791_, v___x_3790_);
return v___x_3793_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3794_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__4, &l_Lake_LeanLib_initFacetConfigs___closed__4_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__4);
v___x_3795_ = l_Lake_LeanLib_sharedFacetConfig;
v___x_3796_ = l_Lake_LeanLib_sharedFacet;
v___x_3797_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3796_, v___x_3795_, v___x_3794_);
return v___x_3797_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3798_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__5, &l_Lake_LeanLib_initFacetConfigs___closed__5_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__5);
v___x_3799_ = l_Lake_LeanLib_extraDepFacetConfig;
v___x_3800_ = l_Lake_LeanLib_extraDepFacet;
v___x_3801_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3800_, v___x_3799_, v___x_3798_);
return v___x_3801_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__6, &l_Lake_LeanLib_initFacetConfigs___closed__6_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__6);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3803_, lean_object* v_k_3804_, lean_object* v_v_3805_, lean_object* v_t_3806_, lean_object* v_hl_3807_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3804_, v_v_3805_, v_t_3806_);
return v___x_3808_;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs(void){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = l_Lake_LeanLib_initFacetConfigs;
return v___x_3809_;
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
