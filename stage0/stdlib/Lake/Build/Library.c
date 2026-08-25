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
uint8_t v___x_7361__boxed_431_; lean_object* v_res_432_; 
v___x_7361__boxed_431_ = lean_unbox(v___x_422_);
v_res_432_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(v_self_419_, v_col_420_, v___x_421_, v___x_7361__boxed_431_, v___x_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
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
size_t v___x_531_; size_t v___x_532_; lean_object* v___x_533_; 
v___x_531_ = ((size_t)0ULL);
v___x_532_ = lean_usize_of_nat(v___x_529_);
v___x_533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_518_, v___x_531_, v___x_532_, v___x_527_);
lean_dec_ref(v_a_518_);
v___y_520_ = v___x_533_;
goto v___jp_519_;
}
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(v_a_518_);
v___x_535_ = l_Lean_Json_compress(v___x_534_);
return v___x_535_;
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
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0___boxed(lean_object* v_fmt_536_, lean_object* v_a_537_){
_start:
{
uint8_t v_fmt_boxed_538_; lean_object* v_res_539_; 
v_fmt_boxed_538_ = lean_unbox(v_fmt_536_);
v_res_539_ = l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(v_fmt_boxed_538_, v_a_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(lean_object* v_as_553_, size_t v_i_554_, size_t v_stop_555_, lean_object* v_b_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
uint8_t v___x_564_; 
v___x_564_ = lean_usize_dec_eq(v_i_554_, v_stop_555_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v_lib_566_; lean_object* v_pkg_567_; lean_object* v_name_568_; lean_object* v_keyName_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_565_ = lean_array_uget_borrowed(v_as_553_, v_i_554_);
v_lib_566_ = lean_ctor_get(v___x_565_, 0);
v_pkg_567_ = lean_ctor_get(v_lib_566_, 0);
v_name_568_ = lean_ctor_get(v___x_565_, 1);
v_keyName_569_ = lean_ctor_get(v_pkg_567_, 2);
v___x_570_ = l_Lake_Module_leanArtsFacet;
lean_inc(v_name_568_);
lean_inc(v_keyName_569_);
v___x_571_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_571_, 0, v_keyName_569_);
lean_ctor_set(v___x_571_, 1, v_name_568_);
v___x_572_ = l_Lake_Module_keyword;
lean_inc(v___x_565_);
v___x_573_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
lean_ctor_set(v___x_573_, 2, v___x_565_);
lean_ctor_set(v___x_573_, 3, v___x_570_);
lean_inc_ref(v___y_557_);
lean_inc_ref(v___y_561_);
lean_inc(v___y_560_);
lean_inc(v___y_559_);
lean_inc(v___y_558_);
v___x_574_ = lean_apply_7(v___y_557_, v___x_573_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, lean_box(0));
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v_a_576_; lean_object* v___x_577_; size_t v___x_578_; size_t v___x_579_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
v_a_576_ = lean_ctor_get(v___x_574_, 1);
lean_inc(v_a_576_);
lean_dec_ref_known(v___x_574_, 2);
v___x_577_ = l_Lake_Job_mix___redArg(v_b_556_, v_a_575_);
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_add(v_i_554_, v___x_578_);
v_i_554_ = v___x_579_;
v_b_556_ = v___x_577_;
v___y_562_ = v_a_576_;
goto _start;
}
else
{
lean_object* v_a_581_; lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec_ref(v___y_557_);
lean_dec_ref(v_b_556_);
v_a_581_ = lean_ctor_get(v___x_574_, 0);
v_a_582_ = lean_ctor_get(v___x_574_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_574_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_inc(v_a_581_);
lean_dec(v___x_574_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_581_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
else
{
lean_object* v___x_590_; 
lean_dec_ref(v___y_557_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v_b_556_);
lean_ctor_set(v___x_590_, 1, v___y_562_);
return v___x_590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0___boxed(lean_object* v_as_591_, lean_object* v_i_592_, lean_object* v_stop_593_, lean_object* v_b_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
size_t v_i_boxed_602_; size_t v_stop_boxed_603_; lean_object* v_res_604_; 
v_i_boxed_602_ = lean_unbox_usize(v_i_592_);
lean_dec(v_i_592_);
v_stop_boxed_603_ = lean_unbox_usize(v_stop_593_);
lean_dec(v_stop_593_);
v_res_604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_as_591_, v_i_boxed_602_, v_stop_boxed_603_, v_b_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v_as_591_);
return v_res_604_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_609_ = 0;
v___x_610_ = 0;
v___x_611_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v___x_612_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_608_);
lean_ctor_set(v___x_612_, 2, v___x_607_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*3, v___x_610_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*3 + 1, v___x_609_);
return v___x_612_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1);
v___x_614_ = lean_box(0);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2);
v___x_617_ = lean_task_pure(v___x_616_);
return v___x_617_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4(void){
_start:
{
uint8_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_618_ = 0;
v___x_619_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_620_ = lean_box(0);
v___x_621_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3);
v___x_622_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v___x_620_);
lean_ctor_set(v___x_622_, 2, v___x_619_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*3, v___x_618_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(lean_object* v_self_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_pkg_631_; lean_object* v_name_632_; lean_object* v_keyName_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_pkg_631_ = lean_ctor_get(v_self_623_, 0);
v_name_632_ = lean_ctor_get(v_self_623_, 1);
v_keyName_633_ = lean_ctor_get(v_pkg_631_, 2);
v___x_634_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_632_);
lean_inc(v_keyName_633_);
v___x_635_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_635_, 0, v_keyName_633_);
lean_ctor_set(v___x_635_, 1, v_name_632_);
v___x_636_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_637_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
lean_ctor_set(v___x_637_, 2, v_self_623_);
lean_ctor_set(v___x_637_, 3, v___x_634_);
lean_inc_ref(v_a_624_);
lean_inc_ref(v_a_628_);
lean_inc(v_a_627_);
lean_inc(v_a_626_);
lean_inc(v_a_625_);
v___x_638_ = lean_apply_7(v_a_624_, v___x_637_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, lean_box(0));
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v_a_640_; lean_object* v___x_641_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
v_a_640_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_638_, 2);
v___x_641_ = l_Lake_Job_await___redArg(v_a_639_, v_a_640_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_664_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_a_643_ = lean_ctor_get(v___x_641_, 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_664_ == 0)
{
v___x_645_ = v___x_641_;
v_isShared_646_ = v_isSharedCheck_664_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_664_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4);
v___x_649_ = lean_array_get_size(v_a_642_);
v___x_650_ = lean_nat_dec_lt(v___x_647_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_652_; 
lean_dec(v_a_642_);
lean_dec_ref(v_a_624_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_648_);
v___x_652_ = v___x_645_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_a_643_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
else
{
uint8_t v___x_654_; 
v___x_654_ = lean_nat_dec_le(v___x_649_, v___x_649_);
if (v___x_654_ == 0)
{
if (v___x_650_ == 0)
{
lean_object* v___x_656_; 
lean_dec(v_a_642_);
lean_dec_ref(v_a_624_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_648_);
v___x_656_ = v___x_645_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_a_643_);
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
size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; 
lean_del_object(v___x_645_);
v___x_658_ = ((size_t)0ULL);
v___x_659_ = lean_usize_of_nat(v___x_649_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_642_, v___x_658_, v___x_659_, v___x_648_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_643_);
lean_dec(v_a_642_);
return v___x_660_;
}
}
else
{
size_t v___x_661_; size_t v___x_662_; lean_object* v___x_663_; 
lean_del_object(v___x_645_);
v___x_661_ = ((size_t)0ULL);
v___x_662_ = lean_usize_of_nat(v___x_649_);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_642_, v___x_661_, v___x_662_, v___x_648_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_643_);
lean_dec(v_a_642_);
return v___x_663_;
}
}
}
}
else
{
lean_object* v_a_665_; lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v_a_624_);
v_a_665_ = lean_ctor_get(v___x_641_, 0);
v_a_666_ = lean_ctor_get(v___x_641_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_641_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_inc(v_a_665_);
lean_dec(v___x_641_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_665_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
lean_object* v_a_674_; lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref(v_a_624_);
v_a_674_ = lean_ctor_get(v___x_638_, 0);
v_a_675_ = lean_ctor_get(v___x_638_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_638_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_inc(v_a_674_);
lean_dec(v___x_638_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_674_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___boxed(lean_object* v_self_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(v_self_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec(v_a_687_);
lean_dec(v_a_686_);
lean_dec(v_a_685_);
return v_res_691_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_box(0);
v___x_693_ = l_Lean_Json_compress(v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(uint8_t v_fmt_694_){
_start:
{
if (v_fmt_694_ == 0)
{
lean_object* v___x_695_; 
v___x_695_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
return v___x_695_;
}
else
{
lean_object* v___x_696_; 
v___x_696_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0);
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_697_){
_start:
{
uint8_t v_fmt_boxed_698_; lean_object* v_res_699_; 
v_fmt_boxed_698_ = lean_unbox(v_fmt_697_);
v_res_699_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_boxed_698_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(uint8_t v_fmt_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_700_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___boxed(lean_object* v_fmt_703_, lean_object* v_a_704_){
_start:
{
uint8_t v_fmt_boxed_705_; lean_object* v_res_706_; 
v_fmt_boxed_705_ = lean_unbox(v_fmt_703_);
v_res_706_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(v_fmt_boxed_705_, v_a_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0(uint8_t v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v___y_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
uint8_t v___y_68__boxed_712_; lean_object* v_res_713_; 
v___y_68__boxed_712_ = lean_unbox(v___y_710_);
v_res_713_ = l_Lake_LeanLib_leanArtsFacetConfig___lam__0(v___y_68__boxed_712_, v___y_711_);
return v_res_713_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_716_; uint8_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___f_716_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_717_ = 1;
v___x_718_ = l_Lake_instDataKindUnit;
v___x_719_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__1));
v___x_720_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_721_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v___x_719_);
lean_ctor_set(v___x_721_, 2, v___x_718_);
lean_ctor_set(v___x_721_, 3, v___f_716_);
lean_ctor_set_uint8(v___x_721_, sizeof(void*)*4, v___x_717_);
lean_ctor_set_uint8(v___x_721_, sizeof(void*)*4 + 1, v___x_717_);
return v___x_721_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig(void){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_obj_once(&l_Lake_LeanLib_leanArtsFacetConfig___closed__2, &l_Lake_LeanLib_leanArtsFacetConfig___closed__2_once, _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(lean_object* v_a_723_, lean_object* v_x_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lake_ModuleFacet_fetch___redArg(v_x_724_, v_a_723_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object* v_a_733_, lean_object* v_x_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(v_a_733_, v_x_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec(v___y_737_);
lean_dec(v___y_736_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(uint8_t v_shouldExport_743_, lean_object* v___x_744_, lean_object* v_bs_745_, lean_object* v_a_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_lib_754_; lean_object* v_config_755_; lean_object* v_nativeFacets_756_; lean_object* v___f_757_; lean_object* v___x_758_; lean_object* v___x_759_; size_t v_sz_760_; size_t v___x_761_; lean_object* v___x_187444__overap_762_; lean_object* v___x_763_; 
v_lib_754_ = lean_ctor_get(v_a_746_, 0);
v_config_755_ = lean_ctor_get(v_lib_754_, 2);
v_nativeFacets_756_ = lean_ctor_get(v_config_755_, 8);
lean_inc_ref(v_nativeFacets_756_);
v___f_757_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed), 9, 1);
lean_closure_set(v___f_757_, 0, v_a_746_);
v___x_758_ = lean_box(v_shouldExport_743_);
v___x_759_ = lean_apply_1(v_nativeFacets_756_, v___x_758_);
v_sz_760_ = lean_array_size(v___x_759_);
v___x_761_ = ((size_t)0ULL);
v___x_187444__overap_762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_744_, v___f_757_, v_sz_760_, v___x_761_, v___x_759_);
lean_inc_ref(v___y_751_);
lean_inc(v___y_750_);
lean_inc(v___y_749_);
lean_inc(v___y_748_);
v___x_763_ = lean_apply_7(v___x_187444__overap_762_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, lean_box(0));
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_773_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
v_a_765_ = lean_ctor_get(v___x_763_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_773_ == 0)
{
v___x_767_ = v___x_763_;
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_inc(v_a_764_);
lean_dec(v___x_763_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = l_Array_append___redArg(v_bs_745_, v_a_764_);
lean_dec(v_a_764_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_a_765_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
else
{
lean_dec_ref(v_bs_745_);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed(lean_object* v_shouldExport_774_, lean_object* v___x_775_, lean_object* v_bs_776_, lean_object* v_a_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
uint8_t v_shouldExport_boxed_785_; lean_object* v_res_786_; 
v_shouldExport_boxed_785_ = lean_unbox(v_shouldExport_774_);
v_res_786_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(v_shouldExport_boxed_785_, v___x_775_, v_bs_776_, v_a_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec(v___y_780_);
lean_dec(v___y_779_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(lean_object* v___x_787_, lean_object* v_pkg_788_, lean_object* v_x_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lake_Target_fetchIn___redArg(v___x_787_, v_pkg_788_, v_x_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object* v___x_798_, lean_object* v_pkg_799_, lean_object* v_x_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(v___x_798_, v_pkg_799_, v_x_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec(v___y_803_);
lean_dec(v___y_802_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object* v_a_809_, lean_object* v_x_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_log_819_; uint8_t v_action_820_; uint8_t v_wantsRebuild_821_; lean_object* v_trace_822_; lean_object* v_buildTime_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_log_819_ = lean_ctor_get(v___y_817_, 0);
v_action_820_ = lean_ctor_get_uint8(v___y_817_, sizeof(void*)*3);
v_wantsRebuild_821_ = lean_ctor_get_uint8(v___y_817_, sizeof(void*)*3 + 1);
v_trace_822_ = lean_ctor_get(v___y_817_, 1);
v_buildTime_823_ = lean_ctor_get(v___y_817_, 2);
v___x_824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_825_ = lean_string_append(v___y_811_, v___x_824_);
v___x_826_ = lean_io_prim_handle_put_str(v_a_809_, v___x_825_);
lean_dec_ref(v___x_825_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_828_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_826_, 1);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v_a_827_);
lean_ctor_set(v___x_828_, 1, v___y_817_);
return v___x_828_;
}
else
{
lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_842_; 
lean_inc(v_buildTime_823_);
lean_inc_ref(v_trace_822_);
lean_inc_ref(v_log_819_);
v_isSharedCheck_842_ = !lean_is_exclusive(v___y_817_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; lean_object* v_unused_844_; lean_object* v_unused_845_; 
v_unused_843_ = lean_ctor_get(v___y_817_, 2);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v___y_817_, 1);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v___y_817_, 0);
lean_dec(v_unused_845_);
v___x_830_ = v___y_817_;
v_isShared_831_ = v_isSharedCheck_842_;
goto v_resetjp_829_;
}
else
{
lean_dec(v___y_817_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_842_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_a_832_; lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; 
v_a_832_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_826_, 1);
v___x_833_ = lean_io_error_to_string(v_a_832_);
v___x_834_ = 3;
v___x_835_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set_uint8(v___x_835_, sizeof(void*)*1, v___x_834_);
v___x_836_ = lean_array_get_size(v_log_819_);
v___x_837_ = lean_array_push(v_log_819_, v___x_835_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_837_);
v___x_839_ = v___x_830_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_trace_822_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_buildTime_823_);
lean_ctor_set_uint8(v_reuseFailAlloc_841_, sizeof(void*)*3, v_action_820_);
lean_ctor_set_uint8(v_reuseFailAlloc_841_, sizeof(void*)*3 + 1, v_wantsRebuild_821_);
v___x_839_ = v_reuseFailAlloc_841_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_840_; 
v___x_840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_836_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object* v_a_846_, lean_object* v_x_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(v_a_846_, v_x_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v_a_846_);
return v_res_856_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_864_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3));
v___x_865_ = lean_unsigned_to_nat(5u);
v___x_866_ = lean_mk_empty_array_with_capacity(v___x_865_);
v___x_867_ = lean_array_push(v___x_866_, v___x_864_);
return v___x_867_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4));
v___x_869_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6);
v___x_870_ = lean_array_push(v___x_869_, v___x_868_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(uint8_t v_bootstrap_873_, lean_object* v___y_874_, lean_object* v_oFiles_875_, uint8_t v_shouldExport_876_, uint8_t v___x_877_, lean_object* v___x_878_, size_t v___x_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
if (v_bootstrap_873_ == 0)
{
lean_object* v_toContext_887_; lean_object* v_lakeEnv_888_; lean_object* v_lean_889_; lean_object* v_log_890_; uint8_t v_action_891_; uint8_t v_wantsRebuild_892_; lean_object* v_trace_893_; lean_object* v_buildTime_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_924_; 
lean_dec_ref(v___y_880_);
lean_dec_ref(v___x_878_);
v_toContext_887_ = lean_ctor_get(v___y_884_, 1);
v_lakeEnv_888_ = lean_ctor_get(v_toContext_887_, 0);
v_lean_889_ = lean_ctor_get(v_lakeEnv_888_, 1);
v_log_890_ = lean_ctor_get(v___y_885_, 0);
v_action_891_ = lean_ctor_get_uint8(v___y_885_, sizeof(void*)*3);
v_wantsRebuild_892_ = lean_ctor_get_uint8(v___y_885_, sizeof(void*)*3 + 1);
v_trace_893_ = lean_ctor_get(v___y_885_, 1);
v_buildTime_894_ = lean_ctor_get(v___y_885_, 2);
v_isSharedCheck_924_ = !lean_is_exclusive(v___y_885_);
if (v_isSharedCheck_924_ == 0)
{
v___x_896_ = v___y_885_;
v_isShared_897_ = v_isSharedCheck_924_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_buildTime_894_);
lean_inc(v_trace_893_);
lean_inc(v_log_890_);
lean_dec(v___y_885_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_924_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_ar_898_; lean_object* v___x_899_; 
v_ar_898_ = lean_ctor_get(v_lean_889_, 13);
lean_inc_ref(v_ar_898_);
v___x_899_ = l_Lake_compileStaticLib(v___y_874_, v_oFiles_875_, v_ar_898_, v_bootstrap_873_, v_log_890_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_911_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
v_a_901_ = lean_ctor_get(v___x_899_, 1);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_911_ == 0)
{
v___x_903_ = v___x_899_;
v_isShared_904_ = v_isSharedCheck_911_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_inc(v_a_900_);
lean_dec(v___x_899_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_911_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v_a_901_);
v___x_906_ = v___x_896_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_901_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_trace_893_);
lean_ctor_set(v_reuseFailAlloc_910_, 2, v_buildTime_894_);
lean_ctor_set_uint8(v_reuseFailAlloc_910_, sizeof(void*)*3, v_action_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_910_, sizeof(void*)*3 + 1, v_wantsRebuild_892_);
v___x_906_ = v_reuseFailAlloc_910_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_908_; 
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 1, v___x_906_);
v___x_908_ = v___x_903_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_900_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_923_; 
v_a_912_ = lean_ctor_get(v___x_899_, 0);
v_a_913_ = lean_ctor_get(v___x_899_, 1);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_923_ == 0)
{
v___x_915_ = v___x_899_;
v_isShared_916_ = v_isSharedCheck_923_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_inc(v_a_912_);
lean_dec(v___x_899_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_923_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v_a_913_);
v___x_918_ = v___x_896_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_913_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_trace_893_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_buildTime_894_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3, v_action_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_922_, sizeof(void*)*3 + 1, v_wantsRebuild_892_);
v___x_918_ = v_reuseFailAlloc_922_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_920_; 
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 1, v___x_918_);
v___x_920_ = v___x_915_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_912_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
else
{
uint8_t v___x_925_; 
v___x_925_ = l_System_Platform_isOSX;
if (v___x_925_ == 0)
{
uint8_t v___x_926_; 
lean_dec_ref(v___y_880_);
lean_dec_ref(v___x_878_);
v___x_926_ = l_System_Platform_isWindows;
if (v___x_926_ == 0)
{
lean_object* v_toContext_927_; lean_object* v_lakeEnv_928_; lean_object* v_lean_929_; lean_object* v_log_930_; uint8_t v_action_931_; uint8_t v_wantsRebuild_932_; lean_object* v_trace_933_; lean_object* v_buildTime_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_964_; 
v_toContext_927_ = lean_ctor_get(v___y_884_, 1);
v_lakeEnv_928_ = lean_ctor_get(v_toContext_927_, 0);
v_lean_929_ = lean_ctor_get(v_lakeEnv_928_, 1);
v_log_930_ = lean_ctor_get(v___y_885_, 0);
v_action_931_ = lean_ctor_get_uint8(v___y_885_, sizeof(void*)*3);
v_wantsRebuild_932_ = lean_ctor_get_uint8(v___y_885_, sizeof(void*)*3 + 1);
v_trace_933_ = lean_ctor_get(v___y_885_, 1);
v_buildTime_934_ = lean_ctor_get(v___y_885_, 2);
v_isSharedCheck_964_ = !lean_is_exclusive(v___y_885_);
if (v_isSharedCheck_964_ == 0)
{
v___x_936_ = v___y_885_;
v_isShared_937_ = v_isSharedCheck_964_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_buildTime_934_);
lean_inc(v_trace_933_);
lean_inc(v_log_930_);
lean_dec(v___y_885_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_964_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_ar_938_; lean_object* v___x_939_; 
v_ar_938_ = lean_ctor_get(v_lean_929_, 13);
lean_inc_ref(v_ar_938_);
v___x_939_ = l_Lake_compileStaticLib(v___y_874_, v_oFiles_875_, v_ar_938_, v___x_926_, v_log_930_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_951_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
v_a_941_ = lean_ctor_get(v___x_939_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_951_ == 0)
{
v___x_943_ = v___x_939_;
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_inc(v_a_940_);
lean_dec(v___x_939_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_a_941_);
v___x_946_ = v___x_936_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_941_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_trace_933_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_buildTime_934_);
lean_ctor_set_uint8(v_reuseFailAlloc_950_, sizeof(void*)*3, v_action_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_950_, sizeof(void*)*3 + 1, v_wantsRebuild_932_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_946_);
v___x_948_ = v___x_943_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_940_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_963_; 
v_a_952_ = lean_ctor_get(v___x_939_, 0);
v_a_953_ = lean_ctor_get(v___x_939_, 1);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_963_ == 0)
{
v___x_955_ = v___x_939_;
v_isShared_956_ = v_isSharedCheck_963_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_inc(v_a_952_);
lean_dec(v___x_939_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_963_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_a_953_);
v___x_958_ = v___x_936_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_953_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_trace_933_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_buildTime_934_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, sizeof(void*)*3, v_action_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_962_, sizeof(void*)*3 + 1, v_wantsRebuild_932_);
v___x_958_ = v_reuseFailAlloc_962_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_960_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v___x_958_);
v___x_960_ = v___x_955_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_952_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_965_; lean_object* v_lakeEnv_966_; lean_object* v_lean_967_; lean_object* v_log_968_; uint8_t v_action_969_; uint8_t v_wantsRebuild_970_; lean_object* v_trace_971_; lean_object* v_buildTime_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1002_; 
v_toContext_965_ = lean_ctor_get(v___y_884_, 1);
v_lakeEnv_966_ = lean_ctor_get(v_toContext_965_, 0);
v_lean_967_ = lean_ctor_get(v_lakeEnv_966_, 1);
v_log_968_ = lean_ctor_get(v___y_885_, 0);
v_action_969_ = lean_ctor_get_uint8(v___y_885_, sizeof(void*)*3);
v_wantsRebuild_970_ = lean_ctor_get_uint8(v___y_885_, sizeof(void*)*3 + 1);
v_trace_971_ = lean_ctor_get(v___y_885_, 1);
v_buildTime_972_ = lean_ctor_get(v___y_885_, 2);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___y_885_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_974_ = v___y_885_;
v_isShared_975_ = v_isSharedCheck_1002_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_buildTime_972_);
lean_inc(v_trace_971_);
lean_inc(v_log_968_);
lean_dec(v___y_885_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1002_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_ar_976_; lean_object* v___x_977_; 
v_ar_976_ = lean_ctor_get(v_lean_967_, 13);
lean_inc_ref(v_ar_976_);
v___x_977_ = l_Lake_compileStaticLib(v___y_874_, v_oFiles_875_, v_ar_976_, v_shouldExport_876_, v_log_968_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_989_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_a_979_ = lean_ctor_get(v___x_977_, 1);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_989_ == 0)
{
v___x_981_ = v___x_977_;
v_isShared_982_ = v_isSharedCheck_989_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_989_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v_a_979_);
v___x_984_ = v___x_974_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_979_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_trace_971_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v_buildTime_972_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, sizeof(void*)*3, v_action_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_988_, sizeof(void*)*3 + 1, v_wantsRebuild_970_);
v___x_984_ = v_reuseFailAlloc_988_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
lean_object* v___x_986_; 
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 1, v___x_984_);
v___x_986_ = v___x_981_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_978_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
else
{
lean_object* v_a_990_; lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1001_; 
v_a_990_ = lean_ctor_get(v___x_977_, 0);
v_a_991_ = lean_ctor_get(v___x_977_, 1);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_993_ = v___x_977_;
v_isShared_994_ = v_isSharedCheck_1001_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_inc(v_a_990_);
lean_dec(v___x_977_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1001_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v_a_991_);
v___x_996_ = v___x_974_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_991_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_trace_971_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v_buildTime_972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1000_, sizeof(void*)*3, v_action_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_1000_, sizeof(void*)*3 + 1, v_wantsRebuild_970_);
v___x_996_ = v_reuseFailAlloc_1000_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
lean_object* v___x_998_; 
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v___x_996_);
v___x_998_ = v___x_993_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_990_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1003_; uint8_t v_action_1004_; uint8_t v_wantsRebuild_1005_; lean_object* v_trace_1006_; lean_object* v_buildTime_1007_; lean_object* v___x_1008_; 
v_log_1003_ = lean_ctor_get(v___y_885_, 0);
v_action_1004_ = lean_ctor_get_uint8(v___y_885_, sizeof(void*)*3);
v_wantsRebuild_1005_ = lean_ctor_get_uint8(v___y_885_, sizeof(void*)*3 + 1);
v_trace_1006_ = lean_ctor_get(v___y_885_, 1);
v_buildTime_1007_ = lean_ctor_get(v___y_885_, 2);
lean_inc_ref(v___y_874_);
v___x_1008_ = l_Lake_createParentDirs(v___y_874_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v_a_1012_; lean_object* v___y_1059_; uint8_t v___x_1061_; lean_object* v___x_1062_; 
lean_dec_ref_known(v___x_1008_, 1);
v___x_1009_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_874_);
v___x_1010_ = l_System_FilePath_addExtension(v___y_874_, v___x_1009_);
v___x_1061_ = 1;
v___x_1062_ = lean_io_prim_handle_mk(v___x_1010_, v___x_1061_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = lean_array_get_size(v_oFiles_875_);
v___x_1066_ = lean_nat_dec_lt(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_dec(v_a_1063_);
lean_dec_ref(v___y_880_);
lean_dec_ref(v___x_878_);
lean_dec_ref(v_oFiles_875_);
v_a_1012_ = v___y_885_;
goto v___jp_1011_;
}
else
{
lean_object* v___f_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___f_1067_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1067_, 0, v_a_1063_);
v___x_1068_ = lean_box(0);
v___x_1069_ = lean_nat_dec_le(v___x_1065_, v___x_1065_);
if (v___x_1069_ == 0)
{
if (v___x_1066_ == 0)
{
lean_dec_ref(v___f_1067_);
lean_dec_ref(v___y_880_);
lean_dec_ref(v___x_878_);
lean_dec_ref(v_oFiles_875_);
v_a_1012_ = v___y_885_;
goto v___jp_1011_;
}
else
{
size_t v___x_1070_; lean_object* v___x_187602__overap_1071_; lean_object* v___x_1072_; 
v___x_1070_ = lean_usize_of_nat(v___x_1065_);
v___x_187602__overap_1071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_878_, v___f_1067_, v_oFiles_875_, v___x_879_, v___x_1070_, v___x_1068_);
lean_inc_ref(v___y_884_);
lean_inc(v___y_883_);
lean_inc(v___y_882_);
lean_inc(v___y_881_);
v___x_1072_ = lean_apply_7(v___x_187602__overap_1071_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, lean_box(0));
v___y_1059_ = v___x_1072_;
goto v___jp_1058_;
}
}
else
{
size_t v___x_1073_; lean_object* v___x_187604__overap_1074_; lean_object* v___x_1075_; 
v___x_1073_ = lean_usize_of_nat(v___x_1065_);
v___x_187604__overap_1074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_878_, v___f_1067_, v_oFiles_875_, v___x_879_, v___x_1073_, v___x_1068_);
lean_inc_ref(v___y_884_);
lean_inc(v___y_883_);
lean_inc(v___y_882_);
lean_inc(v___y_881_);
v___x_1075_ = lean_apply_7(v___x_187604__overap_1074_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, lean_box(0));
v___y_1059_ = v___x_1075_;
goto v___jp_1058_;
}
}
}
else
{
lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1089_; 
lean_inc(v_buildTime_1007_);
lean_inc_ref(v_trace_1006_);
lean_inc_ref(v_log_1003_);
lean_dec_ref(v___x_1010_);
lean_dec_ref(v___y_880_);
lean_dec_ref(v___x_878_);
lean_dec_ref(v_oFiles_875_);
lean_dec_ref(v___y_874_);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___y_885_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; lean_object* v_unused_1091_; lean_object* v_unused_1092_; 
v_unused_1090_ = lean_ctor_get(v___y_885_, 2);
lean_dec(v_unused_1090_);
v_unused_1091_ = lean_ctor_get(v___y_885_, 1);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v___y_885_, 0);
lean_dec(v_unused_1092_);
v___x_1077_ = v___y_885_;
v_isShared_1078_ = v_isSharedCheck_1089_;
goto v_resetjp_1076_;
}
else
{
lean_dec(v___y_885_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1089_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v_a_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v_a_1079_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1062_, 1);
v___x_1080_ = lean_io_error_to_string(v_a_1079_);
v___x_1081_ = 3;
v___x_1082_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set_uint8(v___x_1082_, sizeof(void*)*1, v___x_1081_);
v___x_1083_ = lean_array_get_size(v_log_1003_);
v___x_1084_ = lean_array_push(v_log_1003_, v___x_1082_);
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
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_trace_1006_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_buildTime_1007_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*3, v_action_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1088_, sizeof(void*)*3 + 1, v_wantsRebuild_1005_);
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
v___jp_1011_:
{
lean_object* v___x_1013_; lean_object* v_log_1014_; uint8_t v_action_1015_; uint8_t v_wantsRebuild_1016_; lean_object* v_trace_1017_; lean_object* v_buildTime_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1057_; 
v___x_1013_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1014_ = lean_ctor_get(v_a_1012_, 0);
v_action_1015_ = lean_ctor_get_uint8(v_a_1012_, sizeof(void*)*3);
v_wantsRebuild_1016_ = lean_ctor_get_uint8(v_a_1012_, sizeof(void*)*3 + 1);
v_trace_1017_ = lean_ctor_get(v_a_1012_, 1);
v_buildTime_1018_ = lean_ctor_get(v_a_1012_, 2);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_a_1012_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1020_ = v_a_1012_;
v_isShared_1021_ = v_isSharedCheck_1057_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_buildTime_1018_);
lean_inc(v_trace_1017_);
lean_inc(v_log_1014_);
lean_dec(v_a_1012_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1057_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1022_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1023_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1024_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1025_ = lean_array_push(v___x_1024_, v___y_874_);
v___x_1026_ = lean_array_push(v___x_1025_, v___x_1023_);
v___x_1027_ = lean_array_push(v___x_1026_, v___x_1010_);
v___x_1028_ = lean_box(0);
v___x_1029_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1030_ = 0;
v___x_1031_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1031_, 0, v___x_1013_);
lean_ctor_set(v___x_1031_, 1, v___x_1022_);
lean_ctor_set(v___x_1031_, 2, v___x_1027_);
lean_ctor_set(v___x_1031_, 3, v___x_1028_);
lean_ctor_set(v___x_1031_, 4, v___x_1029_);
lean_ctor_set_uint8(v___x_1031_, sizeof(void*)*5, v___x_877_);
lean_ctor_set_uint8(v___x_1031_, sizeof(void*)*5 + 1, v___x_1030_);
v___x_1032_ = l_Lake_proc(v___x_1031_, v___x_1030_, v___x_1028_, v_log_1014_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1044_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
v_a_1034_ = lean_ctor_get(v___x_1032_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1036_ = v___x_1032_;
v_isShared_1037_ = v_isSharedCheck_1044_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_inc(v_a_1033_);
lean_dec(v___x_1032_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1044_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v_a_1034_);
v___x_1039_ = v___x_1020_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1034_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_trace_1017_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_buildTime_1018_);
lean_ctor_set_uint8(v_reuseFailAlloc_1043_, sizeof(void*)*3, v_action_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1043_, sizeof(void*)*3 + 1, v_wantsRebuild_1016_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v___x_1039_);
v___x_1041_ = v___x_1036_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1033_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1056_; 
v_a_1045_ = lean_ctor_get(v___x_1032_, 0);
v_a_1046_ = lean_ctor_get(v___x_1032_, 1);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1048_ = v___x_1032_;
v_isShared_1049_ = v_isSharedCheck_1056_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_inc(v_a_1045_);
lean_dec(v___x_1032_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1056_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v_a_1046_);
v___x_1051_ = v___x_1020_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1046_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_trace_1017_);
lean_ctor_set(v_reuseFailAlloc_1055_, 2, v_buildTime_1018_);
lean_ctor_set_uint8(v_reuseFailAlloc_1055_, sizeof(void*)*3, v_action_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1055_, sizeof(void*)*3 + 1, v_wantsRebuild_1016_);
v___x_1051_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1053_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v___x_1051_);
v___x_1053_ = v___x_1048_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1045_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
}
v___jp_1058_:
{
if (lean_obj_tag(v___y_1059_) == 0)
{
lean_object* v_a_1060_; 
v_a_1060_ = lean_ctor_get(v___y_1059_, 1);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___y_1059_, 2);
v_a_1012_ = v_a_1060_;
goto v___jp_1011_;
}
else
{
lean_dec_ref(v___x_1010_);
lean_dec_ref(v___y_874_);
return v___y_1059_;
}
}
}
else
{
lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1106_; 
lean_inc(v_buildTime_1007_);
lean_inc_ref(v_trace_1006_);
lean_inc_ref(v_log_1003_);
lean_dec_ref(v___y_880_);
lean_dec_ref(v___x_878_);
lean_dec_ref(v_oFiles_875_);
lean_dec_ref(v___y_874_);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___y_885_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; lean_object* v_unused_1108_; lean_object* v_unused_1109_; 
v_unused_1107_ = lean_ctor_get(v___y_885_, 2);
lean_dec(v_unused_1107_);
v_unused_1108_ = lean_ctor_get(v___y_885_, 1);
lean_dec(v_unused_1108_);
v_unused_1109_ = lean_ctor_get(v___y_885_, 0);
lean_dec(v_unused_1109_);
v___x_1094_ = v___y_885_;
v_isShared_1095_ = v_isSharedCheck_1106_;
goto v_resetjp_1093_;
}
else
{
lean_dec(v___y_885_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1106_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v_a_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v_a_1096_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1097_ = lean_io_error_to_string(v_a_1096_);
v___x_1098_ = 3;
v___x_1099_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set_uint8(v___x_1099_, sizeof(void*)*1, v___x_1098_);
v___x_1100_ = lean_array_get_size(v_log_1003_);
v___x_1101_ = lean_array_push(v_log_1003_, v___x_1099_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1101_);
v___x_1103_ = v___x_1094_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_trace_1006_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_buildTime_1007_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*3, v_action_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1105_, sizeof(void*)*3 + 1, v_wantsRebuild_1005_);
v___x_1103_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1100_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
return v___x_1104_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object* v_bootstrap_1110_, lean_object* v___y_1111_, lean_object* v_oFiles_1112_, lean_object* v_shouldExport_1113_, lean_object* v___x_1114_, lean_object* v___x_1115_, lean_object* v___x_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
uint8_t v_bootstrap_boxed_1124_; uint8_t v_shouldExport_boxed_1125_; uint8_t v___x_187970__boxed_1126_; size_t v___x_187972__boxed_1127_; lean_object* v_res_1128_; 
v_bootstrap_boxed_1124_ = lean_unbox(v_bootstrap_1110_);
v_shouldExport_boxed_1125_ = lean_unbox(v_shouldExport_1113_);
v___x_187970__boxed_1126_ = lean_unbox(v___x_1114_);
v___x_187972__boxed_1127_ = lean_unbox_usize(v___x_1116_);
lean_dec(v___x_1116_);
v_res_1128_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(v_bootstrap_boxed_1124_, v___y_1111_, v_oFiles_1112_, v_shouldExport_boxed_1125_, v___x_187970__boxed_1126_, v___x_1115_, v___x_187972__boxed_1127_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec(v___y_1118_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(uint8_t v_bootstrap_1130_, lean_object* v___y_1131_, uint8_t v_shouldExport_1132_, uint8_t v___x_1133_, lean_object* v___x_1134_, size_t v___x_1135_, lean_object* v_oFiles_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___y_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1144_ = lean_box(v_bootstrap_1130_);
v___x_1145_ = lean_box(v_shouldExport_1132_);
v___x_1146_ = lean_box(v___x_1133_);
v___x_1147_ = lean_box_usize(v___x_1135_);
lean_inc_ref(v___y_1131_);
v___y_1148_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed), 14, 7);
lean_closure_set(v___y_1148_, 0, v___x_1144_);
lean_closure_set(v___y_1148_, 1, v___y_1131_);
lean_closure_set(v___y_1148_, 2, v_oFiles_1136_);
lean_closure_set(v___y_1148_, 3, v___x_1145_);
lean_closure_set(v___y_1148_, 4, v___x_1146_);
lean_closure_set(v___y_1148_, 5, v___x_1134_);
lean_closure_set(v___y_1148_, 6, v___x_1147_);
v___x_1149_ = 0;
v___x_1150_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1151_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1131_, v___y_1148_, v___x_1149_, v___x_1150_, v___x_1133_, v___x_1149_, v___x_1149_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1161_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_a_1153_ = lean_ctor_get(v___x_1151_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1155_ = v___x_1151_;
v_isShared_1156_ = v_isSharedCheck_1161_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1161_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v_path_1157_; lean_object* v___x_1159_; 
v_path_1157_ = lean_ctor_get(v_a_1152_, 1);
lean_inc_ref(v_path_1157_);
lean_dec(v_a_1152_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v_path_1157_);
v___x_1159_ = v___x_1155_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_path_1157_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_a_1153_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
v_a_1162_ = lean_ctor_get(v___x_1151_, 0);
v_a_1163_ = lean_ctor_get(v___x_1151_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1151_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_inc(v_a_1162_);
lean_dec(v___x_1151_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1162_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object* v_bootstrap_1171_, lean_object* v___y_1172_, lean_object* v_shouldExport_1173_, lean_object* v___x_1174_, lean_object* v___x_1175_, lean_object* v___x_1176_, lean_object* v_oFiles_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
uint8_t v_bootstrap_boxed_1185_; uint8_t v_shouldExport_boxed_1186_; uint8_t v___x_188393__boxed_1187_; size_t v___x_188395__boxed_1188_; lean_object* v_res_1189_; 
v_bootstrap_boxed_1185_ = lean_unbox(v_bootstrap_1171_);
v_shouldExport_boxed_1186_ = lean_unbox(v_shouldExport_1173_);
v___x_188393__boxed_1187_ = lean_unbox(v___x_1174_);
v___x_188395__boxed_1188_ = lean_unbox_usize(v___x_1176_);
lean_dec(v___x_1176_);
v_res_1189_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(v_bootstrap_boxed_1185_, v___y_1172_, v_shouldExport_boxed_1186_, v___x_188393__boxed_1187_, v___x_1175_, v___x_188395__boxed_1188_, v_oFiles_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec(v___y_1179_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object* v___x_1194_, lean_object* v___x_1195_, lean_object* v_config_1196_, lean_object* v_config_1197_, lean_object* v___x_1198_, lean_object* v___f_1199_, uint8_t v_shouldExport_1200_, uint8_t v___x_1201_, lean_object* v___x_1202_, lean_object* v___x_1203_, lean_object* v_dir_1204_, lean_object* v_self_1205_, lean_object* v___f_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___y_1215_; uint8_t v___y_1216_; size_t v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v_a_1235_; lean_object* v_a_1236_; lean_object* v___x_1279_; 
lean_inc_ref(v___y_1207_);
lean_inc_ref(v___y_1211_);
lean_inc(v___y_1210_);
lean_inc(v___y_1209_);
lean_inc(v___x_1195_);
v___x_1279_ = lean_apply_7(v___y_1207_, v___x_1194_, v___x_1195_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, lean_box(0));
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v_a_1281_; lean_object* v___x_1282_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
v_a_1281_ = lean_ctor_get(v___x_1279_, 1);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1279_, 2);
v___x_1282_ = l_Lake_Job_await___redArg(v_a_1280_, v_a_1281_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v_a_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
v_a_1284_ = lean_ctor_get(v___x_1282_, 1);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1282_, 2);
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_1287_ = lean_array_get_size(v_a_1283_);
v___x_1288_ = lean_nat_dec_lt(v___x_1285_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_dec(v_a_1283_);
lean_dec_ref(v___f_1206_);
v_a_1235_ = v___x_1286_;
v_a_1236_ = v_a_1284_;
goto v___jp_1234_;
}
else
{
size_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_187730__overap_1291_; lean_object* v___x_1292_; 
v___x_1289_ = ((size_t)0ULL);
v___x_1290_ = lean_usize_of_nat(v___x_1287_);
lean_inc_ref(v___x_1198_);
v___x_187730__overap_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1198_, v___f_1206_, v_a_1283_, v___x_1289_, v___x_1290_, v___x_1286_);
lean_inc_ref(v___y_1211_);
lean_inc(v___y_1210_);
lean_inc(v___y_1209_);
lean_inc(v___x_1195_);
lean_inc_ref(v___y_1207_);
v___x_1292_ = lean_apply_7(v___x_187730__overap_1291_, v___y_1207_, v___x_1195_, v___y_1209_, v___y_1210_, v___y_1211_, v_a_1284_, lean_box(0));
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; lean_object* v_a_1294_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
v_a_1294_ = lean_ctor_get(v___x_1292_, 1);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1292_, 2);
v_a_1235_ = v_a_1293_;
v_a_1236_ = v_a_1294_;
goto v___jp_1234_;
}
else
{
lean_object* v_a_1295_; lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec_ref(v___y_1207_);
lean_dec_ref(v_self_1205_);
lean_dec_ref(v_dir_1204_);
lean_dec(v___x_1203_);
lean_dec_ref(v___x_1202_);
lean_dec_ref(v___f_1199_);
lean_dec_ref(v___x_1198_);
lean_dec_ref(v_config_1196_);
lean_dec(v___x_1195_);
v_a_1295_ = lean_ctor_get(v___x_1292_, 0);
v_a_1296_ = lean_ctor_get(v___x_1292_, 1);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1292_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_inc(v_a_1295_);
lean_dec(v___x_1292_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1295_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec_ref(v___y_1207_);
lean_dec_ref(v___f_1206_);
lean_dec_ref(v_self_1205_);
lean_dec_ref(v_dir_1204_);
lean_dec(v___x_1203_);
lean_dec_ref(v___x_1202_);
lean_dec_ref(v___f_1199_);
lean_dec_ref(v___x_1198_);
lean_dec_ref(v_config_1196_);
lean_dec(v___x_1195_);
v_a_1304_ = lean_ctor_get(v___x_1282_, 0);
v_a_1305_ = lean_ctor_get(v___x_1282_, 1);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1282_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_inc(v_a_1304_);
lean_dec(v___x_1282_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1304_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec_ref(v___y_1207_);
lean_dec_ref(v___f_1206_);
lean_dec_ref(v_self_1205_);
lean_dec_ref(v_dir_1204_);
lean_dec(v___x_1203_);
lean_dec_ref(v___x_1202_);
lean_dec_ref(v___f_1199_);
lean_dec_ref(v___x_1198_);
lean_dec_ref(v_config_1196_);
lean_dec(v___x_1195_);
v_a_1313_ = lean_ctor_get(v___x_1279_, 0);
v_a_1314_ = lean_ctor_get(v___x_1279_, 1);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1279_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_inc(v_a_1313_);
lean_dec(v___x_1279_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1313_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
v___jp_1214_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___f_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1221_ = lean_box(v___y_1216_);
v___x_1222_ = lean_box(v_shouldExport_1200_);
v___x_1223_ = lean_box(v___x_1201_);
v___x_1224_ = lean_box_usize(v___y_1217_);
v___f_1225_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed), 14, 6);
lean_closure_set(v___f_1225_, 0, v___x_1221_);
lean_closure_set(v___f_1225_, 1, v___y_1220_);
lean_closure_set(v___f_1225_, 2, v___x_1222_);
lean_closure_set(v___f_1225_, 3, v___x_1223_);
lean_closure_set(v___f_1225_, 4, v___x_1202_);
lean_closure_set(v___f_1225_, 5, v___x_1224_);
v___x_1226_ = l_Array_append___redArg(v___y_1219_, v___y_1215_);
lean_dec_ref(v___y_1215_);
v___x_1227_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_1228_ = l_Lake_Job_collectArray___redArg(v___x_1226_, v___x_1227_);
lean_dec_ref(v___x_1226_);
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = 0;
v___x_1231_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_1232_ = l_Lake_Job_mapM___redArg(v___x_1203_, v___x_1228_, v___f_1225_, v___x_1229_, v___x_1230_, v___y_1207_, v___x_1195_, v___y_1209_, v___y_1210_, v___y_1211_, v___x_1231_);
lean_dec(v___x_1195_);
v___x_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v___y_1218_);
return v___x_1233_;
}
v___jp_1234_:
{
lean_object* v_toLeanConfig_1237_; lean_object* v_toLeanConfig_1238_; uint8_t v_bootstrap_1239_; lean_object* v_buildDir_1240_; lean_object* v_nativeLibDir_1241_; lean_object* v_moreLinkObjs_1242_; lean_object* v_moreLinkObjs_1243_; lean_object* v___x_1244_; size_t v_sz_1245_; size_t v___x_1246_; lean_object* v___x_187681__overap_1247_; lean_object* v___x_1248_; 
v_toLeanConfig_1237_ = lean_ctor_get(v_config_1196_, 1);
lean_inc_ref(v_toLeanConfig_1237_);
v_toLeanConfig_1238_ = lean_ctor_get(v_config_1197_, 0);
v_bootstrap_1239_ = lean_ctor_get_uint8(v_config_1196_, sizeof(void*)*28);
v_buildDir_1240_ = lean_ctor_get(v_config_1196_, 5);
lean_inc_ref(v_buildDir_1240_);
v_nativeLibDir_1241_ = lean_ctor_get(v_config_1196_, 7);
lean_inc_ref(v_nativeLibDir_1241_);
lean_dec_ref(v_config_1196_);
v_moreLinkObjs_1242_ = lean_ctor_get(v_toLeanConfig_1237_, 6);
lean_inc_ref(v_moreLinkObjs_1242_);
lean_dec_ref(v_toLeanConfig_1237_);
v_moreLinkObjs_1243_ = lean_ctor_get(v_toLeanConfig_1238_, 6);
v___x_1244_ = l_Array_append___redArg(v_moreLinkObjs_1242_, v_moreLinkObjs_1243_);
v_sz_1245_ = lean_array_size(v___x_1244_);
v___x_1246_ = ((size_t)0ULL);
v___x_187681__overap_1247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1198_, v___f_1199_, v_sz_1245_, v___x_1246_, v___x_1244_);
lean_inc_ref(v___y_1211_);
lean_inc(v___y_1210_);
lean_inc(v___y_1209_);
lean_inc(v___x_1195_);
lean_inc_ref(v___y_1207_);
v___x_1248_ = lean_apply_7(v___x_187681__overap_1247_, v___y_1207_, v___x_1195_, v___y_1209_, v___y_1210_, v___y_1211_, v_a_1236_, lean_box(0));
if (lean_obj_tag(v___x_1248_) == 0)
{
if (v_shouldExport_1200_ == 0)
{
lean_object* v_a_1249_; lean_object* v_a_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
v_a_1250_ = lean_ctor_get(v___x_1248_, 1);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1248_, 2);
v___x_1251_ = l_System_FilePath_normalize(v_buildDir_1240_);
v___x_1252_ = l_Lake_joinRelative(v_dir_1204_, v___x_1251_);
v___x_1253_ = l_System_FilePath_normalize(v_nativeLibDir_1241_);
v___x_1254_ = l_Lake_joinRelative(v___x_1252_, v___x_1253_);
v___x_1255_ = l_Lake_LeanLib_libName(v_self_1205_);
v___x_1256_ = l_Lake_nameToStaticLib(v___x_1255_, v_shouldExport_1200_);
v___x_1257_ = l_Lake_joinRelative(v___x_1254_, v___x_1256_);
v___y_1215_ = v_a_1249_;
v___y_1216_ = v_bootstrap_1239_;
v___y_1217_ = v___x_1246_;
v___y_1218_ = v_a_1250_;
v___y_1219_ = v_a_1235_;
v___y_1220_ = v___x_1257_;
goto v___jp_1214_;
}
else
{
lean_object* v_a_1258_; lean_object* v_a_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_a_1258_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1258_);
v_a_1259_ = lean_ctor_get(v___x_1248_, 1);
lean_inc(v_a_1259_);
lean_dec_ref_known(v___x_1248_, 2);
v___x_1260_ = l_System_FilePath_normalize(v_buildDir_1240_);
v___x_1261_ = l_Lake_joinRelative(v_dir_1204_, v___x_1260_);
v___x_1262_ = l_System_FilePath_normalize(v_nativeLibDir_1241_);
v___x_1263_ = l_Lake_joinRelative(v___x_1261_, v___x_1262_);
v___x_1264_ = l_Lake_LeanLib_libName(v_self_1205_);
v___x_1265_ = 0;
v___x_1266_ = l_Lake_nameToStaticLib(v___x_1264_, v___x_1265_);
v___x_1267_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_1268_ = l_System_FilePath_addExtension(v___x_1266_, v___x_1267_);
v___x_1269_ = l_Lake_joinRelative(v___x_1263_, v___x_1268_);
v___y_1215_ = v_a_1258_;
v___y_1216_ = v_bootstrap_1239_;
v___y_1217_ = v___x_1246_;
v___y_1218_ = v_a_1259_;
v___y_1219_ = v_a_1235_;
v___y_1220_ = v___x_1269_;
goto v___jp_1214_;
}
}
else
{
lean_object* v_a_1270_; lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec_ref(v_nativeLibDir_1241_);
lean_dec_ref(v_buildDir_1240_);
lean_dec_ref(v_a_1235_);
lean_dec_ref(v___y_1207_);
lean_dec_ref(v_self_1205_);
lean_dec_ref(v_dir_1204_);
lean_dec(v___x_1203_);
lean_dec_ref(v___x_1202_);
lean_dec(v___x_1195_);
v_a_1270_ = lean_ctor_get(v___x_1248_, 0);
v_a_1271_ = lean_ctor_get(v___x_1248_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1248_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_inc(v_a_1270_);
lean_dec(v___x_1248_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1270_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed(lean_object** _args){
lean_object* v___x_1322_ = _args[0];
lean_object* v___x_1323_ = _args[1];
lean_object* v_config_1324_ = _args[2];
lean_object* v_config_1325_ = _args[3];
lean_object* v___x_1326_ = _args[4];
lean_object* v___f_1327_ = _args[5];
lean_object* v_shouldExport_1328_ = _args[6];
lean_object* v___x_1329_ = _args[7];
lean_object* v___x_1330_ = _args[8];
lean_object* v___x_1331_ = _args[9];
lean_object* v_dir_1332_ = _args[10];
lean_object* v_self_1333_ = _args[11];
lean_object* v___f_1334_ = _args[12];
lean_object* v___y_1335_ = _args[13];
lean_object* v___y_1336_ = _args[14];
lean_object* v___y_1337_ = _args[15];
lean_object* v___y_1338_ = _args[16];
lean_object* v___y_1339_ = _args[17];
lean_object* v___y_1340_ = _args[18];
lean_object* v___y_1341_ = _args[19];
_start:
{
uint8_t v_shouldExport_boxed_1342_; uint8_t v___x_188497__boxed_1343_; lean_object* v_res_1344_; 
v_shouldExport_boxed_1342_ = lean_unbox(v_shouldExport_1328_);
v___x_188497__boxed_1343_ = lean_unbox(v___x_1329_);
v_res_1344_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(v___x_1322_, v___x_1323_, v_config_1324_, v_config_1325_, v___x_1326_, v___f_1327_, v_shouldExport_boxed_1342_, v___x_188497__boxed_1343_, v___x_1330_, v___x_1331_, v_dir_1332_, v_self_1333_, v___f_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v_config_1325_);
return v_res_1344_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0(void){
_start:
{
uint8_t v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = 2;
v___x_1346_ = l_Lake_Verbosity_ctorIdx(v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object* v_self_1350_, uint8_t v_shouldExport_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v___x_1359_; lean_object* v_toApplicative_1360_; lean_object* v_toBind_1361_; lean_object* v_toFunctor_1362_; lean_object* v_toPure_1363_; lean_object* v___f_1364_; lean_object* v___f_1365_; lean_object* v___f_1366_; lean_object* v___f_1367_; lean_object* v___x_1368_; lean_object* v___f_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v_toBuildConfig_1377_; lean_object* v_registeredJobs_1378_; uint8_t v_verbosity_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___f_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; uint8_t v___x_1386_; lean_object* v___y_1388_; 
v___x_1359_ = l_instMonadBaseIO;
v_toApplicative_1360_ = lean_ctor_get(v___x_1359_, 0);
v_toBind_1361_ = lean_ctor_get(v___x_1359_, 1);
v_toFunctor_1362_ = lean_ctor_get(v_toApplicative_1360_, 0);
v_toPure_1363_ = lean_ctor_get(v_toApplicative_1360_, 1);
lean_inc_n(v_toBind_1361_, 3);
lean_inc_n(v_toPure_1363_, 5);
v___f_1364_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1364_, 0, v_toPure_1363_);
lean_closure_set(v___f_1364_, 1, v_toBind_1361_);
v___f_1365_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1365_, 0, v_toPure_1363_);
lean_closure_set(v___f_1365_, 1, v_toBind_1361_);
lean_inc_ref(v___f_1364_);
v___f_1366_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1366_, 0, v_toPure_1363_);
lean_closure_set(v___f_1366_, 1, v___f_1364_);
lean_inc_ref_n(v_toFunctor_1362_, 2);
v___f_1367_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1367_, 0, v_toFunctor_1362_);
lean_closure_set(v___f_1367_, 1, v_toPure_1363_);
lean_closure_set(v___f_1367_, 2, v_toBind_1361_);
v___x_1368_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1362_);
v___f_1369_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1369_, 0, v_toPure_1363_);
v___x_1370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1368_);
lean_ctor_set(v___x_1370_, 1, v___f_1369_);
lean_ctor_set(v___x_1370_, 2, v___f_1367_);
lean_ctor_set(v___x_1370_, 3, v___f_1366_);
lean_ctor_set(v___x_1370_, 4, v___f_1365_);
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v___f_1364_);
v___x_1372_ = l_ReaderT_instMonad___redArg(v___x_1371_);
v___x_1373_ = l_StateRefT_x27_instMonad___redArg(v___x_1372_);
v___x_1374_ = l_ReaderT_instMonad___redArg(v___x_1373_);
v___x_1375_ = l_ReaderT_instMonad___redArg(v___x_1374_);
v___x_1376_ = l_Lake_EquipT_instMonad___redArg(v___x_1375_);
v_toBuildConfig_1377_ = lean_ctor_get(v_a_1356_, 0);
v_registeredJobs_1378_ = lean_ctor_get(v_a_1356_, 4);
v_verbosity_1379_ = lean_ctor_get_uint8(v_toBuildConfig_1377_, sizeof(void*)*4 + 4);
v___x_1380_ = l_Lake_instDataKindFilePath;
v___x_1381_ = lean_box(v_shouldExport_1351_);
lean_inc_ref(v___x_1376_);
v___f_1382_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1382_, 0, v___x_1381_);
lean_closure_set(v___f_1382_, 1, v___x_1376_);
v___x_1383_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1379_);
v___x_1384_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0);
v___x_1385_ = lean_nat_dec_eq(v___x_1383_, v___x_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = 1;
if (v___x_1385_ == 0)
{
lean_object* v___x_1434_; 
v___x_1434_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_1388_ = v___x_1434_;
goto v___jp_1387_;
}
else
{
if (v_shouldExport_1351_ == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_1388_ = v___x_1435_;
goto v___jp_1387_;
}
else
{
lean_object* v___x_1436_; 
v___x_1436_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3));
v___y_1388_ = v___x_1436_;
goto v___jp_1387_;
}
}
v___jp_1387_:
{
lean_object* v_pkg_1389_; lean_object* v_name_1390_; lean_object* v_config_1391_; lean_object* v_keyName_1392_; lean_object* v_dir_1393_; lean_object* v_config_1394_; lean_object* v___f_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___f_1403_; lean_object* v___x_1404_; 
v_pkg_1389_ = lean_ctor_get(v_self_1350_, 0);
v_name_1390_ = lean_ctor_get(v_self_1350_, 1);
lean_inc_n(v_name_1390_, 2);
v_config_1391_ = lean_ctor_get(v_self_1350_, 2);
lean_inc(v_config_1391_);
v_keyName_1392_ = lean_ctor_get(v_pkg_1389_, 2);
v_dir_1393_ = lean_ctor_get(v_pkg_1389_, 4);
lean_inc_ref(v_dir_1393_);
v_config_1394_ = lean_ctor_get(v_pkg_1389_, 6);
lean_inc_ref(v_config_1394_);
lean_inc_ref_n(v_pkg_1389_, 2);
v___f_1395_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(v___f_1395_, 0, v___x_1380_);
lean_closure_set(v___f_1395_, 1, v_pkg_1389_);
v___x_1396_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_1392_);
v___x_1397_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1397_, 0, v_keyName_1392_);
lean_ctor_set(v___x_1397_, 1, v_name_1390_);
v___x_1398_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_1350_);
v___x_1399_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1397_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
lean_ctor_set(v___x_1399_, 2, v_self_1350_);
lean_ctor_set(v___x_1399_, 3, v___x_1396_);
v___x_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1400_, 0, v_pkg_1389_);
v___x_1401_ = lean_box(v_shouldExport_1351_);
v___x_1402_ = lean_box(v___x_1386_);
lean_inc_ref(v___x_1376_);
v___f_1403_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed), 20, 13);
lean_closure_set(v___f_1403_, 0, v___x_1399_);
lean_closure_set(v___f_1403_, 1, v___x_1400_);
lean_closure_set(v___f_1403_, 2, v_config_1394_);
lean_closure_set(v___f_1403_, 3, v_config_1391_);
lean_closure_set(v___f_1403_, 4, v___x_1376_);
lean_closure_set(v___f_1403_, 5, v___f_1395_);
lean_closure_set(v___f_1403_, 6, v___x_1401_);
lean_closure_set(v___f_1403_, 7, v___x_1402_);
lean_closure_set(v___f_1403_, 8, v___x_1376_);
lean_closure_set(v___f_1403_, 9, v___x_1380_);
lean_closure_set(v___f_1403_, 10, v_dir_1393_);
lean_closure_set(v___f_1403_, 11, v_self_1350_);
lean_closure_set(v___f_1403_, 12, v___f_1382_);
v___x_1404_ = l_Lake_ensureJob___redArg(v___x_1380_, v___f_1403_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1433_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_a_1406_ = lean_ctor_get(v___x_1404_, 1);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1408_ = v___x_1404_;
v_isShared_1409_ = v_isSharedCheck_1433_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1433_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v_task_1410_; lean_object* v_kind_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1431_; 
v_task_1410_ = lean_ctor_get(v_a_1405_, 0);
v_kind_1411_ = lean_ctor_get(v_a_1405_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_a_1405_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v_a_1405_, 2);
lean_dec(v_unused_1432_);
v___x_1413_ = v_a_1405_;
v_isShared_1414_ = v_isSharedCheck_1431_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_kind_1411_);
lean_inc(v_task_1410_);
lean_dec(v_a_1405_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1431_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; lean_object* v_job_1422_; 
v___x_1415_ = lean_st_ref_take(v_registeredJobs_1378_);
v___x_1416_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1390_, v___x_1386_);
v___x_1417_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___x_1418_ = lean_string_append(v___x_1416_, v___x_1417_);
v___x_1419_ = lean_string_append(v___x_1418_, v___y_1388_);
v___x_1420_ = 0;
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 2, v___x_1419_);
v_job_1422_ = v___x_1413_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_task_1410_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_kind_1411_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v___x_1419_);
v_job_1422_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
lean_ctor_set_uint8(v_job_1422_, sizeof(void*)*3, v___x_1420_);
lean_inc_ref(v_job_1422_);
v___x_1423_ = l_Lake_Job_toOpaque___redArg(v_job_1422_);
v___x_1424_ = lean_array_push(v___x_1415_, v___x_1423_);
v___x_1425_ = lean_st_ref_put(v_registeredJobs_1378_, v___x_1424_);
v___x_1426_ = l_Lake_Job_renew___redArg(v_job_1422_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1426_);
v___x_1428_ = v___x_1408_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_a_1406_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
else
{
lean_dec(v_name_1390_);
return v___x_1404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object* v_self_1437_, lean_object* v_shouldExport_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
uint8_t v_shouldExport_boxed_1446_; lean_object* v_res_1447_; 
v_shouldExport_boxed_1446_ = lean_unbox(v_shouldExport_1438_);
v_res_1447_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1437_, v_shouldExport_boxed_1446_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec(v_a_1440_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t v_fmt_1448_, lean_object* v_a_1449_){
_start:
{
if (v_fmt_1448_ == 0)
{
return v_a_1449_;
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1450_ = l_Lake_mkRelPathString(v_a_1449_);
v___x_1451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
v___x_1452_ = l_Lean_Json_compress(v___x_1451_);
return v___x_1452_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object* v_fmt_1453_, lean_object* v_a_1454_){
_start:
{
uint8_t v_fmt_boxed_1455_; lean_object* v_res_1456_; 
v_fmt_boxed_1455_ = lean_unbox(v_fmt_1453_);
v_res_1456_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_boxed_1455_, v_a_1454_);
return v_res_1456_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2(void){
_start:
{
uint8_t v___x_1459_; lean_object* v_name_1460_; lean_object* v___x_1461_; 
v___x_1459_ = 1;
v_name_1460_ = l_Lake_instDataKindFilePath;
v___x_1461_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1460_, v___x_1459_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* v_defaultPkg_1465_, lean_object* v_self_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
uint8_t v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = 1;
lean_inc_ref_n(v_self_1466_, 2);
v___x_1475_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1465_, v_self_1466_, v_self_1466_, v___x_1474_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v_snd_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1518_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
v_snd_1477_ = lean_ctor_get(v_a_1476_, 1);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_a_1476_);
if (v_isSharedCheck_1518_ == 0)
{
lean_object* v_unused_1519_; 
v_unused_1519_ = lean_ctor_get(v_a_1476_, 0);
lean_dec(v_unused_1519_);
v___x_1479_ = v_a_1476_;
v_isShared_1480_ = v_isSharedCheck_1518_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_snd_1477_);
lean_dec(v_a_1476_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1518_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1516_; 
v_a_1481_ = lean_ctor_get(v___x_1475_, 1);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v___x_1475_, 0);
lean_dec(v_unused_1517_);
v___x_1483_ = v___x_1475_;
v_isShared_1484_ = v_isSharedCheck_1516_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1475_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1516_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v_kind_1485_; lean_object* v_name_1486_; lean_object* v___y_1488_; uint8_t v___x_1506_; 
v_kind_1485_ = lean_ctor_get(v_snd_1477_, 1);
v_name_1486_ = l_Lake_instDataKindFilePath;
v___x_1506_ = lean_name_eq(v_kind_1485_, v_name_1486_);
if (v___x_1506_ == 0)
{
uint8_t v___x_1507_; 
lean_inc(v_kind_1485_);
lean_del_object(v___x_1479_);
lean_dec(v_snd_1477_);
v___x_1507_ = l_Lean_Name_isAnonymous(v_kind_1485_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1508_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1509_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1485_, v___x_1474_);
v___x_1510_ = lean_string_append(v___x_1508_, v___x_1509_);
lean_dec_ref(v___x_1509_);
v___x_1511_ = lean_string_append(v___x_1510_, v___x_1508_);
v___y_1488_ = v___x_1511_;
goto v___jp_1487_;
}
else
{
lean_object* v___x_1512_; 
lean_dec(v_kind_1485_);
v___x_1512_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1488_ = v___x_1512_;
goto v___jp_1487_;
}
}
else
{
lean_object* v___x_1514_; 
lean_del_object(v___x_1483_);
lean_dec_ref(v_self_1466_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 1, v_a_1481_);
lean_ctor_set(v___x_1479_, 0, v_snd_1477_);
v___x_1514_ = v___x_1479_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_snd_1477_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_a_1481_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
v___jp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1489_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1490_ = l_Lake_PartialBuildKey_toString(v_self_1466_);
v___x_1491_ = lean_string_append(v___x_1489_, v___x_1490_);
lean_dec_ref(v___x_1490_);
v___x_1492_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1493_ = lean_string_append(v___x_1491_, v___x_1492_);
v___x_1494_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
v___x_1495_ = lean_string_append(v___x_1493_, v___x_1494_);
v___x_1496_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1497_ = lean_string_append(v___x_1495_, v___x_1496_);
v___x_1498_ = lean_string_append(v___x_1497_, v___y_1488_);
lean_dec_ref(v___y_1488_);
v___x_1499_ = 3;
v___x_1500_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1500_, 0, v___x_1498_);
lean_ctor_set_uint8(v___x_1500_, sizeof(void*)*1, v___x_1499_);
v___x_1501_ = lean_array_get_size(v_a_1481_);
v___x_1502_ = lean_array_push(v_a_1481_, v___x_1500_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set_tag(v___x_1483_, 1);
lean_ctor_set(v___x_1483_, 1, v___x_1502_);
lean_ctor_set(v___x_1483_, 0, v___x_1501_);
v___x_1504_ = v___x_1483_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec_ref(v_self_1466_);
v_a_1520_ = lean_ctor_get(v___x_1475_, 0);
v_a_1521_ = lean_ctor_get(v___x_1475_, 1);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1475_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_inc(v_a_1520_);
lean_dec(v___x_1475_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1520_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* v_defaultPkg_1529_, lean_object* v_self_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1529_, v_self_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec(v_a_1532_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* v___x_1539_, size_t v_sz_1540_, size_t v_i_1541_, lean_object* v_bs_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
uint8_t v___x_1550_; 
v___x_1550_ = lean_usize_dec_lt(v_i_1541_, v_sz_1540_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_dec_ref(v___y_1543_);
lean_dec_ref(v___x_1539_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v_bs_1542_);
lean_ctor_set(v___x_1551_, 1, v___y_1548_);
return v___x_1551_;
}
else
{
lean_object* v_v_1552_; lean_object* v___x_1553_; 
v_v_1552_ = lean_array_uget_borrowed(v_bs_1542_, v_i_1541_);
lean_inc_ref(v___y_1543_);
lean_inc(v_v_1552_);
lean_inc_ref(v___x_1539_);
v___x_1553_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1539_, v_v_1552_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v_bs_x27_1557_; size_t v___x_1558_; size_t v___x_1559_; lean_object* v___x_1560_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
v_a_1555_ = lean_ctor_get(v___x_1553_, 1);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1553_, 2);
v___x_1556_ = lean_unsigned_to_nat(0u);
v_bs_x27_1557_ = lean_array_uset(v_bs_1542_, v_i_1541_, v___x_1556_);
v___x_1558_ = ((size_t)1ULL);
v___x_1559_ = lean_usize_add(v_i_1541_, v___x_1558_);
v___x_1560_ = lean_array_uset(v_bs_x27_1557_, v_i_1541_, v_a_1554_);
v_i_1541_ = v___x_1559_;
v_bs_1542_ = v___x_1560_;
v___y_1548_ = v_a_1555_;
goto _start;
}
else
{
lean_object* v_a_1562_; lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec_ref(v___y_1543_);
lean_dec_ref(v_bs_1542_);
lean_dec_ref(v___x_1539_);
v_a_1562_ = lean_ctor_get(v___x_1553_, 0);
v_a_1563_ = lean_ctor_get(v___x_1553_, 1);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1553_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_inc(v_a_1562_);
lean_dec(v___x_1553_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1568_; 
if (v_isShared_1566_ == 0)
{
v___x_1568_ = v___x_1565_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1562_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* v___x_1571_, lean_object* v_sz_1572_, lean_object* v_i_1573_, lean_object* v_bs_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
size_t v_sz_boxed_1582_; size_t v_i_boxed_1583_; lean_object* v_res_1584_; 
v_sz_boxed_1582_ = lean_unbox_usize(v_sz_1572_);
lean_dec(v_sz_1572_);
v_i_boxed_1583_ = lean_unbox_usize(v_i_1573_);
lean_dec(v_i_1573_);
v_res_1584_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1571_, v_sz_boxed_1582_, v_i_boxed_1583_, v_bs_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec(v___y_1576_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(lean_object* v_a_1585_, lean_object* v_as_1586_, size_t v_i_1587_, size_t v_stop_1588_, lean_object* v_b_1589_, lean_object* v___y_1590_){
_start:
{
uint8_t v___x_1592_; 
v___x_1592_ = lean_usize_dec_eq(v_i_1587_, v_stop_1588_);
if (v___x_1592_ == 0)
{
lean_object* v_log_1593_; uint8_t v_action_1594_; uint8_t v_wantsRebuild_1595_; lean_object* v_trace_1596_; lean_object* v_buildTime_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_log_1593_ = lean_ctor_get(v___y_1590_, 0);
v_action_1594_ = lean_ctor_get_uint8(v___y_1590_, sizeof(void*)*3);
v_wantsRebuild_1595_ = lean_ctor_get_uint8(v___y_1590_, sizeof(void*)*3 + 1);
v_trace_1596_ = lean_ctor_get(v___y_1590_, 1);
v_buildTime_1597_ = lean_ctor_get(v___y_1590_, 2);
v___x_1598_ = lean_array_uget_borrowed(v_as_1586_, v_i_1587_);
v___x_1599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
lean_inc(v___x_1598_);
v___x_1600_ = lean_string_append(v___x_1598_, v___x_1599_);
v___x_1601_ = lean_io_prim_handle_put_str(v_a_1585_, v___x_1600_);
lean_dec_ref(v___x_1600_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; size_t v___x_1603_; size_t v___x_1604_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1603_ = ((size_t)1ULL);
v___x_1604_ = lean_usize_add(v_i_1587_, v___x_1603_);
v_i_1587_ = v___x_1604_;
v_b_1589_ = v_a_1602_;
goto _start;
}
else
{
lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1619_; 
lean_inc(v_buildTime_1597_);
lean_inc_ref(v_trace_1596_);
lean_inc_ref(v_log_1593_);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___y_1590_);
if (v_isSharedCheck_1619_ == 0)
{
lean_object* v_unused_1620_; lean_object* v_unused_1621_; lean_object* v_unused_1622_; 
v_unused_1620_ = lean_ctor_get(v___y_1590_, 2);
lean_dec(v_unused_1620_);
v_unused_1621_ = lean_ctor_get(v___y_1590_, 1);
lean_dec(v_unused_1621_);
v_unused_1622_ = lean_ctor_get(v___y_1590_, 0);
lean_dec(v_unused_1622_);
v___x_1607_ = v___y_1590_;
v_isShared_1608_ = v_isSharedCheck_1619_;
goto v_resetjp_1606_;
}
else
{
lean_dec(v___y_1590_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1619_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v_a_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1616_; 
v_a_1609_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1610_ = lean_io_error_to_string(v_a_1609_);
v___x_1611_ = 3;
v___x_1612_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set_uint8(v___x_1612_, sizeof(void*)*1, v___x_1611_);
v___x_1613_ = lean_array_get_size(v_log_1593_);
v___x_1614_ = lean_array_push(v_log_1593_, v___x_1612_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v___x_1614_);
v___x_1616_ = v___x_1607_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_trace_1596_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v_buildTime_1597_);
lean_ctor_set_uint8(v_reuseFailAlloc_1618_, sizeof(void*)*3, v_action_1594_);
lean_ctor_set_uint8(v_reuseFailAlloc_1618_, sizeof(void*)*3 + 1, v_wantsRebuild_1595_);
v___x_1616_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1613_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
return v___x_1617_;
}
}
}
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v_b_1589_);
lean_ctor_set(v___x_1623_, 1, v___y_1590_);
return v___x_1623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(lean_object* v_a_1624_, lean_object* v_as_1625_, lean_object* v_i_1626_, lean_object* v_stop_1627_, lean_object* v_b_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
size_t v_i_boxed_1631_; size_t v_stop_boxed_1632_; lean_object* v_res_1633_; 
v_i_boxed_1631_ = lean_unbox_usize(v_i_1626_);
lean_dec(v_i_1626_);
v_stop_boxed_1632_ = lean_unbox_usize(v_stop_1627_);
lean_dec(v_stop_1627_);
v_res_1633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1624_, v_as_1625_, v_i_boxed_1631_, v_stop_boxed_1632_, v_b_1628_, v___y_1629_);
lean_dec_ref(v_as_1625_);
lean_dec(v_a_1624_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(uint8_t v_bootstrap_1634_, lean_object* v___y_1635_, lean_object* v_oFiles_1636_, uint8_t v_shouldExport_1637_, uint8_t v___x_1638_, size_t v___x_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
if (v_bootstrap_1634_ == 0)
{
lean_object* v_toContext_1647_; lean_object* v_lakeEnv_1648_; lean_object* v_lean_1649_; lean_object* v_log_1650_; uint8_t v_action_1651_; uint8_t v_wantsRebuild_1652_; lean_object* v_trace_1653_; lean_object* v_buildTime_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1684_; 
v_toContext_1647_ = lean_ctor_get(v___y_1644_, 1);
v_lakeEnv_1648_ = lean_ctor_get(v_toContext_1647_, 0);
v_lean_1649_ = lean_ctor_get(v_lakeEnv_1648_, 1);
v_log_1650_ = lean_ctor_get(v___y_1645_, 0);
v_action_1651_ = lean_ctor_get_uint8(v___y_1645_, sizeof(void*)*3);
v_wantsRebuild_1652_ = lean_ctor_get_uint8(v___y_1645_, sizeof(void*)*3 + 1);
v_trace_1653_ = lean_ctor_get(v___y_1645_, 1);
v_buildTime_1654_ = lean_ctor_get(v___y_1645_, 2);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___y_1645_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1656_ = v___y_1645_;
v_isShared_1657_ = v_isSharedCheck_1684_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_buildTime_1654_);
lean_inc(v_trace_1653_);
lean_inc(v_log_1650_);
lean_dec(v___y_1645_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1684_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v_ar_1658_; lean_object* v___x_1659_; 
v_ar_1658_ = lean_ctor_get(v_lean_1649_, 13);
lean_inc_ref(v_ar_1658_);
v___x_1659_ = l_Lake_compileStaticLib(v___y_1635_, v_oFiles_1636_, v_ar_1658_, v_bootstrap_1634_, v_log_1650_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1671_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_a_1661_ = lean_ctor_get(v___x_1659_, 1);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1663_ = v___x_1659_;
v_isShared_1664_ = v_isSharedCheck_1671_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1671_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v_a_1661_);
v___x_1666_ = v___x_1656_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1661_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_trace_1653_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v_buildTime_1654_);
lean_ctor_set_uint8(v_reuseFailAlloc_1670_, sizeof(void*)*3, v_action_1651_);
lean_ctor_set_uint8(v_reuseFailAlloc_1670_, sizeof(void*)*3 + 1, v_wantsRebuild_1652_);
v___x_1666_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1668_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 1, v___x_1666_);
v___x_1668_ = v___x_1663_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1660_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1683_; 
v_a_1672_ = lean_ctor_get(v___x_1659_, 0);
v_a_1673_ = lean_ctor_get(v___x_1659_, 1);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1675_ = v___x_1659_;
v_isShared_1676_ = v_isSharedCheck_1683_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_inc(v_a_1672_);
lean_dec(v___x_1659_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1683_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1678_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v_a_1673_);
v___x_1678_ = v___x_1656_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1673_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_trace_1653_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_buildTime_1654_);
lean_ctor_set_uint8(v_reuseFailAlloc_1682_, sizeof(void*)*3, v_action_1651_);
lean_ctor_set_uint8(v_reuseFailAlloc_1682_, sizeof(void*)*3 + 1, v_wantsRebuild_1652_);
v___x_1678_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1680_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 1, v___x_1678_);
v___x_1680_ = v___x_1675_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1672_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
}
else
{
uint8_t v___x_1685_; 
v___x_1685_ = l_System_Platform_isOSX;
if (v___x_1685_ == 0)
{
uint8_t v___x_1686_; 
v___x_1686_ = l_System_Platform_isWindows;
if (v___x_1686_ == 0)
{
lean_object* v_toContext_1687_; lean_object* v_lakeEnv_1688_; lean_object* v_lean_1689_; lean_object* v_log_1690_; uint8_t v_action_1691_; uint8_t v_wantsRebuild_1692_; lean_object* v_trace_1693_; lean_object* v_buildTime_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1724_; 
v_toContext_1687_ = lean_ctor_get(v___y_1644_, 1);
v_lakeEnv_1688_ = lean_ctor_get(v_toContext_1687_, 0);
v_lean_1689_ = lean_ctor_get(v_lakeEnv_1688_, 1);
v_log_1690_ = lean_ctor_get(v___y_1645_, 0);
v_action_1691_ = lean_ctor_get_uint8(v___y_1645_, sizeof(void*)*3);
v_wantsRebuild_1692_ = lean_ctor_get_uint8(v___y_1645_, sizeof(void*)*3 + 1);
v_trace_1693_ = lean_ctor_get(v___y_1645_, 1);
v_buildTime_1694_ = lean_ctor_get(v___y_1645_, 2);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___y_1645_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1696_ = v___y_1645_;
v_isShared_1697_ = v_isSharedCheck_1724_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_buildTime_1694_);
lean_inc(v_trace_1693_);
lean_inc(v_log_1690_);
lean_dec(v___y_1645_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1724_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_ar_1698_; lean_object* v___x_1699_; 
v_ar_1698_ = lean_ctor_get(v_lean_1689_, 13);
lean_inc_ref(v_ar_1698_);
v___x_1699_ = l_Lake_compileStaticLib(v___y_1635_, v_oFiles_1636_, v_ar_1698_, v___x_1686_, v_log_1690_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1711_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_a_1701_ = lean_ctor_get(v___x_1699_, 1);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1703_ = v___x_1699_;
v_isShared_1704_ = v_isSharedCheck_1711_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1711_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v_a_1701_);
v___x_1706_ = v___x_1696_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1701_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_trace_1693_);
lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_buildTime_1694_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*3, v_action_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1710_, sizeof(void*)*3 + 1, v_wantsRebuild_1692_);
v___x_1706_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1708_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 1, v___x_1706_);
v___x_1708_ = v___x_1703_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1700_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1723_; 
v_a_1712_ = lean_ctor_get(v___x_1699_, 0);
v_a_1713_ = lean_ctor_get(v___x_1699_, 1);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1715_ = v___x_1699_;
v_isShared_1716_ = v_isSharedCheck_1723_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_inc(v_a_1712_);
lean_dec(v___x_1699_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1723_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v_a_1713_);
v___x_1718_ = v___x_1696_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1713_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_trace_1693_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_buildTime_1694_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*3, v_action_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*3 + 1, v_wantsRebuild_1692_);
v___x_1718_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1720_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v___x_1718_);
v___x_1720_ = v___x_1715_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1712_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1725_; lean_object* v_lakeEnv_1726_; lean_object* v_lean_1727_; lean_object* v_log_1728_; uint8_t v_action_1729_; uint8_t v_wantsRebuild_1730_; lean_object* v_trace_1731_; lean_object* v_buildTime_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1762_; 
v_toContext_1725_ = lean_ctor_get(v___y_1644_, 1);
v_lakeEnv_1726_ = lean_ctor_get(v_toContext_1725_, 0);
v_lean_1727_ = lean_ctor_get(v_lakeEnv_1726_, 1);
v_log_1728_ = lean_ctor_get(v___y_1645_, 0);
v_action_1729_ = lean_ctor_get_uint8(v___y_1645_, sizeof(void*)*3);
v_wantsRebuild_1730_ = lean_ctor_get_uint8(v___y_1645_, sizeof(void*)*3 + 1);
v_trace_1731_ = lean_ctor_get(v___y_1645_, 1);
v_buildTime_1732_ = lean_ctor_get(v___y_1645_, 2);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___y_1645_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1734_ = v___y_1645_;
v_isShared_1735_ = v_isSharedCheck_1762_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_buildTime_1732_);
lean_inc(v_trace_1731_);
lean_inc(v_log_1728_);
lean_dec(v___y_1645_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1762_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v_ar_1736_; lean_object* v___x_1737_; 
v_ar_1736_ = lean_ctor_get(v_lean_1727_, 13);
lean_inc_ref(v_ar_1736_);
v___x_1737_ = l_Lake_compileStaticLib(v___y_1635_, v_oFiles_1636_, v_ar_1736_, v_shouldExport_1637_, v_log_1728_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1749_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_a_1739_ = lean_ctor_get(v___x_1737_, 1);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1741_ = v___x_1737_;
v_isShared_1742_ = v_isSharedCheck_1749_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1749_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v_a_1739_);
v___x_1744_ = v___x_1734_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1739_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_trace_1731_);
lean_ctor_set(v_reuseFailAlloc_1748_, 2, v_buildTime_1732_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, sizeof(void*)*3, v_action_1729_);
lean_ctor_set_uint8(v_reuseFailAlloc_1748_, sizeof(void*)*3 + 1, v_wantsRebuild_1730_);
v___x_1744_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1746_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 1, v___x_1744_);
v___x_1746_ = v___x_1741_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1738_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
else
{
lean_object* v_a_1750_; lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1761_; 
v_a_1750_ = lean_ctor_get(v___x_1737_, 0);
v_a_1751_ = lean_ctor_get(v___x_1737_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1753_ = v___x_1737_;
v_isShared_1754_ = v_isSharedCheck_1761_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_inc(v_a_1750_);
lean_dec(v___x_1737_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1761_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v_a_1751_);
v___x_1756_ = v___x_1734_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1751_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_trace_1731_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_buildTime_1732_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*3, v_action_1729_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*3 + 1, v_wantsRebuild_1730_);
v___x_1756_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1758_; 
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 1, v___x_1756_);
v___x_1758_ = v___x_1753_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1750_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1763_; uint8_t v_action_1764_; uint8_t v_wantsRebuild_1765_; lean_object* v_trace_1766_; lean_object* v_buildTime_1767_; lean_object* v___x_1768_; 
v_log_1763_ = lean_ctor_get(v___y_1645_, 0);
v_action_1764_ = lean_ctor_get_uint8(v___y_1645_, sizeof(void*)*3);
v_wantsRebuild_1765_ = lean_ctor_get_uint8(v___y_1645_, sizeof(void*)*3 + 1);
v_trace_1766_ = lean_ctor_get(v___y_1645_, 1);
v_buildTime_1767_ = lean_ctor_get(v___y_1645_, 2);
lean_inc_ref(v___y_1635_);
v___x_1768_ = l_Lake_createParentDirs(v___y_1635_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v_a_1772_; uint8_t v___x_1820_; lean_object* v___x_1821_; 
lean_dec_ref_known(v___x_1768_, 1);
v___x_1769_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1635_);
v___x_1770_ = l_System_FilePath_addExtension(v___y_1635_, v___x_1769_);
v___x_1820_ = 1;
v___x_1821_ = lean_io_prim_handle_mk(v___x_1770_, v___x_1820_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref_known(v___x_1821_, 1);
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = lean_array_get_size(v_oFiles_1636_);
v___x_1825_ = lean_nat_dec_lt(v___x_1823_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_dec(v_a_1822_);
lean_dec_ref(v_oFiles_1636_);
v_a_1772_ = v___y_1645_;
goto v___jp_1771_;
}
else
{
lean_object* v___x_1826_; size_t v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_box(0);
v___x_1827_ = lean_usize_of_nat(v___x_1824_);
v___x_1828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1822_, v_oFiles_1636_, v___x_1639_, v___x_1827_, v___x_1826_, v___y_1645_);
lean_dec_ref(v_oFiles_1636_);
lean_dec(v_a_1822_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 1);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1828_, 2);
v_a_1772_ = v_a_1829_;
goto v___jp_1771_;
}
else
{
lean_dec_ref(v___x_1770_);
lean_dec_ref(v___y_1635_);
return v___x_1828_;
}
}
}
else
{
lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1843_; 
lean_inc(v_buildTime_1767_);
lean_inc_ref(v_trace_1766_);
lean_inc_ref(v_log_1763_);
lean_dec_ref(v___x_1770_);
lean_dec_ref(v_oFiles_1636_);
lean_dec_ref(v___y_1635_);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___y_1645_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; lean_object* v_unused_1845_; lean_object* v_unused_1846_; 
v_unused_1844_ = lean_ctor_get(v___y_1645_, 2);
lean_dec(v_unused_1844_);
v_unused_1845_ = lean_ctor_get(v___y_1645_, 1);
lean_dec(v_unused_1845_);
v_unused_1846_ = lean_ctor_get(v___y_1645_, 0);
lean_dec(v_unused_1846_);
v___x_1831_ = v___y_1645_;
v_isShared_1832_ = v_isSharedCheck_1843_;
goto v_resetjp_1830_;
}
else
{
lean_dec(v___y_1645_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1843_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_a_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v_a_1833_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1821_, 1);
v___x_1834_ = lean_io_error_to_string(v_a_1833_);
v___x_1835_ = 3;
v___x_1836_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1836_, 0, v___x_1834_);
lean_ctor_set_uint8(v___x_1836_, sizeof(void*)*1, v___x_1835_);
v___x_1837_ = lean_array_get_size(v_log_1763_);
v___x_1838_ = lean_array_push(v_log_1763_, v___x_1836_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1838_);
v___x_1840_ = v___x_1831_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_trace_1766_);
lean_ctor_set(v_reuseFailAlloc_1842_, 2, v_buildTime_1767_);
lean_ctor_set_uint8(v_reuseFailAlloc_1842_, sizeof(void*)*3, v_action_1764_);
lean_ctor_set_uint8(v_reuseFailAlloc_1842_, sizeof(void*)*3 + 1, v_wantsRebuild_1765_);
v___x_1840_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1837_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
return v___x_1841_;
}
}
}
v___jp_1771_:
{
lean_object* v___x_1773_; lean_object* v_log_1774_; uint8_t v_action_1775_; uint8_t v_wantsRebuild_1776_; lean_object* v_trace_1777_; lean_object* v_buildTime_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1819_; 
v___x_1773_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1774_ = lean_ctor_get(v_a_1772_, 0);
v_action_1775_ = lean_ctor_get_uint8(v_a_1772_, sizeof(void*)*3);
v_wantsRebuild_1776_ = lean_ctor_get_uint8(v_a_1772_, sizeof(void*)*3 + 1);
v_trace_1777_ = lean_ctor_get(v_a_1772_, 1);
v_buildTime_1778_ = lean_ctor_get(v_a_1772_, 2);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_a_1772_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1780_ = v_a_1772_;
v_isShared_1781_ = v_isSharedCheck_1819_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_buildTime_1778_);
lean_inc(v_trace_1777_);
lean_inc(v_log_1774_);
lean_dec(v_a_1772_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1819_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1782_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1783_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1784_ = lean_unsigned_to_nat(5u);
v___x_1785_ = lean_mk_empty_array_with_capacity(v___x_1784_);
lean_dec_ref(v___x_1785_);
v___x_1786_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1787_ = lean_array_push(v___x_1786_, v___y_1635_);
v___x_1788_ = lean_array_push(v___x_1787_, v___x_1783_);
v___x_1789_ = lean_array_push(v___x_1788_, v___x_1770_);
v___x_1790_ = lean_box(0);
v___x_1791_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1792_ = 0;
v___x_1793_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1793_, 0, v___x_1773_);
lean_ctor_set(v___x_1793_, 1, v___x_1782_);
lean_ctor_set(v___x_1793_, 2, v___x_1789_);
lean_ctor_set(v___x_1793_, 3, v___x_1790_);
lean_ctor_set(v___x_1793_, 4, v___x_1791_);
lean_ctor_set_uint8(v___x_1793_, sizeof(void*)*5, v___x_1638_);
lean_ctor_set_uint8(v___x_1793_, sizeof(void*)*5 + 1, v___x_1792_);
v___x_1794_ = l_Lake_proc(v___x_1793_, v___x_1792_, v___x_1790_, v_log_1774_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1806_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_a_1796_ = lean_ctor_get(v___x_1794_, 1);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1798_ = v___x_1794_;
v_isShared_1799_ = v_isSharedCheck_1806_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1806_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_a_1796_);
v___x_1801_ = v___x_1780_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1796_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_trace_1777_);
lean_ctor_set(v_reuseFailAlloc_1805_, 2, v_buildTime_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1805_, sizeof(void*)*3, v_action_1775_);
lean_ctor_set_uint8(v_reuseFailAlloc_1805_, sizeof(void*)*3 + 1, v_wantsRebuild_1776_);
v___x_1801_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1803_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 1, v___x_1801_);
v___x_1803_ = v___x_1798_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1795_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v___x_1801_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1818_; 
v_a_1807_ = lean_ctor_get(v___x_1794_, 0);
v_a_1808_ = lean_ctor_get(v___x_1794_, 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1810_ = v___x_1794_;
v_isShared_1811_ = v_isSharedCheck_1818_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_inc(v_a_1807_);
lean_dec(v___x_1794_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1818_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v_a_1808_);
v___x_1813_ = v___x_1780_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1808_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_trace_1777_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_buildTime_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1817_, sizeof(void*)*3, v_action_1775_);
lean_ctor_set_uint8(v_reuseFailAlloc_1817_, sizeof(void*)*3 + 1, v_wantsRebuild_1776_);
v___x_1813_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1815_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 1, v___x_1813_);
v___x_1815_ = v___x_1810_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1807_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1860_; 
lean_inc(v_buildTime_1767_);
lean_inc_ref(v_trace_1766_);
lean_inc_ref(v_log_1763_);
lean_dec_ref(v_oFiles_1636_);
lean_dec_ref(v___y_1635_);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___y_1645_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; lean_object* v_unused_1862_; lean_object* v_unused_1863_; 
v_unused_1861_ = lean_ctor_get(v___y_1645_, 2);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v___y_1645_, 1);
lean_dec(v_unused_1862_);
v_unused_1863_ = lean_ctor_get(v___y_1645_, 0);
lean_dec(v_unused_1863_);
v___x_1848_ = v___y_1645_;
v_isShared_1849_ = v_isSharedCheck_1860_;
goto v_resetjp_1847_;
}
else
{
lean_dec(v___y_1645_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1860_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v_a_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1857_; 
v_a_1850_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v___x_1768_, 1);
v___x_1851_ = lean_io_error_to_string(v_a_1850_);
v___x_1852_ = 3;
v___x_1853_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set_uint8(v___x_1853_, sizeof(void*)*1, v___x_1852_);
v___x_1854_ = lean_array_get_size(v_log_1763_);
v___x_1855_ = lean_array_push(v_log_1763_, v___x_1853_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1855_);
v___x_1857_ = v___x_1848_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1855_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_trace_1766_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_buildTime_1767_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*3, v_action_1764_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, sizeof(void*)*3 + 1, v_wantsRebuild_1765_);
v___x_1857_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1854_);
lean_ctor_set(v___x_1858_, 1, v___x_1857_);
return v___x_1858_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object* v_bootstrap_1864_, lean_object* v___y_1865_, lean_object* v_oFiles_1866_, lean_object* v_shouldExport_1867_, lean_object* v___x_1868_, lean_object* v___x_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
uint8_t v_bootstrap_boxed_1877_; uint8_t v_shouldExport_boxed_1878_; uint8_t v___x_5803__boxed_1879_; size_t v___x_5804__boxed_1880_; lean_object* v_res_1881_; 
v_bootstrap_boxed_1877_ = lean_unbox(v_bootstrap_1864_);
v_shouldExport_boxed_1878_ = lean_unbox(v_shouldExport_1867_);
v___x_5803__boxed_1879_ = lean_unbox(v___x_1868_);
v___x_5804__boxed_1880_ = lean_unbox_usize(v___x_1869_);
lean_dec(v___x_1869_);
v_res_1881_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_boxed_1877_, v___y_1865_, v_oFiles_1866_, v_shouldExport_boxed_1878_, v___x_5803__boxed_1879_, v___x_5804__boxed_1880_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t v_bootstrap_1882_, lean_object* v___y_1883_, uint8_t v_shouldExport_1884_, uint8_t v___x_1885_, size_t v___x_1886_, lean_object* v_oFiles_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___y_1899_; uint8_t v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1895_ = lean_box(v_bootstrap_1882_);
v___x_1896_ = lean_box(v_shouldExport_1884_);
v___x_1897_ = lean_box(v___x_1885_);
v___x_1898_ = lean_box_usize(v___x_1886_);
lean_inc_ref(v___y_1883_);
v___y_1899_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed), 13, 6);
lean_closure_set(v___y_1899_, 0, v___x_1895_);
lean_closure_set(v___y_1899_, 1, v___y_1883_);
lean_closure_set(v___y_1899_, 2, v_oFiles_1887_);
lean_closure_set(v___y_1899_, 3, v___x_1896_);
lean_closure_set(v___y_1899_, 4, v___x_1897_);
lean_closure_set(v___y_1899_, 5, v___x_1898_);
v___x_1900_ = 0;
v___x_1901_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1902_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1883_, v___y_1899_, v___x_1900_, v___x_1901_, v___x_1885_, v___x_1900_, v___x_1900_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1912_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_a_1904_ = lean_ctor_get(v___x_1902_, 1);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1906_ = v___x_1902_;
v_isShared_1907_ = v_isSharedCheck_1912_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1912_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v_path_1908_; lean_object* v___x_1910_; 
v_path_1908_ = lean_ctor_get(v_a_1903_, 1);
lean_inc_ref(v_path_1908_);
lean_dec(v_a_1903_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v_path_1908_);
v___x_1910_ = v___x_1906_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_path_1908_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_a_1904_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
v_a_1913_ = lean_ctor_get(v___x_1902_, 0);
v_a_1914_ = lean_ctor_get(v___x_1902_, 1);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1902_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_inc(v_a_1913_);
lean_dec(v___x_1902_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1913_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* v_bootstrap_1922_, lean_object* v___y_1923_, lean_object* v_shouldExport_1924_, lean_object* v___x_1925_, lean_object* v___x_1926_, lean_object* v_oFiles_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
uint8_t v_bootstrap_boxed_1935_; uint8_t v_shouldExport_boxed_1936_; uint8_t v___x_6203__boxed_1937_; size_t v___x_6204__boxed_1938_; lean_object* v_res_1939_; 
v_bootstrap_boxed_1935_ = lean_unbox(v_bootstrap_1922_);
v_shouldExport_boxed_1936_ = lean_unbox(v_shouldExport_1924_);
v___x_6203__boxed_1937_ = lean_unbox(v___x_1925_);
v___x_6204__boxed_1938_ = lean_unbox_usize(v___x_1926_);
lean_dec(v___x_1926_);
v_res_1939_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_boxed_1935_, v___y_1923_, v_shouldExport_boxed_1936_, v___x_6203__boxed_1937_, v___x_6204__boxed_1938_, v_oFiles_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec(v___y_1929_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* v_a_1940_, size_t v_sz_1941_, size_t v_i_1942_, lean_object* v_bs_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
uint8_t v___x_1951_; 
v___x_1951_ = lean_usize_dec_lt(v_i_1942_, v_sz_1941_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; 
lean_dec_ref(v___y_1944_);
lean_dec_ref(v_a_1940_);
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v_bs_1943_);
lean_ctor_set(v___x_1952_, 1, v___y_1949_);
return v___x_1952_;
}
else
{
lean_object* v_v_1953_; lean_object* v___x_1954_; 
v_v_1953_ = lean_array_uget_borrowed(v_bs_1943_, v_i_1942_);
lean_inc_ref(v___y_1944_);
lean_inc_ref(v_a_1940_);
lean_inc(v_v_1953_);
v___x_1954_ = l_Lake_ModuleFacet_fetch___redArg(v_v_1953_, v_a_1940_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v_a_1956_; lean_object* v___x_1957_; lean_object* v_bs_x27_1958_; size_t v___x_1959_; size_t v___x_1960_; lean_object* v___x_1961_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
v_a_1956_ = lean_ctor_get(v___x_1954_, 1);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___x_1954_, 2);
v___x_1957_ = lean_unsigned_to_nat(0u);
v_bs_x27_1958_ = lean_array_uset(v_bs_1943_, v_i_1942_, v___x_1957_);
v___x_1959_ = ((size_t)1ULL);
v___x_1960_ = lean_usize_add(v_i_1942_, v___x_1959_);
v___x_1961_ = lean_array_uset(v_bs_x27_1958_, v_i_1942_, v_a_1955_);
v_i_1942_ = v___x_1960_;
v_bs_1943_ = v___x_1961_;
v___y_1949_ = v_a_1956_;
goto _start;
}
else
{
lean_object* v_a_1963_; lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref(v___y_1944_);
lean_dec_ref(v_bs_1943_);
lean_dec_ref(v_a_1940_);
v_a_1963_ = lean_ctor_get(v___x_1954_, 0);
v_a_1964_ = lean_ctor_get(v___x_1954_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1954_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_inc(v_a_1963_);
lean_dec(v___x_1954_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1963_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_a_1964_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object* v_a_1972_, lean_object* v_sz_1973_, lean_object* v_i_1974_, lean_object* v_bs_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
size_t v_sz_boxed_1983_; size_t v_i_boxed_1984_; lean_object* v_res_1985_; 
v_sz_boxed_1983_ = lean_unbox_usize(v_sz_1973_);
lean_dec(v_sz_1973_);
v_i_boxed_1984_ = lean_unbox_usize(v_i_1974_);
lean_dec(v_i_1974_);
v_res_1985_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_1972_, v_sz_boxed_1983_, v_i_boxed_1984_, v_bs_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec(v___y_1977_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(uint8_t v_shouldExport_1986_, lean_object* v_as_1987_, size_t v_i_1988_, size_t v_stop_1989_, lean_object* v_b_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
uint8_t v___x_1998_; 
v___x_1998_ = lean_usize_dec_eq(v_i_1988_, v_stop_1989_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v_lib_2000_; lean_object* v_config_2001_; lean_object* v_nativeFacets_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; size_t v_sz_2005_; size_t v___x_2006_; lean_object* v___x_2007_; 
v___x_1999_ = lean_array_uget_borrowed(v_as_1987_, v_i_1988_);
v_lib_2000_ = lean_ctor_get(v___x_1999_, 0);
v_config_2001_ = lean_ctor_get(v_lib_2000_, 2);
v_nativeFacets_2002_ = lean_ctor_get(v_config_2001_, 8);
v___x_2003_ = lean_box(v_shouldExport_1986_);
lean_inc_ref(v_nativeFacets_2002_);
v___x_2004_ = lean_apply_1(v_nativeFacets_2002_, v___x_2003_);
v_sz_2005_ = lean_array_size(v___x_2004_);
v___x_2006_ = ((size_t)0ULL);
lean_inc_ref(v___y_1991_);
lean_inc(v___x_1999_);
v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_1999_, v_sz_2005_, v___x_2006_, v___x_2004_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v_a_2009_; lean_object* v___x_2010_; size_t v___x_2011_; size_t v___x_2012_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
v_a_2009_ = lean_ctor_get(v___x_2007_, 1);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2007_, 2);
v___x_2010_ = l_Array_append___redArg(v_b_1990_, v_a_2008_);
lean_dec(v_a_2008_);
v___x_2011_ = ((size_t)1ULL);
v___x_2012_ = lean_usize_add(v_i_1988_, v___x_2011_);
v_i_1988_ = v___x_2012_;
v_b_1990_ = v___x_2010_;
v___y_1996_ = v_a_2009_;
goto _start;
}
else
{
lean_dec_ref(v___y_1991_);
lean_dec_ref(v_b_1990_);
return v___x_2007_;
}
}
else
{
lean_object* v___x_2014_; 
lean_dec_ref(v___y_1991_);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v_b_1990_);
lean_ctor_set(v___x_2014_, 1, v___y_1996_);
return v___x_2014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(lean_object* v_shouldExport_2015_, lean_object* v_as_2016_, lean_object* v_i_2017_, lean_object* v_stop_2018_, lean_object* v_b_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
uint8_t v_shouldExport_boxed_2027_; size_t v_i_boxed_2028_; size_t v_stop_boxed_2029_; lean_object* v_res_2030_; 
v_shouldExport_boxed_2027_ = lean_unbox(v_shouldExport_2015_);
v_i_boxed_2028_ = lean_unbox_usize(v_i_2017_);
lean_dec(v_i_2017_);
v_stop_boxed_2029_ = lean_unbox_usize(v_stop_2018_);
lean_dec(v_stop_2018_);
v_res_2030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_boxed_2027_, v_as_2016_, v_i_boxed_2028_, v_stop_boxed_2029_, v_b_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v_as_2016_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object* v___x_2031_, lean_object* v___x_2032_, lean_object* v_config_2033_, lean_object* v_config_2034_, lean_object* v_pkg_2035_, uint8_t v_shouldExport_2036_, uint8_t v___x_2037_, lean_object* v___x_2038_, lean_object* v_dir_2039_, lean_object* v_self_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v___y_2049_; size_t v___y_2050_; lean_object* v___y_2051_; uint8_t v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v_a_2069_; lean_object* v_a_2070_; lean_object* v___x_2112_; 
lean_inc_ref(v___y_2041_);
lean_inc_ref(v___y_2045_);
lean_inc(v___y_2044_);
lean_inc(v___y_2043_);
lean_inc(v___x_2032_);
v___x_2112_ = lean_apply_7(v___y_2041_, v___x_2031_, v___x_2032_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, lean_box(0));
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v_a_2114_; lean_object* v___x_2115_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
v_a_2114_ = lean_ctor_get(v___x_2112_, 1);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2112_, 2);
v___x_2115_ = l_Lake_Job_await___redArg(v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v_a_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
v_a_2117_ = lean_ctor_get(v___x_2115_, 1);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2115_, 2);
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_2120_ = lean_array_get_size(v_a_2116_);
v___x_2121_ = lean_nat_dec_lt(v___x_2118_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_dec(v_a_2116_);
v_a_2069_ = v___x_2119_;
v_a_2070_ = v_a_2117_;
goto v___jp_2068_;
}
else
{
size_t v___x_2122_; size_t v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = ((size_t)0ULL);
v___x_2123_ = lean_usize_of_nat(v___x_2120_);
lean_inc_ref(v___y_2041_);
v___x_2124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2036_, v_a_2116_, v___x_2122_, v___x_2123_, v___x_2119_, v___y_2041_, v___x_2032_, v___y_2043_, v___y_2044_, v___y_2045_, v_a_2117_);
lean_dec(v_a_2116_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v_a_2126_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
v_a_2126_ = lean_ctor_get(v___x_2124_, 1);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2124_, 2);
v_a_2069_ = v_a_2125_;
v_a_2070_ = v_a_2126_;
goto v___jp_2068_;
}
else
{
lean_object* v_a_2127_; lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec_ref(v___y_2041_);
lean_dec_ref(v_self_2040_);
lean_dec_ref(v_dir_2039_);
lean_dec(v___x_2038_);
lean_dec_ref(v_pkg_2035_);
lean_dec_ref(v_config_2033_);
lean_dec(v___x_2032_);
v_a_2127_ = lean_ctor_get(v___x_2124_, 0);
v_a_2128_ = lean_ctor_get(v___x_2124_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2124_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_inc(v_a_2127_);
lean_dec(v___x_2124_);
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
else
{
lean_object* v_a_2136_; lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec_ref(v___y_2041_);
lean_dec_ref(v_self_2040_);
lean_dec_ref(v_dir_2039_);
lean_dec(v___x_2038_);
lean_dec_ref(v_pkg_2035_);
lean_dec_ref(v_config_2033_);
lean_dec(v___x_2032_);
v_a_2136_ = lean_ctor_get(v___x_2115_, 0);
v_a_2137_ = lean_ctor_get(v___x_2115_, 1);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2115_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_inc(v_a_2136_);
lean_dec(v___x_2115_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2136_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec_ref(v___y_2041_);
lean_dec_ref(v_self_2040_);
lean_dec_ref(v_dir_2039_);
lean_dec(v___x_2038_);
lean_dec_ref(v_pkg_2035_);
lean_dec_ref(v_config_2033_);
lean_dec(v___x_2032_);
v_a_2145_ = lean_ctor_get(v___x_2112_, 0);
v_a_2146_ = lean_ctor_get(v___x_2112_, 1);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2112_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_inc(v_a_2145_);
lean_dec(v___x_2112_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2145_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
v___jp_2048_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___f_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2055_ = lean_box(v___y_2052_);
v___x_2056_ = lean_box(v_shouldExport_2036_);
v___x_2057_ = lean_box(v___x_2037_);
v___x_2058_ = lean_box_usize(v___y_2050_);
v___f_2059_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2059_, 0, v___x_2055_);
lean_closure_set(v___f_2059_, 1, v___y_2054_);
lean_closure_set(v___f_2059_, 2, v___x_2056_);
lean_closure_set(v___f_2059_, 3, v___x_2057_);
lean_closure_set(v___f_2059_, 4, v___x_2058_);
v___x_2060_ = l_Array_append___redArg(v___y_2053_, v___y_2051_);
lean_dec_ref(v___y_2051_);
v___x_2061_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_2062_ = l_Lake_Job_collectArray___redArg(v___x_2060_, v___x_2061_);
lean_dec_ref(v___x_2060_);
v___x_2063_ = lean_unsigned_to_nat(0u);
v___x_2064_ = 0;
v___x_2065_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2066_ = l_Lake_Job_mapM___redArg(v___x_2038_, v___x_2062_, v___f_2059_, v___x_2063_, v___x_2064_, v___y_2041_, v___x_2032_, v___y_2043_, v___y_2044_, v___y_2045_, v___x_2065_);
lean_dec(v___x_2032_);
v___x_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v___y_2049_);
return v___x_2067_;
}
v___jp_2068_:
{
lean_object* v_toLeanConfig_2071_; lean_object* v_toLeanConfig_2072_; uint8_t v_bootstrap_2073_; lean_object* v_buildDir_2074_; lean_object* v_nativeLibDir_2075_; lean_object* v_moreLinkObjs_2076_; lean_object* v_moreLinkObjs_2077_; lean_object* v___x_2078_; size_t v_sz_2079_; size_t v___x_2080_; lean_object* v___x_2081_; 
v_toLeanConfig_2071_ = lean_ctor_get(v_config_2033_, 1);
lean_inc_ref(v_toLeanConfig_2071_);
v_toLeanConfig_2072_ = lean_ctor_get(v_config_2034_, 0);
v_bootstrap_2073_ = lean_ctor_get_uint8(v_config_2033_, sizeof(void*)*28);
v_buildDir_2074_ = lean_ctor_get(v_config_2033_, 5);
lean_inc_ref(v_buildDir_2074_);
v_nativeLibDir_2075_ = lean_ctor_get(v_config_2033_, 7);
lean_inc_ref(v_nativeLibDir_2075_);
lean_dec_ref(v_config_2033_);
v_moreLinkObjs_2076_ = lean_ctor_get(v_toLeanConfig_2071_, 6);
lean_inc_ref(v_moreLinkObjs_2076_);
lean_dec_ref(v_toLeanConfig_2071_);
v_moreLinkObjs_2077_ = lean_ctor_get(v_toLeanConfig_2072_, 6);
v___x_2078_ = l_Array_append___redArg(v_moreLinkObjs_2076_, v_moreLinkObjs_2077_);
v_sz_2079_ = lean_array_size(v___x_2078_);
v___x_2080_ = ((size_t)0ULL);
lean_inc_ref(v___y_2041_);
v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_2035_, v_sz_2079_, v___x_2080_, v___x_2078_, v___y_2041_, v___x_2032_, v___y_2043_, v___y_2044_, v___y_2045_, v_a_2070_);
if (lean_obj_tag(v___x_2081_) == 0)
{
if (v_shouldExport_2036_ == 0)
{
lean_object* v_a_2082_; lean_object* v_a_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
v_a_2083_ = lean_ctor_get(v___x_2081_, 1);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2081_, 2);
v___x_2084_ = l_System_FilePath_normalize(v_buildDir_2074_);
v___x_2085_ = l_Lake_joinRelative(v_dir_2039_, v___x_2084_);
v___x_2086_ = l_System_FilePath_normalize(v_nativeLibDir_2075_);
v___x_2087_ = l_Lake_joinRelative(v___x_2085_, v___x_2086_);
v___x_2088_ = l_Lake_LeanLib_libName(v_self_2040_);
v___x_2089_ = l_Lake_nameToStaticLib(v___x_2088_, v_shouldExport_2036_);
v___x_2090_ = l_Lake_joinRelative(v___x_2087_, v___x_2089_);
v___y_2049_ = v_a_2083_;
v___y_2050_ = v___x_2080_;
v___y_2051_ = v_a_2082_;
v___y_2052_ = v_bootstrap_2073_;
v___y_2053_ = v_a_2069_;
v___y_2054_ = v___x_2090_;
goto v___jp_2048_;
}
else
{
lean_object* v_a_2091_; lean_object* v_a_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_a_2091_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2091_);
v_a_2092_ = lean_ctor_get(v___x_2081_, 1);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2081_, 2);
v___x_2093_ = l_System_FilePath_normalize(v_buildDir_2074_);
v___x_2094_ = l_Lake_joinRelative(v_dir_2039_, v___x_2093_);
v___x_2095_ = l_System_FilePath_normalize(v_nativeLibDir_2075_);
v___x_2096_ = l_Lake_joinRelative(v___x_2094_, v___x_2095_);
v___x_2097_ = l_Lake_LeanLib_libName(v_self_2040_);
v___x_2098_ = 0;
v___x_2099_ = l_Lake_nameToStaticLib(v___x_2097_, v___x_2098_);
v___x_2100_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_2101_ = l_System_FilePath_addExtension(v___x_2099_, v___x_2100_);
v___x_2102_ = l_Lake_joinRelative(v___x_2096_, v___x_2101_);
v___y_2049_ = v_a_2092_;
v___y_2050_ = v___x_2080_;
v___y_2051_ = v_a_2091_;
v___y_2052_ = v_bootstrap_2073_;
v___y_2053_ = v_a_2069_;
v___y_2054_ = v___x_2102_;
goto v___jp_2048_;
}
}
else
{
lean_object* v_a_2103_; lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec_ref(v_nativeLibDir_2075_);
lean_dec_ref(v_buildDir_2074_);
lean_dec_ref(v_a_2069_);
lean_dec_ref(v___y_2041_);
lean_dec_ref(v_self_2040_);
lean_dec_ref(v_dir_2039_);
lean_dec(v___x_2038_);
lean_dec(v___x_2032_);
v_a_2103_ = lean_ctor_get(v___x_2081_, 0);
v_a_2104_ = lean_ctor_get(v___x_2081_, 1);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2081_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_inc(v_a_2103_);
lean_dec(v___x_2081_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2103_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(lean_object** _args){
lean_object* v___x_2154_ = _args[0];
lean_object* v___x_2155_ = _args[1];
lean_object* v_config_2156_ = _args[2];
lean_object* v_config_2157_ = _args[3];
lean_object* v_pkg_2158_ = _args[4];
lean_object* v_shouldExport_2159_ = _args[5];
lean_object* v___x_2160_ = _args[6];
lean_object* v___x_2161_ = _args[7];
lean_object* v_dir_2162_ = _args[8];
lean_object* v_self_2163_ = _args[9];
lean_object* v___y_2164_ = _args[10];
lean_object* v___y_2165_ = _args[11];
lean_object* v___y_2166_ = _args[12];
lean_object* v___y_2167_ = _args[13];
lean_object* v___y_2168_ = _args[14];
lean_object* v___y_2169_ = _args[15];
lean_object* v___y_2170_ = _args[16];
_start:
{
uint8_t v_shouldExport_boxed_2171_; uint8_t v___x_6405__boxed_2172_; lean_object* v_res_2173_; 
v_shouldExport_boxed_2171_ = lean_unbox(v_shouldExport_2159_);
v___x_6405__boxed_2172_ = lean_unbox(v___x_2160_);
v_res_2173_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v___x_2154_, v___x_2155_, v_config_2156_, v_config_2157_, v_pkg_2158_, v_shouldExport_boxed_2171_, v___x_6405__boxed_2172_, v___x_2161_, v_dir_2162_, v_self_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec(v_config_2157_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object* v___y_2174_, lean_object* v_self_2175_, uint8_t v_shouldExport_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_toBuildConfig_2183_; lean_object* v_registeredJobs_2184_; uint8_t v_verbosity_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; uint8_t v___x_2190_; lean_object* v___y_2192_; 
v_toBuildConfig_2183_ = lean_ctor_get(v_a_2180_, 0);
v_registeredJobs_2184_ = lean_ctor_get(v_a_2180_, 4);
v_verbosity_2185_ = lean_ctor_get_uint8(v_toBuildConfig_2183_, sizeof(void*)*4 + 4);
v___x_2186_ = l_Lake_instDataKindFilePath;
v___x_2187_ = l_Lake_Verbosity_ctorIdx(v_verbosity_2185_);
v___x_2188_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0);
v___x_2189_ = lean_nat_dec_eq(v___x_2187_, v___x_2188_);
lean_dec(v___x_2187_);
v___x_2190_ = 1;
if (v___x_2189_ == 0)
{
lean_object* v___x_2237_; 
v___x_2237_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_2192_ = v___x_2237_;
goto v___jp_2191_;
}
else
{
if (v_shouldExport_2176_ == 0)
{
lean_object* v___x_2238_; 
v___x_2238_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_2192_ = v___x_2238_;
goto v___jp_2191_;
}
else
{
lean_object* v___x_2239_; 
v___x_2239_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3));
v___y_2192_ = v___x_2239_;
goto v___jp_2191_;
}
}
v___jp_2191_:
{
lean_object* v_pkg_2193_; lean_object* v_name_2194_; lean_object* v_config_2195_; lean_object* v_keyName_2196_; lean_object* v_dir_2197_; lean_object* v_config_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___f_2206_; lean_object* v___x_2207_; 
v_pkg_2193_ = lean_ctor_get(v_self_2175_, 0);
lean_inc_ref_n(v_pkg_2193_, 2);
v_name_2194_ = lean_ctor_get(v_self_2175_, 1);
lean_inc_n(v_name_2194_, 2);
v_config_2195_ = lean_ctor_get(v_self_2175_, 2);
lean_inc(v_config_2195_);
v_keyName_2196_ = lean_ctor_get(v_pkg_2193_, 2);
v_dir_2197_ = lean_ctor_get(v_pkg_2193_, 4);
lean_inc_ref(v_dir_2197_);
v_config_2198_ = lean_ctor_get(v_pkg_2193_, 6);
lean_inc_ref(v_config_2198_);
v___x_2199_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_2196_);
v___x_2200_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2200_, 0, v_keyName_2196_);
lean_ctor_set(v___x_2200_, 1, v_name_2194_);
v___x_2201_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_2175_);
v___x_2202_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
lean_ctor_set(v___x_2202_, 2, v_self_2175_);
lean_ctor_set(v___x_2202_, 3, v___x_2199_);
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v_pkg_2193_);
v___x_2204_ = lean_box(v_shouldExport_2176_);
v___x_2205_ = lean_box(v___x_2190_);
v___f_2206_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed), 17, 10);
lean_closure_set(v___f_2206_, 0, v___x_2202_);
lean_closure_set(v___f_2206_, 1, v___x_2203_);
lean_closure_set(v___f_2206_, 2, v_config_2198_);
lean_closure_set(v___f_2206_, 3, v_config_2195_);
lean_closure_set(v___f_2206_, 4, v_pkg_2193_);
lean_closure_set(v___f_2206_, 5, v___x_2204_);
lean_closure_set(v___f_2206_, 6, v___x_2205_);
lean_closure_set(v___f_2206_, 7, v___x_2186_);
lean_closure_set(v___f_2206_, 8, v_dir_2197_);
lean_closure_set(v___f_2206_, 9, v_self_2175_);
v___x_2207_ = l_Lake_ensureJob___redArg(v___x_2186_, v___f_2206_, v___y_2174_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2236_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_a_2209_ = lean_ctor_get(v___x_2207_, 1);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2211_ = v___x_2207_;
v_isShared_2212_ = v_isSharedCheck_2236_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2236_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v_task_2213_; lean_object* v_kind_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2234_; 
v_task_2213_ = lean_ctor_get(v_a_2208_, 0);
v_kind_2214_ = lean_ctor_get(v_a_2208_, 1);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_a_2208_);
if (v_isSharedCheck_2234_ == 0)
{
lean_object* v_unused_2235_; 
v_unused_2235_ = lean_ctor_get(v_a_2208_, 2);
lean_dec(v_unused_2235_);
v___x_2216_ = v_a_2208_;
v_isShared_2217_ = v_isSharedCheck_2234_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_kind_2214_);
lean_inc(v_task_2213_);
lean_dec(v_a_2208_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2234_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; lean_object* v_job_2225_; 
v___x_2218_ = lean_st_ref_take(v_registeredJobs_2184_);
v___x_2219_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2194_, v___x_2190_);
v___x_2220_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___x_2221_ = lean_string_append(v___x_2219_, v___x_2220_);
v___x_2222_ = lean_string_append(v___x_2221_, v___y_2192_);
v___x_2223_ = 0;
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 2, v___x_2222_);
v_job_2225_ = v___x_2216_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_task_2213_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v_kind_2214_);
lean_ctor_set(v_reuseFailAlloc_2233_, 2, v___x_2222_);
v_job_2225_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2231_; 
lean_ctor_set_uint8(v_job_2225_, sizeof(void*)*3, v___x_2223_);
lean_inc_ref(v_job_2225_);
v___x_2226_ = l_Lake_Job_toOpaque___redArg(v_job_2225_);
v___x_2227_ = lean_array_push(v___x_2218_, v___x_2226_);
v___x_2228_ = lean_st_ref_put(v_registeredJobs_2184_, v___x_2227_);
v___x_2229_ = l_Lake_Job_renew___redArg(v_job_2225_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v___x_2229_);
v___x_2231_ = v___x_2211_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_a_2209_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
else
{
lean_dec(v_name_2194_);
return v___x_2207_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* v___y_2240_, lean_object* v_self_2241_, lean_object* v_shouldExport_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
uint8_t v_shouldExport_boxed_2249_; lean_object* v_res_2250_; 
v_shouldExport_boxed_2249_ = lean_unbox(v_shouldExport_2242_);
v_res_2250_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2240_, v_self_2241_, v_shouldExport_boxed_2249_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_);
lean_dec_ref(v_a_2246_);
lean_dec(v_a_2245_);
lean_dec(v_a_2244_);
lean_dec(v_a_2243_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* v_x_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
uint8_t v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = 0;
v___x_2260_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2252_, v_x_2251_, v___x_2259_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object* v_x_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec(v___y_2263_);
return v_res_2269_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2272_; uint8_t v___x_2273_; lean_object* v___x_2274_; lean_object* v___f_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___f_2272_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2273_ = 1;
v___x_2274_ = l_Lake_instDataKindFilePath;
v___f_2275_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__0));
v___x_2276_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2277_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set(v___x_2277_, 1, v___f_2275_);
lean_ctor_set(v___x_2277_, 2, v___x_2274_);
lean_ctor_set(v___x_2277_, 3, v___f_2272_);
lean_ctor_set_uint8(v___x_2277_, sizeof(void*)*4, v___x_2273_);
lean_ctor_set_uint8(v___x_2277_, sizeof(void*)*4 + 1, v___x_2273_);
return v___x_2277_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_obj_once(&l_Lake_LeanLib_staticFacetConfig___closed__2, &l_Lake_LeanLib_staticFacetConfig___closed__2_once, _init_l_Lake_LeanLib_staticFacetConfig___closed__2);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(lean_object* v_a_2279_, lean_object* v_as_2280_, size_t v_i_2281_, size_t v_stop_2282_, lean_object* v_b_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2279_, v_as_2280_, v_i_2281_, v_stop_2282_, v_b_2283_, v___y_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* v_a_2292_, lean_object* v_as_2293_, lean_object* v_i_2294_, lean_object* v_stop_2295_, lean_object* v_b_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
size_t v_i_boxed_2304_; size_t v_stop_boxed_2305_; lean_object* v_res_2306_; 
v_i_boxed_2304_ = lean_unbox_usize(v_i_2294_);
lean_dec(v_i_2294_);
v_stop_boxed_2305_ = lean_unbox_usize(v_stop_2295_);
lean_dec(v_stop_2295_);
v_res_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_2292_, v_as_2293_, v_i_boxed_2304_, v_stop_boxed_2305_, v_b_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec_ref(v_as_2293_);
lean_dec(v_a_2292_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* v_x_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
uint8_t v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = 1;
v___x_2316_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2308_, v_x_2307_, v___x_2315_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object* v_x_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec(v___y_2319_);
return v_res_2325_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___f_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___f_2327_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2328_ = 1;
v___x_2329_ = l_Lake_instDataKindFilePath;
v___f_2330_ = ((lean_object*)(l_Lake_LeanLib_staticExportFacetConfig___closed__0));
v___x_2331_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2332_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set(v___x_2332_, 1, v___f_2330_);
lean_ctor_set(v___x_2332_, 2, v___x_2329_);
lean_ctor_set(v___x_2332_, 3, v___f_2327_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*4, v___x_2328_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*4 + 1, v___x_2328_);
return v___x_2332_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig(void){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_obj_once(&l_Lake_LeanLib_staticExportFacetConfig___closed__1, &l_Lake_LeanLib_staticExportFacetConfig___closed__1_once, _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1);
return v___x_2333_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0(void){
_start:
{
uint8_t v___x_2334_; lean_object* v_name_2335_; lean_object* v___x_2336_; 
v___x_2334_ = 1;
v_name_2335_ = l_Lake_instDataKindDynlib;
v___x_2336_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2335_, v___x_2334_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object* v_defaultPkg_2337_, lean_object* v_self_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
uint8_t v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = 1;
lean_inc_ref_n(v_self_2338_, 2);
v___x_2347_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_2337_, v_self_2338_, v_self_2338_, v___x_2346_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v_snd_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2390_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
v_snd_2349_ = lean_ctor_get(v_a_2348_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_a_2348_);
if (v_isSharedCheck_2390_ == 0)
{
lean_object* v_unused_2391_; 
v_unused_2391_ = lean_ctor_get(v_a_2348_, 0);
lean_dec(v_unused_2391_);
v___x_2351_ = v_a_2348_;
v_isShared_2352_ = v_isSharedCheck_2390_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_snd_2349_);
lean_dec(v_a_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2390_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2388_; 
v_a_2353_ = lean_ctor_get(v___x_2347_, 1);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2388_ == 0)
{
lean_object* v_unused_2389_; 
v_unused_2389_ = lean_ctor_get(v___x_2347_, 0);
lean_dec(v_unused_2389_);
v___x_2355_ = v___x_2347_;
v_isShared_2356_ = v_isSharedCheck_2388_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2347_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2388_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v_kind_2357_; lean_object* v_name_2358_; lean_object* v___y_2360_; uint8_t v___x_2378_; 
v_kind_2357_ = lean_ctor_get(v_snd_2349_, 1);
v_name_2358_ = l_Lake_instDataKindDynlib;
v___x_2378_ = lean_name_eq(v_kind_2357_, v_name_2358_);
if (v___x_2378_ == 0)
{
uint8_t v___x_2379_; 
lean_inc(v_kind_2357_);
lean_del_object(v___x_2351_);
lean_dec(v_snd_2349_);
v___x_2379_ = l_Lean_Name_isAnonymous(v_kind_2357_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2380_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_2381_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2357_, v___x_2346_);
v___x_2382_ = lean_string_append(v___x_2380_, v___x_2381_);
lean_dec_ref(v___x_2381_);
v___x_2383_ = lean_string_append(v___x_2382_, v___x_2380_);
v___y_2360_ = v___x_2383_;
goto v___jp_2359_;
}
else
{
lean_object* v___x_2384_; 
lean_dec(v_kind_2357_);
v___x_2384_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_2360_ = v___x_2384_;
goto v___jp_2359_;
}
}
else
{
lean_object* v___x_2386_; 
lean_del_object(v___x_2355_);
lean_dec_ref(v_self_2338_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 1, v_a_2353_);
lean_ctor_set(v___x_2351_, 0, v_snd_2349_);
v___x_2386_ = v___x_2351_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_snd_2349_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_a_2353_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
v___jp_2359_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2361_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_2362_ = l_Lake_PartialBuildKey_toString(v_self_2338_);
v___x_2363_ = lean_string_append(v___x_2361_, v___x_2362_);
lean_dec_ref(v___x_2362_);
v___x_2364_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_2365_ = lean_string_append(v___x_2363_, v___x_2364_);
v___x_2366_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0);
v___x_2367_ = lean_string_append(v___x_2365_, v___x_2366_);
v___x_2368_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_2369_ = lean_string_append(v___x_2367_, v___x_2368_);
v___x_2370_ = lean_string_append(v___x_2369_, v___y_2360_);
lean_dec_ref(v___y_2360_);
v___x_2371_ = 3;
v___x_2372_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2372_, 0, v___x_2370_);
lean_ctor_set_uint8(v___x_2372_, sizeof(void*)*1, v___x_2371_);
v___x_2373_ = lean_array_get_size(v_a_2353_);
v___x_2374_ = lean_array_push(v_a_2353_, v___x_2372_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set_tag(v___x_2355_, 1);
lean_ctor_set(v___x_2355_, 1, v___x_2374_);
lean_ctor_set(v___x_2355_, 0, v___x_2373_);
v___x_2376_ = v___x_2355_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2373_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec_ref(v_self_2338_);
v_a_2392_ = lean_ctor_get(v___x_2347_, 0);
v_a_2393_ = lean_ctor_get(v___x_2347_, 1);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2347_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_inc(v_a_2392_);
lean_dec(v___x_2347_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2392_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_a_2393_);
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
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* v_defaultPkg_2401_, lean_object* v_self_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_2401_, v_self_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec(v_a_2404_);
return v_res_2410_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2413_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0));
v___x_2414_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
lean_ctor_set(v___x_2415_, 1, v___x_2413_);
return v___x_2415_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5(void){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object* v___x_2417_, lean_object* v_as_2418_, size_t v_i_2419_, size_t v_stop_2420_, lean_object* v_b_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
uint8_t v___x_2429_; 
v___x_2429_ = lean_usize_dec_eq(v_i_2419_, v_stop_2420_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = lean_array_uget_borrowed(v_as_2418_, v_i_2419_);
lean_inc_ref(v___y_2422_);
lean_inc(v___x_2430_);
lean_inc_ref(v___x_2417_);
v___x_2431_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_2417_, v___x_2430_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v_a_2432_; lean_object* v_a_2433_; lean_object* v___x_2434_; size_t v___x_2435_; size_t v___x_2436_; 
v_a_2432_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_a_2432_);
v_a_2433_ = lean_ctor_get(v___x_2431_, 1);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2431_, 2);
v___x_2434_ = lean_array_push(v_b_2421_, v_a_2432_);
v___x_2435_ = ((size_t)1ULL);
v___x_2436_ = lean_usize_add(v_i_2419_, v___x_2435_);
v_i_2419_ = v___x_2436_;
v_b_2421_ = v___x_2434_;
v___y_2427_ = v_a_2433_;
goto _start;
}
else
{
lean_object* v_a_2438_; lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_dec_ref(v___y_2422_);
lean_dec_ref(v_b_2421_);
lean_dec_ref(v___x_2417_);
v_a_2438_ = lean_ctor_get(v___x_2431_, 0);
v_a_2439_ = lean_ctor_get(v___x_2431_, 1);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2431_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_inc(v_a_2438_);
lean_dec(v___x_2431_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2438_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
else
{
lean_object* v___x_2447_; 
lean_dec_ref(v___y_2422_);
lean_dec_ref(v___x_2417_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v_b_2421_);
lean_ctor_set(v___x_2447_, 1, v___y_2427_);
return v___x_2447_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* v___x_2448_, lean_object* v_as_2449_, lean_object* v_i_2450_, lean_object* v_stop_2451_, lean_object* v_b_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
size_t v_i_boxed_2460_; size_t v_stop_boxed_2461_; lean_object* v_res_2462_; 
v_i_boxed_2460_ = lean_unbox_usize(v_i_2450_);
lean_dec(v_i_2450_);
v_stop_boxed_2461_ = lean_unbox_usize(v_stop_2451_);
lean_dec(v_stop_2451_);
v_res_2462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_2448_, v_as_2449_, v_i_boxed_2460_, v_stop_boxed_2461_, v_b_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v_as_2449_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object* v_self_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_toHashSet_2465_; lean_object* v_toArray_2466_; uint8_t v___x_2467_; 
v_toHashSet_2465_ = lean_ctor_get(v_self_2463_, 0);
v_toArray_2466_ = lean_ctor_get(v_self_2463_, 1);
v___x_2467_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_2465_, v_a_2464_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2477_; 
lean_inc_ref(v_toArray_2466_);
lean_inc_ref(v_toHashSet_2465_);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_self_2463_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; lean_object* v_unused_2479_; 
v_unused_2478_ = lean_ctor_get(v_self_2463_, 1);
lean_dec(v_unused_2478_);
v_unused_2479_ = lean_ctor_get(v_self_2463_, 0);
lean_dec(v_unused_2479_);
v___x_2469_ = v_self_2463_;
v_isShared_2470_ = v_isSharedCheck_2477_;
goto v_resetjp_2468_;
}
else
{
lean_dec(v_self_2463_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2477_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2471_ = lean_box(0);
lean_inc_ref(v_a_2464_);
v___x_2472_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_toHashSet_2465_, v_a_2464_, v___x_2471_);
v___x_2473_ = lean_array_push(v_toArray_2466_, v_a_2464_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 1, v___x_2473_);
lean_ctor_set(v___x_2469_, 0, v___x_2472_);
v___x_2475_ = v___x_2469_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
else
{
lean_dec_ref(v_a_2464_);
return v_self_2463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object* v_as_2480_, size_t v_i_2481_, size_t v_stop_2482_, lean_object* v_b_2483_){
_start:
{
uint8_t v___x_2484_; 
v___x_2484_ = lean_usize_dec_eq(v_i_2481_, v_stop_2482_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; lean_object* v___x_2486_; size_t v___x_2487_; size_t v___x_2488_; 
v___x_2485_ = lean_array_uget_borrowed(v_as_2480_, v_i_2481_);
lean_inc(v___x_2485_);
v___x_2486_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_2483_, v___x_2485_);
v___x_2487_ = ((size_t)1ULL);
v___x_2488_ = lean_usize_add(v_i_2481_, v___x_2487_);
v_i_2481_ = v___x_2488_;
v_b_2483_ = v___x_2486_;
goto _start;
}
else
{
return v_b_2483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object* v_as_2490_, lean_object* v_i_2491_, lean_object* v_stop_2492_, lean_object* v_b_2493_){
_start:
{
size_t v_i_boxed_2494_; size_t v_stop_boxed_2495_; lean_object* v_res_2496_; 
v_i_boxed_2494_ = lean_unbox_usize(v_i_2491_);
lean_dec(v_i_2491_);
v_stop_boxed_2495_ = lean_unbox_usize(v_stop_2492_);
lean_dec(v_stop_2492_);
v_res_2496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_2490_, v_i_boxed_2494_, v_stop_boxed_2495_, v_b_2493_);
lean_dec_ref(v_as_2490_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object* v_self_2497_, lean_object* v_arr_2498_){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2499_ = lean_unsigned_to_nat(0u);
v___x_2500_ = lean_array_get_size(v_arr_2498_);
v___x_2501_ = lean_nat_dec_lt(v___x_2499_, v___x_2500_);
if (v___x_2501_ == 0)
{
return v_self_2497_;
}
else
{
size_t v___x_2502_; size_t v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = ((size_t)0ULL);
v___x_2503_ = lean_usize_of_nat(v___x_2500_);
v___x_2504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2498_, v___x_2502_, v___x_2503_, v_self_2497_);
return v___x_2504_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(lean_object* v_self_2505_, lean_object* v_arr_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_self_2505_, v_arr_2506_);
lean_dec_ref(v_arr_2506_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(lean_object* v_as_2508_, size_t v_i_2509_, size_t v_stop_2510_, lean_object* v_b_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
uint8_t v___x_2519_; 
v___x_2519_ = lean_usize_dec_eq(v_i_2509_, v_stop_2510_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v_lib_2521_; lean_object* v_pkg_2522_; lean_object* v_name_2523_; lean_object* v_keyName_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2520_ = lean_array_uget_borrowed(v_as_2508_, v_i_2509_);
v_lib_2521_ = lean_ctor_get(v___x_2520_, 0);
v_pkg_2522_ = lean_ctor_get(v_lib_2521_, 0);
v_name_2523_ = lean_ctor_get(v___x_2520_, 1);
v_keyName_2524_ = lean_ctor_get(v_pkg_2522_, 2);
v___x_2525_ = l_Lake_Module_transImportsFacet;
lean_inc(v_name_2523_);
lean_inc(v_keyName_2524_);
v___x_2526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2526_, 0, v_keyName_2524_);
lean_ctor_set(v___x_2526_, 1, v_name_2523_);
v___x_2527_ = l_Lake_Module_keyword;
lean_inc(v___x_2520_);
v___x_2528_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2526_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
lean_ctor_set(v___x_2528_, 2, v___x_2520_);
lean_ctor_set(v___x_2528_, 3, v___x_2525_);
lean_inc_ref(v___y_2512_);
lean_inc_ref(v___y_2516_);
lean_inc(v___y_2515_);
lean_inc(v___y_2514_);
lean_inc(v___y_2513_);
v___x_2529_ = lean_apply_7(v___y_2512_, v___x_2528_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, lean_box(0));
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v_a_2531_; lean_object* v___x_2532_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
v_a_2531_ = lean_ctor_get(v___x_2529_, 1);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2529_, 2);
v___x_2532_ = l_Lake_Job_await___redArg(v_a_2530_, v_a_2531_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v_a_2534_; lean_object* v___x_2535_; size_t v___x_2536_; size_t v___x_2537_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
v_a_2534_ = lean_ctor_get(v___x_2532_, 1);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2532_, 2);
v___x_2535_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_b_2511_, v_a_2533_);
lean_dec(v_a_2533_);
v___x_2536_ = ((size_t)1ULL);
v___x_2537_ = lean_usize_add(v_i_2509_, v___x_2536_);
v_i_2509_ = v___x_2537_;
v_b_2511_ = v___x_2535_;
v___y_2517_ = v_a_2534_;
goto _start;
}
else
{
lean_object* v_a_2539_; lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec_ref(v___y_2512_);
lean_dec_ref(v_b_2511_);
v_a_2539_ = lean_ctor_get(v___x_2532_, 0);
v_a_2540_ = lean_ctor_get(v___x_2532_, 1);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2532_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_inc(v_a_2539_);
lean_dec(v___x_2532_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2539_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
else
{
lean_object* v_a_2548_; lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec_ref(v___y_2512_);
lean_dec_ref(v_b_2511_);
v_a_2548_ = lean_ctor_get(v___x_2529_, 0);
v_a_2549_ = lean_ctor_get(v___x_2529_, 1);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2529_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_inc(v_a_2548_);
lean_dec(v___x_2529_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2548_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
else
{
lean_object* v___x_2557_; 
lean_dec_ref(v___y_2512_);
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v_b_2511_);
lean_ctor_set(v___x_2557_, 1, v___y_2517_);
return v___x_2557_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object* v_as_2558_, lean_object* v_i_2559_, lean_object* v_stop_2560_, lean_object* v_b_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_){
_start:
{
size_t v_i_boxed_2569_; size_t v_stop_boxed_2570_; lean_object* v_res_2571_; 
v_i_boxed_2569_ = lean_unbox_usize(v_i_2559_);
lean_dec(v_i_2559_);
v_stop_boxed_2570_ = lean_unbox_usize(v_stop_2560_);
lean_dec(v_stop_2560_);
v_res_2571_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_as_2558_, v_i_boxed_2569_, v_stop_boxed_2570_, v_b_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v_as_2558_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(lean_object* v_as_2572_, size_t v_i_2573_, size_t v_stop_2574_, lean_object* v_b_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
uint8_t v___x_2583_; 
v___x_2583_ = lean_usize_dec_eq(v_i_2573_, v_stop_2574_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; lean_object* v_pkg_2585_; lean_object* v_name_2586_; lean_object* v_keyName_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2584_ = lean_array_uget_borrowed(v_as_2572_, v_i_2573_);
v_pkg_2585_ = lean_ctor_get(v___x_2584_, 0);
v_name_2586_ = lean_ctor_get(v___x_2584_, 1);
v_keyName_2587_ = lean_ctor_get(v_pkg_2585_, 2);
v___x_2588_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_2586_);
lean_inc(v_keyName_2587_);
v___x_2589_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2589_, 0, v_keyName_2587_);
lean_ctor_set(v___x_2589_, 1, v_name_2586_);
v___x_2590_ = l_Lake_ExternLib_keyword;
lean_inc(v___x_2584_);
v___x_2591_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2589_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
lean_ctor_set(v___x_2591_, 2, v___x_2584_);
lean_ctor_set(v___x_2591_, 3, v___x_2588_);
lean_inc_ref(v___y_2576_);
lean_inc_ref(v___y_2580_);
lean_inc(v___y_2579_);
lean_inc(v___y_2578_);
lean_inc(v___y_2577_);
v___x_2592_ = lean_apply_7(v___y_2576_, v___x_2591_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, lean_box(0));
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v_a_2594_; lean_object* v___x_2595_; size_t v___x_2596_; size_t v___x_2597_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
v_a_2594_ = lean_ctor_get(v___x_2592_, 1);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2592_, 2);
v___x_2595_ = lean_array_push(v_b_2575_, v_a_2593_);
v___x_2596_ = ((size_t)1ULL);
v___x_2597_ = lean_usize_add(v_i_2573_, v___x_2596_);
v_i_2573_ = v___x_2597_;
v_b_2575_ = v___x_2595_;
v___y_2581_ = v_a_2594_;
goto _start;
}
else
{
lean_object* v_a_2599_; lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec_ref(v___y_2576_);
lean_dec_ref(v_b_2575_);
v_a_2599_ = lean_ctor_get(v___x_2592_, 0);
v_a_2600_ = lean_ctor_get(v___x_2592_, 1);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2592_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_inc(v_a_2599_);
lean_dec(v___x_2592_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2599_);
lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v___x_2608_; 
lean_dec_ref(v___y_2576_);
v___x_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2608_, 0, v_b_2575_);
lean_ctor_set(v___x_2608_, 1, v___y_2581_);
return v___x_2608_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(lean_object* v_as_2609_, lean_object* v_i_2610_, lean_object* v_stop_2611_, lean_object* v_b_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
size_t v_i_boxed_2620_; size_t v_stop_boxed_2621_; lean_object* v_res_2622_; 
v_i_boxed_2620_ = lean_unbox_usize(v_i_2610_);
lean_dec(v_i_2610_);
v_stop_boxed_2621_ = lean_unbox_usize(v_stop_2611_);
lean_dec(v_stop_2611_);
v_res_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v_as_2609_, v_i_boxed_2620_, v_stop_boxed_2621_, v_b_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v_as_2609_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(lean_object* v_as_2623_, size_t v_i_2624_, size_t v_stop_2625_, lean_object* v_b_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_a_2635_; lean_object* v_a_2636_; uint8_t v___x_2640_; 
v___x_2640_ = lean_usize_dec_eq(v_i_2624_, v_stop_2625_);
if (v___x_2640_ == 0)
{
lean_object* v_fst_2641_; lean_object* v_snd_2642_; lean_object* v___x_2643_; lean_object* v_lib_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2681_; 
v_fst_2641_ = lean_ctor_get(v_b_2626_, 0);
v_snd_2642_ = lean_ctor_get(v_b_2626_, 1);
v___x_2643_ = lean_array_uget(v_as_2623_, v_i_2624_);
v_lib_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2681_ == 0)
{
lean_object* v_unused_2682_; 
v_unused_2682_ = lean_ctor_get(v___x_2643_, 1);
lean_dec(v_unused_2682_);
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2681_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_lib_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2681_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v_pkg_2648_; lean_object* v_name_2649_; uint8_t v___x_2650_; 
v_pkg_2648_ = lean_ctor_get(v_lib_2644_, 0);
v_name_2649_ = lean_ctor_get(v_lib_2644_, 1);
lean_inc(v_name_2649_);
v___x_2650_ = l_Lean_NameSet_contains(v_fst_2641_, v_name_2649_);
if (v___x_2650_ == 0)
{
lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2678_; 
lean_inc(v_snd_2642_);
lean_inc(v_fst_2641_);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_b_2626_);
if (v_isSharedCheck_2678_ == 0)
{
lean_object* v_unused_2679_; lean_object* v_unused_2680_; 
v_unused_2679_ = lean_ctor_get(v_b_2626_, 1);
lean_dec(v_unused_2679_);
v_unused_2680_ = lean_ctor_get(v_b_2626_, 0);
lean_dec(v_unused_2680_);
v___x_2652_ = v_b_2626_;
v_isShared_2653_ = v_isSharedCheck_2678_;
goto v_resetjp_2651_;
}
else
{
lean_dec(v_b_2626_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2678_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v_keyName_2654_; lean_object* v___x_2655_; lean_object* v___x_2657_; 
v_keyName_2654_ = lean_ctor_get(v_pkg_2648_, 2);
v___x_2655_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_2649_);
lean_inc(v_keyName_2654_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set_tag(v___x_2646_, 3);
lean_ctor_set(v___x_2646_, 1, v_name_2649_);
lean_ctor_set(v___x_2646_, 0, v_keyName_2654_);
v___x_2657_ = v___x_2646_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_keyName_2654_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_name_2649_);
v___x_2657_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2658_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2659_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2657_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
lean_ctor_set(v___x_2659_, 2, v_lib_2644_);
lean_ctor_set(v___x_2659_, 3, v___x_2655_);
lean_inc_ref(v___y_2627_);
lean_inc_ref(v___y_2631_);
lean_inc(v___y_2630_);
lean_inc(v___y_2629_);
lean_inc(v___y_2628_);
v___x_2660_ = lean_apply_7(v___y_2627_, v___x_2659_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, lean_box(0));
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v_a_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
v_a_2662_ = lean_ctor_get(v___x_2660_, 1);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2660_, 2);
v___x_2663_ = lean_array_push(v_snd_2642_, v_a_2661_);
v___x_2664_ = l_Lean_NameSet_insert(v_fst_2641_, v_name_2649_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 1, v___x_2663_);
lean_ctor_set(v___x_2652_, 0, v___x_2664_);
v___x_2666_ = v___x_2652_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v___x_2663_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
v_a_2635_ = v___x_2666_;
v_a_2636_ = v_a_2662_;
goto v___jp_2634_;
}
}
else
{
lean_object* v_a_2668_; lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_del_object(v___x_2652_);
lean_dec(v_name_2649_);
lean_dec(v_snd_2642_);
lean_dec(v_fst_2641_);
lean_dec_ref(v___y_2627_);
v_a_2668_ = lean_ctor_get(v___x_2660_, 0);
v_a_2669_ = lean_ctor_get(v___x_2660_, 1);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2660_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_inc(v_a_2668_);
lean_dec(v___x_2660_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2668_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
}
else
{
lean_dec(v_name_2649_);
lean_del_object(v___x_2646_);
lean_dec_ref(v_lib_2644_);
v_a_2635_ = v_b_2626_;
v_a_2636_ = v___y_2632_;
goto v___jp_2634_;
}
}
}
else
{
lean_object* v___x_2683_; 
lean_dec_ref(v___y_2627_);
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v_b_2626_);
lean_ctor_set(v___x_2683_, 1, v___y_2632_);
return v___x_2683_;
}
v___jp_2634_:
{
size_t v___x_2637_; size_t v___x_2638_; 
v___x_2637_ = ((size_t)1ULL);
v___x_2638_ = lean_usize_add(v_i_2624_, v___x_2637_);
v_i_2624_ = v___x_2638_;
v_b_2626_ = v_a_2635_;
v___y_2632_ = v_a_2636_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object* v_as_2684_, lean_object* v_i_2685_, lean_object* v_stop_2686_, lean_object* v_b_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
size_t v_i_boxed_2695_; size_t v_stop_boxed_2696_; lean_object* v_res_2697_; 
v_i_boxed_2695_ = lean_unbox_usize(v_i_2685_);
lean_dec(v_i_2685_);
v_stop_boxed_2696_ = lean_unbox_usize(v_stop_2686_);
lean_dec(v_stop_2686_);
v_res_2697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_as_2684_, v_i_boxed_2695_, v_stop_boxed_2696_, v_b_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v_as_2684_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(lean_object* v___x_2698_, lean_object* v_as_2699_, size_t v_i_2700_, size_t v_stop_2701_, lean_object* v_b_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
uint8_t v___x_2710_; 
v___x_2710_ = lean_usize_dec_eq(v_i_2700_, v_stop_2701_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = lean_array_uget_borrowed(v_as_2699_, v_i_2700_);
lean_inc_ref(v___y_2703_);
lean_inc(v___x_2711_);
lean_inc_ref(v___x_2698_);
v___x_2712_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v___x_2698_, v___x_2711_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v_a_2714_; lean_object* v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_a_2713_);
v_a_2714_ = lean_ctor_get(v___x_2712_, 1);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2712_, 2);
v___x_2715_ = lean_array_push(v_b_2702_, v_a_2713_);
v___x_2716_ = ((size_t)1ULL);
v___x_2717_ = lean_usize_add(v_i_2700_, v___x_2716_);
v_i_2700_ = v___x_2717_;
v_b_2702_ = v___x_2715_;
v___y_2708_ = v_a_2714_;
goto _start;
}
else
{
lean_object* v_a_2719_; lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec_ref(v___y_2703_);
lean_dec_ref(v_b_2702_);
lean_dec_ref(v___x_2698_);
v_a_2719_ = lean_ctor_get(v___x_2712_, 0);
v_a_2720_ = lean_ctor_get(v___x_2712_, 1);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2712_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_inc(v_a_2719_);
lean_dec(v___x_2712_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2719_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
else
{
lean_object* v___x_2728_; 
lean_dec_ref(v___y_2703_);
lean_dec_ref(v___x_2698_);
v___x_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2728_, 0, v_b_2702_);
lean_ctor_set(v___x_2728_, 1, v___y_2708_);
return v___x_2728_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object* v___x_2729_, lean_object* v_as_2730_, lean_object* v_i_2731_, lean_object* v_stop_2732_, lean_object* v_b_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
size_t v_i_boxed_2741_; size_t v_stop_boxed_2742_; lean_object* v_res_2743_; 
v_i_boxed_2741_ = lean_unbox_usize(v_i_2731_);
lean_dec(v_i_2731_);
v_stop_boxed_2742_ = lean_unbox_usize(v_stop_2732_);
lean_dec(v_stop_2732_);
v_res_2743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v___x_2729_, v_as_2730_, v_i_boxed_2741_, v_stop_boxed_2742_, v_b_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v_as_2730_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(lean_object* v___x_2744_, lean_object* v_as_2745_, size_t v_i_2746_, size_t v_stop_2747_, lean_object* v_b_2748_){
_start:
{
lean_object* v___y_2750_; uint8_t v___x_2754_; 
v___x_2754_ = lean_usize_dec_eq(v_i_2746_, v_stop_2747_);
if (v___x_2754_ == 0)
{
lean_object* v_toConfigDecl_2755_; lean_object* v_name_2756_; lean_object* v_kind_2757_; lean_object* v_config_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v_toConfigDecl_2755_ = lean_array_uget_borrowed(v_as_2745_, v_i_2746_);
v_name_2756_ = lean_ctor_get(v_toConfigDecl_2755_, 1);
v_kind_2757_ = lean_ctor_get(v_toConfigDecl_2755_, 2);
v_config_2758_ = lean_ctor_get(v_toConfigDecl_2755_, 3);
v___x_2759_ = l_Lake_ExternLib_keyword;
v___x_2760_ = lean_name_eq(v_kind_2757_, v___x_2759_);
if (v___x_2760_ == 0)
{
v___y_2750_ = v_b_2748_;
goto v___jp_2749_;
}
else
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_inc(v_config_2758_);
lean_inc(v_name_2756_);
lean_inc_ref(v___x_2744_);
v___x_2761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2744_);
lean_ctor_set(v___x_2761_, 1, v_name_2756_);
lean_ctor_set(v___x_2761_, 2, v_config_2758_);
v___x_2762_ = lean_array_push(v_b_2748_, v___x_2761_);
v___y_2750_ = v___x_2762_;
goto v___jp_2749_;
}
}
else
{
lean_dec_ref(v___x_2744_);
return v_b_2748_;
}
v___jp_2749_:
{
size_t v___x_2751_; size_t v___x_2752_; 
v___x_2751_ = ((size_t)1ULL);
v___x_2752_ = lean_usize_add(v_i_2746_, v___x_2751_);
v_i_2746_ = v___x_2752_;
v_b_2748_ = v___y_2750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(lean_object* v___x_2763_, lean_object* v_as_2764_, lean_object* v_i_2765_, lean_object* v_stop_2766_, lean_object* v_b_2767_){
_start:
{
size_t v_i_boxed_2768_; size_t v_stop_boxed_2769_; lean_object* v_res_2770_; 
v_i_boxed_2768_ = lean_unbox_usize(v_i_2765_);
lean_dec(v_i_2765_);
v_stop_boxed_2769_ = lean_unbox_usize(v_stop_2766_);
lean_dec(v_stop_2766_);
v_res_2770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v___x_2763_, v_as_2764_, v_i_boxed_2768_, v_stop_boxed_2769_, v_b_2767_);
lean_dec_ref(v_as_2764_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(lean_object* v_as_2771_, size_t v_i_2772_, size_t v_stop_2773_, lean_object* v_b_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
uint8_t v___x_2782_; 
v___x_2782_ = lean_usize_dec_eq(v_i_2772_, v_stop_2773_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; lean_object* v_lib_2784_; lean_object* v_config_2785_; lean_object* v_nativeFacets_2786_; uint8_t v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; size_t v_sz_2790_; size_t v___x_2791_; lean_object* v___x_2792_; 
v___x_2783_ = lean_array_uget_borrowed(v_as_2771_, v_i_2772_);
v_lib_2784_ = lean_ctor_get(v___x_2783_, 0);
v_config_2785_ = lean_ctor_get(v_lib_2784_, 2);
v_nativeFacets_2786_ = lean_ctor_get(v_config_2785_, 8);
v___x_2787_ = 1;
v___x_2788_ = lean_box(v___x_2787_);
lean_inc_ref(v_nativeFacets_2786_);
v___x_2789_ = lean_apply_1(v_nativeFacets_2786_, v___x_2788_);
v_sz_2790_ = lean_array_size(v___x_2789_);
v___x_2791_ = ((size_t)0ULL);
lean_inc_ref(v___y_2775_);
lean_inc(v___x_2783_);
v___x_2792_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2783_, v_sz_2790_, v___x_2791_, v___x_2789_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v_a_2794_; lean_object* v___x_2795_; size_t v___x_2796_; size_t v___x_2797_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
v_a_2794_ = lean_ctor_get(v___x_2792_, 1);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2792_, 2);
v___x_2795_ = l_Array_append___redArg(v_b_2774_, v_a_2793_);
lean_dec(v_a_2793_);
v___x_2796_ = ((size_t)1ULL);
v___x_2797_ = lean_usize_add(v_i_2772_, v___x_2796_);
v_i_2772_ = v___x_2797_;
v_b_2774_ = v___x_2795_;
v___y_2780_ = v_a_2794_;
goto _start;
}
else
{
lean_dec_ref(v___y_2775_);
lean_dec_ref(v_b_2774_);
return v___x_2792_;
}
}
else
{
lean_object* v___x_2799_; 
lean_dec_ref(v___y_2775_);
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v_b_2774_);
lean_ctor_set(v___x_2799_, 1, v___y_2780_);
return v___x_2799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object* v_as_2800_, lean_object* v_i_2801_, lean_object* v_stop_2802_, lean_object* v_b_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
size_t v_i_boxed_2811_; size_t v_stop_boxed_2812_; lean_object* v_res_2813_; 
v_i_boxed_2811_ = lean_unbox_usize(v_i_2801_);
lean_dec(v_i_2801_);
v_stop_boxed_2812_ = lean_unbox_usize(v_stop_2802_);
lean_dec(v_stop_2802_);
v_res_2813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_as_2800_, v_i_boxed_2811_, v_stop_boxed_2812_, v_b_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v_as_2800_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(lean_object* v___x_2814_, lean_object* v___x_2815_, lean_object* v_self_2816_, lean_object* v_dir_2817_, lean_object* v_targetDecls_2818_, lean_object* v_pkg_2819_, lean_object* v_name_2820_, lean_object* v_config_2821_, lean_object* v_config_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_a_2831_; lean_object* v_a_2832_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v_a_2842_; lean_object* v_a_2843_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v_a_2903_; lean_object* v_a_2904_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v_snd_2936_; lean_object* v_a_2937_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v_a_2959_; lean_object* v_a_2960_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___x_2999_; 
lean_inc_ref(v___y_2823_);
lean_inc_ref(v___y_2827_);
lean_inc(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc(v___x_2815_);
v___x_2999_ = lean_apply_7(v___y_2823_, v___x_2814_, v___x_2815_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, lean_box(0));
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v_a_3001_; lean_object* v___x_3002_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
v_a_3001_ = lean_ctor_get(v___x_2999_, 1);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_2999_, 2);
v___x_3002_ = l_Lake_Job_await___redArg(v_a_3000_, v_a_3001_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v_a_3004_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v_a_3015_; lean_object* v_a_3016_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v_a_3050_; lean_object* v_a_3051_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
v_a_3004_ = lean_ctor_get(v___x_3002_, 1);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3002_, 2);
v___x_3075_ = lean_unsigned_to_nat(0u);
v___x_3076_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_3077_ = lean_array_get_size(v_a_3003_);
v___x_3078_ = lean_nat_dec_lt(v___x_3075_, v___x_3077_);
if (v___x_3078_ == 0)
{
v_a_3050_ = v___x_3076_;
v_a_3051_ = v_a_3004_;
goto v___jp_3049_;
}
else
{
size_t v___x_3079_; size_t v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = ((size_t)0ULL);
v___x_3080_ = lean_usize_of_nat(v___x_3077_);
lean_inc_ref(v___y_2823_);
v___x_3081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_3003_, v___x_3079_, v___x_3080_, v___x_3076_, v___y_2823_, v___x_2815_, v___y_2825_, v___y_2826_, v___y_2827_, v_a_3004_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v_a_3083_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
v_a_3083_ = lean_ctor_get(v___x_3081_, 1);
lean_inc(v_a_3083_);
lean_dec_ref_known(v___x_3081_, 2);
v_a_3050_ = v_a_3082_;
v_a_3051_ = v_a_3083_;
goto v___jp_3049_;
}
else
{
lean_object* v_a_3084_; lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v_a_3003_);
lean_dec_ref(v___y_2823_);
lean_dec_ref(v_config_2821_);
lean_dec(v_name_2820_);
lean_dec_ref(v_pkg_2819_);
lean_dec_ref(v_dir_2817_);
lean_dec_ref(v_self_2816_);
lean_dec(v___x_2815_);
v_a_3084_ = lean_ctor_get(v___x_3081_, 0);
v_a_3085_ = lean_ctor_get(v___x_3081_, 1);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3081_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_inc(v_a_3084_);
lean_dec(v___x_3081_);
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
v___jp_3005_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v___x_3017_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
v___x_3018_ = lean_array_get_size(v_a_3003_);
v___x_3019_ = lean_nat_dec_lt(v___y_3014_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_dec(v_a_3003_);
v___y_2949_ = v___y_3006_;
v___y_2950_ = v___y_3007_;
v___y_2951_ = v_a_3015_;
v___y_2952_ = v___y_3008_;
v___y_2953_ = v___y_3009_;
v___y_2954_ = v___y_3010_;
v___y_2955_ = v___y_3011_;
v___y_2956_ = v___y_3012_;
v___y_2957_ = v___y_3013_;
v___y_2958_ = v___y_3014_;
v_a_2959_ = v___x_3017_;
v_a_2960_ = v_a_3016_;
goto v___jp_2948_;
}
else
{
uint8_t v___x_3020_; 
v___x_3020_ = lean_nat_dec_le(v___x_3018_, v___x_3018_);
if (v___x_3020_ == 0)
{
if (v___x_3019_ == 0)
{
lean_dec(v_a_3003_);
v___y_2949_ = v___y_3006_;
v___y_2950_ = v___y_3007_;
v___y_2951_ = v_a_3015_;
v___y_2952_ = v___y_3008_;
v___y_2953_ = v___y_3009_;
v___y_2954_ = v___y_3010_;
v___y_2955_ = v___y_3011_;
v___y_2956_ = v___y_3012_;
v___y_2957_ = v___y_3013_;
v___y_2958_ = v___y_3014_;
v_a_2959_ = v___x_3017_;
v_a_2960_ = v_a_3016_;
goto v___jp_2948_;
}
else
{
size_t v___x_3021_; size_t v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = ((size_t)0ULL);
v___x_3022_ = lean_usize_of_nat(v___x_3018_);
lean_inc_ref(v___y_2823_);
v___x_3023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3003_, v___x_3021_, v___x_3022_, v___x_3017_, v___y_2823_, v___x_2815_, v___y_2825_, v___y_2826_, v___y_2827_, v_a_3016_);
lean_dec(v_a_3003_);
v___y_2984_ = v___y_3006_;
v___y_2985_ = v___y_3007_;
v___y_2986_ = v___y_3008_;
v___y_2987_ = v_a_3015_;
v___y_2988_ = v___y_3010_;
v___y_2989_ = v___y_3009_;
v___y_2990_ = v___y_3011_;
v___y_2991_ = v___y_3012_;
v___y_2992_ = v___y_3014_;
v___y_2993_ = v___y_3013_;
v___y_2994_ = v___x_3023_;
goto v___jp_2983_;
}
}
else
{
size_t v___x_3024_; size_t v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = ((size_t)0ULL);
v___x_3025_ = lean_usize_of_nat(v___x_3018_);
lean_inc_ref(v___y_2823_);
v___x_3026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_3003_, v___x_3024_, v___x_3025_, v___x_3017_, v___y_2823_, v___x_2815_, v___y_2825_, v___y_2826_, v___y_2827_, v_a_3016_);
lean_dec(v_a_3003_);
v___y_2984_ = v___y_3006_;
v___y_2985_ = v___y_3007_;
v___y_2986_ = v___y_3008_;
v___y_2987_ = v_a_3015_;
v___y_2988_ = v___y_3010_;
v___y_2989_ = v___y_3009_;
v___y_2990_ = v___y_3011_;
v___y_2991_ = v___y_3012_;
v___y_2992_ = v___y_3014_;
v___y_2993_ = v___y_3013_;
v___y_2994_ = v___x_3026_;
goto v___jp_2983_;
}
}
}
v___jp_3027_:
{
if (lean_obj_tag(v___y_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v_a_3039_; 
v_a_3038_ = lean_ctor_get(v___y_3037_, 0);
lean_inc(v_a_3038_);
v_a_3039_ = lean_ctor_get(v___y_3037_, 1);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___y_3037_, 2);
v___y_3006_ = v___y_3028_;
v___y_3007_ = v___y_3029_;
v___y_3008_ = v___y_3030_;
v___y_3009_ = v___y_3032_;
v___y_3010_ = v___y_3031_;
v___y_3011_ = v___y_3033_;
v___y_3012_ = v___y_3034_;
v___y_3013_ = v___y_3036_;
v___y_3014_ = v___y_3035_;
v_a_3015_ = v_a_3038_;
v_a_3016_ = v_a_3039_;
goto v___jp_3005_;
}
else
{
lean_object* v_a_3040_; lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec_ref(v___y_3036_);
lean_dec_ref(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec_ref(v___y_3030_);
lean_dec_ref(v___y_3028_);
lean_dec(v_a_3003_);
lean_dec_ref(v___y_2823_);
lean_dec(v_name_2820_);
lean_dec_ref(v_pkg_2819_);
lean_dec_ref(v_dir_2817_);
lean_dec_ref(v_self_2816_);
lean_dec(v___x_2815_);
v_a_3040_ = lean_ctor_get(v___y_3037_, 0);
v_a_3041_ = lean_ctor_get(v___y_3037_, 1);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___y_3037_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___y_3037_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_inc(v_a_3040_);
lean_dec(v___y_3037_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3040_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
v___jp_3049_:
{
lean_object* v_toLeanConfig_3052_; lean_object* v_toLeanConfig_3053_; lean_object* v_buildDir_3054_; lean_object* v_nativeLibDir_3055_; lean_object* v_moreLinkObjs_3056_; lean_object* v_moreLinkLibs_3057_; lean_object* v_moreLinkArgs_3058_; lean_object* v_weakLinkArgs_3059_; lean_object* v_moreLinkObjs_3060_; lean_object* v_moreLinkLibs_3061_; lean_object* v_moreLinkArgs_3062_; lean_object* v_weakLinkArgs_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
v_toLeanConfig_3052_ = lean_ctor_get(v_config_2821_, 1);
lean_inc_ref(v_toLeanConfig_3052_);
v_toLeanConfig_3053_ = lean_ctor_get(v_config_2822_, 0);
v_buildDir_3054_ = lean_ctor_get(v_config_2821_, 5);
lean_inc_ref(v_buildDir_3054_);
v_nativeLibDir_3055_ = lean_ctor_get(v_config_2821_, 7);
lean_inc_ref(v_nativeLibDir_3055_);
lean_dec_ref(v_config_2821_);
v_moreLinkObjs_3056_ = lean_ctor_get(v_toLeanConfig_3052_, 6);
lean_inc_ref(v_moreLinkObjs_3056_);
v_moreLinkLibs_3057_ = lean_ctor_get(v_toLeanConfig_3052_, 7);
lean_inc_ref(v_moreLinkLibs_3057_);
v_moreLinkArgs_3058_ = lean_ctor_get(v_toLeanConfig_3052_, 8);
lean_inc_ref(v_moreLinkArgs_3058_);
v_weakLinkArgs_3059_ = lean_ctor_get(v_toLeanConfig_3052_, 9);
lean_inc_ref(v_weakLinkArgs_3059_);
lean_dec_ref(v_toLeanConfig_3052_);
v_moreLinkObjs_3060_ = lean_ctor_get(v_toLeanConfig_3053_, 6);
v_moreLinkLibs_3061_ = lean_ctor_get(v_toLeanConfig_3053_, 7);
v_moreLinkArgs_3062_ = lean_ctor_get(v_toLeanConfig_3053_, 8);
v_weakLinkArgs_3063_ = lean_ctor_get(v_toLeanConfig_3053_, 9);
v___x_3064_ = l_Array_append___redArg(v_moreLinkObjs_3056_, v_moreLinkObjs_3060_);
v___x_3065_ = lean_unsigned_to_nat(0u);
v___x_3066_ = lean_array_get_size(v___x_3064_);
v___x_3067_ = lean_nat_dec_lt(v___x_3065_, v___x_3066_);
if (v___x_3067_ == 0)
{
lean_dec_ref(v___x_3064_);
v___y_3006_ = v_weakLinkArgs_3059_;
v___y_3007_ = v_weakLinkArgs_3063_;
v___y_3008_ = v_nativeLibDir_3055_;
v___y_3009_ = v_moreLinkLibs_3057_;
v___y_3010_ = v_moreLinkLibs_3061_;
v___y_3011_ = v_moreLinkArgs_3058_;
v___y_3012_ = v_moreLinkArgs_3062_;
v___y_3013_ = v_buildDir_3054_;
v___y_3014_ = v___x_3065_;
v_a_3015_ = v_a_3050_;
v_a_3016_ = v_a_3051_;
goto v___jp_3005_;
}
else
{
uint8_t v___x_3068_; 
v___x_3068_ = lean_nat_dec_le(v___x_3066_, v___x_3066_);
if (v___x_3068_ == 0)
{
if (v___x_3067_ == 0)
{
lean_dec_ref(v___x_3064_);
v___y_3006_ = v_weakLinkArgs_3059_;
v___y_3007_ = v_weakLinkArgs_3063_;
v___y_3008_ = v_nativeLibDir_3055_;
v___y_3009_ = v_moreLinkLibs_3057_;
v___y_3010_ = v_moreLinkLibs_3061_;
v___y_3011_ = v_moreLinkArgs_3058_;
v___y_3012_ = v_moreLinkArgs_3062_;
v___y_3013_ = v_buildDir_3054_;
v___y_3014_ = v___x_3065_;
v_a_3015_ = v_a_3050_;
v_a_3016_ = v_a_3051_;
goto v___jp_3005_;
}
else
{
size_t v___x_3069_; size_t v___x_3070_; lean_object* v___x_3071_; 
v___x_3069_ = ((size_t)0ULL);
v___x_3070_ = lean_usize_of_nat(v___x_3066_);
lean_inc_ref(v___y_2823_);
lean_inc_ref(v_pkg_2819_);
v___x_3071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2819_, v___x_3064_, v___x_3069_, v___x_3070_, v_a_3050_, v___y_2823_, v___x_2815_, v___y_2825_, v___y_2826_, v___y_2827_, v_a_3051_);
lean_dec_ref(v___x_3064_);
v___y_3028_ = v_weakLinkArgs_3059_;
v___y_3029_ = v_weakLinkArgs_3063_;
v___y_3030_ = v_nativeLibDir_3055_;
v___y_3031_ = v_moreLinkLibs_3061_;
v___y_3032_ = v_moreLinkLibs_3057_;
v___y_3033_ = v_moreLinkArgs_3058_;
v___y_3034_ = v_moreLinkArgs_3062_;
v___y_3035_ = v___x_3065_;
v___y_3036_ = v_buildDir_3054_;
v___y_3037_ = v___x_3071_;
goto v___jp_3027_;
}
}
else
{
size_t v___x_3072_; size_t v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = ((size_t)0ULL);
v___x_3073_ = lean_usize_of_nat(v___x_3066_);
lean_inc_ref(v___y_2823_);
lean_inc_ref(v_pkg_2819_);
v___x_3074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2819_, v___x_3064_, v___x_3072_, v___x_3073_, v_a_3050_, v___y_2823_, v___x_2815_, v___y_2825_, v___y_2826_, v___y_2827_, v_a_3051_);
lean_dec_ref(v___x_3064_);
v___y_3028_ = v_weakLinkArgs_3059_;
v___y_3029_ = v_weakLinkArgs_3063_;
v___y_3030_ = v_nativeLibDir_3055_;
v___y_3031_ = v_moreLinkLibs_3061_;
v___y_3032_ = v_moreLinkLibs_3057_;
v___y_3033_ = v_moreLinkArgs_3058_;
v___y_3034_ = v_moreLinkArgs_3062_;
v___y_3035_ = v___x_3065_;
v___y_3036_ = v_buildDir_3054_;
v___y_3037_ = v___x_3074_;
goto v___jp_3027_;
}
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec_ref(v___y_2823_);
lean_dec_ref(v_config_2821_);
lean_dec(v_name_2820_);
lean_dec_ref(v_pkg_2819_);
lean_dec_ref(v_dir_2817_);
lean_dec_ref(v_self_2816_);
lean_dec(v___x_2815_);
v_a_3093_ = lean_ctor_get(v___x_3002_, 0);
v_a_3094_ = lean_ctor_get(v___x_3002_, 1);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3002_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_inc(v_a_3093_);
lean_dec(v___x_3002_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3093_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
else
{
lean_object* v_a_3102_; lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec_ref(v___y_2823_);
lean_dec_ref(v_config_2821_);
lean_dec(v_name_2820_);
lean_dec_ref(v_pkg_2819_);
lean_dec_ref(v_dir_2817_);
lean_dec_ref(v_self_2816_);
lean_dec(v___x_2815_);
v_a_3102_ = lean_ctor_get(v___x_2999_, 0);
v_a_3103_ = lean_ctor_get(v___x_2999_, 1);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_2999_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_inc(v_a_3102_);
lean_dec(v___x_2999_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3102_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
v___jp_2830_:
{
lean_object* v___x_2833_; 
v___x_2833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2833_, 0, v_a_2831_);
lean_ctor_set(v___x_2833_, 1, v_a_2832_);
return v___x_2833_;
}
v___jp_2834_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; uint8_t v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_inc_ref(v_self_2816_);
v___x_2844_ = l_Lake_LeanLib_libName(v_self_2816_);
v___x_2845_ = l_System_FilePath_normalize(v___y_2841_);
v___x_2846_ = l_Lake_joinRelative(v_dir_2817_, v___x_2845_);
v___x_2847_ = l_System_FilePath_normalize(v___y_2838_);
v___x_2848_ = l_Lake_joinRelative(v___x_2846_, v___x_2847_);
v___x_2849_ = 0;
v___x_2850_ = l_Lake_nameToSharedLib(v___x_2844_, v___x_2849_);
v___x_2851_ = l_Lake_joinRelative(v___x_2848_, v___x_2850_);
v___x_2852_ = l_Array_append___redArg(v___y_2835_, v___y_2836_);
v___x_2853_ = l_Array_append___redArg(v___y_2839_, v___y_2840_);
v___x_2854_ = l_Lake_LeanLib_isPlugin(v_self_2816_);
v___x_2855_ = l_System_Platform_isWindows;
v___x_2856_ = lean_box(0);
v___x_2857_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2858_ = l_Lake_buildLeanSharedLib(v___x_2844_, v___x_2851_, v___y_2837_, v_a_2842_, v___x_2852_, v___x_2853_, v___x_2854_, v___x_2855_, v___x_2856_, v___y_2823_, v___x_2815_, v___y_2825_, v___y_2826_, v___y_2827_, v___x_2857_);
lean_dec(v___x_2815_);
lean_dec_ref(v___y_2837_);
v___x_2859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
lean_ctor_set(v___x_2859_, 1, v_a_2843_);
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
lean_dec_ref_known(v___y_2868_, 2);
v___y_2835_ = v___y_2861_;
v___y_2836_ = v___y_2862_;
v___y_2837_ = v___y_2864_;
v___y_2838_ = v___y_2863_;
v___y_2839_ = v___y_2865_;
v___y_2840_ = v___y_2866_;
v___y_2841_ = v___y_2867_;
v_a_2842_ = v_a_2869_;
v_a_2843_ = v_a_2870_;
goto v___jp_2834_;
}
else
{
lean_object* v_a_2871_; lean_object* v_a_2872_; 
lean_dec_ref(v___y_2867_);
lean_dec_ref(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec_ref(v___y_2861_);
lean_dec_ref(v___y_2823_);
lean_dec_ref(v_dir_2817_);
lean_dec_ref(v_self_2816_);
lean_dec(v___x_2815_);
v_a_2871_ = lean_ctor_get(v___y_2868_, 0);
lean_inc(v_a_2871_);
v_a_2872_ = lean_ctor_get(v___y_2868_, 1);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___y_2868_, 2);
v_a_2831_ = v_a_2871_;
v_a_2832_ = v_a_2872_;
goto v___jp_2830_;
}
}
v___jp_2873_:
{
lean_object* v___x_2885_; uint8_t v___x_2886_; 
v___x_2885_ = lean_array_get_size(v___y_2884_);
v___x_2886_ = lean_nat_dec_lt(v___y_2882_, v___x_2885_);
if (v___x_2886_ == 0)
{
lean_dec_ref(v___y_2884_);
v___y_2835_ = v___y_2874_;
v___y_2836_ = v___y_2876_;
v___y_2837_ = v___y_2878_;
v___y_2838_ = v___y_2877_;
v___y_2839_ = v___y_2879_;
v___y_2840_ = v___y_2881_;
v___y_2841_ = v___y_2883_;
v_a_2842_ = v___y_2880_;
v_a_2843_ = v___y_2875_;
goto v___jp_2834_;
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
v___y_2835_ = v___y_2874_;
v___y_2836_ = v___y_2876_;
v___y_2837_ = v___y_2878_;
v___y_2838_ = v___y_2877_;
v___y_2839_ = v___y_2879_;
v___y_2840_ = v___y_2881_;
v___y_2841_ = v___y_2883_;
v_a_2842_ = v___y_2880_;
v_a_2843_ = v___y_2875_;
goto v___jp_2834_;
}
else
{
size_t v___x_2888_; size_t v___x_2889_; lean_object* v___x_2890_; 
v___x_2888_ = ((size_t)0ULL);
v___x_2889_ = lean_usize_of_nat(v___x_2885_);
lean_inc_ref(v___y_2823_);
v___x_2890_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2884_, v___x_2888_, v___x_2889_, v___y_2880_, v___y_2823_, v___x_2815_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2875_);
lean_dec_ref(v___y_2884_);
v___y_2861_ = v___y_2874_;
v___y_2862_ = v___y_2876_;
v___y_2863_ = v___y_2877_;
v___y_2864_ = v___y_2878_;
v___y_2865_ = v___y_2879_;
v___y_2866_ = v___y_2881_;
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
lean_inc_ref(v___y_2823_);
v___x_2893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2884_, v___x_2891_, v___x_2892_, v___y_2880_, v___y_2823_, v___x_2815_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2875_);
lean_dec_ref(v___y_2884_);
v___y_2861_ = v___y_2874_;
v___y_2862_ = v___y_2876_;
v___y_2863_ = v___y_2877_;
v___y_2864_ = v___y_2878_;
v___y_2865_ = v___y_2879_;
v___y_2866_ = v___y_2881_;
v___y_2867_ = v___y_2883_;
v___y_2868_ = v___x_2893_;
goto v___jp_2860_;
}
}
}
v___jp_2894_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v___x_2905_ = lean_mk_empty_array_with_capacity(v___y_2902_);
v___x_2906_ = lean_array_get_size(v_targetDecls_2818_);
v___x_2907_ = lean_nat_dec_lt(v___y_2902_, v___x_2906_);
if (v___x_2907_ == 0)
{
lean_dec_ref(v_pkg_2819_);
v___y_2874_ = v___y_2895_;
v___y_2875_ = v_a_2904_;
v___y_2876_ = v___y_2896_;
v___y_2877_ = v___y_2898_;
v___y_2878_ = v___y_2897_;
v___y_2879_ = v___y_2899_;
v___y_2880_ = v_a_2903_;
v___y_2881_ = v___y_2900_;
v___y_2882_ = v___y_2902_;
v___y_2883_ = v___y_2901_;
v___y_2884_ = v___x_2905_;
goto v___jp_2873_;
}
else
{
size_t v___x_2908_; size_t v___x_2909_; lean_object* v___x_2910_; 
v___x_2908_ = ((size_t)0ULL);
v___x_2909_ = lean_usize_of_nat(v___x_2906_);
v___x_2910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2819_, v_targetDecls_2818_, v___x_2908_, v___x_2909_, v___x_2905_);
v___y_2874_ = v___y_2895_;
v___y_2875_ = v_a_2904_;
v___y_2876_ = v___y_2896_;
v___y_2877_ = v___y_2898_;
v___y_2878_ = v___y_2897_;
v___y_2879_ = v___y_2899_;
v___y_2880_ = v_a_2903_;
v___y_2881_ = v___y_2900_;
v___y_2882_ = v___y_2902_;
v___y_2883_ = v___y_2901_;
v___y_2884_ = v___x_2910_;
goto v___jp_2873_;
}
}
v___jp_2911_:
{
if (lean_obj_tag(v___y_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v_a_2922_; 
v_a_2921_ = lean_ctor_get(v___y_2920_, 0);
lean_inc(v_a_2921_);
v_a_2922_ = lean_ctor_get(v___y_2920_, 1);
lean_inc(v_a_2922_);
lean_dec_ref_known(v___y_2920_, 2);
v___y_2895_ = v___y_2912_;
v___y_2896_ = v___y_2913_;
v___y_2897_ = v___y_2915_;
v___y_2898_ = v___y_2914_;
v___y_2899_ = v___y_2916_;
v___y_2900_ = v___y_2917_;
v___y_2901_ = v___y_2919_;
v___y_2902_ = v___y_2918_;
v_a_2903_ = v_a_2921_;
v_a_2904_ = v_a_2922_;
goto v___jp_2894_;
}
else
{
lean_object* v_a_2923_; lean_object* v_a_2924_; 
lean_dec_ref(v___y_2919_);
lean_dec_ref(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec_ref(v___y_2912_);
lean_dec_ref(v___y_2823_);
lean_dec_ref(v_pkg_2819_);
lean_dec_ref(v_dir_2817_);
lean_dec_ref(v_self_2816_);
lean_dec(v___x_2815_);
v_a_2923_ = lean_ctor_get(v___y_2920_, 0);
lean_inc(v_a_2923_);
v_a_2924_ = lean_ctor_get(v___y_2920_, 1);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___y_2920_, 2);
v_a_2831_ = v_a_2923_;
v_a_2832_ = v_a_2924_;
goto v___jp_2830_;
}
}
v___jp_2925_:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v___x_2938_ = l_Array_append___redArg(v___y_2931_, v___y_2930_);
v___x_2939_ = lean_array_get_size(v___x_2938_);
v___x_2940_ = lean_nat_dec_lt(v___y_2934_, v___x_2939_);
if (v___x_2940_ == 0)
{
lean_dec_ref(v___x_2938_);
v___y_2895_ = v___y_2926_;
v___y_2896_ = v___y_2927_;
v___y_2897_ = v___y_2929_;
v___y_2898_ = v___y_2928_;
v___y_2899_ = v___y_2932_;
v___y_2900_ = v___y_2933_;
v___y_2901_ = v___y_2935_;
v___y_2902_ = v___y_2934_;
v_a_2903_ = v_snd_2936_;
v_a_2904_ = v_a_2937_;
goto v___jp_2894_;
}
else
{
uint8_t v___x_2941_; 
v___x_2941_ = lean_nat_dec_le(v___x_2939_, v___x_2939_);
if (v___x_2941_ == 0)
{
if (v___x_2940_ == 0)
{
lean_dec_ref(v___x_2938_);
v___y_2895_ = v___y_2926_;
v___y_2896_ = v___y_2927_;
v___y_2897_ = v___y_2929_;
v___y_2898_ = v___y_2928_;
v___y_2899_ = v___y_2932_;
v___y_2900_ = v___y_2933_;
v___y_2901_ = v___y_2935_;
v___y_2902_ = v___y_2934_;
v_a_2903_ = v_snd_2936_;
v_a_2904_ = v_a_2937_;
goto v___jp_2894_;
}
else
{
size_t v___x_2942_; size_t v___x_2943_; lean_object* v___x_2944_; 
v___x_2942_ = ((size_t)0ULL);
v___x_2943_ = lean_usize_of_nat(v___x_2939_);
lean_inc_ref(v___y_2823_);
lean_inc_ref(v_pkg_2819_);
v___x_2944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2819_, v___x_2938_, v___x_2942_, v___x_2943_, v_snd_2936_, v___y_2823_, v___x_2815_, v___y_2825_, v___y_2826_, v___y_2827_, v_a_2937_);
lean_dec_ref(v___x_2938_);
v___y_2912_ = v___y_2926_;
v___y_2913_ = v___y_2927_;
v___y_2914_ = v___y_2928_;
v___y_2915_ = v___y_2929_;
v___y_2916_ = v___y_2932_;
v___y_2917_ = v___y_2933_;
v___y_2918_ = v___y_2934_;
v___y_2919_ = v___y_2935_;
v___y_2920_ = v___x_2944_;
goto v___jp_2911_;
}
}
else
{
size_t v___x_2945_; size_t v___x_2946_; lean_object* v___x_2947_; 
v___x_2945_ = ((size_t)0ULL);
v___x_2946_ = lean_usize_of_nat(v___x_2939_);
lean_inc_ref(v___y_2823_);
lean_inc_ref(v_pkg_2819_);
v___x_2947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2819_, v___x_2938_, v___x_2945_, v___x_2946_, v_snd_2936_, v___y_2823_, v___x_2815_, v___y_2825_, v___y_2826_, v___y_2827_, v_a_2937_);
lean_dec_ref(v___x_2938_);
v___y_2912_ = v___y_2926_;
v___y_2913_ = v___y_2927_;
v___y_2914_ = v___y_2928_;
v___y_2915_ = v___y_2929_;
v___y_2916_ = v___y_2932_;
v___y_2917_ = v___y_2933_;
v___y_2918_ = v___y_2934_;
v___y_2919_ = v___y_2935_;
v___y_2920_ = v___x_2947_;
goto v___jp_2911_;
}
}
}
v___jp_2948_:
{
lean_object* v_toArray_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2981_; 
v_toArray_2961_ = lean_ctor_get(v_a_2959_, 1);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_a_2959_);
if (v_isSharedCheck_2981_ == 0)
{
lean_object* v_unused_2982_; 
v_unused_2982_ = lean_ctor_get(v_a_2959_, 0);
lean_dec(v_unused_2982_);
v___x_2963_ = v_a_2959_;
v_isShared_2964_ = v_isSharedCheck_2981_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_toArray_2961_);
lean_dec(v_a_2959_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2981_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2965_ = lean_mk_empty_array_with_capacity(v___y_2958_);
v___x_2966_ = lean_array_get_size(v_toArray_2961_);
v___x_2967_ = lean_nat_dec_lt(v___y_2958_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_del_object(v___x_2963_);
lean_dec_ref(v_toArray_2961_);
lean_dec(v_name_2820_);
v___y_2926_ = v___y_2949_;
v___y_2927_ = v___y_2950_;
v___y_2928_ = v___y_2952_;
v___y_2929_ = v___y_2951_;
v___y_2930_ = v___y_2954_;
v___y_2931_ = v___y_2953_;
v___y_2932_ = v___y_2955_;
v___y_2933_ = v___y_2956_;
v___y_2934_ = v___y_2958_;
v___y_2935_ = v___y_2957_;
v_snd_2936_ = v___x_2965_;
v_a_2937_ = v_a_2960_;
goto v___jp_2925_;
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2971_; 
v___x_2968_ = l_Lean_NameSet_empty;
v___x_2969_ = l_Lean_NameSet_insert(v___x_2968_, v_name_2820_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v___x_2965_);
lean_ctor_set(v___x_2963_, 0, v___x_2969_);
v___x_2971_ = v___x_2963_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v___x_2965_);
v___x_2971_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
size_t v___x_2972_; size_t v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = ((size_t)0ULL);
v___x_2973_ = lean_usize_of_nat(v___x_2966_);
lean_inc_ref(v___y_2823_);
v___x_2974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_2961_, v___x_2972_, v___x_2973_, v___x_2971_, v___y_2823_, v___x_2815_, v___y_2825_, v___y_2826_, v___y_2827_, v_a_2960_);
lean_dec_ref(v_toArray_2961_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v_a_2976_; lean_object* v_snd_2977_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
v_a_2976_ = lean_ctor_get(v___x_2974_, 1);
lean_inc(v_a_2976_);
lean_dec_ref_known(v___x_2974_, 2);
v_snd_2977_ = lean_ctor_get(v_a_2975_, 1);
lean_inc(v_snd_2977_);
lean_dec(v_a_2975_);
v___y_2926_ = v___y_2949_;
v___y_2927_ = v___y_2950_;
v___y_2928_ = v___y_2952_;
v___y_2929_ = v___y_2951_;
v___y_2930_ = v___y_2954_;
v___y_2931_ = v___y_2953_;
v___y_2932_ = v___y_2955_;
v___y_2933_ = v___y_2956_;
v___y_2934_ = v___y_2958_;
v___y_2935_ = v___y_2957_;
v_snd_2936_ = v_snd_2977_;
v_a_2937_ = v_a_2976_;
goto v___jp_2925_;
}
else
{
lean_object* v_a_2978_; lean_object* v_a_2979_; 
lean_dec_ref(v___y_2957_);
lean_dec_ref(v___y_2955_);
lean_dec_ref(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v___y_2949_);
lean_dec_ref(v___y_2823_);
lean_dec_ref(v_pkg_2819_);
lean_dec_ref(v_dir_2817_);
lean_dec_ref(v_self_2816_);
lean_dec(v___x_2815_);
v_a_2978_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2978_);
v_a_2979_ = lean_ctor_get(v___x_2974_, 1);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2974_, 2);
v_a_2831_ = v_a_2978_;
v_a_2832_ = v_a_2979_;
goto v___jp_2830_;
}
}
}
}
}
v___jp_2983_:
{
if (lean_obj_tag(v___y_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v_a_2996_; 
v_a_2995_ = lean_ctor_get(v___y_2994_, 0);
lean_inc(v_a_2995_);
v_a_2996_ = lean_ctor_get(v___y_2994_, 1);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___y_2994_, 2);
v___y_2949_ = v___y_2984_;
v___y_2950_ = v___y_2985_;
v___y_2951_ = v___y_2987_;
v___y_2952_ = v___y_2986_;
v___y_2953_ = v___y_2989_;
v___y_2954_ = v___y_2988_;
v___y_2955_ = v___y_2990_;
v___y_2956_ = v___y_2991_;
v___y_2957_ = v___y_2993_;
v___y_2958_ = v___y_2992_;
v_a_2959_ = v_a_2995_;
v_a_2960_ = v_a_2996_;
goto v___jp_2948_;
}
else
{
lean_object* v_a_2997_; lean_object* v_a_2998_; 
lean_dec_ref(v___y_2993_);
lean_dec_ref(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec_ref(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec_ref(v___y_2984_);
lean_dec_ref(v___y_2823_);
lean_dec(v_name_2820_);
lean_dec_ref(v_pkg_2819_);
lean_dec_ref(v_dir_2817_);
lean_dec_ref(v_self_2816_);
lean_dec(v___x_2815_);
v_a_2997_ = lean_ctor_get(v___y_2994_, 0);
lean_inc(v_a_2997_);
v_a_2998_ = lean_ctor_get(v___y_2994_, 1);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___y_2994_, 2);
v_a_2831_ = v_a_2997_;
v_a_2832_ = v_a_2998_;
goto v___jp_2830_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* v___x_3111_, lean_object* v___x_3112_, lean_object* v_self_3113_, lean_object* v_dir_3114_, lean_object* v_targetDecls_3115_, lean_object* v_pkg_3116_, lean_object* v_name_3117_, lean_object* v_config_3118_, lean_object* v_config_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v___x_3111_, v___x_3112_, v_self_3113_, v_dir_3114_, v_targetDecls_3115_, v_pkg_3116_, v_name_3117_, v_config_3118_, v_config_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec(v_config_3119_);
lean_dec_ref(v_targetDecls_3115_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object* v_self_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_pkg_3137_; lean_object* v_name_3138_; lean_object* v_config_3139_; lean_object* v_keyName_3140_; lean_object* v_dir_3141_; lean_object* v_config_3142_; lean_object* v_targetDecls_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___f_3150_; lean_object* v___x_3151_; 
v_pkg_3137_ = lean_ctor_get(v_self_3129_, 0);
lean_inc_ref_n(v_pkg_3137_, 2);
v_name_3138_ = lean_ctor_get(v_self_3129_, 1);
lean_inc_n(v_name_3138_, 3);
v_config_3139_ = lean_ctor_get(v_self_3129_, 2);
lean_inc(v_config_3139_);
v_keyName_3140_ = lean_ctor_get(v_pkg_3137_, 2);
v_dir_3141_ = lean_ctor_get(v_pkg_3137_, 4);
lean_inc_ref(v_dir_3141_);
v_config_3142_ = lean_ctor_get(v_pkg_3137_, 6);
lean_inc_ref(v_config_3142_);
v_targetDecls_3143_ = lean_ctor_get(v_pkg_3137_, 15);
lean_inc_ref(v_targetDecls_3143_);
v___x_3144_ = l_Lake_instDataKindDynlib;
v___x_3145_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_3140_);
v___x_3146_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3146_, 0, v_keyName_3140_);
lean_ctor_set(v___x_3146_, 1, v_name_3138_);
v___x_3147_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3129_);
v___x_3148_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3146_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
lean_ctor_set(v___x_3148_, 2, v_self_3129_);
lean_ctor_set(v___x_3148_, 3, v___x_3145_);
v___x_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3149_, 0, v_pkg_3137_);
v___f_3150_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3150_, 0, v___x_3148_);
lean_closure_set(v___f_3150_, 1, v___x_3149_);
lean_closure_set(v___f_3150_, 2, v_self_3129_);
lean_closure_set(v___f_3150_, 3, v_dir_3141_);
lean_closure_set(v___f_3150_, 4, v_targetDecls_3143_);
lean_closure_set(v___f_3150_, 5, v_pkg_3137_);
lean_closure_set(v___f_3150_, 6, v_name_3138_);
lean_closure_set(v___f_3150_, 7, v_config_3142_);
lean_closure_set(v___f_3150_, 8, v_config_3139_);
v___x_3151_ = l_Lake_ensureJob___redArg(v___x_3144_, v___f_3150_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3181_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_a_3153_ = lean_ctor_get(v___x_3151_, 1);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3155_ = v___x_3151_;
v_isShared_3156_ = v_isSharedCheck_3181_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3181_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v_task_3157_; lean_object* v_kind_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3179_; 
v_task_3157_ = lean_ctor_get(v_a_3152_, 0);
v_kind_3158_ = lean_ctor_get(v_a_3152_, 1);
v_isSharedCheck_3179_ = !lean_is_exclusive(v_a_3152_);
if (v_isSharedCheck_3179_ == 0)
{
lean_object* v_unused_3180_; 
v_unused_3180_ = lean_ctor_get(v_a_3152_, 2);
lean_dec(v_unused_3180_);
v___x_3160_ = v_a_3152_;
v_isShared_3161_ = v_isSharedCheck_3179_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_kind_3158_);
lean_inc(v_task_3157_);
lean_dec(v_a_3152_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3179_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v_registeredJobs_3162_; lean_object* v___x_3163_; uint8_t v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; uint8_t v___x_3168_; lean_object* v_job_3170_; 
v_registeredJobs_3162_ = lean_ctor_get(v_a_3134_, 4);
v___x_3163_ = lean_st_ref_take(v_registeredJobs_3162_);
v___x_3164_ = 1;
v___x_3165_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3138_, v___x_3164_);
v___x_3166_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0));
v___x_3167_ = lean_string_append(v___x_3165_, v___x_3166_);
v___x_3168_ = 0;
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 2, v___x_3167_);
v_job_3170_ = v___x_3160_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_task_3157_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_kind_3158_);
lean_ctor_set(v_reuseFailAlloc_3178_, 2, v___x_3167_);
v_job_3170_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3176_; 
lean_ctor_set_uint8(v_job_3170_, sizeof(void*)*3, v___x_3168_);
lean_inc_ref(v_job_3170_);
v___x_3171_ = l_Lake_Job_toOpaque___redArg(v_job_3170_);
v___x_3172_ = lean_array_push(v___x_3163_, v___x_3171_);
v___x_3173_ = lean_st_ref_put(v_registeredJobs_3162_, v___x_3172_);
v___x_3174_ = l_Lake_Job_renew___redArg(v_job_3170_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v___x_3174_);
v___x_3176_ = v___x_3155_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_a_3153_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
else
{
lean_dec(v_name_3138_);
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object* v_self_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec(v_a_3185_);
lean_dec(v_a_3184_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t v_fmt_3191_, lean_object* v_a_3192_){
_start:
{
if (v_fmt_3191_ == 0)
{
lean_object* v_path_3193_; 
v_path_3193_ = lean_ctor_get(v_a_3192_, 0);
lean_inc_ref(v_path_3193_);
return v_path_3193_;
}
else
{
lean_object* v_path_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v_path_3194_ = lean_ctor_get(v_a_3192_, 0);
lean_inc_ref(v_path_3194_);
v___x_3195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3195_, 0, v_path_3194_);
v___x_3196_ = l_Lean_Json_compress(v___x_3195_);
return v___x_3196_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* v_fmt_3197_, lean_object* v_a_3198_){
_start:
{
uint8_t v_fmt_boxed_3199_; lean_object* v_res_3200_; 
v_fmt_boxed_3199_ = lean_unbox(v_fmt_3197_);
v_res_3200_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_boxed_3199_, v_a_3198_);
lean_dec_ref(v_a_3198_);
return v_res_3200_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3203_; uint8_t v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___f_3203_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__0));
v___x_3204_ = 1;
v___x_3205_ = l_Lake_instDataKindDynlib;
v___x_3206_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__1));
v___x_3207_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3208_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
lean_ctor_set(v___x_3208_, 1, v___x_3206_);
lean_ctor_set(v___x_3208_, 2, v___x_3205_);
lean_ctor_set(v___x_3208_, 3, v___f_3203_);
lean_ctor_set_uint8(v___x_3208_, sizeof(void*)*4, v___x_3204_);
lean_ctor_set_uint8(v___x_3208_, sizeof(void*)*4 + 1, v___x_3204_);
return v___x_3208_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_3209_; 
v___x_3209_ = lean_obj_once(&l_Lake_LeanLib_sharedFacetConfig___closed__2, &l_Lake_LeanLib_sharedFacetConfig___closed__2_once, _init_l_Lake_LeanLib_sharedFacetConfig___closed__2);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* v___x_3210_, lean_object* v_as_3211_, size_t v_sz_3212_, size_t v_i_3213_, lean_object* v_b_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
uint8_t v___x_3222_; 
v___x_3222_ = lean_usize_dec_lt(v_i_3213_, v_sz_3212_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; 
lean_dec_ref(v___y_3215_);
lean_dec_ref(v___x_3210_);
v___x_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3223_, 0, v_b_3214_);
lean_ctor_set(v___x_3223_, 1, v___y_3220_);
return v___x_3223_;
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3225_; 
v_a_3224_ = lean_array_uget_borrowed(v_as_3211_, v_i_3213_);
lean_inc_ref(v___y_3215_);
lean_inc_n(v_a_3224_, 2);
lean_inc_ref(v___x_3210_);
v___x_3225_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v___x_3210_, v_a_3224_, v_a_3224_, v___x_3222_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v_a_3227_; lean_object* v_snd_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; size_t v___x_3231_; size_t v___x_3232_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
v_a_3227_ = lean_ctor_get(v___x_3225_, 1);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3225_, 2);
v_snd_3228_ = lean_ctor_get(v_a_3226_, 1);
lean_inc(v_snd_3228_);
lean_dec(v_a_3226_);
v___x_3229_ = l_Lake_Job_toOpaque___redArg(v_snd_3228_);
v___x_3230_ = l_Lake_Job_mix___redArg(v_b_3214_, v___x_3229_);
v___x_3231_ = ((size_t)1ULL);
v___x_3232_ = lean_usize_add(v_i_3213_, v___x_3231_);
v_i_3213_ = v___x_3232_;
v_b_3214_ = v___x_3230_;
v___y_3220_ = v_a_3227_;
goto _start;
}
else
{
lean_object* v_a_3234_; lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_dec_ref(v___y_3215_);
lean_dec_ref(v_b_3214_);
lean_dec_ref(v___x_3210_);
v_a_3234_ = lean_ctor_get(v___x_3225_, 0);
v_a_3235_ = lean_ctor_get(v___x_3225_, 1);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3225_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_inc(v_a_3234_);
lean_dec(v___x_3225_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3234_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* v___x_3243_, lean_object* v_as_3244_, lean_object* v_sz_3245_, lean_object* v_i_3246_, lean_object* v_b_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
size_t v_sz_boxed_3255_; size_t v_i_boxed_3256_; lean_object* v_res_3257_; 
v_sz_boxed_3255_ = lean_unbox_usize(v_sz_3245_);
lean_dec(v_sz_3245_);
v_i_boxed_3256_ = lean_unbox_usize(v_i_3246_);
lean_dec(v_i_3246_);
v_res_3257_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_3243_, v_as_3244_, v_sz_boxed_3255_, v_i_boxed_3256_, v_b_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v_as_3244_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* v___x_3258_, lean_object* v_as_3259_, size_t v_sz_3260_, size_t v_i_3261_, lean_object* v_b_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
uint8_t v___x_3270_; 
v___x_3270_ = lean_usize_dec_lt(v_i_3261_, v_sz_3260_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; 
lean_dec_ref(v___y_3263_);
lean_dec_ref(v___x_3258_);
v___x_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3271_, 0, v_b_3262_);
lean_ctor_set(v___x_3271_, 1, v___y_3268_);
return v___x_3271_;
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3273_; 
v_a_3272_ = lean_array_uget_borrowed(v_as_3259_, v_i_3261_);
lean_inc_ref(v___y_3263_);
lean_inc(v_a_3272_);
lean_inc_ref(v___x_3258_);
v___x_3273_ = l_Lake_Package_fetchTargetJob(v___x_3258_, v_a_3272_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v_a_3275_; lean_object* v___x_3276_; size_t v___x_3277_; size_t v___x_3278_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
v_a_3275_ = lean_ctor_get(v___x_3273_, 1);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3273_, 2);
v___x_3276_ = l_Lake_Job_mix___redArg(v_b_3262_, v_a_3274_);
v___x_3277_ = ((size_t)1ULL);
v___x_3278_ = lean_usize_add(v_i_3261_, v___x_3277_);
v_i_3261_ = v___x_3278_;
v_b_3262_ = v___x_3276_;
v___y_3268_ = v_a_3275_;
goto _start;
}
else
{
lean_object* v_a_3280_; lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec_ref(v___y_3263_);
lean_dec_ref(v_b_3262_);
lean_dec_ref(v___x_3258_);
v_a_3280_ = lean_ctor_get(v___x_3273_, 0);
v_a_3281_ = lean_ctor_get(v___x_3273_, 1);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3273_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_inc(v_a_3280_);
lean_dec(v___x_3273_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3280_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* v___x_3289_, lean_object* v_as_3290_, lean_object* v_sz_3291_, lean_object* v_i_3292_, lean_object* v_b_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
size_t v_sz_boxed_3301_; size_t v_i_boxed_3302_; lean_object* v_res_3303_; 
v_sz_boxed_3301_ = lean_unbox_usize(v_sz_3291_);
lean_dec(v_sz_3291_);
v_i_boxed_3302_ = lean_unbox_usize(v_i_3292_);
lean_dec(v_i_3292_);
v_res_3303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_3289_, v_as_3290_, v_sz_boxed_3301_, v_i_boxed_3302_, v_b_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v_as_3290_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object* v_self_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v_pkg_3314_; lean_object* v_name_3315_; lean_object* v_config_3316_; lean_object* v_baseName_3317_; lean_object* v_keyName_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v_pkg_3314_ = lean_ctor_get(v_self_3306_, 0);
lean_inc_ref_n(v_pkg_3314_, 2);
v_name_3315_ = lean_ctor_get(v_self_3306_, 1);
lean_inc(v_name_3315_);
v_config_3316_ = lean_ctor_get(v_self_3306_, 2);
lean_inc(v_config_3316_);
lean_dec_ref(v_self_3306_);
v_baseName_3317_ = lean_ctor_get(v_pkg_3314_, 1);
v_keyName_3318_ = lean_ctor_get(v_pkg_3314_, 2);
v___x_3319_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_3318_);
v___x_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3320_, 0, v_keyName_3318_);
v___x_3321_ = l_Lake_Package_keyword;
v___x_3322_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3320_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
lean_ctor_set(v___x_3322_, 2, v_pkg_3314_);
lean_ctor_set(v___x_3322_, 3, v___x_3319_);
lean_inc_ref(v_a_3307_);
lean_inc_ref(v_a_3311_);
lean_inc(v_a_3310_);
lean_inc(v_a_3309_);
lean_inc(v_a_3308_);
v___x_3323_ = lean_apply_7(v_a_3307_, v___x_3322_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, lean_box(0));
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3361_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
v_a_3325_ = lean_ctor_get(v___x_3323_, 1);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3327_ = v___x_3323_;
v_isShared_3328_ = v_isSharedCheck_3361_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_inc(v_a_3324_);
lean_dec(v___x_3323_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3361_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
uint8_t v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v_needs_3333_; lean_object* v_extraDepTargets_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; uint8_t v___x_3341_; uint8_t v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3329_ = 1;
lean_inc(v_baseName_3317_);
v___x_3330_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3317_, v___x_3329_);
v___x_3331_ = lean_unsigned_to_nat(0u);
v___x_3332_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v_needs_3333_ = lean_ctor_get(v_config_3316_, 5);
lean_inc_ref(v_needs_3333_);
v_extraDepTargets_3334_ = lean_ctor_get(v_config_3316_, 6);
lean_inc_ref(v_extraDepTargets_3334_);
lean_dec(v_config_3316_);
v___x_3335_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0));
v___x_3336_ = lean_string_append(v___x_3330_, v___x_3335_);
v___x_3337_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3315_, v___x_3329_);
v___x_3338_ = lean_string_append(v___x_3336_, v___x_3337_);
lean_dec_ref(v___x_3337_);
v___x_3339_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1));
v___x_3340_ = lean_string_append(v___x_3338_, v___x_3339_);
v___x_3341_ = 0;
v___x_3342_ = 0;
v___x_3343_ = l_Lake_BuildTrace_nil(v___x_3340_);
v___x_3344_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3344_, 0, v___x_3332_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
lean_ctor_set(v___x_3344_, 2, v___x_3331_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*3, v___x_3341_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*3 + 1, v___x_3342_);
v___x_3345_ = lean_box(0);
v___x_3346_ = lean_box(0);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 1, v___x_3344_);
lean_ctor_set(v___x_3327_, 0, v___x_3346_);
v___x_3348_ = v___x_3327_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3346_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v___x_3344_);
v___x_3348_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v_job_3351_; lean_object* v___x_3352_; size_t v_sz_3353_; size_t v___x_3354_; lean_object* v___x_3355_; 
v___x_3349_ = lean_task_pure(v___x_3348_);
v___x_3350_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v_job_3351_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_3351_, 0, v___x_3349_);
lean_ctor_set(v_job_3351_, 1, v___x_3345_);
lean_ctor_set(v_job_3351_, 2, v___x_3350_);
lean_ctor_set_uint8(v_job_3351_, sizeof(void*)*3, v___x_3342_);
v___x_3352_ = l_Lake_Job_mix___redArg(v_job_3351_, v_a_3324_);
v_sz_3353_ = lean_array_size(v_extraDepTargets_3334_);
v___x_3354_ = ((size_t)0ULL);
lean_inc_ref(v_a_3307_);
lean_inc_ref(v_pkg_3314_);
v___x_3355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_3314_, v_extraDepTargets_3334_, v_sz_3353_, v___x_3354_, v___x_3352_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3325_);
lean_dec_ref(v_extraDepTargets_3334_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v_a_3357_; size_t v_sz_3358_; lean_object* v___x_3359_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_a_3356_);
v_a_3357_ = lean_ctor_get(v___x_3355_, 1);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3355_, 2);
v_sz_3358_ = lean_array_size(v_needs_3333_);
v___x_3359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_3314_, v_needs_3333_, v_sz_3358_, v___x_3354_, v_a_3356_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3357_);
lean_dec_ref(v_needs_3333_);
return v___x_3359_;
}
else
{
lean_dec_ref(v_needs_3333_);
lean_dec_ref(v_pkg_3314_);
lean_dec_ref(v_a_3307_);
return v___x_3355_;
}
}
}
}
else
{
lean_dec(v_config_3316_);
lean_dec(v_name_3315_);
lean_dec_ref(v_pkg_3314_);
lean_dec_ref(v_a_3307_);
return v___x_3323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object* v_self_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec(v_a_3365_);
lean_dec(v_a_3364_);
return v_res_3370_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3372_; uint8_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___f_3372_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3373_ = 1;
v___x_3374_ = l_Lake_instDataKindUnit;
v___x_3375_ = ((lean_object*)(l_Lake_LeanLib_extraDepFacetConfig___closed__0));
v___x_3376_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3377_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
lean_ctor_set(v___x_3377_, 1, v___x_3375_);
lean_ctor_set(v___x_3377_, 2, v___x_3374_);
lean_ctor_set(v___x_3377_, 3, v___f_3372_);
lean_ctor_set_uint8(v___x_3377_, sizeof(void*)*4, v___x_3373_);
lean_ctor_set_uint8(v___x_3377_, sizeof(void*)*4 + 1, v___x_3373_);
return v___x_3377_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_3378_; 
v___x_3378_ = lean_obj_once(&l_Lake_LeanLib_extraDepFacetConfig___closed__1, &l_Lake_LeanLib_extraDepFacetConfig___closed__1_once, _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* v_self_3379_, size_t v_sz_3380_, size_t v_i_3381_, lean_object* v_bs_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
uint8_t v___x_3390_; 
v___x_3390_ = lean_usize_dec_lt(v_i_3381_, v_sz_3380_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; 
lean_dec_ref(v___y_3383_);
lean_dec_ref(v_self_3379_);
v___x_3391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3391_, 0, v_bs_3382_);
lean_ctor_set(v___x_3391_, 1, v___y_3388_);
return v___x_3391_;
}
else
{
lean_object* v_pkg_3392_; lean_object* v_name_3393_; lean_object* v_keyName_3394_; lean_object* v_v_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v_pkg_3392_ = lean_ctor_get(v_self_3379_, 0);
v_name_3393_ = lean_ctor_get(v_self_3379_, 1);
v_keyName_3394_ = lean_ctor_get(v_pkg_3392_, 2);
v_v_3395_ = lean_array_uget_borrowed(v_bs_3382_, v_i_3381_);
lean_inc(v_name_3393_);
lean_inc(v_keyName_3394_);
v___x_3396_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3396_, 0, v_keyName_3394_);
lean_ctor_set(v___x_3396_, 1, v_name_3393_);
v___x_3397_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc(v_v_3395_);
lean_inc_ref(v_self_3379_);
v___x_3398_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3396_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
lean_ctor_set(v___x_3398_, 2, v_self_3379_);
lean_ctor_set(v___x_3398_, 3, v_v_3395_);
lean_inc_ref(v___y_3383_);
lean_inc_ref(v___y_3387_);
lean_inc(v___y_3386_);
lean_inc(v___y_3385_);
lean_inc(v___y_3384_);
v___x_3399_ = lean_apply_7(v___y_3383_, v___x_3398_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, lean_box(0));
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v_a_3401_; lean_object* v___x_3402_; lean_object* v_bs_x27_3403_; lean_object* v___x_3404_; size_t v___x_3405_; size_t v___x_3406_; lean_object* v___x_3407_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
v_a_3401_ = lean_ctor_get(v___x_3399_, 1);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3399_, 2);
v___x_3402_ = lean_unsigned_to_nat(0u);
v_bs_x27_3403_ = lean_array_uset(v_bs_3382_, v_i_3381_, v___x_3402_);
v___x_3404_ = l_Lake_Job_toOpaque___redArg(v_a_3400_);
v___x_3405_ = ((size_t)1ULL);
v___x_3406_ = lean_usize_add(v_i_3381_, v___x_3405_);
v___x_3407_ = lean_array_uset(v_bs_x27_3403_, v_i_3381_, v___x_3404_);
v_i_3381_ = v___x_3406_;
v_bs_3382_ = v___x_3407_;
v___y_3388_ = v_a_3401_;
goto _start;
}
else
{
lean_object* v_a_3409_; lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_dec_ref(v___y_3383_);
lean_dec_ref(v_bs_3382_);
lean_dec_ref(v_self_3379_);
v_a_3409_ = lean_ctor_get(v___x_3399_, 0);
v_a_3410_ = lean_ctor_get(v___x_3399_, 1);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3399_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_inc(v_a_3409_);
lean_dec(v___x_3399_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3409_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* v_self_3418_, lean_object* v_sz_3419_, lean_object* v_i_3420_, lean_object* v_bs_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
size_t v_sz_boxed_3429_; size_t v_i_boxed_3430_; lean_object* v_res_3431_; 
v_sz_boxed_3429_ = lean_unbox_usize(v_sz_3419_);
lean_dec(v_sz_3419_);
v_i_boxed_3430_ = lean_unbox_usize(v_i_3420_);
lean_dec(v_i_3420_);
v_res_3431_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3418_, v_sz_boxed_3429_, v_i_boxed_3430_, v_bs_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec(v___y_3423_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object* v_self_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v_config_3441_; lean_object* v_defaultFacets_3442_; size_t v_sz_3443_; size_t v___x_3444_; lean_object* v___x_3445_; 
v_config_3441_ = lean_ctor_get(v_self_3433_, 2);
v_defaultFacets_3442_ = lean_ctor_get(v_config_3441_, 7);
lean_inc_ref(v_defaultFacets_3442_);
v_sz_3443_ = lean_array_size(v_defaultFacets_3442_);
v___x_3444_ = ((size_t)0ULL);
v___x_3445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3433_, v_sz_3443_, v___x_3444_, v_defaultFacets_3442_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_object* v_a_3446_; lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3456_; 
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
v_a_3447_ = lean_ctor_get(v___x_3445_, 1);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3449_ = v___x_3445_;
v_isShared_3450_ = v_isSharedCheck_3456_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_inc(v_a_3446_);
lean_dec(v___x_3445_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3456_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3454_; 
v___x_3451_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0));
v___x_3452_ = l_Lake_Job_mixArray___redArg(v_a_3446_, v___x_3451_);
lean_dec(v_a_3446_);
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v___x_3452_);
v___x_3454_ = v___x_3449_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3452_);
lean_ctor_set(v_reuseFailAlloc_3455_, 1, v_a_3447_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
v_a_3457_ = lean_ctor_get(v___x_3445_, 0);
v_a_3458_ = lean_ctor_get(v___x_3445_, 1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3445_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_inc(v_a_3457_);
lean_dec(v___x_3445_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3457_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object* v_self_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_a_3470_);
lean_dec(v_a_3469_);
lean_dec(v_a_3468_);
return v_res_3474_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3476_; uint8_t v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___f_3476_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3477_ = 1;
v___x_3478_ = l_Lake_instDataKindUnit;
v___x_3479_ = ((lean_object*)(l_Lake_LeanLib_defaultFacetConfig___closed__0));
v___x_3480_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3481_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3481_, 0, v___x_3480_);
lean_ctor_set(v___x_3481_, 1, v___x_3479_);
lean_ctor_set(v___x_3481_, 2, v___x_3478_);
lean_ctor_set(v___x_3481_, 3, v___f_3476_);
lean_ctor_set_uint8(v___x_3481_, sizeof(void*)*4, v___x_3477_);
lean_ctor_set_uint8(v___x_3481_, sizeof(void*)*4 + 1, v___x_3477_);
return v___x_3481_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_3482_; 
v___x_3482_ = lean_obj_once(&l_Lake_LeanLib_defaultFacetConfig___closed__1, &l_Lake_LeanLib_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanLib_defaultFacetConfig___closed__1);
return v___x_3482_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_3483_, lean_object* v_v_3484_, lean_object* v_t_3485_){
_start:
{
if (lean_obj_tag(v_t_3485_) == 0)
{
lean_object* v_size_3486_; lean_object* v_k_3487_; lean_object* v_v_3488_; lean_object* v_l_3489_; lean_object* v_r_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3770_; 
v_size_3486_ = lean_ctor_get(v_t_3485_, 0);
v_k_3487_ = lean_ctor_get(v_t_3485_, 1);
v_v_3488_ = lean_ctor_get(v_t_3485_, 2);
v_l_3489_ = lean_ctor_get(v_t_3485_, 3);
v_r_3490_ = lean_ctor_get(v_t_3485_, 4);
v_isSharedCheck_3770_ = !lean_is_exclusive(v_t_3485_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3492_ = v_t_3485_;
v_isShared_3493_ = v_isSharedCheck_3770_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_r_3490_);
lean_inc(v_l_3489_);
lean_inc(v_v_3488_);
lean_inc(v_k_3487_);
lean_inc(v_size_3486_);
lean_dec(v_t_3485_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3770_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
uint8_t v___x_3494_; 
v___x_3494_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3483_, v_k_3487_);
switch(v___x_3494_)
{
case 0:
{
lean_object* v_impl_3495_; lean_object* v___x_3496_; 
lean_dec(v_size_3486_);
v_impl_3495_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3483_, v_v_3484_, v_l_3489_);
v___x_3496_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3490_) == 0)
{
lean_object* v_size_3497_; lean_object* v_size_3498_; lean_object* v_k_3499_; lean_object* v_v_3500_; lean_object* v_l_3501_; lean_object* v_r_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; uint8_t v___x_3505_; 
v_size_3497_ = lean_ctor_get(v_r_3490_, 0);
v_size_3498_ = lean_ctor_get(v_impl_3495_, 0);
lean_inc(v_size_3498_);
v_k_3499_ = lean_ctor_get(v_impl_3495_, 1);
lean_inc(v_k_3499_);
v_v_3500_ = lean_ctor_get(v_impl_3495_, 2);
lean_inc(v_v_3500_);
v_l_3501_ = lean_ctor_get(v_impl_3495_, 3);
lean_inc(v_l_3501_);
v_r_3502_ = lean_ctor_get(v_impl_3495_, 4);
lean_inc(v_r_3502_);
v___x_3503_ = lean_unsigned_to_nat(3u);
v___x_3504_ = lean_nat_mul(v___x_3503_, v_size_3497_);
v___x_3505_ = lean_nat_dec_lt(v___x_3504_, v_size_3498_);
lean_dec(v___x_3504_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3509_; 
lean_dec(v_r_3502_);
lean_dec(v_l_3501_);
lean_dec(v_v_3500_);
lean_dec(v_k_3499_);
v___x_3506_ = lean_nat_add(v___x_3496_, v_size_3498_);
lean_dec(v_size_3498_);
v___x_3507_ = lean_nat_add(v___x_3506_, v_size_3497_);
lean_dec(v___x_3506_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 3, v_impl_3495_);
lean_ctor_set(v___x_3492_, 0, v___x_3507_);
v___x_3509_ = v___x_3492_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3507_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_k_3487_);
lean_ctor_set(v_reuseFailAlloc_3510_, 2, v_v_3488_);
lean_ctor_set(v_reuseFailAlloc_3510_, 3, v_impl_3495_);
lean_ctor_set(v_reuseFailAlloc_3510_, 4, v_r_3490_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
else
{
lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3576_; 
v_isSharedCheck_3576_ = !lean_is_exclusive(v_impl_3495_);
if (v_isSharedCheck_3576_ == 0)
{
lean_object* v_unused_3577_; lean_object* v_unused_3578_; lean_object* v_unused_3579_; lean_object* v_unused_3580_; lean_object* v_unused_3581_; 
v_unused_3577_ = lean_ctor_get(v_impl_3495_, 4);
lean_dec(v_unused_3577_);
v_unused_3578_ = lean_ctor_get(v_impl_3495_, 3);
lean_dec(v_unused_3578_);
v_unused_3579_ = lean_ctor_get(v_impl_3495_, 2);
lean_dec(v_unused_3579_);
v_unused_3580_ = lean_ctor_get(v_impl_3495_, 1);
lean_dec(v_unused_3580_);
v_unused_3581_ = lean_ctor_get(v_impl_3495_, 0);
lean_dec(v_unused_3581_);
v___x_3512_ = v_impl_3495_;
v_isShared_3513_ = v_isSharedCheck_3576_;
goto v_resetjp_3511_;
}
else
{
lean_dec(v_impl_3495_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3576_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v_size_3514_; lean_object* v_size_3515_; lean_object* v_k_3516_; lean_object* v_v_3517_; lean_object* v_l_3518_; lean_object* v_r_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v_size_3514_ = lean_ctor_get(v_l_3501_, 0);
v_size_3515_ = lean_ctor_get(v_r_3502_, 0);
v_k_3516_ = lean_ctor_get(v_r_3502_, 1);
v_v_3517_ = lean_ctor_get(v_r_3502_, 2);
v_l_3518_ = lean_ctor_get(v_r_3502_, 3);
v_r_3519_ = lean_ctor_get(v_r_3502_, 4);
v___x_3520_ = lean_unsigned_to_nat(2u);
v___x_3521_ = lean_nat_mul(v___x_3520_, v_size_3514_);
v___x_3522_ = lean_nat_dec_lt(v_size_3515_, v___x_3521_);
lean_dec(v___x_3521_);
if (v___x_3522_ == 0)
{
lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3551_; 
lean_inc(v_r_3519_);
lean_inc(v_l_3518_);
lean_inc(v_v_3517_);
lean_inc(v_k_3516_);
v_isSharedCheck_3551_ = !lean_is_exclusive(v_r_3502_);
if (v_isSharedCheck_3551_ == 0)
{
lean_object* v_unused_3552_; lean_object* v_unused_3553_; lean_object* v_unused_3554_; lean_object* v_unused_3555_; lean_object* v_unused_3556_; 
v_unused_3552_ = lean_ctor_get(v_r_3502_, 4);
lean_dec(v_unused_3552_);
v_unused_3553_ = lean_ctor_get(v_r_3502_, 3);
lean_dec(v_unused_3553_);
v_unused_3554_ = lean_ctor_get(v_r_3502_, 2);
lean_dec(v_unused_3554_);
v_unused_3555_ = lean_ctor_get(v_r_3502_, 1);
lean_dec(v_unused_3555_);
v_unused_3556_ = lean_ctor_get(v_r_3502_, 0);
lean_dec(v_unused_3556_);
v___x_3524_ = v_r_3502_;
v_isShared_3525_ = v_isSharedCheck_3551_;
goto v_resetjp_3523_;
}
else
{
lean_dec(v_r_3502_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3551_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___x_3539_; lean_object* v___y_3541_; 
v___x_3526_ = lean_nat_add(v___x_3496_, v_size_3498_);
lean_dec(v_size_3498_);
v___x_3527_ = lean_nat_add(v___x_3526_, v_size_3497_);
lean_dec(v___x_3526_);
v___x_3539_ = lean_nat_add(v___x_3496_, v_size_3514_);
if (lean_obj_tag(v_l_3518_) == 0)
{
lean_object* v_size_3549_; 
v_size_3549_ = lean_ctor_get(v_l_3518_, 0);
lean_inc(v_size_3549_);
v___y_3541_ = v_size_3549_;
goto v___jp_3540_;
}
else
{
lean_object* v___x_3550_; 
v___x_3550_ = lean_unsigned_to_nat(0u);
v___y_3541_ = v___x_3550_;
goto v___jp_3540_;
}
v___jp_3528_:
{
lean_object* v___x_3532_; lean_object* v___x_3534_; 
v___x_3532_ = lean_nat_add(v___y_3529_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec(v___y_3529_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 4, v_r_3490_);
lean_ctor_set(v___x_3524_, 3, v_r_3519_);
lean_ctor_set(v___x_3524_, 2, v_v_3488_);
lean_ctor_set(v___x_3524_, 1, v_k_3487_);
lean_ctor_set(v___x_3524_, 0, v___x_3532_);
v___x_3534_ = v___x_3524_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3532_);
lean_ctor_set(v_reuseFailAlloc_3538_, 1, v_k_3487_);
lean_ctor_set(v_reuseFailAlloc_3538_, 2, v_v_3488_);
lean_ctor_set(v_reuseFailAlloc_3538_, 3, v_r_3519_);
lean_ctor_set(v_reuseFailAlloc_3538_, 4, v_r_3490_);
v___x_3534_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3536_; 
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 4, v___x_3534_);
lean_ctor_set(v___x_3512_, 3, v___y_3530_);
lean_ctor_set(v___x_3512_, 2, v_v_3517_);
lean_ctor_set(v___x_3512_, 1, v_k_3516_);
lean_ctor_set(v___x_3512_, 0, v___x_3527_);
v___x_3536_ = v___x_3512_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3527_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_k_3516_);
lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_v_3517_);
lean_ctor_set(v_reuseFailAlloc_3537_, 3, v___y_3530_);
lean_ctor_set(v_reuseFailAlloc_3537_, 4, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
v___jp_3540_:
{
lean_object* v___x_3542_; lean_object* v___x_3544_; 
v___x_3542_ = lean_nat_add(v___x_3539_, v___y_3541_);
lean_dec(v___y_3541_);
lean_dec(v___x_3539_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 4, v_l_3518_);
lean_ctor_set(v___x_3492_, 3, v_l_3501_);
lean_ctor_set(v___x_3492_, 2, v_v_3500_);
lean_ctor_set(v___x_3492_, 1, v_k_3499_);
lean_ctor_set(v___x_3492_, 0, v___x_3542_);
v___x_3544_ = v___x_3492_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3542_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_k_3499_);
lean_ctor_set(v_reuseFailAlloc_3548_, 2, v_v_3500_);
lean_ctor_set(v_reuseFailAlloc_3548_, 3, v_l_3501_);
lean_ctor_set(v_reuseFailAlloc_3548_, 4, v_l_3518_);
v___x_3544_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
lean_object* v___x_3545_; 
v___x_3545_ = lean_nat_add(v___x_3496_, v_size_3497_);
if (lean_obj_tag(v_r_3519_) == 0)
{
lean_object* v_size_3546_; 
v_size_3546_ = lean_ctor_get(v_r_3519_, 0);
lean_inc(v_size_3546_);
v___y_3529_ = v___x_3545_;
v___y_3530_ = v___x_3544_;
v___y_3531_ = v_size_3546_;
goto v___jp_3528_;
}
else
{
lean_object* v___x_3547_; 
v___x_3547_ = lean_unsigned_to_nat(0u);
v___y_3529_ = v___x_3545_;
v___y_3530_ = v___x_3544_;
v___y_3531_ = v___x_3547_;
goto v___jp_3528_;
}
}
}
}
}
else
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3562_; 
lean_del_object(v___x_3492_);
v___x_3557_ = lean_nat_add(v___x_3496_, v_size_3498_);
lean_dec(v_size_3498_);
v___x_3558_ = lean_nat_add(v___x_3557_, v_size_3497_);
lean_dec(v___x_3557_);
v___x_3559_ = lean_nat_add(v___x_3496_, v_size_3497_);
v___x_3560_ = lean_nat_add(v___x_3559_, v_size_3515_);
lean_dec(v___x_3559_);
lean_inc_ref(v_r_3490_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 4, v_r_3490_);
lean_ctor_set(v___x_3512_, 3, v_r_3502_);
lean_ctor_set(v___x_3512_, 2, v_v_3488_);
lean_ctor_set(v___x_3512_, 1, v_k_3487_);
lean_ctor_set(v___x_3512_, 0, v___x_3560_);
v___x_3562_ = v___x_3512_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3560_);
lean_ctor_set(v_reuseFailAlloc_3575_, 1, v_k_3487_);
lean_ctor_set(v_reuseFailAlloc_3575_, 2, v_v_3488_);
lean_ctor_set(v_reuseFailAlloc_3575_, 3, v_r_3502_);
lean_ctor_set(v_reuseFailAlloc_3575_, 4, v_r_3490_);
v___x_3562_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
v_isSharedCheck_3569_ = !lean_is_exclusive(v_r_3490_);
if (v_isSharedCheck_3569_ == 0)
{
lean_object* v_unused_3570_; lean_object* v_unused_3571_; lean_object* v_unused_3572_; lean_object* v_unused_3573_; lean_object* v_unused_3574_; 
v_unused_3570_ = lean_ctor_get(v_r_3490_, 4);
lean_dec(v_unused_3570_);
v_unused_3571_ = lean_ctor_get(v_r_3490_, 3);
lean_dec(v_unused_3571_);
v_unused_3572_ = lean_ctor_get(v_r_3490_, 2);
lean_dec(v_unused_3572_);
v_unused_3573_ = lean_ctor_get(v_r_3490_, 1);
lean_dec(v_unused_3573_);
v_unused_3574_ = lean_ctor_get(v_r_3490_, 0);
lean_dec(v_unused_3574_);
v___x_3564_ = v_r_3490_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_dec(v_r_3490_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 4, v___x_3562_);
lean_ctor_set(v___x_3564_, 3, v_l_3501_);
lean_ctor_set(v___x_3564_, 2, v_v_3500_);
lean_ctor_set(v___x_3564_, 1, v_k_3499_);
lean_ctor_set(v___x_3564_, 0, v___x_3558_);
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3558_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_k_3499_);
lean_ctor_set(v_reuseFailAlloc_3568_, 2, v_v_3500_);
lean_ctor_set(v_reuseFailAlloc_3568_, 3, v_l_3501_);
lean_ctor_set(v_reuseFailAlloc_3568_, 4, v___x_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3582_; 
v_l_3582_ = lean_ctor_get(v_impl_3495_, 3);
lean_inc(v_l_3582_);
if (lean_obj_tag(v_l_3582_) == 0)
{
lean_object* v_r_3583_; lean_object* v_k_3584_; lean_object* v_v_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3596_; 
v_r_3583_ = lean_ctor_get(v_impl_3495_, 4);
v_k_3584_ = lean_ctor_get(v_impl_3495_, 1);
v_v_3585_ = lean_ctor_get(v_impl_3495_, 2);
v_isSharedCheck_3596_ = !lean_is_exclusive(v_impl_3495_);
if (v_isSharedCheck_3596_ == 0)
{
lean_object* v_unused_3597_; lean_object* v_unused_3598_; 
v_unused_3597_ = lean_ctor_get(v_impl_3495_, 3);
lean_dec(v_unused_3597_);
v_unused_3598_ = lean_ctor_get(v_impl_3495_, 0);
lean_dec(v_unused_3598_);
v___x_3587_ = v_impl_3495_;
v_isShared_3588_ = v_isSharedCheck_3596_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_r_3583_);
lean_inc(v_v_3585_);
lean_inc(v_k_3584_);
lean_dec(v_impl_3495_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3596_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3589_; lean_object* v___x_3591_; 
v___x_3589_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3583_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 3, v_r_3583_);
lean_ctor_set(v___x_3587_, 2, v_v_3488_);
lean_ctor_set(v___x_3587_, 1, v_k_3487_);
lean_ctor_set(v___x_3587_, 0, v___x_3496_);
v___x_3591_ = v___x_3587_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3496_);
lean_ctor_set(v_reuseFailAlloc_3595_, 1, v_k_3487_);
lean_ctor_set(v_reuseFailAlloc_3595_, 2, v_v_3488_);
lean_ctor_set(v_reuseFailAlloc_3595_, 3, v_r_3583_);
lean_ctor_set(v_reuseFailAlloc_3595_, 4, v_r_3583_);
v___x_3591_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
lean_object* v___x_3593_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 4, v___x_3591_);
lean_ctor_set(v___x_3492_, 3, v_l_3582_);
lean_ctor_set(v___x_3492_, 2, v_v_3585_);
lean_ctor_set(v___x_3492_, 1, v_k_3584_);
lean_ctor_set(v___x_3492_, 0, v___x_3589_);
v___x_3593_ = v___x_3492_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3589_);
lean_ctor_set(v_reuseFailAlloc_3594_, 1, v_k_3584_);
lean_ctor_set(v_reuseFailAlloc_3594_, 2, v_v_3585_);
lean_ctor_set(v_reuseFailAlloc_3594_, 3, v_l_3582_);
lean_ctor_set(v_reuseFailAlloc_3594_, 4, v___x_3591_);
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
else
{
lean_object* v_r_3599_; 
v_r_3599_ = lean_ctor_get(v_impl_3495_, 4);
lean_inc(v_r_3599_);
if (lean_obj_tag(v_r_3599_) == 0)
{
lean_object* v_k_3600_; lean_object* v_v_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3624_; 
v_k_3600_ = lean_ctor_get(v_impl_3495_, 1);
v_v_3601_ = lean_ctor_get(v_impl_3495_, 2);
v_isSharedCheck_3624_ = !lean_is_exclusive(v_impl_3495_);
if (v_isSharedCheck_3624_ == 0)
{
lean_object* v_unused_3625_; lean_object* v_unused_3626_; lean_object* v_unused_3627_; 
v_unused_3625_ = lean_ctor_get(v_impl_3495_, 4);
lean_dec(v_unused_3625_);
v_unused_3626_ = lean_ctor_get(v_impl_3495_, 3);
lean_dec(v_unused_3626_);
v_unused_3627_ = lean_ctor_get(v_impl_3495_, 0);
lean_dec(v_unused_3627_);
v___x_3603_ = v_impl_3495_;
v_isShared_3604_ = v_isSharedCheck_3624_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_v_3601_);
lean_inc(v_k_3600_);
lean_dec(v_impl_3495_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3624_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v_k_3605_; lean_object* v_v_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3620_; 
v_k_3605_ = lean_ctor_get(v_r_3599_, 1);
v_v_3606_ = lean_ctor_get(v_r_3599_, 2);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_r_3599_);
if (v_isSharedCheck_3620_ == 0)
{
lean_object* v_unused_3621_; lean_object* v_unused_3622_; lean_object* v_unused_3623_; 
v_unused_3621_ = lean_ctor_get(v_r_3599_, 4);
lean_dec(v_unused_3621_);
v_unused_3622_ = lean_ctor_get(v_r_3599_, 3);
lean_dec(v_unused_3622_);
v_unused_3623_ = lean_ctor_get(v_r_3599_, 0);
lean_dec(v_unused_3623_);
v___x_3608_ = v_r_3599_;
v_isShared_3609_ = v_isSharedCheck_3620_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_v_3606_);
lean_inc(v_k_3605_);
lean_dec(v_r_3599_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3620_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3610_; lean_object* v___x_3612_; 
v___x_3610_ = lean_unsigned_to_nat(3u);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 4, v_l_3582_);
lean_ctor_set(v___x_3608_, 3, v_l_3582_);
lean_ctor_set(v___x_3608_, 2, v_v_3601_);
lean_ctor_set(v___x_3608_, 1, v_k_3600_);
lean_ctor_set(v___x_3608_, 0, v___x_3496_);
v___x_3612_ = v___x_3608_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3496_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_k_3600_);
lean_ctor_set(v_reuseFailAlloc_3619_, 2, v_v_3601_);
lean_ctor_set(v_reuseFailAlloc_3619_, 3, v_l_3582_);
lean_ctor_set(v_reuseFailAlloc_3619_, 4, v_l_3582_);
v___x_3612_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
lean_object* v___x_3614_; 
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 4, v_l_3582_);
lean_ctor_set(v___x_3603_, 2, v_v_3488_);
lean_ctor_set(v___x_3603_, 1, v_k_3487_);
lean_ctor_set(v___x_3603_, 0, v___x_3496_);
v___x_3614_ = v___x_3603_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3496_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v_k_3487_);
lean_ctor_set(v_reuseFailAlloc_3618_, 2, v_v_3488_);
lean_ctor_set(v_reuseFailAlloc_3618_, 3, v_l_3582_);
lean_ctor_set(v_reuseFailAlloc_3618_, 4, v_l_3582_);
v___x_3614_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3616_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 4, v___x_3614_);
lean_ctor_set(v___x_3492_, 3, v___x_3612_);
lean_ctor_set(v___x_3492_, 2, v_v_3606_);
lean_ctor_set(v___x_3492_, 1, v_k_3605_);
lean_ctor_set(v___x_3492_, 0, v___x_3610_);
v___x_3616_ = v___x_3492_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3610_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_k_3605_);
lean_ctor_set(v_reuseFailAlloc_3617_, 2, v_v_3606_);
lean_ctor_set(v_reuseFailAlloc_3617_, 3, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3617_, 4, v___x_3614_);
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
else
{
lean_object* v___x_3628_; lean_object* v___x_3630_; 
v___x_3628_ = lean_unsigned_to_nat(2u);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 4, v_r_3599_);
lean_ctor_set(v___x_3492_, 3, v_impl_3495_);
lean_ctor_set(v___x_3492_, 0, v___x_3628_);
v___x_3630_ = v___x_3492_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3628_);
lean_ctor_set(v_reuseFailAlloc_3631_, 1, v_k_3487_);
lean_ctor_set(v_reuseFailAlloc_3631_, 2, v_v_3488_);
lean_ctor_set(v_reuseFailAlloc_3631_, 3, v_impl_3495_);
lean_ctor_set(v_reuseFailAlloc_3631_, 4, v_r_3599_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3633_; 
lean_dec(v_v_3488_);
lean_dec(v_k_3487_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 2, v_v_3484_);
lean_ctor_set(v___x_3492_, 1, v_k_3483_);
v___x_3633_ = v___x_3492_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_size_3486_);
lean_ctor_set(v_reuseFailAlloc_3634_, 1, v_k_3483_);
lean_ctor_set(v_reuseFailAlloc_3634_, 2, v_v_3484_);
lean_ctor_set(v_reuseFailAlloc_3634_, 3, v_l_3489_);
lean_ctor_set(v_reuseFailAlloc_3634_, 4, v_r_3490_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
default: 
{
lean_object* v_impl_3635_; lean_object* v___x_3636_; 
lean_dec(v_size_3486_);
v_impl_3635_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3483_, v_v_3484_, v_r_3490_);
v___x_3636_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3489_) == 0)
{
lean_object* v_size_3637_; lean_object* v_size_3638_; lean_object* v_k_3639_; lean_object* v_v_3640_; lean_object* v_l_3641_; lean_object* v_r_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; uint8_t v___x_3645_; 
v_size_3637_ = lean_ctor_get(v_l_3489_, 0);
v_size_3638_ = lean_ctor_get(v_impl_3635_, 0);
lean_inc(v_size_3638_);
v_k_3639_ = lean_ctor_get(v_impl_3635_, 1);
lean_inc(v_k_3639_);
v_v_3640_ = lean_ctor_get(v_impl_3635_, 2);
lean_inc(v_v_3640_);
v_l_3641_ = lean_ctor_get(v_impl_3635_, 3);
lean_inc(v_l_3641_);
v_r_3642_ = lean_ctor_get(v_impl_3635_, 4);
lean_inc(v_r_3642_);
v___x_3643_ = lean_unsigned_to_nat(3u);
v___x_3644_ = lean_nat_mul(v___x_3643_, v_size_3637_);
v___x_3645_ = lean_nat_dec_lt(v___x_3644_, v_size_3638_);
lean_dec(v___x_3644_);
if (v___x_3645_ == 0)
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3649_; 
lean_dec(v_r_3642_);
lean_dec(v_l_3641_);
lean_dec(v_v_3640_);
lean_dec(v_k_3639_);
v___x_3646_ = lean_nat_add(v___x_3636_, v_size_3637_);
v___x_3647_ = lean_nat_add(v___x_3646_, v_size_3638_);
lean_dec(v_size_3638_);
lean_dec(v___x_3646_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 4, v_impl_3635_);
lean_ctor_set(v___x_3492_, 0, v___x_3647_);
v___x_3649_ = v___x_3492_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_k_3487_);
lean_ctor_set(v_reuseFailAlloc_3650_, 2, v_v_3488_);
lean_ctor_set(v_reuseFailAlloc_3650_, 3, v_l_3489_);
lean_ctor_set(v_reuseFailAlloc_3650_, 4, v_impl_3635_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
else
{
lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3714_; 
v_isSharedCheck_3714_ = !lean_is_exclusive(v_impl_3635_);
if (v_isSharedCheck_3714_ == 0)
{
lean_object* v_unused_3715_; lean_object* v_unused_3716_; lean_object* v_unused_3717_; lean_object* v_unused_3718_; lean_object* v_unused_3719_; 
v_unused_3715_ = lean_ctor_get(v_impl_3635_, 4);
lean_dec(v_unused_3715_);
v_unused_3716_ = lean_ctor_get(v_impl_3635_, 3);
lean_dec(v_unused_3716_);
v_unused_3717_ = lean_ctor_get(v_impl_3635_, 2);
lean_dec(v_unused_3717_);
v_unused_3718_ = lean_ctor_get(v_impl_3635_, 1);
lean_dec(v_unused_3718_);
v_unused_3719_ = lean_ctor_get(v_impl_3635_, 0);
lean_dec(v_unused_3719_);
v___x_3652_ = v_impl_3635_;
v_isShared_3653_ = v_isSharedCheck_3714_;
goto v_resetjp_3651_;
}
else
{
lean_dec(v_impl_3635_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3714_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v_size_3654_; lean_object* v_k_3655_; lean_object* v_v_3656_; lean_object* v_l_3657_; lean_object* v_r_3658_; lean_object* v_size_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; uint8_t v___x_3662_; 
v_size_3654_ = lean_ctor_get(v_l_3641_, 0);
v_k_3655_ = lean_ctor_get(v_l_3641_, 1);
v_v_3656_ = lean_ctor_get(v_l_3641_, 2);
v_l_3657_ = lean_ctor_get(v_l_3641_, 3);
v_r_3658_ = lean_ctor_get(v_l_3641_, 4);
v_size_3659_ = lean_ctor_get(v_r_3642_, 0);
v___x_3660_ = lean_unsigned_to_nat(2u);
v___x_3661_ = lean_nat_mul(v___x_3660_, v_size_3659_);
v___x_3662_ = lean_nat_dec_lt(v_size_3654_, v___x_3661_);
lean_dec(v___x_3661_);
if (v___x_3662_ == 0)
{
lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3690_; 
lean_inc(v_r_3658_);
lean_inc(v_l_3657_);
lean_inc(v_v_3656_);
lean_inc(v_k_3655_);
v_isSharedCheck_3690_ = !lean_is_exclusive(v_l_3641_);
if (v_isSharedCheck_3690_ == 0)
{
lean_object* v_unused_3691_; lean_object* v_unused_3692_; lean_object* v_unused_3693_; lean_object* v_unused_3694_; lean_object* v_unused_3695_; 
v_unused_3691_ = lean_ctor_get(v_l_3641_, 4);
lean_dec(v_unused_3691_);
v_unused_3692_ = lean_ctor_get(v_l_3641_, 3);
lean_dec(v_unused_3692_);
v_unused_3693_ = lean_ctor_get(v_l_3641_, 2);
lean_dec(v_unused_3693_);
v_unused_3694_ = lean_ctor_get(v_l_3641_, 1);
lean_dec(v_unused_3694_);
v_unused_3695_ = lean_ctor_get(v_l_3641_, 0);
lean_dec(v_unused_3695_);
v___x_3664_ = v_l_3641_;
v_isShared_3665_ = v_isSharedCheck_3690_;
goto v_resetjp_3663_;
}
else
{
lean_dec(v_l_3641_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3690_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3680_; 
v___x_3666_ = lean_nat_add(v___x_3636_, v_size_3637_);
v___x_3667_ = lean_nat_add(v___x_3666_, v_size_3638_);
lean_dec(v_size_3638_);
if (lean_obj_tag(v_l_3657_) == 0)
{
lean_object* v_size_3688_; 
v_size_3688_ = lean_ctor_get(v_l_3657_, 0);
lean_inc(v_size_3688_);
v___y_3680_ = v_size_3688_;
goto v___jp_3679_;
}
else
{
lean_object* v___x_3689_; 
v___x_3689_ = lean_unsigned_to_nat(0u);
v___y_3680_ = v___x_3689_;
goto v___jp_3679_;
}
v___jp_3668_:
{
lean_object* v___x_3672_; lean_object* v___x_3674_; 
v___x_3672_ = lean_nat_add(v___y_3669_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec(v___y_3669_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 4, v_r_3642_);
lean_ctor_set(v___x_3664_, 3, v_r_3658_);
lean_ctor_set(v___x_3664_, 2, v_v_3640_);
lean_ctor_set(v___x_3664_, 1, v_k_3639_);
lean_ctor_set(v___x_3664_, 0, v___x_3672_);
v___x_3674_ = v___x_3664_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3672_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v_k_3639_);
lean_ctor_set(v_reuseFailAlloc_3678_, 2, v_v_3640_);
lean_ctor_set(v_reuseFailAlloc_3678_, 3, v_r_3658_);
lean_ctor_set(v_reuseFailAlloc_3678_, 4, v_r_3642_);
v___x_3674_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3676_; 
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 4, v___x_3674_);
lean_ctor_set(v___x_3652_, 3, v___y_3670_);
lean_ctor_set(v___x_3652_, 2, v_v_3656_);
lean_ctor_set(v___x_3652_, 1, v_k_3655_);
lean_ctor_set(v___x_3652_, 0, v___x_3667_);
v___x_3676_ = v___x_3652_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v_k_3655_);
lean_ctor_set(v_reuseFailAlloc_3677_, 2, v_v_3656_);
lean_ctor_set(v_reuseFailAlloc_3677_, 3, v___y_3670_);
lean_ctor_set(v_reuseFailAlloc_3677_, 4, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
v___jp_3679_:
{
lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3681_ = lean_nat_add(v___x_3666_, v___y_3680_);
lean_dec(v___y_3680_);
lean_dec(v___x_3666_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 4, v_l_3657_);
lean_ctor_set(v___x_3492_, 0, v___x_3681_);
v___x_3683_ = v___x_3492_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_k_3487_);
lean_ctor_set(v_reuseFailAlloc_3687_, 2, v_v_3488_);
lean_ctor_set(v_reuseFailAlloc_3687_, 3, v_l_3489_);
lean_ctor_set(v_reuseFailAlloc_3687_, 4, v_l_3657_);
v___x_3683_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
lean_object* v___x_3684_; 
v___x_3684_ = lean_nat_add(v___x_3636_, v_size_3659_);
if (lean_obj_tag(v_r_3658_) == 0)
{
lean_object* v_size_3685_; 
v_size_3685_ = lean_ctor_get(v_r_3658_, 0);
lean_inc(v_size_3685_);
v___y_3669_ = v___x_3684_;
v___y_3670_ = v___x_3683_;
v___y_3671_ = v_size_3685_;
goto v___jp_3668_;
}
else
{
lean_object* v___x_3686_; 
v___x_3686_ = lean_unsigned_to_nat(0u);
v___y_3669_ = v___x_3684_;
v___y_3670_ = v___x_3683_;
v___y_3671_ = v___x_3686_;
goto v___jp_3668_;
}
}
}
}
}
else
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3700_; 
lean_del_object(v___x_3492_);
v___x_3696_ = lean_nat_add(v___x_3636_, v_size_3637_);
v___x_3697_ = lean_nat_add(v___x_3696_, v_size_3638_);
lean_dec(v_size_3638_);
v___x_3698_ = lean_nat_add(v___x_3696_, v_size_3654_);
lean_dec(v___x_3696_);
lean_inc_ref(v_l_3489_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 4, v_l_3641_);
lean_ctor_set(v___x_3652_, 3, v_l_3489_);
lean_ctor_set(v___x_3652_, 2, v_v_3488_);
lean_ctor_set(v___x_3652_, 1, v_k_3487_);
lean_ctor_set(v___x_3652_, 0, v___x_3698_);
v___x_3700_ = v___x_3652_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_k_3487_);
lean_ctor_set(v_reuseFailAlloc_3713_, 2, v_v_3488_);
lean_ctor_set(v_reuseFailAlloc_3713_, 3, v_l_3489_);
lean_ctor_set(v_reuseFailAlloc_3713_, 4, v_l_3641_);
v___x_3700_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
v_isSharedCheck_3707_ = !lean_is_exclusive(v_l_3489_);
if (v_isSharedCheck_3707_ == 0)
{
lean_object* v_unused_3708_; lean_object* v_unused_3709_; lean_object* v_unused_3710_; lean_object* v_unused_3711_; lean_object* v_unused_3712_; 
v_unused_3708_ = lean_ctor_get(v_l_3489_, 4);
lean_dec(v_unused_3708_);
v_unused_3709_ = lean_ctor_get(v_l_3489_, 3);
lean_dec(v_unused_3709_);
v_unused_3710_ = lean_ctor_get(v_l_3489_, 2);
lean_dec(v_unused_3710_);
v_unused_3711_ = lean_ctor_get(v_l_3489_, 1);
lean_dec(v_unused_3711_);
v_unused_3712_ = lean_ctor_get(v_l_3489_, 0);
lean_dec(v_unused_3712_);
v___x_3702_ = v_l_3489_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_dec(v_l_3489_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 4, v_r_3642_);
lean_ctor_set(v___x_3702_, 3, v___x_3700_);
lean_ctor_set(v___x_3702_, 2, v_v_3640_);
lean_ctor_set(v___x_3702_, 1, v_k_3639_);
lean_ctor_set(v___x_3702_, 0, v___x_3697_);
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3697_);
lean_ctor_set(v_reuseFailAlloc_3706_, 1, v_k_3639_);
lean_ctor_set(v_reuseFailAlloc_3706_, 2, v_v_3640_);
lean_ctor_set(v_reuseFailAlloc_3706_, 3, v___x_3700_);
lean_ctor_set(v_reuseFailAlloc_3706_, 4, v_r_3642_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3720_; 
v_l_3720_ = lean_ctor_get(v_impl_3635_, 3);
lean_inc(v_l_3720_);
if (lean_obj_tag(v_l_3720_) == 0)
{
lean_object* v_r_3721_; lean_object* v_k_3722_; lean_object* v_v_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3746_; 
v_r_3721_ = lean_ctor_get(v_impl_3635_, 4);
v_k_3722_ = lean_ctor_get(v_impl_3635_, 1);
v_v_3723_ = lean_ctor_get(v_impl_3635_, 2);
v_isSharedCheck_3746_ = !lean_is_exclusive(v_impl_3635_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; lean_object* v_unused_3748_; 
v_unused_3747_ = lean_ctor_get(v_impl_3635_, 3);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_impl_3635_, 0);
lean_dec(v_unused_3748_);
v___x_3725_ = v_impl_3635_;
v_isShared_3726_ = v_isSharedCheck_3746_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_r_3721_);
lean_inc(v_v_3723_);
lean_inc(v_k_3722_);
lean_dec(v_impl_3635_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3746_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v_k_3727_; lean_object* v_v_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3742_; 
v_k_3727_ = lean_ctor_get(v_l_3720_, 1);
v_v_3728_ = lean_ctor_get(v_l_3720_, 2);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_l_3720_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; lean_object* v_unused_3744_; lean_object* v_unused_3745_; 
v_unused_3743_ = lean_ctor_get(v_l_3720_, 4);
lean_dec(v_unused_3743_);
v_unused_3744_ = lean_ctor_get(v_l_3720_, 3);
lean_dec(v_unused_3744_);
v_unused_3745_ = lean_ctor_get(v_l_3720_, 0);
lean_dec(v_unused_3745_);
v___x_3730_ = v_l_3720_;
v_isShared_3731_ = v_isSharedCheck_3742_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_v_3728_);
lean_inc(v_k_3727_);
lean_dec(v_l_3720_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3742_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3732_; lean_object* v___x_3734_; 
v___x_3732_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3721_, 2);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 4, v_r_3721_);
lean_ctor_set(v___x_3730_, 3, v_r_3721_);
lean_ctor_set(v___x_3730_, 2, v_v_3488_);
lean_ctor_set(v___x_3730_, 1, v_k_3487_);
lean_ctor_set(v___x_3730_, 0, v___x_3636_);
v___x_3734_ = v___x_3730_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3636_);
lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_k_3487_);
lean_ctor_set(v_reuseFailAlloc_3741_, 2, v_v_3488_);
lean_ctor_set(v_reuseFailAlloc_3741_, 3, v_r_3721_);
lean_ctor_set(v_reuseFailAlloc_3741_, 4, v_r_3721_);
v___x_3734_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
lean_object* v___x_3736_; 
lean_inc(v_r_3721_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 3, v_r_3721_);
lean_ctor_set(v___x_3725_, 0, v___x_3636_);
v___x_3736_ = v___x_3725_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3636_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_k_3722_);
lean_ctor_set(v_reuseFailAlloc_3740_, 2, v_v_3723_);
lean_ctor_set(v_reuseFailAlloc_3740_, 3, v_r_3721_);
lean_ctor_set(v_reuseFailAlloc_3740_, 4, v_r_3721_);
v___x_3736_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3738_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 4, v___x_3736_);
lean_ctor_set(v___x_3492_, 3, v___x_3734_);
lean_ctor_set(v___x_3492_, 2, v_v_3728_);
lean_ctor_set(v___x_3492_, 1, v_k_3727_);
lean_ctor_set(v___x_3492_, 0, v___x_3732_);
v___x_3738_ = v___x_3492_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3732_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v_k_3727_);
lean_ctor_set(v_reuseFailAlloc_3739_, 2, v_v_3728_);
lean_ctor_set(v_reuseFailAlloc_3739_, 3, v___x_3734_);
lean_ctor_set(v_reuseFailAlloc_3739_, 4, v___x_3736_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
}
}
else
{
lean_object* v_r_3749_; 
v_r_3749_ = lean_ctor_get(v_impl_3635_, 4);
lean_inc(v_r_3749_);
if (lean_obj_tag(v_r_3749_) == 0)
{
lean_object* v_k_3750_; lean_object* v_v_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3762_; 
v_k_3750_ = lean_ctor_get(v_impl_3635_, 1);
v_v_3751_ = lean_ctor_get(v_impl_3635_, 2);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_impl_3635_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; lean_object* v_unused_3764_; lean_object* v_unused_3765_; 
v_unused_3763_ = lean_ctor_get(v_impl_3635_, 4);
lean_dec(v_unused_3763_);
v_unused_3764_ = lean_ctor_get(v_impl_3635_, 3);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_impl_3635_, 0);
lean_dec(v_unused_3765_);
v___x_3753_ = v_impl_3635_;
v_isShared_3754_ = v_isSharedCheck_3762_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_v_3751_);
lean_inc(v_k_3750_);
lean_dec(v_impl_3635_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3762_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3755_; lean_object* v___x_3757_; 
v___x_3755_ = lean_unsigned_to_nat(3u);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 4, v_l_3720_);
lean_ctor_set(v___x_3753_, 2, v_v_3488_);
lean_ctor_set(v___x_3753_, 1, v_k_3487_);
lean_ctor_set(v___x_3753_, 0, v___x_3636_);
v___x_3757_ = v___x_3753_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3636_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v_k_3487_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v_v_3488_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v_l_3720_);
lean_ctor_set(v_reuseFailAlloc_3761_, 4, v_l_3720_);
v___x_3757_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
lean_object* v___x_3759_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 4, v_r_3749_);
lean_ctor_set(v___x_3492_, 3, v___x_3757_);
lean_ctor_set(v___x_3492_, 2, v_v_3751_);
lean_ctor_set(v___x_3492_, 1, v_k_3750_);
lean_ctor_set(v___x_3492_, 0, v___x_3755_);
v___x_3759_ = v___x_3492_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3755_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v_k_3750_);
lean_ctor_set(v_reuseFailAlloc_3760_, 2, v_v_3751_);
lean_ctor_set(v_reuseFailAlloc_3760_, 3, v___x_3757_);
lean_ctor_set(v_reuseFailAlloc_3760_, 4, v_r_3749_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
else
{
lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3766_ = lean_unsigned_to_nat(2u);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 4, v_impl_3635_);
lean_ctor_set(v___x_3492_, 3, v_r_3749_);
lean_ctor_set(v___x_3492_, 0, v___x_3766_);
v___x_3768_ = v___x_3492_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3766_);
lean_ctor_set(v_reuseFailAlloc_3769_, 1, v_k_3487_);
lean_ctor_set(v_reuseFailAlloc_3769_, 2, v_v_3488_);
lean_ctor_set(v_reuseFailAlloc_3769_, 3, v_r_3749_);
lean_ctor_set(v_reuseFailAlloc_3769_, 4, v_impl_3635_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
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
lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = lean_unsigned_to_nat(1u);
v___x_3772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
lean_ctor_set(v___x_3772_, 1, v_k_3483_);
lean_ctor_set(v___x_3772_, 2, v_v_3484_);
lean_ctor_set(v___x_3772_, 3, v_t_3485_);
lean_ctor_set(v___x_3772_, 4, v_t_3485_);
return v___x_3772_;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3773_ = lean_box(1);
v___x_3774_ = l_Lake_LeanLib_defaultFacetConfig;
v___x_3775_ = l_Lake_LeanLib_defaultFacet;
v___x_3776_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3775_, v___x_3774_, v___x_3773_);
return v___x_3776_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3777_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__0, &l_Lake_LeanLib_initFacetConfigs___closed__0_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__0);
v___x_3778_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig));
v___x_3779_ = l_Lake_LeanLib_modulesFacet;
v___x_3780_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3779_, v___x_3778_, v___x_3777_);
return v___x_3780_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3781_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__1, &l_Lake_LeanLib_initFacetConfigs___closed__1_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__1);
v___x_3782_ = l_Lake_LeanLib_leanArtsFacetConfig;
v___x_3783_ = l_Lake_LeanLib_leanArtsFacet;
v___x_3784_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3783_, v___x_3782_, v___x_3781_);
return v___x_3784_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3785_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__2, &l_Lake_LeanLib_initFacetConfigs___closed__2_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__2);
v___x_3786_ = l_Lake_LeanLib_staticFacetConfig;
v___x_3787_ = l_Lake_LeanLib_staticFacet;
v___x_3788_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3787_, v___x_3786_, v___x_3785_);
return v___x_3788_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3789_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__3, &l_Lake_LeanLib_initFacetConfigs___closed__3_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__3);
v___x_3790_ = l_Lake_LeanLib_staticExportFacetConfig;
v___x_3791_ = l_Lake_LeanLib_staticExportFacet;
v___x_3792_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3791_, v___x_3790_, v___x_3789_);
return v___x_3792_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3793_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__4, &l_Lake_LeanLib_initFacetConfigs___closed__4_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__4);
v___x_3794_ = l_Lake_LeanLib_sharedFacetConfig;
v___x_3795_ = l_Lake_LeanLib_sharedFacet;
v___x_3796_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3795_, v___x_3794_, v___x_3793_);
return v___x_3796_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3797_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__5, &l_Lake_LeanLib_initFacetConfigs___closed__5_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__5);
v___x_3798_ = l_Lake_LeanLib_extraDepFacetConfig;
v___x_3799_ = l_Lake_LeanLib_extraDepFacet;
v___x_3800_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3799_, v___x_3798_, v___x_3797_);
return v___x_3800_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_3801_; 
v___x_3801_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__6, &l_Lake_LeanLib_initFacetConfigs___closed__6_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__6);
return v___x_3801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3802_, lean_object* v_k_3803_, lean_object* v_v_3804_, lean_object* v_t_3805_, lean_object* v_hl_3806_){
_start:
{
lean_object* v___x_3807_; 
v___x_3807_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3803_, v_v_3804_, v_t_3805_);
return v___x_3807_;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs(void){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lake_LeanLib_initFacetConfigs;
return v___x_3808_;
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
