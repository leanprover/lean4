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
lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_219_; 
lean_inc_ref(v_modSet_156_);
lean_inc_ref(v_mods_155_);
v_isSharedCheck_219_ = !lean_is_exclusive(v_col_142_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; lean_object* v_unused_221_; 
v_unused_220_ = lean_ctor_get(v_col_142_, 1);
lean_dec(v_unused_220_);
v_unused_221_ = lean_ctor_get(v_col_142_, 0);
lean_dec(v_unused_221_);
v___x_160_ = v_col_142_;
v_isShared_161_ = v_isSharedCheck_219_;
goto v_resetjp_159_;
}
else
{
lean_dec(v_col_142_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_219_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_lib_162_; lean_object* v_pkg_163_; lean_object* v_name_164_; lean_object* v_keyName_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v_col_170_; 
v_lib_162_ = lean_ctor_get(v_root_141_, 0);
v_pkg_163_ = lean_ctor_get(v_lib_162_, 0);
v_name_164_ = lean_ctor_get(v_root_141_, 1);
v_keyName_165_ = lean_ctor_get(v_pkg_163_, 2);
v___x_166_ = 1;
v___x_167_ = lean_box(0);
lean_inc_ref(v_root_141_);
v___x_168_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_modSet_156_, v_root_141_, v___x_167_);
lean_inc_ref(v___x_168_);
lean_inc_ref(v_mods_155_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_168_);
v_col_170_ = v___x_160_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_mods_155_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_168_);
lean_ctor_set_uint8(v_reuseFailAlloc_218_, sizeof(void*)*2, v_hasErrors_157_);
v_col_170_ = v_reuseFailAlloc_218_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_171_ = l_Lake_Module_importsFacet;
lean_inc(v_name_164_);
lean_inc(v_keyName_165_);
v___x_172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_172_, 0, v_keyName_165_);
lean_ctor_set(v___x_172_, 1, v_name_164_);
v___x_173_ = l_Lake_Module_keyword;
lean_inc_ref(v_root_141_);
v___x_174_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_174_, 0, v___x_172_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
lean_ctor_set(v___x_174_, 2, v_root_141_);
lean_ctor_set(v___x_174_, 3, v___x_171_);
lean_inc_ref(v_a_144_);
lean_inc_ref(v_a_148_);
lean_inc(v_a_147_);
lean_inc(v_a_146_);
lean_inc(v_a_145_);
v___x_175_ = lean_apply_7(v_a_144_, v___x_174_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, lean_box(0));
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_208_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_a_177_ = lean_ctor_get(v___x_175_, 1);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_208_ == 0)
{
v___x_179_ = v___x_175_;
v_isShared_180_ = v_isSharedCheck_208_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_208_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v_task_181_; lean_object* v___x_182_; lean_object* v___y_184_; 
v_task_181_ = lean_ctor_get(v_a_176_, 0);
lean_inc_ref(v_task_181_);
lean_dec(v_a_176_);
v___x_182_ = lean_io_wait(v_task_181_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_188_; size_t v_sz_189_; size_t v___x_190_; lean_object* v___x_191_; 
lean_del_object(v___x_179_);
lean_dec_ref(v___x_168_);
lean_dec_ref(v_mods_155_);
v_a_188_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_182_, 2);
v_sz_189_ = lean_array_size(v_a_188_);
v___x_190_ = ((size_t)0ULL);
v___x_191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_140_, v_a_188_, v_sz_189_, v___x_190_, v_col_170_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_177_);
lean_dec(v_a_188_);
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
v___x_200_ = lean_array_push(v_mods_194_, v_root_141_);
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
v_col_152_ = v___x_202_;
v___y_153_ = v_a_193_;
goto v___jp_151_;
}
}
}
else
{
lean_dec_ref(v_root_141_);
return v___x_191_;
}
}
else
{
lean_dec_ref_known(v___x_182_, 2);
lean_dec_ref(v_col_170_);
lean_dec_ref(v_a_144_);
if (v_viaImport_143_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_array_push(v_mods_155_, v_root_141_);
v___x_206_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___x_168_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*2, v___x_166_);
v___y_184_ = v___x_206_;
goto v___jp_183_;
}
else
{
lean_object* v___x_207_; 
lean_dec_ref(v_root_141_);
v___x_207_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_207_, 0, v_mods_155_);
lean_ctor_set(v___x_207_, 1, v___x_168_);
lean_ctor_set_uint8(v___x_207_, sizeof(void*)*2, v___x_166_);
v___y_184_ = v___x_207_;
goto v___jp_183_;
}
}
v___jp_183_:
{
lean_object* v___x_186_; 
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___y_184_);
v___x_186_ = v___x_179_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___y_184_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v_a_177_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
else
{
lean_object* v_a_209_; lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec_ref(v_col_170_);
lean_dec_ref(v___x_168_);
lean_dec_ref(v_mods_155_);
lean_dec_ref(v_a_144_);
lean_dec_ref(v_root_141_);
v_a_209_ = lean_ctor_get(v___x_175_, 0);
v_a_210_ = lean_ctor_get(v___x_175_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_175_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_inc(v_a_209_);
lean_dec(v___x_175_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_209_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(lean_object* v_self_222_, lean_object* v_as_223_, size_t v_sz_224_, size_t v_i_225_, lean_object* v_b_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_a_235_; lean_object* v_a_236_; uint8_t v___x_240_; 
v___x_240_ = lean_usize_dec_lt(v_i_225_, v_sz_224_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
lean_dec_ref(v___y_227_);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_b_226_);
lean_ctor_set(v___x_241_, 1, v___y_232_);
return v___x_241_;
}
else
{
lean_object* v_a_242_; lean_object* v_lib_243_; lean_object* v_name_244_; lean_object* v_name_245_; uint8_t v___x_246_; 
v_a_242_ = lean_array_uget_borrowed(v_as_223_, v_i_225_);
v_lib_243_ = lean_ctor_get(v_a_242_, 0);
v_name_244_ = lean_ctor_get(v_lib_243_, 1);
v_name_245_ = lean_ctor_get(v_self_222_, 1);
v___x_246_ = lean_name_eq(v_name_244_, v_name_245_);
if (v___x_246_ == 0)
{
v_a_235_ = v_b_226_;
v_a_236_ = v___y_232_;
goto v___jp_234_;
}
else
{
lean_object* v___x_247_; 
lean_inc_ref(v___y_227_);
lean_inc(v_a_242_);
v___x_247_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_222_, v_a_242_, v_b_226_, v___x_246_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
if (lean_obj_tag(v___x_247_) == 0)
{
lean_object* v_a_248_; lean_object* v_a_249_; 
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
v_a_249_ = lean_ctor_get(v___x_247_, 1);
lean_inc(v_a_249_);
lean_dec_ref_known(v___x_247_, 2);
v_a_235_ = v_a_248_;
v_a_236_ = v_a_249_;
goto v___jp_234_;
}
else
{
lean_dec_ref(v___y_227_);
return v___x_247_;
}
}
}
v___jp_234_:
{
size_t v___x_237_; size_t v___x_238_; 
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_add(v_i_225_, v___x_237_);
v_i_225_ = v___x_238_;
v_b_226_ = v_a_235_;
v___y_232_ = v_a_236_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2___boxed(lean_object* v_self_250_, lean_object* v_as_251_, lean_object* v_sz_252_, lean_object* v_i_253_, lean_object* v_b_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
size_t v_sz_boxed_262_; size_t v_i_boxed_263_; lean_object* v_res_264_; 
v_sz_boxed_262_ = lean_unbox_usize(v_sz_252_);
lean_dec(v_sz_252_);
v_i_boxed_263_ = lean_unbox_usize(v_i_253_);
lean_dec(v_i_253_);
v_res_264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__2(v_self_250_, v_as_251_, v_sz_boxed_262_, v_i_boxed_263_, v_b_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v_as_251_);
lean_dec_ref(v_self_250_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go___boxed(lean_object* v_self_265_, lean_object* v_root_266_, lean_object* v_col_267_, lean_object* v_viaImport_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
uint8_t v_viaImport_boxed_276_; lean_object* v_res_277_; 
v_viaImport_boxed_276_ = lean_unbox(v_viaImport_268_);
v_res_277_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_265_, v_root_266_, v_col_267_, v_viaImport_boxed_276_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_self_265_);
return v_res_277_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(lean_object* v_00_u03b2_278_, lean_object* v_m_279_, lean_object* v_a_280_){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_m_279_, v_a_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___boxed(lean_object* v_00_u03b2_282_, lean_object* v_m_283_, lean_object* v_a_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0(v_00_u03b2_282_, v_m_283_, v_a_284_);
lean_dec_ref(v_a_284_);
lean_dec_ref(v_m_283_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1(lean_object* v_00_u03b2_287_, lean_object* v_m_288_, lean_object* v_a_289_, lean_object* v_b_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_m_288_, v_a_289_, v_b_290_);
return v___x_291_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(lean_object* v_00_u03b2_292_, lean_object* v_a_293_, lean_object* v_x_294_){
_start:
{
uint8_t v___x_295_; 
v___x_295_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___redArg(v_a_293_, v_x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_296_, lean_object* v_a_297_, lean_object* v_x_298_){
_start:
{
uint8_t v_res_299_; lean_object* v_r_300_; 
v_res_299_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0_spec__0(v_00_u03b2_296_, v_a_297_, v_x_298_);
lean_dec(v_x_298_);
lean_dec_ref(v_a_297_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2(lean_object* v_00_u03b2_301_, lean_object* v_data_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2___redArg(v_data_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_304_, lean_object* v_i_305_, lean_object* v_source_306_, lean_object* v_target_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3___redArg(v_i_305_, v_source_306_, v_target_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_309_, lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1_spec__2_spec__3_spec__5___redArg(v_x_310_, v_x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(lean_object* v_self_313_, lean_object* v_as_314_, size_t v_sz_315_, size_t v_i_316_, lean_object* v_b_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = lean_usize_dec_lt(v_i_316_, v_sz_315_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec_ref(v___y_318_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v_b_317_);
lean_ctor_set(v___x_326_, 1, v___y_323_);
return v___x_326_;
}
else
{
uint8_t v___x_327_; lean_object* v_a_328_; lean_object* v___x_329_; 
v___x_327_ = 0;
v_a_328_ = lean_array_uget_borrowed(v_as_314_, v_i_316_);
lean_inc_ref(v___y_318_);
lean_inc(v_a_328_);
v___x_329_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go(v_self_313_, v_a_328_, v_b_317_, v___x_327_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v_a_331_; size_t v___x_332_; size_t v___x_333_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
v_a_331_ = lean_ctor_get(v___x_329_, 1);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_329_, 2);
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_316_, v___x_332_);
v_i_316_ = v___x_333_;
v_b_317_ = v_a_330_;
v___y_323_ = v_a_331_;
goto _start;
}
else
{
lean_dec_ref(v___y_318_);
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0___boxed(lean_object* v_self_335_, lean_object* v_as_336_, lean_object* v_sz_337_, lean_object* v_i_338_, lean_object* v_b_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
size_t v_sz_boxed_347_; size_t v_i_boxed_348_; lean_object* v_res_349_; 
v_sz_boxed_347_ = lean_unbox_usize(v_sz_337_);
lean_dec(v_sz_337_);
v_i_boxed_348_ = lean_unbox_usize(v_i_338_);
lean_dec(v_i_338_);
v_res_349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_335_, v_as_336_, v_sz_boxed_347_, v_i_boxed_348_, v_b_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v_as_336_);
lean_dec_ref(v_self_335_);
return v_res_349_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__1));
v___x_353_ = l_Lake_BuildTrace_nil(v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(lean_object* v_self_355_, lean_object* v_col_356_, lean_object* v___x_357_, uint8_t v___x_358_, lean_object* v___x_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v___x_367_; 
lean_inc_ref(v_self_355_);
v___x_367_ = l_Lake_LeanLib_getModuleArray(v_self_355_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; size_t v_sz_369_; size_t v___x_370_; lean_object* v___x_371_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
v_sz_369_ = lean_array_size(v_a_368_);
v___x_370_ = ((size_t)0ULL);
v___x_371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_spec__0(v_self_355_, v_a_368_, v_sz_369_, v___x_370_, v_col_356_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_);
lean_dec(v_a_368_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_399_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_a_373_ = lean_ctor_get(v___x_371_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_399_ == 0)
{
v___x_375_ = v___x_371_;
v_isShared_376_ = v_isSharedCheck_399_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_399_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v_mods_377_; uint8_t v_hasErrors_378_; lean_object* v___y_380_; 
v_mods_377_ = lean_ctor_get(v_a_372_, 0);
lean_inc_ref(v_mods_377_);
v_hasErrors_378_ = lean_ctor_get_uint8(v_a_372_, sizeof(void*)*2);
lean_dec(v_a_372_);
if (v_hasErrors_378_ == 0)
{
lean_dec_ref(v_self_355_);
v___y_380_ = v_a_373_;
goto v___jp_379_;
}
else
{
lean_object* v_name_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_name_392_ = lean_ctor_get(v_self_355_, 1);
lean_inc(v_name_392_);
lean_dec_ref(v_self_355_);
v___x_393_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_392_, v_hasErrors_378_);
v___x_394_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__3));
v___x_395_ = lean_string_append(v___x_393_, v___x_394_);
v___x_396_ = 3;
v___x_397_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*1, v___x_396_);
v___x_398_ = lean_array_push(v_a_373_, v___x_397_);
v___y_380_ = v___x_398_;
goto v___jp_379_;
}
v___jp_379_:
{
lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_381_ = lean_mk_empty_array_with_capacity(v___x_357_);
v___x_382_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_383_ = 0;
v___x_384_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_385_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_385_, 0, v___x_381_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
lean_ctor_set(v___x_385_, 2, v___x_357_);
lean_ctor_set_uint8(v___x_385_, sizeof(void*)*3, v___x_383_);
lean_ctor_set_uint8(v___x_385_, sizeof(void*)*3 + 1, v___x_358_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 1, v___x_385_);
lean_ctor_set(v___x_375_, 0, v_mods_377_);
v___x_387_ = v___x_375_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_mods_377_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v___x_385_);
v___x_387_ = v_reuseFailAlloc_391_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = lean_task_pure(v___x_387_);
v___x_389_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_359_);
lean_ctor_set(v___x_389_, 2, v___x_382_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*3, v___x_358_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___y_380_);
return v___x_390_;
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec(v___x_359_);
lean_dec(v___x_357_);
lean_dec_ref(v_self_355_);
v_a_400_ = lean_ctor_get(v___x_371_, 0);
v_a_401_ = lean_ctor_get(v___x_371_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_371_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_inc(v_a_400_);
lean_dec(v___x_371_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_400_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_410_; uint8_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec_ref(v___y_360_);
lean_dec(v___x_359_);
lean_dec(v___x_357_);
lean_dec_ref(v_col_356_);
lean_dec_ref(v_self_355_);
v_a_409_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_409_);
lean_dec_ref_known(v___x_367_, 1);
v___x_410_ = lean_io_error_to_string(v_a_409_);
v___x_411_ = 3;
v___x_412_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*1, v___x_411_);
v___x_413_ = lean_array_get_size(v___y_365_);
v___x_414_ = lean_array_push(v___y_365_, v___x_412_);
v___x_415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_413_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed(lean_object* v_self_416_, lean_object* v_col_417_, lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v___x_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
uint8_t v___x_7362__boxed_428_; lean_object* v_res_429_; 
v___x_7362__boxed_428_ = lean_unbox(v___x_419_);
v_res_429_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0(v_self_416_, v_col_417_, v___x_418_, v___x_7362__boxed_428_, v___x_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec(v___y_423_);
lean_dec(v___y_422_);
return v_res_429_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_box(0);
v___x_433_ = lean_unsigned_to_nat(16u);
v___x_434_ = lean_mk_array(v___x_433_, v___x_432_);
return v___x_434_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__1);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_435_);
return v___x_437_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3(void){
_start:
{
uint8_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_col_441_; 
v___x_438_ = 0;
v___x_439_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_440_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__0));
v_col_441_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_col_441_, 0, v___x_440_);
lean_ctor_set(v_col_441_, 1, v___x_439_);
lean_ctor_set_uint8(v_col_441_, sizeof(void*)*2, v___x_438_);
return v_col_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(lean_object* v_self_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; lean_object* v_col_453_; lean_object* v___x_454_; lean_object* v___f_455_; lean_object* v___x_456_; 
v___x_450_ = lean_box(0);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = 0;
v_col_453_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__3);
v___x_454_ = lean_box(v___x_452_);
v___f_455_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___boxed), 12, 5);
lean_closure_set(v___f_455_, 0, v_self_442_);
lean_closure_set(v___f_455_, 1, v_col_453_);
lean_closure_set(v___f_455_, 2, v___x_451_);
lean_closure_set(v___f_455_, 3, v___x_454_);
lean_closure_set(v___f_455_, 4, v___x_450_);
v___x_456_ = l_Lake_ensureJob___redArg(v___x_450_, v___f_455_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___boxed(lean_object* v_self_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules(v_self_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec(v_a_460_);
lean_dec(v_a_459_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(lean_object* v_as_467_, size_t v_i_468_, size_t v_stop_469_, lean_object* v_b_470_){
_start:
{
uint8_t v___x_471_; 
v___x_471_ = lean_usize_dec_eq(v_i_468_, v_stop_469_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v_name_473_; uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; size_t v___x_479_; size_t v___x_480_; 
v___x_472_ = lean_array_uget_borrowed(v_as_467_, v_i_468_);
v_name_473_ = lean_ctor_get(v___x_472_, 1);
v___x_474_ = 1;
lean_inc(v_name_473_);
v___x_475_ = l_Lean_Name_toString(v_name_473_, v___x_474_);
v___x_476_ = lean_string_append(v_b_470_, v___x_475_);
lean_dec_ref(v___x_475_);
v___x_477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_478_ = lean_string_append(v___x_476_, v___x_477_);
v___x_479_ = ((size_t)1ULL);
v___x_480_ = lean_usize_add(v_i_468_, v___x_479_);
v_i_468_ = v___x_480_;
v_b_470_ = v___x_478_;
goto _start;
}
else
{
return v_b_470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_482_, lean_object* v_i_483_, lean_object* v_stop_484_, lean_object* v_b_485_){
_start:
{
size_t v_i_boxed_486_; size_t v_stop_boxed_487_; lean_object* v_res_488_; 
v_i_boxed_486_ = lean_unbox_usize(v_i_483_);
lean_dec(v_i_483_);
v_stop_boxed_487_ = lean_unbox_usize(v_stop_484_);
lean_dec(v_stop_484_);
v_res_488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_as_482_, v_i_boxed_486_, v_stop_boxed_487_, v_b_485_);
lean_dec_ref(v_as_482_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(size_t v_sz_489_, size_t v_i_490_, lean_object* v_bs_491_){
_start:
{
uint8_t v___x_492_; 
v___x_492_ = lean_usize_dec_lt(v_i_490_, v_sz_489_);
if (v___x_492_ == 0)
{
return v_bs_491_;
}
else
{
lean_object* v_v_493_; lean_object* v_name_494_; lean_object* v___x_495_; lean_object* v_bs_x27_496_; lean_object* v___x_497_; lean_object* v___x_498_; size_t v___x_499_; size_t v___x_500_; lean_object* v___x_501_; 
v_v_493_ = lean_array_uget_borrowed(v_bs_491_, v_i_490_);
v_name_494_ = lean_ctor_get(v_v_493_, 1);
lean_inc(v_name_494_);
v___x_495_ = lean_unsigned_to_nat(0u);
v_bs_x27_496_ = lean_array_uset(v_bs_491_, v_i_490_, v___x_495_);
v___x_497_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_494_, v___x_492_);
v___x_498_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_490_, v___x_499_);
v___x_501_ = lean_array_uset(v_bs_x27_496_, v_i_490_, v___x_498_);
v_i_490_ = v___x_500_;
v_bs_491_ = v___x_501_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_503_, lean_object* v_i_504_, lean_object* v_bs_505_){
_start:
{
size_t v_sz_boxed_506_; size_t v_i_boxed_507_; lean_object* v_res_508_; 
v_sz_boxed_506_ = lean_unbox_usize(v_sz_503_);
lean_dec(v_sz_503_);
v_i_boxed_507_ = lean_unbox_usize(v_i_504_);
lean_dec(v_i_504_);
v_res_508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_506_, v_i_boxed_507_, v_bs_505_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(lean_object* v_a_509_){
_start:
{
size_t v_sz_510_; size_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_sz_510_ = lean_array_size(v_a_509_);
v___x_511_ = ((size_t)0ULL);
v___x_512_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1_spec__2(v_sz_510_, v___x_511_, v_a_509_);
v___x_513_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(uint8_t v_fmt_514_, lean_object* v_a_515_){
_start:
{
lean_object* v___y_517_; 
if (v_fmt_514_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_524_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_525_ = lean_unsigned_to_nat(0u);
v___x_526_ = lean_array_get_size(v_a_515_);
v___x_527_ = lean_nat_dec_lt(v___x_525_, v___x_526_);
if (v___x_527_ == 0)
{
lean_dec_ref(v_a_515_);
v___y_517_ = v___x_524_;
goto v___jp_516_;
}
else
{
size_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; 
v___x_528_ = ((size_t)0ULL);
v___x_529_ = lean_usize_of_nat(v___x_526_);
v___x_530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0(v_a_515_, v___x_528_, v___x_529_, v___x_524_);
lean_dec_ref(v_a_515_);
v___y_517_ = v___x_530_;
goto v___jp_516_;
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = l_Lean_Array_toJson___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__1(v_a_515_);
v___x_532_ = l_Lean_Json_compress(v___x_531_);
return v___x_532_;
}
v___jp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = lean_string_utf8_byte_size(v___y_517_);
lean_inc_ref(v___y_517_);
v___x_521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_521_, 0, v___y_517_);
lean_ctor_set(v___x_521_, 1, v___x_519_);
lean_ctor_set(v___x_521_, 2, v___x_520_);
v___x_522_ = l_String_Slice_Pos_prevn(v___x_521_, v___x_520_, v___x_518_);
lean_dec_ref_known(v___x_521_, 3);
v___x_523_ = lean_string_utf8_extract_fast(v___y_517_, v___x_519_, v___x_522_);
lean_dec(v___x_522_);
lean_dec_ref(v___y_517_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0___boxed(lean_object* v_fmt_533_, lean_object* v_a_534_){
_start:
{
uint8_t v_fmt_boxed_535_; lean_object* v_res_536_; 
v_fmt_boxed_535_ = lean_unbox(v_fmt_533_);
v_res_536_ = l_Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0(v_fmt_boxed_535_, v_a_534_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(lean_object* v_as_550_, size_t v_i_551_, size_t v_stop_552_, lean_object* v_b_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
uint8_t v___x_561_; 
v___x_561_ = lean_usize_dec_eq(v_i_551_, v_stop_552_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v_lib_563_; lean_object* v_pkg_564_; lean_object* v_name_565_; lean_object* v_keyName_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_562_ = lean_array_uget_borrowed(v_as_550_, v_i_551_);
v_lib_563_ = lean_ctor_get(v___x_562_, 0);
v_pkg_564_ = lean_ctor_get(v_lib_563_, 0);
v_name_565_ = lean_ctor_get(v___x_562_, 1);
v_keyName_566_ = lean_ctor_get(v_pkg_564_, 2);
v___x_567_ = l_Lake_Module_leanArtsFacet;
lean_inc(v_name_565_);
lean_inc(v_keyName_566_);
v___x_568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_568_, 0, v_keyName_566_);
lean_ctor_set(v___x_568_, 1, v_name_565_);
v___x_569_ = l_Lake_Module_keyword;
lean_inc(v___x_562_);
v___x_570_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
lean_ctor_set(v___x_570_, 2, v___x_562_);
lean_ctor_set(v___x_570_, 3, v___x_567_);
lean_inc_ref(v___y_554_);
lean_inc_ref(v___y_558_);
lean_inc(v___y_557_);
lean_inc(v___y_556_);
lean_inc(v___y_555_);
v___x_571_ = lean_apply_7(v___y_554_, v___x_570_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, lean_box(0));
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v_a_573_; lean_object* v___x_574_; size_t v___x_575_; size_t v___x_576_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
v_a_573_ = lean_ctor_get(v___x_571_, 1);
lean_inc(v_a_573_);
lean_dec_ref_known(v___x_571_, 2);
v___x_574_ = l_Lake_Job_mix___redArg(v_b_553_, v_a_572_);
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_add(v_i_551_, v___x_575_);
v_i_551_ = v___x_576_;
v_b_553_ = v___x_574_;
v___y_559_ = v_a_573_;
goto _start;
}
else
{
lean_object* v_a_578_; lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v___y_554_);
lean_dec_ref(v_b_553_);
v_a_578_ = lean_ctor_get(v___x_571_, 0);
v_a_579_ = lean_ctor_get(v___x_571_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_571_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_inc(v_a_578_);
lean_dec(v___x_571_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_578_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
else
{
lean_object* v___x_587_; 
lean_dec_ref(v___y_554_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v_b_553_);
lean_ctor_set(v___x_587_, 1, v___y_559_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0___boxed(lean_object* v_as_588_, lean_object* v_i_589_, lean_object* v_stop_590_, lean_object* v_b_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
size_t v_i_boxed_599_; size_t v_stop_boxed_600_; lean_object* v_res_601_; 
v_i_boxed_599_ = lean_unbox_usize(v_i_589_);
lean_dec(v_i_589_);
v_stop_boxed_600_ = lean_unbox_usize(v_stop_590_);
lean_dec(v_stop_590_);
v_res_601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_as_588_, v_i_boxed_599_, v_stop_boxed_600_, v_b_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v_as_588_);
return v_res_601_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; uint8_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_606_ = 0;
v___x_607_ = 0;
v___x_608_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v___x_609_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set(v___x_609_, 1, v___x_605_);
lean_ctor_set(v___x_609_, 2, v___x_604_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*3, v___x_607_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*3 + 1, v___x_606_);
return v___x_609_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__1);
v___x_611_ = lean_box(0);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_610_);
return v___x_612_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__2);
v___x_614_ = lean_task_pure(v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4(void){
_start:
{
uint8_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_615_ = 0;
v___x_616_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___x_617_ = lean_box(0);
v___x_618_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__3);
v___x_619_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v___x_617_);
lean_ctor_set(v___x_619_, 2, v___x_616_);
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3, v___x_615_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(lean_object* v_self_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_pkg_628_; lean_object* v_name_629_; lean_object* v_keyName_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_pkg_628_ = lean_ctor_get(v_self_620_, 0);
v_name_629_ = lean_ctor_get(v_self_620_, 1);
v_keyName_630_ = lean_ctor_get(v_pkg_628_, 2);
v___x_631_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_name_629_);
lean_inc(v_keyName_630_);
v___x_632_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_632_, 0, v_keyName_630_);
lean_ctor_set(v___x_632_, 1, v_name_629_);
v___x_633_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_634_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
lean_ctor_set(v___x_634_, 2, v_self_620_);
lean_ctor_set(v___x_634_, 3, v___x_631_);
lean_inc_ref(v_a_621_);
lean_inc_ref(v_a_625_);
lean_inc(v_a_624_);
lean_inc(v_a_623_);
lean_inc(v_a_622_);
v___x_635_ = lean_apply_7(v_a_621_, v___x_634_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, lean_box(0));
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v_a_637_; lean_object* v___x_638_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
v_a_637_ = lean_ctor_get(v___x_635_, 1);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_635_, 2);
v___x_638_ = l_Lake_Job_await___redArg(v_a_636_, v_a_637_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_661_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_a_640_ = lean_ctor_get(v___x_638_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_661_ == 0)
{
v___x_642_ = v___x_638_;
v_isShared_643_ = v_isSharedCheck_661_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_661_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__4);
v___x_646_ = lean_array_get_size(v_a_639_);
v___x_647_ = lean_nat_dec_lt(v___x_644_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_649_; 
lean_dec(v_a_639_);
lean_dec_ref(v_a_621_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_645_);
v___x_649_ = v___x_642_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_a_640_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
else
{
uint8_t v___x_651_; 
v___x_651_ = lean_nat_dec_le(v___x_646_, v___x_646_);
if (v___x_651_ == 0)
{
if (v___x_647_ == 0)
{
lean_object* v___x_653_; 
lean_dec(v_a_639_);
lean_dec_ref(v_a_621_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_645_);
v___x_653_ = v___x_642_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_a_640_);
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
size_t v___x_655_; size_t v___x_656_; lean_object* v___x_657_; 
lean_del_object(v___x_642_);
v___x_655_ = ((size_t)0ULL);
v___x_656_ = lean_usize_of_nat(v___x_646_);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_639_, v___x_655_, v___x_656_, v___x_645_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_640_);
lean_dec(v_a_639_);
return v___x_657_;
}
}
else
{
size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; 
lean_del_object(v___x_642_);
v___x_658_ = ((size_t)0ULL);
v___x_659_ = lean_usize_of_nat(v___x_646_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean_spec__0(v_a_639_, v___x_658_, v___x_659_, v___x_645_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_640_);
lean_dec(v_a_639_);
return v___x_660_;
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec_ref(v_a_621_);
v_a_662_ = lean_ctor_get(v___x_638_, 0);
v_a_663_ = lean_ctor_get(v___x_638_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_638_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_inc(v_a_662_);
lean_dec(v___x_638_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_662_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
lean_dec_ref(v_a_621_);
v_a_671_ = lean_ctor_get(v___x_635_, 0);
v_a_672_ = lean_ctor_get(v___x_635_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_635_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_inc(v_a_671_);
lean_dec(v___x_635_);
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
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___boxed(lean_object* v_self_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean(v_self_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec(v_a_683_);
lean_dec(v_a_682_);
return v_res_688_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_box(0);
v___x_690_ = l_Lean_Json_compress(v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(uint8_t v_fmt_691_){
_start:
{
if (v_fmt_691_ == 0)
{
lean_object* v___x_692_; 
v___x_692_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
return v___x_692_;
}
else
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___closed__0);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_694_){
_start:
{
uint8_t v_fmt_boxed_695_; lean_object* v_res_696_; 
v_fmt_boxed_695_ = lean_unbox(v_fmt_694_);
v_res_696_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_boxed_695_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(uint8_t v_fmt_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v_fmt_697_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___boxed(lean_object* v_fmt_700_, lean_object* v_a_701_){
_start:
{
uint8_t v_fmt_boxed_702_; lean_object* v_res_703_; 
v_fmt_boxed_702_ = lean_unbox(v_fmt_700_);
v_res_703_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0(v_fmt_boxed_702_, v_a_701_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0(uint8_t v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Lake_formatQuery___at___00Lake_LeanLib_leanArtsFacetConfig_spec__0___redArg(v___y_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_leanArtsFacetConfig___lam__0___boxed(lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
uint8_t v___y_68__boxed_709_; lean_object* v_res_710_; 
v___y_68__boxed_709_ = lean_unbox(v___y_707_);
v_res_710_ = l_Lake_LeanLib_leanArtsFacetConfig___lam__0(v___y_68__boxed_709_, v___y_708_);
return v_res_710_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v___f_713_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_714_ = 1;
v___x_715_ = l_Lake_instDataKindUnit;
v___x_716_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__1));
v___x_717_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_718_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v___x_716_);
lean_ctor_set(v___x_718_, 2, v___x_715_);
lean_ctor_set(v___x_718_, 3, v___f_713_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*4, v___x_714_);
lean_ctor_set_uint8(v___x_718_, sizeof(void*)*4 + 1, v___x_714_);
return v___x_718_;
}
}
static lean_object* _init_l_Lake_LeanLib_leanArtsFacetConfig(void){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_obj_once(&l_Lake_LeanLib_leanArtsFacetConfig___closed__2, &l_Lake_LeanLib_leanArtsFacetConfig___closed__2_once, _init_l_Lake_LeanLib_leanArtsFacetConfig___closed__2);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(lean_object* v_a_720_, lean_object* v_x_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lake_ModuleFacet_fetch___redArg(v_x_721_, v_a_720_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed(lean_object* v_a_730_, lean_object* v_x_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0(v_a_730_, v_x_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec(v___y_734_);
lean_dec(v___y_733_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(uint8_t v_shouldExport_740_, lean_object* v___x_741_, lean_object* v_bs_742_, lean_object* v_a_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_lib_751_; lean_object* v_config_752_; lean_object* v_nativeFacets_753_; lean_object* v___f_754_; lean_object* v___x_755_; lean_object* v___x_756_; size_t v_sz_757_; size_t v___x_758_; lean_object* v___x_187465__overap_759_; lean_object* v___x_760_; 
v_lib_751_ = lean_ctor_get(v_a_743_, 0);
v_config_752_ = lean_ctor_get(v_lib_751_, 2);
v_nativeFacets_753_ = lean_ctor_get(v_config_752_, 8);
lean_inc_ref(v_nativeFacets_753_);
v___f_754_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__0___boxed), 9, 1);
lean_closure_set(v___f_754_, 0, v_a_743_);
v___x_755_ = lean_box(v_shouldExport_740_);
v___x_756_ = lean_apply_1(v_nativeFacets_753_, v___x_755_);
v_sz_757_ = lean_array_size(v___x_756_);
v___x_758_ = ((size_t)0ULL);
v___x_187465__overap_759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_741_, v___f_754_, v_sz_757_, v___x_758_, v___x_756_);
lean_inc_ref(v___y_748_);
lean_inc(v___y_747_);
lean_inc(v___y_746_);
lean_inc(v___y_745_);
v___x_760_ = lean_apply_7(v___x_187465__overap_759_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, lean_box(0));
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_770_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_a_762_ = lean_ctor_get(v___x_760_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_770_ == 0)
{
v___x_764_ = v___x_760_;
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_770_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = l_Array_append___redArg(v_bs_742_, v_a_761_);
lean_dec(v_a_761_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_766_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_a_762_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
else
{
lean_dec_ref(v_bs_742_);
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed(lean_object* v_shouldExport_771_, lean_object* v___x_772_, lean_object* v_bs_773_, lean_object* v_a_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
uint8_t v_shouldExport_boxed_782_; lean_object* v_res_783_; 
v_shouldExport_boxed_782_ = lean_unbox(v_shouldExport_771_);
v_res_783_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1(v_shouldExport_boxed_782_, v___x_772_, v_bs_773_, v_a_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec(v___y_777_);
lean_dec(v___y_776_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(lean_object* v___x_784_, lean_object* v_pkg_785_, lean_object* v_x_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lake_Target_fetchIn___redArg(v___x_784_, v_pkg_785_, v_x_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed(lean_object* v___x_795_, lean_object* v_pkg_796_, lean_object* v_x_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2(v___x_795_, v_pkg_796_, v_x_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec(v___y_800_);
lean_dec(v___y_799_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(lean_object* v_a_806_, lean_object* v_x_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_log_816_; uint8_t v_action_817_; uint8_t v_wantsRebuild_818_; lean_object* v_trace_819_; lean_object* v_buildTime_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_log_816_ = lean_ctor_get(v___y_814_, 0);
v_action_817_ = lean_ctor_get_uint8(v___y_814_, sizeof(void*)*3);
v_wantsRebuild_818_ = lean_ctor_get_uint8(v___y_814_, sizeof(void*)*3 + 1);
v_trace_819_ = lean_ctor_get(v___y_814_, 1);
v_buildTime_820_ = lean_ctor_get(v___y_814_, 2);
v___x_821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
v___x_822_ = lean_string_append(v___y_808_, v___x_821_);
v___x_823_ = lean_io_prim_handle_put_str(v_a_806_, v___x_822_);
lean_dec_ref(v___x_822_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_825_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_a_824_);
lean_ctor_set(v___x_825_, 1, v___y_814_);
return v___x_825_;
}
else
{
lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_839_; 
lean_inc(v_buildTime_820_);
lean_inc_ref(v_trace_819_);
lean_inc_ref(v_log_816_);
v_isSharedCheck_839_ = !lean_is_exclusive(v___y_814_);
if (v_isSharedCheck_839_ == 0)
{
lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; 
v_unused_840_ = lean_ctor_get(v___y_814_, 2);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v___y_814_, 1);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v___y_814_, 0);
lean_dec(v_unused_842_);
v___x_827_ = v___y_814_;
v_isShared_828_ = v_isSharedCheck_839_;
goto v_resetjp_826_;
}
else
{
lean_dec(v___y_814_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_839_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v_a_829_; lean_object* v___x_830_; uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v_a_829_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_823_, 1);
v___x_830_ = lean_io_error_to_string(v_a_829_);
v___x_831_ = 3;
v___x_832_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_832_, 0, v___x_830_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*1, v___x_831_);
v___x_833_ = lean_array_get_size(v_log_816_);
v___x_834_ = lean_array_push(v_log_816_, v___x_832_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_834_);
v___x_836_ = v___x_827_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_trace_819_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v_buildTime_820_);
lean_ctor_set_uint8(v_reuseFailAlloc_838_, sizeof(void*)*3, v_action_817_);
lean_ctor_set_uint8(v_reuseFailAlloc_838_, sizeof(void*)*3 + 1, v_wantsRebuild_818_);
v___x_836_ = v_reuseFailAlloc_838_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_837_; 
v___x_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_833_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
return v___x_837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed(lean_object* v_a_843_, lean_object* v_x_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3(v_a_843_, v_x_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v_a_843_);
return v_res_853_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_861_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__3));
v___x_862_ = lean_unsigned_to_nat(5u);
v___x_863_ = lean_mk_empty_array_with_capacity(v___x_862_);
v___x_864_ = lean_array_push(v___x_863_, v___x_861_);
return v___x_864_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_865_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__4));
v___x_866_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__6);
v___x_867_ = lean_array_push(v___x_866_, v___x_865_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(uint8_t v_bootstrap_870_, lean_object* v___y_871_, lean_object* v_oFiles_872_, uint8_t v_shouldExport_873_, uint8_t v___x_874_, lean_object* v___x_875_, size_t v___x_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
if (v_bootstrap_870_ == 0)
{
lean_object* v_toContext_884_; lean_object* v_lakeEnv_885_; lean_object* v_lean_886_; lean_object* v_log_887_; uint8_t v_action_888_; uint8_t v_wantsRebuild_889_; lean_object* v_trace_890_; lean_object* v_buildTime_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_921_; 
lean_dec_ref(v___y_877_);
lean_dec_ref(v___x_875_);
v_toContext_884_ = lean_ctor_get(v___y_881_, 1);
v_lakeEnv_885_ = lean_ctor_get(v_toContext_884_, 0);
v_lean_886_ = lean_ctor_get(v_lakeEnv_885_, 1);
v_log_887_ = lean_ctor_get(v___y_882_, 0);
v_action_888_ = lean_ctor_get_uint8(v___y_882_, sizeof(void*)*3);
v_wantsRebuild_889_ = lean_ctor_get_uint8(v___y_882_, sizeof(void*)*3 + 1);
v_trace_890_ = lean_ctor_get(v___y_882_, 1);
v_buildTime_891_ = lean_ctor_get(v___y_882_, 2);
v_isSharedCheck_921_ = !lean_is_exclusive(v___y_882_);
if (v_isSharedCheck_921_ == 0)
{
v___x_893_ = v___y_882_;
v_isShared_894_ = v_isSharedCheck_921_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_buildTime_891_);
lean_inc(v_trace_890_);
lean_inc(v_log_887_);
lean_dec(v___y_882_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_921_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v_ar_895_; lean_object* v___x_896_; 
v_ar_895_ = lean_ctor_get(v_lean_886_, 13);
lean_inc_ref(v_ar_895_);
v___x_896_ = l_Lake_compileStaticLib(v___y_871_, v_oFiles_872_, v_ar_895_, v_bootstrap_870_, v_log_887_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_908_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_a_898_ = lean_ctor_get(v___x_896_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_908_ == 0)
{
v___x_900_ = v___x_896_;
v_isShared_901_ = v_isSharedCheck_908_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_908_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v_a_898_);
v___x_903_ = v___x_893_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_898_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_trace_890_);
lean_ctor_set(v_reuseFailAlloc_907_, 2, v_buildTime_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*3, v_action_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_907_, sizeof(void*)*3 + 1, v_wantsRebuild_889_);
v___x_903_ = v_reuseFailAlloc_907_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_905_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v___x_903_);
v___x_905_ = v___x_900_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_897_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_920_; 
v_a_909_ = lean_ctor_get(v___x_896_, 0);
v_a_910_ = lean_ctor_get(v___x_896_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_920_ == 0)
{
v___x_912_ = v___x_896_;
v_isShared_913_ = v_isSharedCheck_920_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_inc(v_a_909_);
lean_dec(v___x_896_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_920_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 0, v_a_910_);
v___x_915_ = v___x_893_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_910_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_trace_890_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_buildTime_891_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*3, v_action_888_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*3 + 1, v_wantsRebuild_889_);
v___x_915_ = v_reuseFailAlloc_919_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_917_; 
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v___x_915_);
v___x_917_ = v___x_912_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_909_);
lean_ctor_set(v_reuseFailAlloc_918_, 1, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
}
else
{
uint8_t v___x_922_; 
v___x_922_ = l_System_Platform_isOSX;
if (v___x_922_ == 0)
{
uint8_t v___x_923_; 
lean_dec_ref(v___y_877_);
lean_dec_ref(v___x_875_);
v___x_923_ = l_System_Platform_isWindows;
if (v___x_923_ == 0)
{
lean_object* v_toContext_924_; lean_object* v_lakeEnv_925_; lean_object* v_lean_926_; lean_object* v_log_927_; uint8_t v_action_928_; uint8_t v_wantsRebuild_929_; lean_object* v_trace_930_; lean_object* v_buildTime_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_961_; 
v_toContext_924_ = lean_ctor_get(v___y_881_, 1);
v_lakeEnv_925_ = lean_ctor_get(v_toContext_924_, 0);
v_lean_926_ = lean_ctor_get(v_lakeEnv_925_, 1);
v_log_927_ = lean_ctor_get(v___y_882_, 0);
v_action_928_ = lean_ctor_get_uint8(v___y_882_, sizeof(void*)*3);
v_wantsRebuild_929_ = lean_ctor_get_uint8(v___y_882_, sizeof(void*)*3 + 1);
v_trace_930_ = lean_ctor_get(v___y_882_, 1);
v_buildTime_931_ = lean_ctor_get(v___y_882_, 2);
v_isSharedCheck_961_ = !lean_is_exclusive(v___y_882_);
if (v_isSharedCheck_961_ == 0)
{
v___x_933_ = v___y_882_;
v_isShared_934_ = v_isSharedCheck_961_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_buildTime_931_);
lean_inc(v_trace_930_);
lean_inc(v_log_927_);
lean_dec(v___y_882_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_961_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_ar_935_; lean_object* v___x_936_; 
v_ar_935_ = lean_ctor_get(v_lean_926_, 13);
lean_inc_ref(v_ar_935_);
v___x_936_ = l_Lake_compileStaticLib(v___y_871_, v_oFiles_872_, v_ar_935_, v___x_923_, v_log_927_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_948_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_a_938_ = lean_ctor_get(v___x_936_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_948_ == 0)
{
v___x_940_ = v___x_936_;
v_isShared_941_ = v_isSharedCheck_948_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_948_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v_a_938_);
v___x_943_ = v___x_933_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_938_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_trace_930_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_buildTime_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*3, v_action_928_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*3 + 1, v_wantsRebuild_929_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_945_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v___x_943_);
v___x_945_ = v___x_940_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_937_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v_a_949_; lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_960_; 
v_a_949_ = lean_ctor_get(v___x_936_, 0);
v_a_950_ = lean_ctor_get(v___x_936_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_960_ == 0)
{
v___x_952_ = v___x_936_;
v_isShared_953_ = v_isSharedCheck_960_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_inc(v_a_949_);
lean_dec(v___x_936_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_960_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v_a_950_);
v___x_955_ = v___x_933_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_950_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_trace_930_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v_buildTime_931_);
lean_ctor_set_uint8(v_reuseFailAlloc_959_, sizeof(void*)*3, v_action_928_);
lean_ctor_set_uint8(v_reuseFailAlloc_959_, sizeof(void*)*3 + 1, v_wantsRebuild_929_);
v___x_955_ = v_reuseFailAlloc_959_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_957_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v___x_955_);
v___x_957_ = v___x_952_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_949_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_962_; lean_object* v_lakeEnv_963_; lean_object* v_lean_964_; lean_object* v_log_965_; uint8_t v_action_966_; uint8_t v_wantsRebuild_967_; lean_object* v_trace_968_; lean_object* v_buildTime_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_999_; 
v_toContext_962_ = lean_ctor_get(v___y_881_, 1);
v_lakeEnv_963_ = lean_ctor_get(v_toContext_962_, 0);
v_lean_964_ = lean_ctor_get(v_lakeEnv_963_, 1);
v_log_965_ = lean_ctor_get(v___y_882_, 0);
v_action_966_ = lean_ctor_get_uint8(v___y_882_, sizeof(void*)*3);
v_wantsRebuild_967_ = lean_ctor_get_uint8(v___y_882_, sizeof(void*)*3 + 1);
v_trace_968_ = lean_ctor_get(v___y_882_, 1);
v_buildTime_969_ = lean_ctor_get(v___y_882_, 2);
v_isSharedCheck_999_ = !lean_is_exclusive(v___y_882_);
if (v_isSharedCheck_999_ == 0)
{
v___x_971_ = v___y_882_;
v_isShared_972_ = v_isSharedCheck_999_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_buildTime_969_);
lean_inc(v_trace_968_);
lean_inc(v_log_965_);
lean_dec(v___y_882_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_999_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v_ar_973_; lean_object* v___x_974_; 
v_ar_973_ = lean_ctor_get(v_lean_964_, 13);
lean_inc_ref(v_ar_973_);
v___x_974_ = l_Lake_compileStaticLib(v___y_871_, v_oFiles_872_, v_ar_973_, v_shouldExport_873_, v_log_965_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_986_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_a_976_ = lean_ctor_get(v___x_974_, 1);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_986_ == 0)
{
v___x_978_ = v___x_974_;
v_isShared_979_ = v_isSharedCheck_986_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_986_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v_a_976_);
v___x_981_ = v___x_971_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_976_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_trace_968_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_buildTime_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*3, v_action_966_);
lean_ctor_set_uint8(v_reuseFailAlloc_985_, sizeof(void*)*3 + 1, v_wantsRebuild_967_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_983_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 1, v___x_981_);
v___x_983_ = v___x_978_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_975_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_981_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v_a_987_; lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_998_; 
v_a_987_ = lean_ctor_get(v___x_974_, 0);
v_a_988_ = lean_ctor_get(v___x_974_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_998_ == 0)
{
v___x_990_ = v___x_974_;
v_isShared_991_ = v_isSharedCheck_998_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_inc(v_a_987_);
lean_dec(v___x_974_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_998_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v_a_988_);
v___x_993_ = v___x_971_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_988_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_trace_968_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_buildTime_969_);
lean_ctor_set_uint8(v_reuseFailAlloc_997_, sizeof(void*)*3, v_action_966_);
lean_ctor_set_uint8(v_reuseFailAlloc_997_, sizeof(void*)*3 + 1, v_wantsRebuild_967_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 1, v___x_993_);
v___x_995_ = v___x_990_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_987_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1000_; uint8_t v_action_1001_; uint8_t v_wantsRebuild_1002_; lean_object* v_trace_1003_; lean_object* v_buildTime_1004_; lean_object* v___x_1005_; 
v_log_1000_ = lean_ctor_get(v___y_882_, 0);
v_action_1001_ = lean_ctor_get_uint8(v___y_882_, sizeof(void*)*3);
v_wantsRebuild_1002_ = lean_ctor_get_uint8(v___y_882_, sizeof(void*)*3 + 1);
v_trace_1003_ = lean_ctor_get(v___y_882_, 1);
v_buildTime_1004_ = lean_ctor_get(v___y_882_, 2);
lean_inc_ref(v___y_871_);
v___x_1005_ = l_Lake_createParentDirs(v___y_871_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v_a_1009_; lean_object* v___y_1056_; uint8_t v___x_1058_; lean_object* v___x_1059_; 
lean_dec_ref_known(v___x_1005_, 1);
v___x_1006_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_871_);
v___x_1007_ = l_System_FilePath_addExtension(v___y_871_, v___x_1006_);
v___x_1058_ = 1;
v___x_1059_ = lean_io_prim_handle_mk(v___x_1007_, v___x_1058_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = lean_array_get_size(v_oFiles_872_);
v___x_1063_ = lean_nat_dec_lt(v___x_1061_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_dec(v_a_1060_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v_oFiles_872_);
v_a_1009_ = v___y_882_;
goto v___jp_1008_;
}
else
{
lean_object* v___f_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___f_1064_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__3___boxed), 10, 1);
lean_closure_set(v___f_1064_, 0, v_a_1060_);
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_nat_dec_le(v___x_1062_, v___x_1062_);
if (v___x_1066_ == 0)
{
if (v___x_1063_ == 0)
{
lean_dec_ref(v___f_1064_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v_oFiles_872_);
v_a_1009_ = v___y_882_;
goto v___jp_1008_;
}
else
{
size_t v___x_1067_; lean_object* v___x_187623__overap_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_usize_of_nat(v___x_1062_);
v___x_187623__overap_1068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_875_, v___f_1064_, v_oFiles_872_, v___x_876_, v___x_1067_, v___x_1065_);
lean_inc_ref(v___y_881_);
lean_inc(v___y_880_);
lean_inc(v___y_879_);
lean_inc(v___y_878_);
v___x_1069_ = lean_apply_7(v___x_187623__overap_1068_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, lean_box(0));
v___y_1056_ = v___x_1069_;
goto v___jp_1055_;
}
}
else
{
size_t v___x_1070_; lean_object* v___x_187625__overap_1071_; lean_object* v___x_1072_; 
v___x_1070_ = lean_usize_of_nat(v___x_1062_);
v___x_187625__overap_1071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_875_, v___f_1064_, v_oFiles_872_, v___x_876_, v___x_1070_, v___x_1065_);
lean_inc_ref(v___y_881_);
lean_inc(v___y_880_);
lean_inc(v___y_879_);
lean_inc(v___y_878_);
v___x_1072_ = lean_apply_7(v___x_187625__overap_1071_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, lean_box(0));
v___y_1056_ = v___x_1072_;
goto v___jp_1055_;
}
}
}
else
{
lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1086_; 
lean_inc(v_buildTime_1004_);
lean_inc_ref(v_trace_1003_);
lean_inc_ref(v_log_1000_);
lean_dec_ref(v___x_1007_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v_oFiles_872_);
lean_dec_ref(v___y_871_);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___y_882_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; lean_object* v_unused_1088_; lean_object* v_unused_1089_; 
v_unused_1087_ = lean_ctor_get(v___y_882_, 2);
lean_dec(v_unused_1087_);
v_unused_1088_ = lean_ctor_get(v___y_882_, 1);
lean_dec(v_unused_1088_);
v_unused_1089_ = lean_ctor_get(v___y_882_, 0);
lean_dec(v_unused_1089_);
v___x_1074_ = v___y_882_;
v_isShared_1075_ = v_isSharedCheck_1086_;
goto v_resetjp_1073_;
}
else
{
lean_dec(v___y_882_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1086_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v_a_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v_a_1076_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1077_ = lean_io_error_to_string(v_a_1076_);
v___x_1078_ = 3;
v___x_1079_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set_uint8(v___x_1079_, sizeof(void*)*1, v___x_1078_);
v___x_1080_ = lean_array_get_size(v_log_1000_);
v___x_1081_ = lean_array_push(v_log_1000_, v___x_1079_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1081_);
v___x_1083_ = v___x_1074_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_trace_1003_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_buildTime_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*3, v_action_1001_);
lean_ctor_set_uint8(v_reuseFailAlloc_1085_, sizeof(void*)*3 + 1, v_wantsRebuild_1002_);
v___x_1083_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1080_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
return v___x_1084_;
}
}
}
v___jp_1008_:
{
lean_object* v___x_1010_; lean_object* v_log_1011_; uint8_t v_action_1012_; uint8_t v_wantsRebuild_1013_; lean_object* v_trace_1014_; lean_object* v_buildTime_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1054_; 
v___x_1010_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1011_ = lean_ctor_get(v_a_1009_, 0);
v_action_1012_ = lean_ctor_get_uint8(v_a_1009_, sizeof(void*)*3);
v_wantsRebuild_1013_ = lean_ctor_get_uint8(v_a_1009_, sizeof(void*)*3 + 1);
v_trace_1014_ = lean_ctor_get(v_a_1009_, 1);
v_buildTime_1015_ = lean_ctor_get(v_a_1009_, 2);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_a_1009_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1017_ = v_a_1009_;
v_isShared_1018_ = v_isSharedCheck_1054_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_buildTime_1015_);
lean_inc(v_trace_1014_);
lean_inc(v_log_1011_);
lean_dec(v_a_1009_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1054_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1019_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1020_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1021_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1022_ = lean_array_push(v___x_1021_, v___y_871_);
v___x_1023_ = lean_array_push(v___x_1022_, v___x_1020_);
v___x_1024_ = lean_array_push(v___x_1023_, v___x_1007_);
v___x_1025_ = lean_box(0);
v___x_1026_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1027_ = 0;
v___x_1028_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1028_, 0, v___x_1010_);
lean_ctor_set(v___x_1028_, 1, v___x_1019_);
lean_ctor_set(v___x_1028_, 2, v___x_1024_);
lean_ctor_set(v___x_1028_, 3, v___x_1025_);
lean_ctor_set(v___x_1028_, 4, v___x_1026_);
lean_ctor_set_uint8(v___x_1028_, sizeof(void*)*5, v___x_874_);
lean_ctor_set_uint8(v___x_1028_, sizeof(void*)*5 + 1, v___x_1027_);
v___x_1029_ = l_Lake_proc(v___x_1028_, v___x_1027_, v___x_1025_, v_log_1011_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1041_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_a_1031_ = lean_ctor_get(v___x_1029_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1033_ = v___x_1029_;
v_isShared_1034_ = v_isSharedCheck_1041_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1041_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v_a_1031_);
v___x_1036_ = v___x_1017_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1031_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_trace_1014_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v_buildTime_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, sizeof(void*)*3, v_action_1012_);
lean_ctor_set_uint8(v_reuseFailAlloc_1040_, sizeof(void*)*3 + 1, v_wantsRebuild_1013_);
v___x_1036_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 1, v___x_1036_);
v___x_1038_ = v___x_1033_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1030_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1053_; 
v_a_1042_ = lean_ctor_get(v___x_1029_, 0);
v_a_1043_ = lean_ctor_get(v___x_1029_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1045_ = v___x_1029_;
v_isShared_1046_ = v_isSharedCheck_1053_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_inc(v_a_1042_);
lean_dec(v___x_1029_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1053_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v_a_1043_);
v___x_1048_ = v___x_1017_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1043_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_trace_1014_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v_buildTime_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1052_, sizeof(void*)*3, v_action_1012_);
lean_ctor_set_uint8(v_reuseFailAlloc_1052_, sizeof(void*)*3 + 1, v_wantsRebuild_1013_);
v___x_1048_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1050_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 1, v___x_1048_);
v___x_1050_ = v___x_1045_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1042_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
}
v___jp_1055_:
{
if (lean_obj_tag(v___y_1056_) == 0)
{
lean_object* v_a_1057_; 
v_a_1057_ = lean_ctor_get(v___y_1056_, 1);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___y_1056_, 2);
v_a_1009_ = v_a_1057_;
goto v___jp_1008_;
}
else
{
lean_dec_ref(v___x_1007_);
lean_dec_ref(v___y_871_);
return v___y_1056_;
}
}
}
else
{
lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1103_; 
lean_inc(v_buildTime_1004_);
lean_inc_ref(v_trace_1003_);
lean_inc_ref(v_log_1000_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v___x_875_);
lean_dec_ref(v_oFiles_872_);
lean_dec_ref(v___y_871_);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___y_882_);
if (v_isSharedCheck_1103_ == 0)
{
lean_object* v_unused_1104_; lean_object* v_unused_1105_; lean_object* v_unused_1106_; 
v_unused_1104_ = lean_ctor_get(v___y_882_, 2);
lean_dec(v_unused_1104_);
v_unused_1105_ = lean_ctor_get(v___y_882_, 1);
lean_dec(v_unused_1105_);
v_unused_1106_ = lean_ctor_get(v___y_882_, 0);
lean_dec(v_unused_1106_);
v___x_1091_ = v___y_882_;
v_isShared_1092_ = v_isSharedCheck_1103_;
goto v_resetjp_1090_;
}
else
{
lean_dec(v___y_882_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1103_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_a_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v_a_1093_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1094_ = lean_io_error_to_string(v_a_1093_);
v___x_1095_ = 3;
v___x_1096_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set_uint8(v___x_1096_, sizeof(void*)*1, v___x_1095_);
v___x_1097_ = lean_array_get_size(v_log_1000_);
v___x_1098_ = lean_array_push(v_log_1000_, v___x_1096_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1098_);
v___x_1100_ = v___x_1091_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v_trace_1003_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_buildTime_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*3, v_action_1001_);
lean_ctor_set_uint8(v_reuseFailAlloc_1102_, sizeof(void*)*3 + 1, v_wantsRebuild_1002_);
v___x_1100_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1097_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
return v___x_1101_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed(lean_object* v_bootstrap_1107_, lean_object* v___y_1108_, lean_object* v_oFiles_1109_, lean_object* v_shouldExport_1110_, lean_object* v___x_1111_, lean_object* v___x_1112_, lean_object* v___x_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
uint8_t v_bootstrap_boxed_1121_; uint8_t v_shouldExport_boxed_1122_; uint8_t v___x_187993__boxed_1123_; size_t v___x_187995__boxed_1124_; lean_object* v_res_1125_; 
v_bootstrap_boxed_1121_ = lean_unbox(v_bootstrap_1107_);
v_shouldExport_boxed_1122_ = lean_unbox(v_shouldExport_1110_);
v___x_187993__boxed_1123_ = lean_unbox(v___x_1111_);
v___x_187995__boxed_1124_ = lean_unbox_usize(v___x_1113_);
lean_dec(v___x_1113_);
v_res_1125_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4(v_bootstrap_boxed_1121_, v___y_1108_, v_oFiles_1109_, v_shouldExport_boxed_1122_, v___x_187993__boxed_1123_, v___x_1112_, v___x_187995__boxed_1124_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec(v___y_1115_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(uint8_t v_bootstrap_1127_, lean_object* v___y_1128_, uint8_t v_shouldExport_1129_, uint8_t v___x_1130_, lean_object* v___x_1131_, size_t v___x_1132_, lean_object* v_oFiles_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___y_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1141_ = lean_box(v_bootstrap_1127_);
v___x_1142_ = lean_box(v_shouldExport_1129_);
v___x_1143_ = lean_box(v___x_1130_);
v___x_1144_ = lean_box_usize(v___x_1132_);
lean_inc_ref(v___y_1128_);
v___y_1145_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___boxed), 14, 7);
lean_closure_set(v___y_1145_, 0, v___x_1141_);
lean_closure_set(v___y_1145_, 1, v___y_1128_);
lean_closure_set(v___y_1145_, 2, v_oFiles_1133_);
lean_closure_set(v___y_1145_, 3, v___x_1142_);
lean_closure_set(v___y_1145_, 4, v___x_1143_);
lean_closure_set(v___y_1145_, 5, v___x_1131_);
lean_closure_set(v___y_1145_, 6, v___x_1144_);
v___x_1146_ = 0;
v___x_1147_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1148_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1128_, v___y_1145_, v___x_1146_, v___x_1147_, v___x_1130_, v___x_1146_, v___x_1146_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1158_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_a_1150_ = lean_ctor_get(v___x_1148_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1152_ = v___x_1148_;
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1158_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_path_1154_; lean_object* v___x_1156_; 
v_path_1154_ = lean_ctor_get(v_a_1149_, 1);
lean_inc_ref(v_path_1154_);
lean_dec(v_a_1149_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v_path_1154_);
v___x_1156_ = v___x_1152_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_path_1154_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_a_1150_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
v_a_1159_ = lean_ctor_get(v___x_1148_, 0);
v_a_1160_ = lean_ctor_get(v___x_1148_, 1);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1148_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_inc(v_a_1159_);
lean_dec(v___x_1148_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1159_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_a_1160_);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed(lean_object* v_bootstrap_1168_, lean_object* v___y_1169_, lean_object* v_shouldExport_1170_, lean_object* v___x_1171_, lean_object* v___x_1172_, lean_object* v___x_1173_, lean_object* v_oFiles_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v_bootstrap_boxed_1182_; uint8_t v_shouldExport_boxed_1183_; uint8_t v___x_188416__boxed_1184_; size_t v___x_188418__boxed_1185_; lean_object* v_res_1186_; 
v_bootstrap_boxed_1182_ = lean_unbox(v_bootstrap_1168_);
v_shouldExport_boxed_1183_ = lean_unbox(v_shouldExport_1170_);
v___x_188416__boxed_1184_ = lean_unbox(v___x_1171_);
v___x_188418__boxed_1185_ = lean_unbox_usize(v___x_1173_);
lean_dec(v___x_1173_);
v_res_1186_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5(v_bootstrap_boxed_1182_, v___y_1169_, v_shouldExport_boxed_1183_, v___x_188416__boxed_1184_, v___x_1172_, v___x_188418__boxed_1185_, v_oFiles_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec(v___y_1176_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(lean_object* v_config_1191_, lean_object* v_config_1192_, uint8_t v_shouldExport_1193_, uint8_t v___x_1194_, lean_object* v___x_1195_, lean_object* v___x_1196_, lean_object* v___x_1197_, lean_object* v___x_1198_, lean_object* v___f_1199_, lean_object* v_dir_1200_, lean_object* v_self_1201_, lean_object* v___x_1202_, lean_object* v___f_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
size_t v___y_1212_; uint8_t v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v_a_1232_; lean_object* v_a_1233_; lean_object* v___x_1276_; 
lean_inc_ref(v___y_1204_);
lean_inc_ref(v___y_1208_);
lean_inc(v___y_1207_);
lean_inc(v___y_1206_);
lean_inc(v___x_1197_);
v___x_1276_ = lean_apply_7(v___y_1204_, v___x_1202_, v___x_1197_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, lean_box(0));
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v_a_1278_; lean_object* v___x_1279_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
v_a_1278_ = lean_ctor_get(v___x_1276_, 1);
lean_inc(v_a_1278_);
lean_dec_ref_known(v___x_1276_, 2);
v___x_1279_ = l_Lake_Job_await___redArg(v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v_a_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
v_a_1281_ = lean_ctor_get(v___x_1279_, 1);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1279_, 2);
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_1284_ = lean_array_get_size(v_a_1280_);
v___x_1285_ = lean_nat_dec_lt(v___x_1282_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_dec(v_a_1280_);
lean_dec_ref(v___f_1203_);
v_a_1232_ = v___x_1283_;
v_a_1233_ = v_a_1281_;
goto v___jp_1231_;
}
else
{
size_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_187753__overap_1288_; lean_object* v___x_1289_; 
v___x_1286_ = ((size_t)0ULL);
v___x_1287_ = lean_usize_of_nat(v___x_1284_);
lean_inc_ref(v___x_1198_);
v___x_187753__overap_1288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1198_, v___f_1203_, v_a_1280_, v___x_1286_, v___x_1287_, v___x_1283_);
lean_inc_ref(v___y_1208_);
lean_inc(v___y_1207_);
lean_inc(v___y_1206_);
lean_inc(v___x_1197_);
lean_inc_ref(v___y_1204_);
v___x_1289_ = lean_apply_7(v___x_187753__overap_1288_, v___y_1204_, v___x_1197_, v___y_1206_, v___y_1207_, v___y_1208_, v_a_1281_, lean_box(0));
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v_a_1291_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
v_a_1291_ = lean_ctor_get(v___x_1289_, 1);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1289_, 2);
v_a_1232_ = v_a_1290_;
v_a_1233_ = v_a_1291_;
goto v___jp_1231_;
}
else
{
lean_object* v_a_1292_; lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_self_1201_);
lean_dec_ref(v_dir_1200_);
lean_dec_ref(v___f_1199_);
lean_dec_ref(v___x_1198_);
lean_dec(v___x_1197_);
lean_dec(v___x_1196_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v_config_1191_);
v_a_1292_ = lean_ctor_get(v___x_1289_, 0);
v_a_1293_ = lean_ctor_get(v___x_1289_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1289_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_inc(v_a_1292_);
lean_dec(v___x_1289_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1292_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec_ref(v___y_1204_);
lean_dec_ref(v___f_1203_);
lean_dec_ref(v_self_1201_);
lean_dec_ref(v_dir_1200_);
lean_dec_ref(v___f_1199_);
lean_dec_ref(v___x_1198_);
lean_dec(v___x_1197_);
lean_dec(v___x_1196_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v_config_1191_);
v_a_1301_ = lean_ctor_get(v___x_1279_, 0);
v_a_1302_ = lean_ctor_get(v___x_1279_, 1);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1279_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_inc(v_a_1301_);
lean_dec(v___x_1279_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1301_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref(v___y_1204_);
lean_dec_ref(v___f_1203_);
lean_dec_ref(v_self_1201_);
lean_dec_ref(v_dir_1200_);
lean_dec_ref(v___f_1199_);
lean_dec_ref(v___x_1198_);
lean_dec(v___x_1197_);
lean_dec(v___x_1196_);
lean_dec_ref(v___x_1195_);
lean_dec_ref(v_config_1191_);
v_a_1310_ = lean_ctor_get(v___x_1276_, 0);
v_a_1311_ = lean_ctor_get(v___x_1276_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1276_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_inc(v_a_1310_);
lean_dec(v___x_1276_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1310_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
v___jp_1211_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1218_ = lean_box(v___y_1213_);
v___x_1219_ = lean_box(v_shouldExport_1193_);
v___x_1220_ = lean_box(v___x_1194_);
v___x_1221_ = lean_box_usize(v___y_1212_);
v___f_1222_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___boxed), 14, 6);
lean_closure_set(v___f_1222_, 0, v___x_1218_);
lean_closure_set(v___f_1222_, 1, v___y_1217_);
lean_closure_set(v___f_1222_, 2, v___x_1219_);
lean_closure_set(v___f_1222_, 3, v___x_1220_);
lean_closure_set(v___f_1222_, 4, v___x_1195_);
lean_closure_set(v___f_1222_, 5, v___x_1221_);
v___x_1223_ = l_Array_append___redArg(v___y_1216_, v___y_1214_);
lean_dec_ref(v___y_1214_);
v___x_1224_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_1225_ = l_Lake_Job_collectArray___redArg(v___x_1223_, v___x_1224_);
lean_dec_ref(v___x_1223_);
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = 0;
v___x_1228_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_1229_ = l_Lake_Job_mapM___redArg(v___x_1196_, v___x_1225_, v___f_1222_, v___x_1226_, v___x_1227_, v___y_1204_, v___x_1197_, v___y_1206_, v___y_1207_, v___y_1208_, v___x_1228_);
lean_dec(v___x_1197_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v___y_1215_);
return v___x_1230_;
}
v___jp_1231_:
{
lean_object* v_toLeanConfig_1234_; lean_object* v_toLeanConfig_1235_; uint8_t v_bootstrap_1236_; lean_object* v_buildDir_1237_; lean_object* v_nativeLibDir_1238_; lean_object* v_moreLinkObjs_1239_; lean_object* v_moreLinkObjs_1240_; lean_object* v___x_1241_; size_t v_sz_1242_; size_t v___x_1243_; lean_object* v___x_187711__overap_1244_; lean_object* v___x_1245_; 
v_toLeanConfig_1234_ = lean_ctor_get(v_config_1191_, 1);
lean_inc_ref(v_toLeanConfig_1234_);
v_toLeanConfig_1235_ = lean_ctor_get(v_config_1192_, 0);
v_bootstrap_1236_ = lean_ctor_get_uint8(v_config_1191_, sizeof(void*)*28);
v_buildDir_1237_ = lean_ctor_get(v_config_1191_, 5);
lean_inc_ref(v_buildDir_1237_);
v_nativeLibDir_1238_ = lean_ctor_get(v_config_1191_, 7);
lean_inc_ref(v_nativeLibDir_1238_);
lean_dec_ref(v_config_1191_);
v_moreLinkObjs_1239_ = lean_ctor_get(v_toLeanConfig_1234_, 6);
lean_inc_ref(v_moreLinkObjs_1239_);
lean_dec_ref(v_toLeanConfig_1234_);
v_moreLinkObjs_1240_ = lean_ctor_get(v_toLeanConfig_1235_, 6);
v___x_1241_ = l_Array_append___redArg(v_moreLinkObjs_1239_, v_moreLinkObjs_1240_);
v_sz_1242_ = lean_array_size(v___x_1241_);
v___x_1243_ = ((size_t)0ULL);
v___x_187711__overap_1244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1198_, v___f_1199_, v_sz_1242_, v___x_1243_, v___x_1241_);
lean_inc_ref(v___y_1208_);
lean_inc(v___y_1207_);
lean_inc(v___y_1206_);
lean_inc(v___x_1197_);
lean_inc_ref(v___y_1204_);
v___x_1245_ = lean_apply_7(v___x_187711__overap_1244_, v___y_1204_, v___x_1197_, v___y_1206_, v___y_1207_, v___y_1208_, v_a_1233_, lean_box(0));
if (lean_obj_tag(v___x_1245_) == 0)
{
if (v_shouldExport_1193_ == 0)
{
lean_object* v_a_1246_; lean_object* v_a_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
v_a_1247_ = lean_ctor_get(v___x_1245_, 1);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1245_, 2);
v___x_1248_ = l_System_FilePath_normalize(v_buildDir_1237_);
v___x_1249_ = l_Lake_joinRelative(v_dir_1200_, v___x_1248_);
v___x_1250_ = l_System_FilePath_normalize(v_nativeLibDir_1238_);
v___x_1251_ = l_Lake_joinRelative(v___x_1249_, v___x_1250_);
v___x_1252_ = l_Lake_LeanLib_libName(v_self_1201_);
v___x_1253_ = l_Lake_nameToStaticLib(v___x_1252_, v_shouldExport_1193_);
v___x_1254_ = l_Lake_joinRelative(v___x_1251_, v___x_1253_);
v___y_1212_ = v___x_1243_;
v___y_1213_ = v_bootstrap_1236_;
v___y_1214_ = v_a_1246_;
v___y_1215_ = v_a_1247_;
v___y_1216_ = v_a_1232_;
v___y_1217_ = v___x_1254_;
goto v___jp_1211_;
}
else
{
lean_object* v_a_1255_; lean_object* v_a_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v_a_1255_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1255_);
v_a_1256_ = lean_ctor_get(v___x_1245_, 1);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1245_, 2);
v___x_1257_ = l_System_FilePath_normalize(v_buildDir_1237_);
v___x_1258_ = l_Lake_joinRelative(v_dir_1200_, v___x_1257_);
v___x_1259_ = l_System_FilePath_normalize(v_nativeLibDir_1238_);
v___x_1260_ = l_Lake_joinRelative(v___x_1258_, v___x_1259_);
v___x_1261_ = l_Lake_LeanLib_libName(v_self_1201_);
v___x_1262_ = 0;
v___x_1263_ = l_Lake_nameToStaticLib(v___x_1261_, v___x_1262_);
v___x_1264_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_1265_ = l_System_FilePath_addExtension(v___x_1263_, v___x_1264_);
v___x_1266_ = l_Lake_joinRelative(v___x_1260_, v___x_1265_);
v___y_1212_ = v___x_1243_;
v___y_1213_ = v_bootstrap_1236_;
v___y_1214_ = v_a_1255_;
v___y_1215_ = v_a_1256_;
v___y_1216_ = v_a_1232_;
v___y_1217_ = v___x_1266_;
goto v___jp_1211_;
}
}
else
{
lean_object* v_a_1267_; lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v_nativeLibDir_1238_);
lean_dec_ref(v_buildDir_1237_);
lean_dec_ref(v_a_1232_);
lean_dec_ref(v___y_1204_);
lean_dec_ref(v_self_1201_);
lean_dec_ref(v_dir_1200_);
lean_dec(v___x_1197_);
lean_dec(v___x_1196_);
lean_dec_ref(v___x_1195_);
v_a_1267_ = lean_ctor_get(v___x_1245_, 0);
v_a_1268_ = lean_ctor_get(v___x_1245_, 1);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1245_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_inc(v_a_1267_);
lean_dec(v___x_1245_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1267_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed(lean_object** _args){
lean_object* v_config_1319_ = _args[0];
lean_object* v_config_1320_ = _args[1];
lean_object* v_shouldExport_1321_ = _args[2];
lean_object* v___x_1322_ = _args[3];
lean_object* v___x_1323_ = _args[4];
lean_object* v___x_1324_ = _args[5];
lean_object* v___x_1325_ = _args[6];
lean_object* v___x_1326_ = _args[7];
lean_object* v___f_1327_ = _args[8];
lean_object* v_dir_1328_ = _args[9];
lean_object* v_self_1329_ = _args[10];
lean_object* v___x_1330_ = _args[11];
lean_object* v___f_1331_ = _args[12];
lean_object* v___y_1332_ = _args[13];
lean_object* v___y_1333_ = _args[14];
lean_object* v___y_1334_ = _args[15];
lean_object* v___y_1335_ = _args[16];
lean_object* v___y_1336_ = _args[17];
lean_object* v___y_1337_ = _args[18];
lean_object* v___y_1338_ = _args[19];
_start:
{
uint8_t v_shouldExport_boxed_1339_; uint8_t v___x_188514__boxed_1340_; lean_object* v_res_1341_; 
v_shouldExport_boxed_1339_ = lean_unbox(v_shouldExport_1321_);
v___x_188514__boxed_1340_ = lean_unbox(v___x_1322_);
v_res_1341_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6(v_config_1319_, v_config_1320_, v_shouldExport_boxed_1339_, v___x_188514__boxed_1340_, v___x_1323_, v___x_1324_, v___x_1325_, v___x_1326_, v___f_1327_, v_dir_1328_, v_self_1329_, v___x_1330_, v___f_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec(v_config_1320_);
return v_res_1341_;
}
}
static lean_object* _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0(void){
_start:
{
uint8_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = 2;
v___x_1343_ = l_Lake_Verbosity_ctorIdx(v___x_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(lean_object* v_self_1347_, uint8_t v_shouldExport_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; lean_object* v_toApplicative_1357_; lean_object* v_toBind_1358_; lean_object* v_toFunctor_1359_; lean_object* v_toPure_1360_; lean_object* v___f_1361_; lean_object* v___f_1362_; lean_object* v___f_1363_; lean_object* v___f_1364_; lean_object* v___x_1365_; lean_object* v___f_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_toBuildConfig_1374_; lean_object* v_registeredJobs_1375_; uint8_t v_verbosity_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___f_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; uint8_t v___x_1383_; lean_object* v___y_1385_; 
v___x_1356_ = l_instMonadBaseIO;
v_toApplicative_1357_ = lean_ctor_get(v___x_1356_, 0);
v_toBind_1358_ = lean_ctor_get(v___x_1356_, 1);
v_toFunctor_1359_ = lean_ctor_get(v_toApplicative_1357_, 0);
v_toPure_1360_ = lean_ctor_get(v_toApplicative_1357_, 1);
lean_inc_n(v_toBind_1358_, 3);
lean_inc_n(v_toPure_1360_, 5);
v___f_1361_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_1361_, 0, v_toPure_1360_);
lean_closure_set(v___f_1361_, 1, v_toBind_1358_);
v___f_1362_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_1362_, 0, v_toPure_1360_);
lean_closure_set(v___f_1362_, 1, v_toBind_1358_);
lean_inc_ref(v___f_1361_);
v___f_1363_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_1363_, 0, v_toPure_1360_);
lean_closure_set(v___f_1363_, 1, v___f_1361_);
lean_inc_ref_n(v_toFunctor_1359_, 2);
v___f_1364_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_1364_, 0, v_toFunctor_1359_);
lean_closure_set(v___f_1364_, 1, v_toPure_1360_);
lean_closure_set(v___f_1364_, 2, v_toBind_1358_);
v___x_1365_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_1359_);
v___f_1366_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1366_, 0, v_toPure_1360_);
v___x_1367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___f_1366_);
lean_ctor_set(v___x_1367_, 2, v___f_1364_);
lean_ctor_set(v___x_1367_, 3, v___f_1363_);
lean_ctor_set(v___x_1367_, 4, v___f_1362_);
v___x_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v___f_1361_);
v___x_1369_ = l_ReaderT_instMonad___redArg(v___x_1368_);
v___x_1370_ = l_StateRefT_x27_instMonad___redArg(v___x_1369_);
v___x_1371_ = l_ReaderT_instMonad___redArg(v___x_1370_);
v___x_1372_ = l_ReaderT_instMonad___redArg(v___x_1371_);
v___x_1373_ = l_Lake_EquipT_instMonad___redArg(v___x_1372_);
v_toBuildConfig_1374_ = lean_ctor_get(v_a_1353_, 0);
v_registeredJobs_1375_ = lean_ctor_get(v_a_1353_, 4);
v_verbosity_1376_ = lean_ctor_get_uint8(v_toBuildConfig_1374_, sizeof(void*)*4 + 4);
v___x_1377_ = l_Lake_instDataKindFilePath;
v___x_1378_ = lean_box(v_shouldExport_1348_);
lean_inc_ref(v___x_1373_);
v___f_1379_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__1___boxed), 11, 2);
lean_closure_set(v___f_1379_, 0, v___x_1378_);
lean_closure_set(v___f_1379_, 1, v___x_1373_);
v___x_1380_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1376_);
v___x_1381_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0);
v___x_1382_ = lean_nat_dec_eq(v___x_1380_, v___x_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = 1;
if (v___x_1382_ == 0)
{
lean_object* v___x_1431_; 
v___x_1431_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_1385_ = v___x_1431_;
goto v___jp_1384_;
}
else
{
if (v_shouldExport_1348_ == 0)
{
lean_object* v___x_1432_; 
v___x_1432_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_1385_ = v___x_1432_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3));
v___y_1385_ = v___x_1433_;
goto v___jp_1384_;
}
}
v___jp_1384_:
{
lean_object* v_pkg_1386_; lean_object* v_name_1387_; lean_object* v_config_1388_; lean_object* v_keyName_1389_; lean_object* v_dir_1390_; lean_object* v_config_1391_; lean_object* v___f_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___f_1404_; uint8_t v___x_1405_; lean_object* v___x_1406_; 
v_pkg_1386_ = lean_ctor_get(v_self_1347_, 0);
v_name_1387_ = lean_ctor_get(v_self_1347_, 1);
v_config_1388_ = lean_ctor_get(v_self_1347_, 2);
lean_inc(v_config_1388_);
v_keyName_1389_ = lean_ctor_get(v_pkg_1386_, 2);
v_dir_1390_ = lean_ctor_get(v_pkg_1386_, 4);
lean_inc_ref(v_dir_1390_);
v_config_1391_ = lean_ctor_get(v_pkg_1386_, 6);
lean_inc_ref(v_config_1391_);
lean_inc_ref_n(v_pkg_1386_, 2);
v___f_1392_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__2___boxed), 10, 2);
lean_closure_set(v___f_1392_, 0, v___x_1377_);
lean_closure_set(v___f_1392_, 1, v_pkg_1386_);
lean_inc_n(v_name_1387_, 2);
v___x_1393_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1387_, v___x_1383_);
v___x_1394_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___x_1395_ = lean_string_append(v___x_1393_, v___x_1394_);
v___x_1396_ = lean_string_append(v___x_1395_, v___y_1385_);
v___x_1397_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_1389_);
v___x_1398_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1398_, 0, v_keyName_1389_);
lean_ctor_set(v___x_1398_, 1, v_name_1387_);
v___x_1399_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_1347_);
v___x_1400_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1398_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
lean_ctor_set(v___x_1400_, 2, v_self_1347_);
lean_ctor_set(v___x_1400_, 3, v___x_1397_);
v___x_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1401_, 0, v_pkg_1386_);
v___x_1402_ = lean_box(v_shouldExport_1348_);
v___x_1403_ = lean_box(v___x_1383_);
lean_inc_ref(v___x_1373_);
v___f_1404_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___boxed), 20, 13);
lean_closure_set(v___f_1404_, 0, v_config_1391_);
lean_closure_set(v___f_1404_, 1, v_config_1388_);
lean_closure_set(v___f_1404_, 2, v___x_1402_);
lean_closure_set(v___f_1404_, 3, v___x_1403_);
lean_closure_set(v___f_1404_, 4, v___x_1373_);
lean_closure_set(v___f_1404_, 5, v___x_1377_);
lean_closure_set(v___f_1404_, 6, v___x_1401_);
lean_closure_set(v___f_1404_, 7, v___x_1373_);
lean_closure_set(v___f_1404_, 8, v___f_1392_);
lean_closure_set(v___f_1404_, 9, v_dir_1390_);
lean_closure_set(v___f_1404_, 10, v_self_1347_);
lean_closure_set(v___f_1404_, 11, v___x_1400_);
lean_closure_set(v___f_1404_, 12, v___f_1379_);
v___x_1405_ = 0;
v___x_1406_ = l_Lake_ensureJob___redArg(v___x_1377_, v___f_1404_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1430_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_a_1408_ = lean_ctor_get(v___x_1406_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1410_ = v___x_1406_;
v_isShared_1411_ = v_isSharedCheck_1430_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1430_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_task_1412_; lean_object* v_kind_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1428_; 
v_task_1412_ = lean_ctor_get(v_a_1407_, 0);
v_kind_1413_ = lean_ctor_get(v_a_1407_, 1);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_a_1407_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v_a_1407_, 2);
lean_dec(v_unused_1429_);
v___x_1415_ = v_a_1407_;
v_isShared_1416_ = v_isSharedCheck_1428_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_kind_1413_);
lean_inc(v_task_1412_);
lean_dec(v_a_1407_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1428_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v_job_1418_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 2, v___x_1396_);
v_job_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_task_1412_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_kind_1413_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v___x_1396_);
v_job_1418_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1425_; 
lean_ctor_set_uint8(v_job_1418_, sizeof(void*)*3, v___x_1405_);
v___x_1419_ = lean_st_ref_take(v_registeredJobs_1375_);
lean_inc_ref(v_job_1418_);
v___x_1420_ = l_Lake_Job_toOpaque___redArg(v_job_1418_);
v___x_1421_ = lean_array_push(v___x_1419_, v___x_1420_);
v___x_1422_ = lean_st_ref_put(v_registeredJobs_1375_, v___x_1421_);
v___x_1423_ = l_Lake_Job_renew___redArg(v_job_1418_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1423_);
v___x_1425_ = v___x_1410_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_a_1408_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1396_);
return v___x_1406_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___boxed(lean_object* v_self_1434_, lean_object* v_shouldExport_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
uint8_t v_shouldExport_boxed_1443_; lean_object* v_res_1444_; 
v_shouldExport_boxed_1443_ = lean_unbox(v_shouldExport_1435_);
v_res_1444_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic(v_self_1434_, v_shouldExport_boxed_1443_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec(v_a_1437_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(uint8_t v_fmt_1445_, lean_object* v_a_1446_){
_start:
{
if (v_fmt_1445_ == 0)
{
return v_a_1446_;
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = l_Lake_mkRelPathString(v_a_1446_);
v___x_1448_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
v___x_1449_ = l_Lean_Json_compress(v___x_1448_);
return v___x_1449_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1___boxed(lean_object* v_fmt_1450_, lean_object* v_a_1451_){
_start:
{
uint8_t v_fmt_boxed_1452_; lean_object* v_res_1453_; 
v_fmt_boxed_1452_ = lean_unbox(v_fmt_1450_);
v_res_1453_ = l_Lake_formatQuery___at___00Lake_LeanLib_staticFacetConfig_spec__1(v_fmt_boxed_1452_, v_a_1451_);
return v_res_1453_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2(void){
_start:
{
uint8_t v___x_1456_; lean_object* v_name_1457_; lean_object* v___x_1458_; 
v___x_1456_ = 1;
v_name_1457_ = l_Lake_instDataKindFilePath;
v___x_1458_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1457_, v___x_1456_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(lean_object* v_defaultPkg_1462_, lean_object* v_self_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_name_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; 
v_name_1471_ = l_Lake_instDataKindFilePath;
v___x_1472_ = 1;
lean_inc_ref_n(v_self_1463_, 2);
v___x_1473_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_1462_, v_self_1463_, v_self_1463_, v___x_1472_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1515_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_a_1475_ = lean_ctor_get(v___x_1473_, 1);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1477_ = v___x_1473_;
v_isShared_1478_ = v_isSharedCheck_1515_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1515_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___y_1480_; lean_object* v_snd_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1513_; 
v_snd_1498_ = lean_ctor_get(v_a_1474_, 1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_a_1474_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; 
v_unused_1514_ = lean_ctor_get(v_a_1474_, 0);
lean_dec(v_unused_1514_);
v___x_1500_ = v_a_1474_;
v_isShared_1501_ = v_isSharedCheck_1513_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_snd_1498_);
lean_dec(v_a_1474_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1513_;
goto v_resetjp_1499_;
}
v___jp_1479_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; uint8_t v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1481_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_1482_ = l_Lake_PartialBuildKey_toString(v_self_1463_);
v___x_1483_ = lean_string_append(v___x_1481_, v___x_1482_);
lean_dec_ref(v___x_1482_);
v___x_1484_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_1485_ = lean_string_append(v___x_1483_, v___x_1484_);
v___x_1486_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__2);
v___x_1487_ = lean_string_append(v___x_1485_, v___x_1486_);
v___x_1488_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_1489_ = lean_string_append(v___x_1487_, v___x_1488_);
v___x_1490_ = lean_string_append(v___x_1489_, v___y_1480_);
lean_dec_ref(v___y_1480_);
v___x_1491_ = 3;
v___x_1492_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1492_, 0, v___x_1490_);
lean_ctor_set_uint8(v___x_1492_, sizeof(void*)*1, v___x_1491_);
v___x_1493_ = lean_array_get_size(v_a_1475_);
v___x_1494_ = lean_array_push(v_a_1475_, v___x_1492_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 1);
lean_ctor_set(v___x_1477_, 1, v___x_1494_);
lean_ctor_set(v___x_1477_, 0, v___x_1493_);
v___x_1496_ = v___x_1477_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v___x_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
v_resetjp_1499_:
{
lean_object* v_kind_1502_; uint8_t v___x_1503_; 
v_kind_1502_ = lean_ctor_get(v_snd_1498_, 1);
v___x_1503_ = lean_name_eq(v_kind_1502_, v_name_1471_);
if (v___x_1503_ == 0)
{
uint8_t v___x_1504_; 
lean_inc(v_kind_1502_);
lean_del_object(v___x_1500_);
lean_dec(v_snd_1498_);
v___x_1504_ = l_Lean_Name_isAnonymous(v_kind_1502_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1505_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_1506_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_1502_, v___x_1472_);
v___x_1507_ = lean_string_append(v___x_1505_, v___x_1506_);
lean_dec_ref(v___x_1506_);
v___x_1508_ = lean_string_append(v___x_1507_, v___x_1505_);
v___y_1480_ = v___x_1508_;
goto v___jp_1479_;
}
else
{
lean_object* v___x_1509_; 
lean_dec(v_kind_1502_);
v___x_1509_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_1480_ = v___x_1509_;
goto v___jp_1479_;
}
}
else
{
lean_object* v___x_1511_; 
lean_del_object(v___x_1477_);
lean_dec_ref(v_self_1463_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v_a_1475_);
lean_ctor_set(v___x_1500_, 0, v_snd_1498_);
v___x_1511_ = v___x_1500_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_snd_1498_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_a_1475_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec_ref(v_self_1463_);
v_a_1516_ = lean_ctor_get(v___x_1473_, 0);
v_a_1517_ = lean_ctor_get(v___x_1473_, 1);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1473_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_inc(v_a_1516_);
lean_dec(v___x_1473_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1516_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___boxed(lean_object* v_defaultPkg_1525_, lean_object* v_self_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v_defaultPkg_1525_, v_self_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec(v_a_1529_);
lean_dec(v_a_1528_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(lean_object* v___x_1535_, size_t v_sz_1536_, size_t v_i_1537_, lean_object* v_bs_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
uint8_t v___x_1546_; 
v___x_1546_ = lean_usize_dec_lt(v_i_1537_, v_sz_1536_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
lean_dec_ref(v___y_1539_);
lean_dec_ref(v___x_1535_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v_bs_1538_);
lean_ctor_set(v___x_1547_, 1, v___y_1544_);
return v___x_1547_;
}
else
{
lean_object* v_v_1548_; lean_object* v___x_1549_; lean_object* v_bs_x27_1550_; lean_object* v___x_1551_; 
v_v_1548_ = lean_array_uget(v_bs_1538_, v_i_1537_);
v___x_1549_ = lean_unsigned_to_nat(0u);
v_bs_x27_1550_ = lean_array_uset(v_bs_1538_, v_i_1537_, v___x_1549_);
lean_inc_ref(v___y_1539_);
lean_inc_ref(v___x_1535_);
v___x_1551_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_1535_, v_v_1548_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v_a_1553_; size_t v___x_1554_; size_t v___x_1555_; lean_object* v___x_1556_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
v_a_1553_ = lean_ctor_get(v___x_1551_, 1);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1551_, 2);
v___x_1554_ = ((size_t)1ULL);
v___x_1555_ = lean_usize_add(v_i_1537_, v___x_1554_);
v___x_1556_ = lean_array_uset(v_bs_x27_1550_, v_i_1537_, v_a_1552_);
v_i_1537_ = v___x_1555_;
v_bs_1538_ = v___x_1556_;
v___y_1544_ = v_a_1553_;
goto _start;
}
else
{
lean_object* v_a_1558_; lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec_ref(v_bs_x27_1550_);
lean_dec_ref(v___y_1539_);
lean_dec_ref(v___x_1535_);
v_a_1558_ = lean_ctor_get(v___x_1551_, 0);
v_a_1559_ = lean_ctor_get(v___x_1551_, 1);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1551_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_inc(v_a_1558_);
lean_dec(v___x_1551_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1558_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2___boxed(lean_object* v___x_1567_, lean_object* v_sz_1568_, lean_object* v_i_1569_, lean_object* v_bs_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
size_t v_sz_boxed_1578_; size_t v_i_boxed_1579_; lean_object* v_res_1580_; 
v_sz_boxed_1578_ = lean_unbox_usize(v_sz_1568_);
lean_dec(v_sz_1568_);
v_i_boxed_1579_ = lean_unbox_usize(v_i_1569_);
lean_dec(v_i_1569_);
v_res_1580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v___x_1567_, v_sz_boxed_1578_, v_i_boxed_1579_, v_bs_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec(v___y_1572_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(lean_object* v_a_1581_, lean_object* v_as_1582_, size_t v_i_1583_, size_t v_stop_1584_, lean_object* v_b_1585_, lean_object* v___y_1586_){
_start:
{
uint8_t v___x_1588_; 
v___x_1588_ = lean_usize_dec_eq(v_i_1583_, v_stop_1584_);
if (v___x_1588_ == 0)
{
lean_object* v_log_1589_; uint8_t v_action_1590_; uint8_t v_wantsRebuild_1591_; lean_object* v_trace_1592_; lean_object* v_buildTime_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_log_1589_ = lean_ctor_get(v___y_1586_, 0);
v_action_1590_ = lean_ctor_get_uint8(v___y_1586_, sizeof(void*)*3);
v_wantsRebuild_1591_ = lean_ctor_get_uint8(v___y_1586_, sizeof(void*)*3 + 1);
v_trace_1592_ = lean_ctor_get(v___y_1586_, 1);
v_buildTime_1593_ = lean_ctor_get(v___y_1586_, 2);
v___x_1594_ = lean_array_uget_borrowed(v_as_1582_, v_i_1583_);
v___x_1595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00__private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig_spec__0_spec__0___closed__0));
lean_inc(v___x_1594_);
v___x_1596_ = lean_string_append(v___x_1594_, v___x_1595_);
v___x_1597_ = lean_io_prim_handle_put_str(v_a_1581_, v___x_1596_);
lean_dec_ref(v___x_1596_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; size_t v___x_1599_; size_t v___x_1600_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v___x_1597_, 1);
v___x_1599_ = ((size_t)1ULL);
v___x_1600_ = lean_usize_add(v_i_1583_, v___x_1599_);
v_i_1583_ = v___x_1600_;
v_b_1585_ = v_a_1598_;
goto _start;
}
else
{
lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1615_; 
lean_inc(v_buildTime_1593_);
lean_inc_ref(v_trace_1592_);
lean_inc_ref(v_log_1589_);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___y_1586_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; lean_object* v_unused_1617_; lean_object* v_unused_1618_; 
v_unused_1616_ = lean_ctor_get(v___y_1586_, 2);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v___y_1586_, 1);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v___y_1586_, 0);
lean_dec(v_unused_1618_);
v___x_1603_ = v___y_1586_;
v_isShared_1604_ = v_isSharedCheck_1615_;
goto v_resetjp_1602_;
}
else
{
lean_dec(v___y_1586_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1615_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v_a_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v_a_1605_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1597_, 1);
v___x_1606_ = lean_io_error_to_string(v_a_1605_);
v___x_1607_ = 3;
v___x_1608_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set_uint8(v___x_1608_, sizeof(void*)*1, v___x_1607_);
v___x_1609_ = lean_array_get_size(v_log_1589_);
v___x_1610_ = lean_array_push(v_log_1589_, v___x_1608_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1610_);
v___x_1612_ = v___x_1603_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_trace_1592_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_buildTime_1593_);
lean_ctor_set_uint8(v_reuseFailAlloc_1614_, sizeof(void*)*3, v_action_1590_);
lean_ctor_set_uint8(v_reuseFailAlloc_1614_, sizeof(void*)*3 + 1, v_wantsRebuild_1591_);
v___x_1612_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1609_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
return v___x_1613_;
}
}
}
}
else
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v_b_1585_);
lean_ctor_set(v___x_1619_, 1, v___y_1586_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg___boxed(lean_object* v_a_1620_, lean_object* v_as_1621_, lean_object* v_i_1622_, lean_object* v_stop_1623_, lean_object* v_b_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
size_t v_i_boxed_1627_; size_t v_stop_boxed_1628_; lean_object* v_res_1629_; 
v_i_boxed_1627_ = lean_unbox_usize(v_i_1622_);
lean_dec(v_i_1622_);
v_stop_boxed_1628_ = lean_unbox_usize(v_stop_1623_);
lean_dec(v_stop_1623_);
v_res_1629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1620_, v_as_1621_, v_i_boxed_1627_, v_stop_boxed_1628_, v_b_1624_, v___y_1625_);
lean_dec_ref(v_as_1621_);
lean_dec(v_a_1620_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(uint8_t v_bootstrap_1630_, lean_object* v___y_1631_, lean_object* v_oFiles_1632_, uint8_t v_shouldExport_1633_, uint8_t v___x_1634_, size_t v___x_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
if (v_bootstrap_1630_ == 0)
{
lean_object* v_toContext_1643_; lean_object* v_lakeEnv_1644_; lean_object* v_lean_1645_; lean_object* v_log_1646_; uint8_t v_action_1647_; uint8_t v_wantsRebuild_1648_; lean_object* v_trace_1649_; lean_object* v_buildTime_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1680_; 
v_toContext_1643_ = lean_ctor_get(v___y_1640_, 1);
v_lakeEnv_1644_ = lean_ctor_get(v_toContext_1643_, 0);
v_lean_1645_ = lean_ctor_get(v_lakeEnv_1644_, 1);
v_log_1646_ = lean_ctor_get(v___y_1641_, 0);
v_action_1647_ = lean_ctor_get_uint8(v___y_1641_, sizeof(void*)*3);
v_wantsRebuild_1648_ = lean_ctor_get_uint8(v___y_1641_, sizeof(void*)*3 + 1);
v_trace_1649_ = lean_ctor_get(v___y_1641_, 1);
v_buildTime_1650_ = lean_ctor_get(v___y_1641_, 2);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___y_1641_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1652_ = v___y_1641_;
v_isShared_1653_ = v_isSharedCheck_1680_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_buildTime_1650_);
lean_inc(v_trace_1649_);
lean_inc(v_log_1646_);
lean_dec(v___y_1641_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1680_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v_ar_1654_; lean_object* v___x_1655_; 
v_ar_1654_ = lean_ctor_get(v_lean_1645_, 13);
lean_inc_ref(v_ar_1654_);
v___x_1655_ = l_Lake_compileStaticLib(v___y_1631_, v_oFiles_1632_, v_ar_1654_, v_bootstrap_1630_, v_log_1646_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1667_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_a_1657_ = lean_ctor_get(v___x_1655_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1659_ = v___x_1655_;
v_isShared_1660_ = v_isSharedCheck_1667_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1667_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v_a_1657_);
v___x_1662_ = v___x_1652_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1657_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_trace_1649_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_buildTime_1650_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*3, v_action_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1666_, sizeof(void*)*3 + 1, v_wantsRebuild_1648_);
v___x_1662_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1664_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v___x_1662_);
v___x_1664_ = v___x_1659_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1656_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1679_; 
v_a_1668_ = lean_ctor_get(v___x_1655_, 0);
v_a_1669_ = lean_ctor_get(v___x_1655_, 1);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1671_ = v___x_1655_;
v_isShared_1672_ = v_isSharedCheck_1679_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_inc(v_a_1668_);
lean_dec(v___x_1655_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1679_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 0, v_a_1669_);
v___x_1674_ = v___x_1652_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1669_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_trace_1649_);
lean_ctor_set(v_reuseFailAlloc_1678_, 2, v_buildTime_1650_);
lean_ctor_set_uint8(v_reuseFailAlloc_1678_, sizeof(void*)*3, v_action_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1678_, sizeof(void*)*3 + 1, v_wantsRebuild_1648_);
v___x_1674_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1676_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 1, v___x_1674_);
v___x_1676_ = v___x_1671_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1668_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
}
else
{
uint8_t v___x_1681_; 
v___x_1681_ = l_System_Platform_isOSX;
if (v___x_1681_ == 0)
{
uint8_t v___x_1682_; 
v___x_1682_ = l_System_Platform_isWindows;
if (v___x_1682_ == 0)
{
lean_object* v_toContext_1683_; lean_object* v_lakeEnv_1684_; lean_object* v_lean_1685_; lean_object* v_log_1686_; uint8_t v_action_1687_; uint8_t v_wantsRebuild_1688_; lean_object* v_trace_1689_; lean_object* v_buildTime_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1720_; 
v_toContext_1683_ = lean_ctor_get(v___y_1640_, 1);
v_lakeEnv_1684_ = lean_ctor_get(v_toContext_1683_, 0);
v_lean_1685_ = lean_ctor_get(v_lakeEnv_1684_, 1);
v_log_1686_ = lean_ctor_get(v___y_1641_, 0);
v_action_1687_ = lean_ctor_get_uint8(v___y_1641_, sizeof(void*)*3);
v_wantsRebuild_1688_ = lean_ctor_get_uint8(v___y_1641_, sizeof(void*)*3 + 1);
v_trace_1689_ = lean_ctor_get(v___y_1641_, 1);
v_buildTime_1690_ = lean_ctor_get(v___y_1641_, 2);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___y_1641_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1692_ = v___y_1641_;
v_isShared_1693_ = v_isSharedCheck_1720_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_buildTime_1690_);
lean_inc(v_trace_1689_);
lean_inc(v_log_1686_);
lean_dec(v___y_1641_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1720_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v_ar_1694_; lean_object* v___x_1695_; 
v_ar_1694_ = lean_ctor_get(v_lean_1685_, 13);
lean_inc_ref(v_ar_1694_);
v___x_1695_ = l_Lake_compileStaticLib(v___y_1631_, v_oFiles_1632_, v_ar_1694_, v___x_1682_, v_log_1686_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1707_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
v_a_1697_ = lean_ctor_get(v___x_1695_, 1);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1699_ = v___x_1695_;
v_isShared_1700_ = v_isSharedCheck_1707_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_inc(v_a_1696_);
lean_dec(v___x_1695_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1707_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v_a_1697_);
v___x_1702_ = v___x_1692_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1697_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_trace_1689_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_buildTime_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*3, v_action_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1706_, sizeof(void*)*3 + 1, v_wantsRebuild_1688_);
v___x_1702_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1704_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v___x_1702_);
v___x_1704_ = v___x_1699_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1696_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1719_; 
v_a_1708_ = lean_ctor_get(v___x_1695_, 0);
v_a_1709_ = lean_ctor_get(v___x_1695_, 1);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1711_ = v___x_1695_;
v_isShared_1712_ = v_isSharedCheck_1719_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_inc(v_a_1708_);
lean_dec(v___x_1695_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1719_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v_a_1709_);
v___x_1714_ = v___x_1692_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1709_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_trace_1689_);
lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_buildTime_1690_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, sizeof(void*)*3, v_action_1687_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, sizeof(void*)*3 + 1, v_wantsRebuild_1688_);
v___x_1714_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1716_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 1, v___x_1714_);
v___x_1716_ = v___x_1711_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1708_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
}
}
else
{
lean_object* v_toContext_1721_; lean_object* v_lakeEnv_1722_; lean_object* v_lean_1723_; lean_object* v_log_1724_; uint8_t v_action_1725_; uint8_t v_wantsRebuild_1726_; lean_object* v_trace_1727_; lean_object* v_buildTime_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1758_; 
v_toContext_1721_ = lean_ctor_get(v___y_1640_, 1);
v_lakeEnv_1722_ = lean_ctor_get(v_toContext_1721_, 0);
v_lean_1723_ = lean_ctor_get(v_lakeEnv_1722_, 1);
v_log_1724_ = lean_ctor_get(v___y_1641_, 0);
v_action_1725_ = lean_ctor_get_uint8(v___y_1641_, sizeof(void*)*3);
v_wantsRebuild_1726_ = lean_ctor_get_uint8(v___y_1641_, sizeof(void*)*3 + 1);
v_trace_1727_ = lean_ctor_get(v___y_1641_, 1);
v_buildTime_1728_ = lean_ctor_get(v___y_1641_, 2);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___y_1641_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1730_ = v___y_1641_;
v_isShared_1731_ = v_isSharedCheck_1758_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_buildTime_1728_);
lean_inc(v_trace_1727_);
lean_inc(v_log_1724_);
lean_dec(v___y_1641_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1758_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v_ar_1732_; lean_object* v___x_1733_; 
v_ar_1732_ = lean_ctor_get(v_lean_1723_, 13);
lean_inc_ref(v_ar_1732_);
v___x_1733_ = l_Lake_compileStaticLib(v___y_1631_, v_oFiles_1632_, v_ar_1732_, v_shouldExport_1633_, v_log_1724_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1745_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
v_a_1735_ = lean_ctor_get(v___x_1733_, 1);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1737_ = v___x_1733_;
v_isShared_1738_ = v_isSharedCheck_1745_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_inc(v_a_1734_);
lean_dec(v___x_1733_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1745_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v_a_1735_);
v___x_1740_ = v___x_1730_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1735_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_trace_1727_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v_buildTime_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1744_, sizeof(void*)*3, v_action_1725_);
lean_ctor_set_uint8(v_reuseFailAlloc_1744_, sizeof(void*)*3 + 1, v_wantsRebuild_1726_);
v___x_1740_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1742_; 
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 1, v___x_1740_);
v___x_1742_ = v___x_1737_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1734_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1757_; 
v_a_1746_ = lean_ctor_get(v___x_1733_, 0);
v_a_1747_ = lean_ctor_get(v___x_1733_, 1);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1749_ = v___x_1733_;
v_isShared_1750_ = v_isSharedCheck_1757_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_inc(v_a_1746_);
lean_dec(v___x_1733_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1757_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v_a_1747_);
v___x_1752_ = v___x_1730_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1747_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_trace_1727_);
lean_ctor_set(v_reuseFailAlloc_1756_, 2, v_buildTime_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*3, v_action_1725_);
lean_ctor_set_uint8(v_reuseFailAlloc_1756_, sizeof(void*)*3 + 1, v_wantsRebuild_1726_);
v___x_1752_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1754_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v___x_1752_);
v___x_1754_ = v___x_1749_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1746_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
}
}
else
{
lean_object* v_log_1759_; uint8_t v_action_1760_; uint8_t v_wantsRebuild_1761_; lean_object* v_trace_1762_; lean_object* v_buildTime_1763_; lean_object* v___x_1764_; 
v_log_1759_ = lean_ctor_get(v___y_1641_, 0);
v_action_1760_ = lean_ctor_get_uint8(v___y_1641_, sizeof(void*)*3);
v_wantsRebuild_1761_ = lean_ctor_get_uint8(v___y_1641_, sizeof(void*)*3 + 1);
v_trace_1762_ = lean_ctor_get(v___y_1641_, 1);
v_buildTime_1763_ = lean_ctor_get(v___y_1641_, 2);
lean_inc_ref(v___y_1631_);
v___x_1764_ = l_Lake_createParentDirs(v___y_1631_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v_a_1768_; uint8_t v___x_1816_; lean_object* v___x_1817_; 
lean_dec_ref_known(v___x_1764_, 1);
v___x_1765_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__0));
lean_inc_ref(v___y_1631_);
v___x_1766_ = l_System_FilePath_addExtension(v___y_1631_, v___x_1765_);
v___x_1816_ = 1;
v___x_1817_ = lean_io_prim_handle_mk(v___x_1766_, v___x_1816_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref_known(v___x_1817_, 1);
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = lean_array_get_size(v_oFiles_1632_);
v___x_1821_ = lean_nat_dec_lt(v___x_1819_, v___x_1820_);
if (v___x_1821_ == 0)
{
lean_dec(v_a_1818_);
lean_dec_ref(v_oFiles_1632_);
v_a_1768_ = v___y_1641_;
goto v___jp_1767_;
}
else
{
lean_object* v___x_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = lean_box(0);
v___x_1823_ = lean_usize_of_nat(v___x_1820_);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_1818_, v_oFiles_1632_, v___x_1635_, v___x_1823_, v___x_1822_, v___y_1641_);
lean_dec_ref(v_oFiles_1632_);
lean_dec(v_a_1818_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 1);
lean_inc(v_a_1825_);
lean_dec_ref_known(v___x_1824_, 2);
v_a_1768_ = v_a_1825_;
goto v___jp_1767_;
}
else
{
lean_dec_ref(v___x_1766_);
lean_dec_ref(v___y_1631_);
return v___x_1824_;
}
}
}
else
{
lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1839_; 
lean_inc(v_buildTime_1763_);
lean_inc_ref(v_trace_1762_);
lean_inc_ref(v_log_1759_);
lean_dec_ref(v___x_1766_);
lean_dec_ref(v_oFiles_1632_);
lean_dec_ref(v___y_1631_);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___y_1641_);
if (v_isSharedCheck_1839_ == 0)
{
lean_object* v_unused_1840_; lean_object* v_unused_1841_; lean_object* v_unused_1842_; 
v_unused_1840_ = lean_ctor_get(v___y_1641_, 2);
lean_dec(v_unused_1840_);
v_unused_1841_ = lean_ctor_get(v___y_1641_, 1);
lean_dec(v_unused_1841_);
v_unused_1842_ = lean_ctor_get(v___y_1641_, 0);
lean_dec(v_unused_1842_);
v___x_1827_ = v___y_1641_;
v_isShared_1828_ = v_isSharedCheck_1839_;
goto v_resetjp_1826_;
}
else
{
lean_dec(v___y_1641_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1839_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_a_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; 
v_a_1829_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1817_, 1);
v___x_1830_ = lean_io_error_to_string(v_a_1829_);
v___x_1831_ = 3;
v___x_1832_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*1, v___x_1831_);
v___x_1833_ = lean_array_get_size(v_log_1759_);
v___x_1834_ = lean_array_push(v_log_1759_, v___x_1832_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1834_);
v___x_1836_ = v___x_1827_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_trace_1762_);
lean_ctor_set(v_reuseFailAlloc_1838_, 2, v_buildTime_1763_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, sizeof(void*)*3, v_action_1760_);
lean_ctor_set_uint8(v_reuseFailAlloc_1838_, sizeof(void*)*3 + 1, v_wantsRebuild_1761_);
v___x_1836_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1837_; 
v___x_1837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1833_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
return v___x_1837_;
}
}
}
v___jp_1767_:
{
lean_object* v___x_1769_; lean_object* v_log_1770_; uint8_t v_action_1771_; uint8_t v_wantsRebuild_1772_; lean_object* v_trace_1773_; lean_object* v_buildTime_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1815_; 
v___x_1769_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__1));
v_log_1770_ = lean_ctor_get(v_a_1768_, 0);
v_action_1771_ = lean_ctor_get_uint8(v_a_1768_, sizeof(void*)*3);
v_wantsRebuild_1772_ = lean_ctor_get_uint8(v_a_1768_, sizeof(void*)*3 + 1);
v_trace_1773_ = lean_ctor_get(v_a_1768_, 1);
v_buildTime_1774_ = lean_ctor_get(v_a_1768_, 2);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_a_1768_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1776_ = v_a_1768_;
v_isShared_1777_ = v_isSharedCheck_1815_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_buildTime_1774_);
lean_inc(v_trace_1773_);
lean_inc(v_log_1770_);
lean_dec(v_a_1768_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1815_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1778_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__2));
v___x_1779_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__5));
v___x_1780_ = lean_unsigned_to_nat(5u);
v___x_1781_ = lean_mk_empty_array_with_capacity(v___x_1780_);
lean_dec_ref(v___x_1781_);
v___x_1782_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__7);
v___x_1783_ = lean_array_push(v___x_1782_, v___y_1631_);
v___x_1784_ = lean_array_push(v___x_1783_, v___x_1779_);
v___x_1785_ = lean_array_push(v___x_1784_, v___x_1766_);
v___x_1786_ = lean_box(0);
v___x_1787_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__4___closed__8));
v___x_1788_ = 0;
v___x_1789_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1789_, 0, v___x_1769_);
lean_ctor_set(v___x_1789_, 1, v___x_1778_);
lean_ctor_set(v___x_1789_, 2, v___x_1785_);
lean_ctor_set(v___x_1789_, 3, v___x_1786_);
lean_ctor_set(v___x_1789_, 4, v___x_1787_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*5, v___x_1634_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*5 + 1, v___x_1788_);
v___x_1790_ = l_Lake_proc(v___x_1789_, v___x_1788_, v___x_1786_, v_log_1770_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1802_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_a_1792_ = lean_ctor_get(v___x_1790_, 1);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1794_ = v___x_1790_;
v_isShared_1795_ = v_isSharedCheck_1802_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1802_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v_a_1792_);
v___x_1797_ = v___x_1776_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1792_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_trace_1773_);
lean_ctor_set(v_reuseFailAlloc_1801_, 2, v_buildTime_1774_);
lean_ctor_set_uint8(v_reuseFailAlloc_1801_, sizeof(void*)*3, v_action_1771_);
lean_ctor_set_uint8(v_reuseFailAlloc_1801_, sizeof(void*)*3 + 1, v_wantsRebuild_1772_);
v___x_1797_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1799_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 1, v___x_1797_);
v___x_1799_ = v___x_1794_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1791_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1814_; 
v_a_1803_ = lean_ctor_get(v___x_1790_, 0);
v_a_1804_ = lean_ctor_get(v___x_1790_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1806_ = v___x_1790_;
v_isShared_1807_ = v_isSharedCheck_1814_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_inc(v_a_1803_);
lean_dec(v___x_1790_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1814_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v_a_1804_);
v___x_1809_ = v___x_1776_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1804_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_trace_1773_);
lean_ctor_set(v_reuseFailAlloc_1813_, 2, v_buildTime_1774_);
lean_ctor_set_uint8(v_reuseFailAlloc_1813_, sizeof(void*)*3, v_action_1771_);
lean_ctor_set_uint8(v_reuseFailAlloc_1813_, sizeof(void*)*3 + 1, v_wantsRebuild_1772_);
v___x_1809_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1811_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 1, v___x_1809_);
v___x_1811_ = v___x_1806_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1803_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1856_; 
lean_inc(v_buildTime_1763_);
lean_inc_ref(v_trace_1762_);
lean_inc_ref(v_log_1759_);
lean_dec_ref(v_oFiles_1632_);
lean_dec_ref(v___y_1631_);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___y_1641_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; 
v_unused_1857_ = lean_ctor_get(v___y_1641_, 2);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v___y_1641_, 1);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v___y_1641_, 0);
lean_dec(v_unused_1859_);
v___x_1844_ = v___y_1641_;
v_isShared_1845_ = v_isSharedCheck_1856_;
goto v_resetjp_1843_;
}
else
{
lean_dec(v___y_1641_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1856_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v_a_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
v_a_1846_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1847_ = lean_io_error_to_string(v_a_1846_);
v___x_1848_ = 3;
v___x_1849_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1849_, 0, v___x_1847_);
lean_ctor_set_uint8(v___x_1849_, sizeof(void*)*1, v___x_1848_);
v___x_1850_ = lean_array_get_size(v_log_1759_);
v___x_1851_ = lean_array_push(v_log_1759_, v___x_1849_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1851_);
v___x_1853_ = v___x_1844_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_trace_1762_);
lean_ctor_set(v_reuseFailAlloc_1855_, 2, v_buildTime_1763_);
lean_ctor_set_uint8(v_reuseFailAlloc_1855_, sizeof(void*)*3, v_action_1760_);
lean_ctor_set_uint8(v_reuseFailAlloc_1855_, sizeof(void*)*3 + 1, v_wantsRebuild_1761_);
v___x_1853_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1850_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
return v___x_1854_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed(lean_object* v_bootstrap_1860_, lean_object* v___y_1861_, lean_object* v_oFiles_1862_, lean_object* v_shouldExport_1863_, lean_object* v___x_1864_, lean_object* v___x_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
uint8_t v_bootstrap_boxed_1873_; uint8_t v_shouldExport_boxed_1874_; uint8_t v___x_5813__boxed_1875_; size_t v___x_5814__boxed_1876_; lean_object* v_res_1877_; 
v_bootstrap_boxed_1873_ = lean_unbox(v_bootstrap_1860_);
v_shouldExport_boxed_1874_ = lean_unbox(v_shouldExport_1863_);
v___x_5813__boxed_1875_ = lean_unbox(v___x_1864_);
v___x_5814__boxed_1876_ = lean_unbox_usize(v___x_1865_);
lean_dec(v___x_1865_);
v_res_1877_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0(v_bootstrap_boxed_1873_, v___y_1861_, v_oFiles_1862_, v_shouldExport_boxed_1874_, v___x_5813__boxed_1875_, v___x_5814__boxed_1876_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(uint8_t v_bootstrap_1878_, lean_object* v___y_1879_, uint8_t v_shouldExport_1880_, uint8_t v___x_1881_, size_t v___x_1882_, lean_object* v_oFiles_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___y_1895_; uint8_t v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1891_ = lean_box(v_bootstrap_1878_);
v___x_1892_ = lean_box(v_shouldExport_1880_);
v___x_1893_ = lean_box(v___x_1881_);
v___x_1894_ = lean_box_usize(v___x_1882_);
lean_inc_ref(v___y_1879_);
v___y_1895_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__0___boxed), 13, 6);
lean_closure_set(v___y_1895_, 0, v___x_1891_);
lean_closure_set(v___y_1895_, 1, v___y_1879_);
lean_closure_set(v___y_1895_, 2, v_oFiles_1883_);
lean_closure_set(v___y_1895_, 3, v___x_1892_);
lean_closure_set(v___y_1895_, 4, v___x_1893_);
lean_closure_set(v___y_1895_, 5, v___x_1894_);
v___x_1896_ = 0;
v___x_1897_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__5___closed__0));
v___x_1898_ = l_Lake_buildArtifactUnlessUpToDate(v___y_1879_, v___y_1895_, v___x_1896_, v___x_1897_, v___x_1881_, v___x_1896_, v___x_1896_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1908_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_a_1900_ = lean_ctor_get(v___x_1898_, 1);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1902_ = v___x_1898_;
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1908_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v_path_1904_; lean_object* v___x_1906_; 
v_path_1904_ = lean_ctor_get(v_a_1899_, 1);
lean_inc_ref(v_path_1904_);
lean_dec(v_a_1899_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v_path_1904_);
v___x_1906_ = v___x_1902_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_path_1904_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_a_1900_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
v_a_1909_ = lean_ctor_get(v___x_1898_, 0);
v_a_1910_ = lean_ctor_get(v___x_1898_, 1);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1898_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_inc(v_a_1909_);
lean_dec(v___x_1898_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1909_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed(lean_object* v_bootstrap_1918_, lean_object* v___y_1919_, lean_object* v_shouldExport_1920_, lean_object* v___x_1921_, lean_object* v___x_1922_, lean_object* v_oFiles_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
uint8_t v_bootstrap_boxed_1931_; uint8_t v_shouldExport_boxed_1932_; uint8_t v___x_6213__boxed_1933_; size_t v___x_6214__boxed_1934_; lean_object* v_res_1935_; 
v_bootstrap_boxed_1931_ = lean_unbox(v_bootstrap_1918_);
v_shouldExport_boxed_1932_ = lean_unbox(v_shouldExport_1920_);
v___x_6213__boxed_1933_ = lean_unbox(v___x_1921_);
v___x_6214__boxed_1934_ = lean_unbox_usize(v___x_1922_);
lean_dec(v___x_1922_);
v_res_1935_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1(v_bootstrap_boxed_1931_, v___y_1919_, v_shouldExport_boxed_1932_, v___x_6213__boxed_1933_, v___x_6214__boxed_1934_, v_oFiles_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
lean_dec_ref(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec(v___y_1925_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(lean_object* v_a_1936_, size_t v_sz_1937_, size_t v_i_1938_, lean_object* v_bs_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_usize_dec_lt(v_i_1938_, v_sz_1937_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; 
lean_dec_ref(v___y_1940_);
lean_dec_ref(v_a_1936_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v_bs_1939_);
lean_ctor_set(v___x_1948_, 1, v___y_1945_);
return v___x_1948_;
}
else
{
lean_object* v_v_1949_; lean_object* v___x_1950_; lean_object* v_bs_x27_1951_; lean_object* v___x_1952_; 
v_v_1949_ = lean_array_uget(v_bs_1939_, v_i_1938_);
v___x_1950_ = lean_unsigned_to_nat(0u);
v_bs_x27_1951_ = lean_array_uset(v_bs_1939_, v_i_1938_, v___x_1950_);
lean_inc_ref(v___y_1940_);
lean_inc_ref(v_a_1936_);
v___x_1952_ = l_Lake_ModuleFacet_fetch___redArg(v_v_1949_, v_a_1936_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v_a_1954_; size_t v___x_1955_; size_t v___x_1956_; lean_object* v___x_1957_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
v_a_1954_ = lean_ctor_get(v___x_1952_, 1);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1952_, 2);
v___x_1955_ = ((size_t)1ULL);
v___x_1956_ = lean_usize_add(v_i_1938_, v___x_1955_);
v___x_1957_ = lean_array_uset(v_bs_x27_1951_, v_i_1938_, v_a_1953_);
v_i_1938_ = v___x_1956_;
v_bs_1939_ = v___x_1957_;
v___y_1945_ = v_a_1954_;
goto _start;
}
else
{
lean_object* v_a_1959_; lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_dec_ref(v_bs_x27_1951_);
lean_dec_ref(v___y_1940_);
lean_dec_ref(v_a_1936_);
v_a_1959_ = lean_ctor_get(v___x_1952_, 0);
v_a_1960_ = lean_ctor_get(v___x_1952_, 1);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1952_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_inc(v_a_1959_);
lean_dec(v___x_1952_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1959_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0___boxed(lean_object* v_a_1968_, lean_object* v_sz_1969_, lean_object* v_i_1970_, lean_object* v_bs_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
size_t v_sz_boxed_1979_; size_t v_i_boxed_1980_; lean_object* v_res_1981_; 
v_sz_boxed_1979_ = lean_unbox_usize(v_sz_1969_);
lean_dec(v_sz_1969_);
v_i_boxed_1980_ = lean_unbox_usize(v_i_1970_);
lean_dec(v_i_1970_);
v_res_1981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v_a_1968_, v_sz_boxed_1979_, v_i_boxed_1980_, v_bs_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec(v___y_1973_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(uint8_t v_shouldExport_1982_, lean_object* v_as_1983_, size_t v_i_1984_, size_t v_stop_1985_, lean_object* v_b_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_usize_dec_eq(v_i_1984_, v_stop_1985_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; lean_object* v_lib_1996_; lean_object* v_config_1997_; lean_object* v_nativeFacets_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; size_t v_sz_2001_; size_t v___x_2002_; lean_object* v___x_2003_; 
v___x_1995_ = lean_array_uget_borrowed(v_as_1983_, v_i_1984_);
v_lib_1996_ = lean_ctor_get(v___x_1995_, 0);
v_config_1997_ = lean_ctor_get(v_lib_1996_, 2);
v_nativeFacets_1998_ = lean_ctor_get(v_config_1997_, 8);
v___x_1999_ = lean_box(v_shouldExport_1982_);
lean_inc_ref(v_nativeFacets_1998_);
v___x_2000_ = lean_apply_1(v_nativeFacets_1998_, v___x_1999_);
v_sz_2001_ = lean_array_size(v___x_2000_);
v___x_2002_ = ((size_t)0ULL);
lean_inc_ref(v___y_1987_);
lean_inc(v___x_1995_);
v___x_2003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_1995_, v_sz_2001_, v___x_2002_, v___x_2000_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v_a_2005_; lean_object* v___x_2006_; size_t v___x_2007_; size_t v___x_2008_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
v_a_2005_ = lean_ctor_get(v___x_2003_, 1);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2003_, 2);
v___x_2006_ = l_Array_append___redArg(v_b_1986_, v_a_2004_);
lean_dec(v_a_2004_);
v___x_2007_ = ((size_t)1ULL);
v___x_2008_ = lean_usize_add(v_i_1984_, v___x_2007_);
v_i_1984_ = v___x_2008_;
v_b_1986_ = v___x_2006_;
v___y_1992_ = v_a_2005_;
goto _start;
}
else
{
lean_dec_ref(v___y_1987_);
lean_dec_ref(v_b_1986_);
return v___x_2003_;
}
}
else
{
lean_object* v___x_2010_; 
lean_dec_ref(v___y_1987_);
v___x_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2010_, 0, v_b_1986_);
lean_ctor_set(v___x_2010_, 1, v___y_1992_);
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4___boxed(lean_object* v_shouldExport_2011_, lean_object* v_as_2012_, lean_object* v_i_2013_, lean_object* v_stop_2014_, lean_object* v_b_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
uint8_t v_shouldExport_boxed_2023_; size_t v_i_boxed_2024_; size_t v_stop_boxed_2025_; lean_object* v_res_2026_; 
v_shouldExport_boxed_2023_ = lean_unbox(v_shouldExport_2011_);
v_i_boxed_2024_ = lean_unbox_usize(v_i_2013_);
lean_dec(v_i_2013_);
v_stop_boxed_2025_ = lean_unbox_usize(v_stop_2014_);
lean_dec(v_stop_2014_);
v_res_2026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_boxed_2023_, v_as_2012_, v_i_boxed_2024_, v_stop_boxed_2025_, v_b_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v_as_2012_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(lean_object* v_config_2027_, lean_object* v_config_2028_, uint8_t v_shouldExport_2029_, uint8_t v___x_2030_, lean_object* v___x_2031_, lean_object* v___x_2032_, lean_object* v_pkg_2033_, lean_object* v_dir_2034_, lean_object* v_self_2035_, lean_object* v___x_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
size_t v___y_2045_; uint8_t v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v_a_2065_; lean_object* v_a_2066_; lean_object* v___x_2108_; 
lean_inc_ref(v___y_2037_);
lean_inc_ref(v___y_2041_);
lean_inc(v___y_2040_);
lean_inc(v___y_2039_);
lean_inc(v___x_2032_);
v___x_2108_ = lean_apply_7(v___y_2037_, v___x_2036_, v___x_2032_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, lean_box(0));
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v_a_2110_; lean_object* v___x_2111_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
v_a_2110_ = lean_ctor_get(v___x_2108_, 1);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2108_, 2);
v___x_2111_ = l_Lake_Job_await___redArg(v_a_2109_, v_a_2110_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v_a_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; uint8_t v___x_2117_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
v_a_2113_ = lean_ctor_get(v___x_2111_, 1);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2111_, 2);
v___x_2114_ = lean_unsigned_to_nat(0u);
v___x_2115_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_2116_ = lean_array_get_size(v_a_2112_);
v___x_2117_ = lean_nat_dec_lt(v___x_2114_, v___x_2116_);
if (v___x_2117_ == 0)
{
lean_dec(v_a_2112_);
v_a_2065_ = v___x_2115_;
v_a_2066_ = v_a_2113_;
goto v___jp_2064_;
}
else
{
size_t v___x_2118_; size_t v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = ((size_t)0ULL);
v___x_2119_ = lean_usize_of_nat(v___x_2116_);
lean_inc_ref(v___y_2037_);
v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__4(v_shouldExport_2029_, v_a_2112_, v___x_2118_, v___x_2119_, v___x_2115_, v___y_2037_, v___x_2032_, v___y_2039_, v___y_2040_, v___y_2041_, v_a_2113_);
lean_dec(v_a_2112_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v_a_2122_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
v_a_2122_ = lean_ctor_get(v___x_2120_, 1);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2120_, 2);
v_a_2065_ = v_a_2121_;
v_a_2066_ = v_a_2122_;
goto v___jp_2064_;
}
else
{
lean_object* v_a_2123_; lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v___y_2037_);
lean_dec_ref(v_self_2035_);
lean_dec_ref(v_dir_2034_);
lean_dec_ref(v_pkg_2033_);
lean_dec(v___x_2032_);
lean_dec(v___x_2031_);
lean_dec_ref(v_config_2027_);
v_a_2123_ = lean_ctor_get(v___x_2120_, 0);
v_a_2124_ = lean_ctor_get(v___x_2120_, 1);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2120_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_inc(v_a_2123_);
lean_dec(v___x_2120_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2123_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v___y_2037_);
lean_dec_ref(v_self_2035_);
lean_dec_ref(v_dir_2034_);
lean_dec_ref(v_pkg_2033_);
lean_dec(v___x_2032_);
lean_dec(v___x_2031_);
lean_dec_ref(v_config_2027_);
v_a_2132_ = lean_ctor_get(v___x_2111_, 0);
v_a_2133_ = lean_ctor_get(v___x_2111_, 1);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2111_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_inc(v_a_2132_);
lean_dec(v___x_2111_);
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
else
{
lean_object* v_a_2141_; lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec_ref(v___y_2037_);
lean_dec_ref(v_self_2035_);
lean_dec_ref(v_dir_2034_);
lean_dec_ref(v_pkg_2033_);
lean_dec(v___x_2032_);
lean_dec(v___x_2031_);
lean_dec_ref(v_config_2027_);
v_a_2141_ = lean_ctor_get(v___x_2108_, 0);
v_a_2142_ = lean_ctor_get(v___x_2108_, 1);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2108_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_inc(v_a_2141_);
lean_dec(v___x_2108_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2141_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
v___jp_2044_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___f_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2051_ = lean_box(v___y_2046_);
v___x_2052_ = lean_box(v_shouldExport_2029_);
v___x_2053_ = lean_box(v___x_2030_);
v___x_2054_ = lean_box_usize(v___y_2045_);
v___f_2055_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2055_, 0, v___x_2051_);
lean_closure_set(v___f_2055_, 1, v___y_2050_);
lean_closure_set(v___f_2055_, 2, v___x_2052_);
lean_closure_set(v___f_2055_, 3, v___x_2053_);
lean_closure_set(v___f_2055_, 4, v___x_2054_);
v___x_2056_ = l_Array_append___redArg(v___y_2048_, v___y_2049_);
lean_dec_ref(v___y_2049_);
v___x_2057_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__0));
v___x_2058_ = l_Lake_Job_collectArray___redArg(v___x_2056_, v___x_2057_);
lean_dec_ref(v___x_2056_);
v___x_2059_ = lean_unsigned_to_nat(0u);
v___x_2060_ = 0;
v___x_2061_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2062_ = l_Lake_Job_mapM___redArg(v___x_2031_, v___x_2058_, v___f_2055_, v___x_2059_, v___x_2060_, v___y_2037_, v___x_2032_, v___y_2039_, v___y_2040_, v___y_2041_, v___x_2061_);
lean_dec(v___x_2032_);
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v___y_2047_);
return v___x_2063_;
}
v___jp_2064_:
{
lean_object* v_toLeanConfig_2067_; lean_object* v_toLeanConfig_2068_; uint8_t v_bootstrap_2069_; lean_object* v_buildDir_2070_; lean_object* v_nativeLibDir_2071_; lean_object* v_moreLinkObjs_2072_; lean_object* v_moreLinkObjs_2073_; lean_object* v___x_2074_; size_t v_sz_2075_; size_t v___x_2076_; lean_object* v___x_2077_; 
v_toLeanConfig_2067_ = lean_ctor_get(v_config_2027_, 1);
lean_inc_ref(v_toLeanConfig_2067_);
v_toLeanConfig_2068_ = lean_ctor_get(v_config_2028_, 0);
v_bootstrap_2069_ = lean_ctor_get_uint8(v_config_2027_, sizeof(void*)*28);
v_buildDir_2070_ = lean_ctor_get(v_config_2027_, 5);
lean_inc_ref(v_buildDir_2070_);
v_nativeLibDir_2071_ = lean_ctor_get(v_config_2027_, 7);
lean_inc_ref(v_nativeLibDir_2071_);
lean_dec_ref(v_config_2027_);
v_moreLinkObjs_2072_ = lean_ctor_get(v_toLeanConfig_2067_, 6);
lean_inc_ref(v_moreLinkObjs_2072_);
lean_dec_ref(v_toLeanConfig_2067_);
v_moreLinkObjs_2073_ = lean_ctor_get(v_toLeanConfig_2068_, 6);
v___x_2074_ = l_Array_append___redArg(v_moreLinkObjs_2072_, v_moreLinkObjs_2073_);
v_sz_2075_ = lean_array_size(v___x_2074_);
v___x_2076_ = ((size_t)0ULL);
lean_inc_ref(v___y_2037_);
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__2(v_pkg_2033_, v_sz_2075_, v___x_2076_, v___x_2074_, v___y_2037_, v___x_2032_, v___y_2039_, v___y_2040_, v___y_2041_, v_a_2066_);
if (lean_obj_tag(v___x_2077_) == 0)
{
if (v_shouldExport_2029_ == 0)
{
lean_object* v_a_2078_; lean_object* v_a_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
v_a_2079_ = lean_ctor_get(v___x_2077_, 1);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2077_, 2);
v___x_2080_ = l_System_FilePath_normalize(v_buildDir_2070_);
v___x_2081_ = l_Lake_joinRelative(v_dir_2034_, v___x_2080_);
v___x_2082_ = l_System_FilePath_normalize(v_nativeLibDir_2071_);
v___x_2083_ = l_Lake_joinRelative(v___x_2081_, v___x_2082_);
v___x_2084_ = l_Lake_LeanLib_libName(v_self_2035_);
v___x_2085_ = l_Lake_nameToStaticLib(v___x_2084_, v_shouldExport_2029_);
v___x_2086_ = l_Lake_joinRelative(v___x_2083_, v___x_2085_);
v___y_2045_ = v___x_2076_;
v___y_2046_ = v_bootstrap_2069_;
v___y_2047_ = v_a_2079_;
v___y_2048_ = v_a_2065_;
v___y_2049_ = v_a_2078_;
v___y_2050_ = v___x_2086_;
goto v___jp_2044_;
}
else
{
lean_object* v_a_2087_; lean_object* v_a_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_a_2087_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2087_);
v_a_2088_ = lean_ctor_get(v___x_2077_, 1);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2077_, 2);
v___x_2089_ = l_System_FilePath_normalize(v_buildDir_2070_);
v___x_2090_ = l_Lake_joinRelative(v_dir_2034_, v___x_2089_);
v___x_2091_ = l_System_FilePath_normalize(v_nativeLibDir_2071_);
v___x_2092_ = l_Lake_joinRelative(v___x_2090_, v___x_2091_);
v___x_2093_ = l_Lake_LeanLib_libName(v_self_2035_);
v___x_2094_ = 0;
v___x_2095_ = l_Lake_nameToStaticLib(v___x_2093_, v___x_2094_);
v___x_2096_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__1));
v___x_2097_ = l_System_FilePath_addExtension(v___x_2095_, v___x_2096_);
v___x_2098_ = l_Lake_joinRelative(v___x_2092_, v___x_2097_);
v___y_2045_ = v___x_2076_;
v___y_2046_ = v_bootstrap_2069_;
v___y_2047_ = v_a_2088_;
v___y_2048_ = v_a_2065_;
v___y_2049_ = v_a_2087_;
v___y_2050_ = v___x_2098_;
goto v___jp_2044_;
}
}
else
{
lean_object* v_a_2099_; lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref(v_nativeLibDir_2071_);
lean_dec_ref(v_buildDir_2070_);
lean_dec_ref(v_a_2065_);
lean_dec_ref(v___y_2037_);
lean_dec_ref(v_self_2035_);
lean_dec_ref(v_dir_2034_);
lean_dec(v___x_2032_);
lean_dec(v___x_2031_);
v_a_2099_ = lean_ctor_get(v___x_2077_, 0);
v_a_2100_ = lean_ctor_get(v___x_2077_, 1);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2077_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_inc(v_a_2099_);
lean_dec(v___x_2077_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2099_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed(lean_object** _args){
lean_object* v_config_2150_ = _args[0];
lean_object* v_config_2151_ = _args[1];
lean_object* v_shouldExport_2152_ = _args[2];
lean_object* v___x_2153_ = _args[3];
lean_object* v___x_2154_ = _args[4];
lean_object* v___x_2155_ = _args[5];
lean_object* v_pkg_2156_ = _args[6];
lean_object* v_dir_2157_ = _args[7];
lean_object* v_self_2158_ = _args[8];
lean_object* v___x_2159_ = _args[9];
lean_object* v___y_2160_ = _args[10];
lean_object* v___y_2161_ = _args[11];
lean_object* v___y_2162_ = _args[12];
lean_object* v___y_2163_ = _args[13];
lean_object* v___y_2164_ = _args[14];
lean_object* v___y_2165_ = _args[15];
lean_object* v___y_2166_ = _args[16];
_start:
{
uint8_t v_shouldExport_boxed_2167_; uint8_t v___x_6411__boxed_2168_; lean_object* v_res_2169_; 
v_shouldExport_boxed_2167_ = lean_unbox(v_shouldExport_2152_);
v___x_6411__boxed_2168_ = lean_unbox(v___x_2153_);
v_res_2169_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2(v_config_2150_, v_config_2151_, v_shouldExport_boxed_2167_, v___x_6411__boxed_2168_, v___x_2154_, v___x_2155_, v_pkg_2156_, v_dir_2157_, v_self_2158_, v___x_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec(v_config_2151_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(lean_object* v___y_2170_, lean_object* v_self_2171_, uint8_t v_shouldExport_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_toBuildConfig_2179_; lean_object* v_registeredJobs_2180_; uint8_t v_verbosity_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; uint8_t v___x_2186_; lean_object* v___y_2188_; 
v_toBuildConfig_2179_ = lean_ctor_get(v_a_2176_, 0);
v_registeredJobs_2180_ = lean_ctor_get(v_a_2176_, 4);
v_verbosity_2181_ = lean_ctor_get_uint8(v_toBuildConfig_2179_, sizeof(void*)*4 + 4);
v___x_2182_ = l_Lake_instDataKindFilePath;
v___x_2183_ = l_Lake_Verbosity_ctorIdx(v_verbosity_2181_);
v___x_2184_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0, &l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__0);
v___x_2185_ = lean_nat_dec_eq(v___x_2183_, v___x_2184_);
lean_dec(v___x_2183_);
v___x_2186_ = 1;
if (v___x_2185_ == 0)
{
lean_object* v___x_2233_; 
v___x_2233_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v___y_2188_ = v___x_2233_;
goto v___jp_2187_;
}
else
{
if (v_shouldExport_2172_ == 0)
{
lean_object* v___x_2234_; 
v___x_2234_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__2));
v___y_2188_ = v___x_2234_;
goto v___jp_2187_;
}
else
{
lean_object* v___x_2235_; 
v___x_2235_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__3));
v___y_2188_ = v___x_2235_;
goto v___jp_2187_;
}
}
v___jp_2187_:
{
lean_object* v_pkg_2189_; lean_object* v_name_2190_; lean_object* v_config_2191_; lean_object* v_keyName_2192_; lean_object* v_dir_2193_; lean_object* v_config_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___f_2206_; uint8_t v___x_2207_; lean_object* v___x_2208_; 
v_pkg_2189_ = lean_ctor_get(v_self_2171_, 0);
lean_inc_ref_n(v_pkg_2189_, 2);
v_name_2190_ = lean_ctor_get(v_self_2171_, 1);
v_config_2191_ = lean_ctor_get(v_self_2171_, 2);
lean_inc(v_config_2191_);
v_keyName_2192_ = lean_ctor_get(v_pkg_2189_, 2);
v_dir_2193_ = lean_ctor_get(v_pkg_2189_, 4);
lean_inc_ref(v_dir_2193_);
v_config_2194_ = lean_ctor_get(v_pkg_2189_, 6);
lean_inc_ref(v_config_2194_);
lean_inc_n(v_name_2190_, 2);
v___x_2195_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2190_, v___x_2186_);
v___x_2196_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___closed__1));
v___x_2197_ = lean_string_append(v___x_2195_, v___x_2196_);
v___x_2198_ = lean_string_append(v___x_2197_, v___y_2188_);
v___x_2199_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_2192_);
v___x_2200_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2200_, 0, v_keyName_2192_);
lean_ctor_set(v___x_2200_, 1, v_name_2190_);
v___x_2201_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_2171_);
v___x_2202_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
lean_ctor_set(v___x_2202_, 2, v_self_2171_);
lean_ctor_set(v___x_2202_, 3, v___x_2199_);
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v_pkg_2189_);
v___x_2204_ = lean_box(v_shouldExport_2172_);
v___x_2205_ = lean_box(v___x_2186_);
v___f_2206_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___lam__2___boxed), 17, 10);
lean_closure_set(v___f_2206_, 0, v_config_2194_);
lean_closure_set(v___f_2206_, 1, v_config_2191_);
lean_closure_set(v___f_2206_, 2, v___x_2204_);
lean_closure_set(v___f_2206_, 3, v___x_2205_);
lean_closure_set(v___f_2206_, 4, v___x_2182_);
lean_closure_set(v___f_2206_, 5, v___x_2203_);
lean_closure_set(v___f_2206_, 6, v_pkg_2189_);
lean_closure_set(v___f_2206_, 7, v_dir_2193_);
lean_closure_set(v___f_2206_, 8, v_self_2171_);
lean_closure_set(v___f_2206_, 9, v___x_2202_);
v___x_2207_ = 0;
v___x_2208_ = l_Lake_ensureJob___redArg(v___x_2182_, v___f_2206_, v___y_2170_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2232_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
v_a_2210_ = lean_ctor_get(v___x_2208_, 1);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2212_ = v___x_2208_;
v_isShared_2213_ = v_isSharedCheck_2232_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_inc(v_a_2209_);
lean_dec(v___x_2208_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2232_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v_task_2214_; lean_object* v_kind_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2230_; 
v_task_2214_ = lean_ctor_get(v_a_2209_, 0);
v_kind_2215_ = lean_ctor_get(v_a_2209_, 1);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_a_2209_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v_a_2209_, 2);
lean_dec(v_unused_2231_);
v___x_2217_ = v_a_2209_;
v_isShared_2218_ = v_isSharedCheck_2230_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_kind_2215_);
lean_inc(v_task_2214_);
lean_dec(v_a_2209_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2230_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v_job_2220_; 
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 2, v___x_2198_);
v_job_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_task_2214_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_kind_2215_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v___x_2198_);
v_job_2220_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
lean_ctor_set_uint8(v_job_2220_, sizeof(void*)*3, v___x_2207_);
v___x_2221_ = lean_st_ref_take(v_registeredJobs_2180_);
lean_inc_ref(v_job_2220_);
v___x_2222_ = l_Lake_Job_toOpaque___redArg(v_job_2220_);
v___x_2223_ = lean_array_push(v___x_2221_, v___x_2222_);
v___x_2224_ = lean_st_ref_put(v_registeredJobs_2180_, v___x_2223_);
v___x_2225_ = l_Lake_Job_renew___redArg(v_job_2220_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2225_);
v___x_2227_ = v___x_2212_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_a_2210_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2198_);
return v___x_2208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0___boxed(lean_object* v___y_2236_, lean_object* v_self_2237_, lean_object* v_shouldExport_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
uint8_t v_shouldExport_boxed_2245_; lean_object* v_res_2246_; 
v_shouldExport_boxed_2245_ = lean_unbox(v_shouldExport_2238_);
v_res_2246_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2236_, v_self_2237_, v_shouldExport_boxed_2245_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec(v_a_2240_);
lean_dec(v_a_2239_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0(lean_object* v_x_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
uint8_t v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = 0;
v___x_2256_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2248_, v_x_2247_, v___x_2255_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticFacetConfig___lam__0___boxed(lean_object* v_x_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lake_LeanLib_staticFacetConfig___lam__0(v_x_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec(v___y_2259_);
return v_res_2265_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___f_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___f_2268_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2269_ = 1;
v___x_2270_ = l_Lake_instDataKindFilePath;
v___f_2271_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__0));
v___x_2272_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2273_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v___f_2271_);
lean_ctor_set(v___x_2273_, 2, v___x_2270_);
lean_ctor_set(v___x_2273_, 3, v___f_2268_);
lean_ctor_set_uint8(v___x_2273_, sizeof(void*)*4, v___x_2269_);
lean_ctor_set_uint8(v___x_2273_, sizeof(void*)*4 + 1, v___x_2269_);
return v___x_2273_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticFacetConfig(void){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = lean_obj_once(&l_Lake_LeanLib_staticFacetConfig___closed__2, &l_Lake_LeanLib_staticFacetConfig___closed__2_once, _init_l_Lake_LeanLib_staticFacetConfig___closed__2);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(lean_object* v_a_2275_, lean_object* v_as_2276_, size_t v_i_2277_, size_t v_stop_2278_, lean_object* v_b_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___redArg(v_a_2275_, v_as_2276_, v_i_2277_, v_stop_2278_, v_b_2279_, v___y_2285_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3___boxed(lean_object* v_a_2288_, lean_object* v_as_2289_, lean_object* v_i_2290_, lean_object* v_stop_2291_, lean_object* v_b_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
size_t v_i_boxed_2300_; size_t v_stop_boxed_2301_; lean_object* v_res_2302_; 
v_i_boxed_2300_ = lean_unbox_usize(v_i_2290_);
lean_dec(v_i_2290_);
v_stop_boxed_2301_ = lean_unbox_usize(v_stop_2291_);
lean_dec(v_stop_2291_);
v_res_2302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__3(v_a_2288_, v_as_2289_, v_i_boxed_2300_, v_stop_boxed_2301_, v_b_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec_ref(v_as_2289_);
lean_dec(v_a_2288_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0(lean_object* v_x_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
uint8_t v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = 1;
v___x_2312_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0(v___y_2304_, v_x_2303_, v___x_2311_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLib_staticExportFacetConfig___lam__0___boxed(lean_object* v_x_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lake_LeanLib_staticExportFacetConfig___lam__0(v_x_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec(v___y_2315_);
return v_res_2321_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2323_; uint8_t v___x_2324_; lean_object* v___x_2325_; lean_object* v___f_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___f_2323_ = ((lean_object*)(l_Lake_LeanLib_staticFacetConfig___closed__1));
v___x_2324_ = 1;
v___x_2325_ = l_Lake_instDataKindFilePath;
v___f_2326_ = ((lean_object*)(l_Lake_LeanLib_staticExportFacetConfig___closed__0));
v___x_2327_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2328_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
lean_ctor_set(v___x_2328_, 1, v___f_2326_);
lean_ctor_set(v___x_2328_, 2, v___x_2325_);
lean_ctor_set(v___x_2328_, 3, v___f_2323_);
lean_ctor_set_uint8(v___x_2328_, sizeof(void*)*4, v___x_2324_);
lean_ctor_set_uint8(v___x_2328_, sizeof(void*)*4 + 1, v___x_2324_);
return v___x_2328_;
}
}
static lean_object* _init_l_Lake_LeanLib_staticExportFacetConfig(void){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_obj_once(&l_Lake_LeanLib_staticExportFacetConfig___closed__1, &l_Lake_LeanLib_staticExportFacetConfig___closed__1_once, _init_l_Lake_LeanLib_staticExportFacetConfig___closed__1);
return v___x_2329_;
}
}
static lean_object* _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0(void){
_start:
{
uint8_t v___x_2330_; lean_object* v_name_2331_; lean_object* v___x_2332_; 
v___x_2330_ = 1;
v_name_2331_ = l_Lake_instDataKindDynlib;
v___x_2332_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2331_, v___x_2330_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(lean_object* v_defaultPkg_2333_, lean_object* v_self_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v_name_2342_; uint8_t v___x_2343_; lean_object* v___x_2344_; 
v_name_2342_ = l_Lake_instDataKindDynlib;
v___x_2343_ = 1;
lean_inc_ref_n(v_self_2334_, 2);
v___x_2344_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v_defaultPkg_2333_, v_self_2334_, v_self_2334_, v___x_2343_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2386_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_a_2346_ = lean_ctor_get(v___x_2344_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2348_ = v___x_2344_;
v_isShared_2349_ = v_isSharedCheck_2386_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2386_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___y_2351_; lean_object* v_snd_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2384_; 
v_snd_2369_ = lean_ctor_get(v_a_2345_, 1);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_a_2345_);
if (v_isSharedCheck_2384_ == 0)
{
lean_object* v_unused_2385_; 
v_unused_2385_ = lean_ctor_get(v_a_2345_, 0);
lean_dec(v_unused_2385_);
v___x_2371_ = v_a_2345_;
v_isShared_2372_ = v_isSharedCheck_2384_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_snd_2369_);
lean_dec(v_a_2345_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2384_;
goto v_resetjp_2370_;
}
v___jp_2350_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2352_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__0));
v___x_2353_ = l_Lake_PartialBuildKey_toString(v_self_2334_);
v___x_2354_ = lean_string_append(v___x_2352_, v___x_2353_);
lean_dec_ref(v___x_2353_);
v___x_2355_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__1));
v___x_2356_ = lean_string_append(v___x_2354_, v___x_2355_);
v___x_2357_ = lean_obj_once(&l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0, &l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0_once, _init_l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___closed__0);
v___x_2358_ = lean_string_append(v___x_2356_, v___x_2357_);
v___x_2359_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__3));
v___x_2360_ = lean_string_append(v___x_2358_, v___x_2359_);
v___x_2361_ = lean_string_append(v___x_2360_, v___y_2351_);
lean_dec_ref(v___y_2351_);
v___x_2362_ = 3;
v___x_2363_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2363_, 0, v___x_2361_);
lean_ctor_set_uint8(v___x_2363_, sizeof(void*)*1, v___x_2362_);
v___x_2364_ = lean_array_get_size(v_a_2346_);
v___x_2365_ = lean_array_push(v_a_2346_, v___x_2363_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set_tag(v___x_2348_, 1);
lean_ctor_set(v___x_2348_, 1, v___x_2365_);
lean_ctor_set(v___x_2348_, 0, v___x_2364_);
v___x_2367_ = v___x_2348_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
v_resetjp_2370_:
{
lean_object* v_kind_2373_; uint8_t v___x_2374_; 
v_kind_2373_ = lean_ctor_get(v_snd_2369_, 1);
v___x_2374_ = lean_name_eq(v_kind_2373_, v_name_2342_);
if (v___x_2374_ == 0)
{
uint8_t v___x_2375_; 
lean_inc(v_kind_2373_);
lean_del_object(v___x_2371_);
lean_dec(v_snd_2369_);
v___x_2375_ = l_Lean_Name_isAnonymous(v_kind_2373_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2376_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__4));
v___x_2377_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_kind_2373_, v___x_2343_);
v___x_2378_ = lean_string_append(v___x_2376_, v___x_2377_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = lean_string_append(v___x_2378_, v___x_2376_);
v___y_2351_ = v___x_2379_;
goto v___jp_2350_;
}
else
{
lean_object* v___x_2380_; 
lean_dec(v_kind_2373_);
v___x_2380_ = ((lean_object*)(l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1___closed__5));
v___y_2351_ = v___x_2380_;
goto v___jp_2350_;
}
}
else
{
lean_object* v___x_2382_; 
lean_del_object(v___x_2348_);
lean_dec_ref(v_self_2334_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 1, v_a_2346_);
lean_ctor_set(v___x_2371_, 0, v_snd_2369_);
v___x_2382_ = v___x_2371_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_snd_2369_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v_a_2346_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec_ref(v_self_2334_);
v_a_2387_ = lean_ctor_get(v___x_2344_, 0);
v_a_2388_ = lean_ctor_get(v___x_2344_, 1);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2344_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_inc(v_a_2387_);
lean_dec(v___x_2344_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2387_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1___boxed(lean_object* v_defaultPkg_2396_, lean_object* v_self_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v_defaultPkg_2396_, v_self_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec(v_a_2399_);
return v_res_2405_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__0));
v___x_2409_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___closed__2);
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
lean_ctor_set(v___x_2410_, 1, v___x_2408_);
return v___x_2410_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5(void){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5___closed__1);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(lean_object* v___x_2412_, lean_object* v_as_2413_, size_t v_i_2414_, size_t v_stop_2415_, lean_object* v_b_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
uint8_t v___x_2424_; 
v___x_2424_ = lean_usize_dec_eq(v_i_2414_, v_stop_2415_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_array_uget_borrowed(v_as_2413_, v_i_2414_);
lean_inc_ref(v___y_2417_);
lean_inc(v___x_2425_);
lean_inc_ref(v___x_2412_);
v___x_2426_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__1(v___x_2412_, v___x_2425_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v_a_2428_; lean_object* v___x_2429_; size_t v___x_2430_; size_t v___x_2431_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2427_);
v_a_2428_ = lean_ctor_get(v___x_2426_, 1);
lean_inc(v_a_2428_);
lean_dec_ref_known(v___x_2426_, 2);
v___x_2429_ = lean_array_push(v_b_2416_, v_a_2427_);
v___x_2430_ = ((size_t)1ULL);
v___x_2431_ = lean_usize_add(v_i_2414_, v___x_2430_);
v_i_2414_ = v___x_2431_;
v_b_2416_ = v___x_2429_;
v___y_2422_ = v_a_2428_;
goto _start;
}
else
{
lean_object* v_a_2433_; lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec_ref(v___y_2417_);
lean_dec_ref(v_b_2416_);
lean_dec_ref(v___x_2412_);
v_a_2433_ = lean_ctor_get(v___x_2426_, 0);
v_a_2434_ = lean_ctor_get(v___x_2426_, 1);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2426_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_inc(v_a_2433_);
lean_dec(v___x_2426_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2433_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v___x_2442_; 
lean_dec_ref(v___y_2417_);
lean_dec_ref(v___x_2412_);
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v_b_2416_);
lean_ctor_set(v___x_2442_, 1, v___y_2422_);
return v___x_2442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8___boxed(lean_object* v___x_2443_, lean_object* v_as_2444_, lean_object* v_i_2445_, lean_object* v_stop_2446_, lean_object* v_b_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
size_t v_i_boxed_2455_; size_t v_stop_boxed_2456_; lean_object* v_res_2457_; 
v_i_boxed_2455_ = lean_unbox_usize(v_i_2445_);
lean_dec(v_i_2445_);
v_stop_boxed_2456_ = lean_unbox_usize(v_stop_2446_);
lean_dec(v_stop_2446_);
v_res_2457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v___x_2443_, v_as_2444_, v_i_boxed_2455_, v_stop_boxed_2456_, v_b_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v_as_2444_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(lean_object* v_self_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v_toHashSet_2460_; lean_object* v_toArray_2461_; uint8_t v___x_2462_; 
v_toHashSet_2460_ = lean_ctor_get(v_self_2458_, 0);
v_toArray_2461_ = lean_ctor_get(v_self_2458_, 1);
v___x_2462_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__0___redArg(v_toHashSet_2460_, v_a_2459_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2472_; 
lean_inc_ref(v_toArray_2461_);
lean_inc_ref(v_toHashSet_2460_);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_self_2458_);
if (v_isSharedCheck_2472_ == 0)
{
lean_object* v_unused_2473_; lean_object* v_unused_2474_; 
v_unused_2473_ = lean_ctor_get(v_self_2458_, 1);
lean_dec(v_unused_2473_);
v_unused_2474_ = lean_ctor_get(v_self_2458_, 0);
lean_dec(v_unused_2474_);
v___x_2464_ = v_self_2458_;
v_isShared_2465_ = v_isSharedCheck_2472_;
goto v_resetjp_2463_;
}
else
{
lean_dec(v_self_2458_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2472_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2466_ = lean_box(0);
lean_inc_ref(v_a_2459_);
v___x_2467_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules_go_spec__1___redArg(v_toHashSet_2460_, v_a_2459_, v___x_2466_);
v___x_2468_ = lean_array_push(v_toArray_2461_, v_a_2459_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 1, v___x_2468_);
lean_ctor_set(v___x_2464_, 0, v___x_2467_);
v___x_2470_ = v___x_2464_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
else
{
lean_dec_ref(v_a_2459_);
return v_self_2458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(lean_object* v_as_2475_, size_t v_i_2476_, size_t v_stop_2477_, lean_object* v_b_2478_){
_start:
{
uint8_t v___x_2479_; 
v___x_2479_ = lean_usize_dec_eq(v_i_2476_, v_stop_2477_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; lean_object* v___x_2481_; size_t v___x_2482_; size_t v___x_2483_; 
v___x_2480_ = lean_array_uget_borrowed(v_as_2475_, v_i_2476_);
lean_inc(v___x_2480_);
v___x_2481_ = l_Lake_OrdHashSet_insert___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__0(v_b_2478_, v___x_2480_);
v___x_2482_ = ((size_t)1ULL);
v___x_2483_ = lean_usize_add(v_i_2476_, v___x_2482_);
v_i_2476_ = v___x_2483_;
v_b_2478_ = v___x_2481_;
goto _start;
}
else
{
return v_b_2478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1___boxed(lean_object* v_as_2485_, lean_object* v_i_2486_, lean_object* v_stop_2487_, lean_object* v_b_2488_){
_start:
{
size_t v_i_boxed_2489_; size_t v_stop_boxed_2490_; lean_object* v_res_2491_; 
v_i_boxed_2489_ = lean_unbox_usize(v_i_2486_);
lean_dec(v_i_2486_);
v_stop_boxed_2490_ = lean_unbox_usize(v_stop_2487_);
lean_dec(v_stop_2487_);
v_res_2491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_as_2485_, v_i_boxed_2489_, v_stop_boxed_2490_, v_b_2488_);
lean_dec_ref(v_as_2485_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(lean_object* v_self_2492_, lean_object* v_arr_2493_){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; 
v___x_2494_ = lean_unsigned_to_nat(0u);
v___x_2495_ = lean_array_get_size(v_arr_2493_);
v___x_2496_ = lean_nat_dec_lt(v___x_2494_, v___x_2495_);
if (v___x_2496_ == 0)
{
return v_self_2492_;
}
else
{
size_t v___x_2497_; size_t v___x_2498_; lean_object* v___x_2499_; 
v___x_2497_ = ((size_t)0ULL);
v___x_2498_ = lean_usize_of_nat(v___x_2495_);
v___x_2499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0_spec__1(v_arr_2493_, v___x_2497_, v___x_2498_, v_self_2492_);
return v___x_2499_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0___boxed(lean_object* v_self_2500_, lean_object* v_arr_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_self_2500_, v_arr_2501_);
lean_dec_ref(v_arr_2501_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(lean_object* v_as_2503_, size_t v_i_2504_, size_t v_stop_2505_, lean_object* v_b_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
uint8_t v___x_2514_; 
v___x_2514_ = lean_usize_dec_eq(v_i_2504_, v_stop_2505_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; lean_object* v_lib_2516_; lean_object* v_pkg_2517_; lean_object* v_name_2518_; lean_object* v_keyName_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2515_ = lean_array_uget_borrowed(v_as_2503_, v_i_2504_);
v_lib_2516_ = lean_ctor_get(v___x_2515_, 0);
v_pkg_2517_ = lean_ctor_get(v_lib_2516_, 0);
v_name_2518_ = lean_ctor_get(v___x_2515_, 1);
v_keyName_2519_ = lean_ctor_get(v_pkg_2517_, 2);
v___x_2520_ = l_Lake_Module_transImportsFacet;
lean_inc(v_name_2518_);
lean_inc(v_keyName_2519_);
v___x_2521_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2521_, 0, v_keyName_2519_);
lean_ctor_set(v___x_2521_, 1, v_name_2518_);
v___x_2522_ = l_Lake_Module_keyword;
lean_inc(v___x_2515_);
v___x_2523_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2521_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
lean_ctor_set(v___x_2523_, 2, v___x_2515_);
lean_ctor_set(v___x_2523_, 3, v___x_2520_);
lean_inc_ref(v___y_2507_);
lean_inc_ref(v___y_2511_);
lean_inc(v___y_2510_);
lean_inc(v___y_2509_);
lean_inc(v___y_2508_);
v___x_2524_ = lean_apply_7(v___y_2507_, v___x_2523_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, lean_box(0));
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v_a_2526_; lean_object* v___x_2527_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
v_a_2526_ = lean_ctor_get(v___x_2524_, 1);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2524_, 2);
v___x_2527_ = l_Lake_Job_await___redArg(v_a_2525_, v_a_2526_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v_a_2529_; lean_object* v___x_2530_; size_t v___x_2531_; size_t v___x_2532_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
v_a_2529_ = lean_ctor_get(v___x_2527_, 1);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2527_, 2);
v___x_2530_ = l_Lake_OrdHashSet_appendArray___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__0(v_b_2506_, v_a_2528_);
lean_dec(v_a_2528_);
v___x_2531_ = ((size_t)1ULL);
v___x_2532_ = lean_usize_add(v_i_2504_, v___x_2531_);
v_i_2504_ = v___x_2532_;
v_b_2506_ = v___x_2530_;
v___y_2512_ = v_a_2529_;
goto _start;
}
else
{
lean_object* v_a_2534_; lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec_ref(v___y_2507_);
lean_dec_ref(v_b_2506_);
v_a_2534_ = lean_ctor_get(v___x_2527_, 0);
v_a_2535_ = lean_ctor_get(v___x_2527_, 1);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2527_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_inc(v_a_2534_);
lean_dec(v___x_2527_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2534_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec_ref(v___y_2507_);
lean_dec_ref(v_b_2506_);
v_a_2543_ = lean_ctor_get(v___x_2524_, 0);
v_a_2544_ = lean_ctor_get(v___x_2524_, 1);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2524_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_inc(v_a_2543_);
lean_dec(v___x_2524_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2543_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
else
{
lean_object* v___x_2552_; 
lean_dec_ref(v___y_2507_);
v___x_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2552_, 0, v_b_2506_);
lean_ctor_set(v___x_2552_, 1, v___y_2512_);
return v___x_2552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7___boxed(lean_object* v_as_2553_, lean_object* v_i_2554_, lean_object* v_stop_2555_, lean_object* v_b_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
size_t v_i_boxed_2564_; size_t v_stop_boxed_2565_; lean_object* v_res_2566_; 
v_i_boxed_2564_ = lean_unbox_usize(v_i_2554_);
lean_dec(v_i_2554_);
v_stop_boxed_2565_ = lean_unbox_usize(v_stop_2555_);
lean_dec(v_stop_2555_);
v_res_2566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_as_2553_, v_i_boxed_2564_, v_stop_boxed_2565_, v_b_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
lean_dec_ref(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v_as_2553_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(lean_object* v_as_2567_, size_t v_i_2568_, size_t v_stop_2569_, lean_object* v_b_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
uint8_t v___x_2578_; 
v___x_2578_ = lean_usize_dec_eq(v_i_2568_, v_stop_2569_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; lean_object* v_pkg_2580_; lean_object* v_name_2581_; lean_object* v_keyName_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2579_ = lean_array_uget_borrowed(v_as_2567_, v_i_2568_);
v_pkg_2580_ = lean_ctor_get(v___x_2579_, 0);
v_name_2581_ = lean_ctor_get(v___x_2579_, 1);
v_keyName_2582_ = lean_ctor_get(v_pkg_2580_, 2);
v___x_2583_ = l_Lake_ExternLib_dynlibFacet;
lean_inc(v_name_2581_);
lean_inc(v_keyName_2582_);
v___x_2584_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2584_, 0, v_keyName_2582_);
lean_ctor_set(v___x_2584_, 1, v_name_2581_);
v___x_2585_ = l_Lake_ExternLib_keyword;
lean_inc(v___x_2579_);
v___x_2586_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2584_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
lean_ctor_set(v___x_2586_, 2, v___x_2579_);
lean_ctor_set(v___x_2586_, 3, v___x_2583_);
lean_inc_ref(v___y_2571_);
lean_inc_ref(v___y_2575_);
lean_inc(v___y_2574_);
lean_inc(v___y_2573_);
lean_inc(v___y_2572_);
v___x_2587_ = lean_apply_7(v___y_2571_, v___x_2586_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, lean_box(0));
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v_a_2589_; lean_object* v___x_2590_; size_t v___x_2591_; size_t v___x_2592_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2588_);
v_a_2589_ = lean_ctor_get(v___x_2587_, 1);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___x_2587_, 2);
v___x_2590_ = lean_array_push(v_b_2570_, v_a_2588_);
v___x_2591_ = ((size_t)1ULL);
v___x_2592_ = lean_usize_add(v_i_2568_, v___x_2591_);
v_i_2568_ = v___x_2592_;
v_b_2570_ = v___x_2590_;
v___y_2576_ = v_a_2589_;
goto _start;
}
else
{
lean_object* v_a_2594_; lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec_ref(v___y_2571_);
lean_dec_ref(v_b_2570_);
v_a_2594_ = lean_ctor_get(v___x_2587_, 0);
v_a_2595_ = lean_ctor_get(v___x_2587_, 1);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2587_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_inc(v_a_2594_);
lean_dec(v___x_2587_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2594_);
lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v___x_2603_; 
lean_dec_ref(v___y_2571_);
v___x_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2603_, 0, v_b_2570_);
lean_ctor_set(v___x_2603_, 1, v___y_2576_);
return v___x_2603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2___boxed(lean_object* v_as_2604_, lean_object* v_i_2605_, lean_object* v_stop_2606_, lean_object* v_b_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
size_t v_i_boxed_2615_; size_t v_stop_boxed_2616_; lean_object* v_res_2617_; 
v_i_boxed_2615_ = lean_unbox_usize(v_i_2605_);
lean_dec(v_i_2605_);
v_stop_boxed_2616_ = lean_unbox_usize(v_stop_2606_);
lean_dec(v_stop_2606_);
v_res_2617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v_as_2604_, v_i_boxed_2615_, v_stop_boxed_2616_, v_b_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v_as_2604_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(lean_object* v_as_2618_, size_t v_i_2619_, size_t v_stop_2620_, lean_object* v_b_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_a_2630_; lean_object* v_a_2631_; uint8_t v___x_2635_; 
v___x_2635_ = lean_usize_dec_eq(v_i_2619_, v_stop_2620_);
if (v___x_2635_ == 0)
{
lean_object* v_fst_2636_; lean_object* v_snd_2637_; lean_object* v___x_2638_; lean_object* v_lib_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2676_; 
v_fst_2636_ = lean_ctor_get(v_b_2621_, 0);
v_snd_2637_ = lean_ctor_get(v_b_2621_, 1);
v___x_2638_ = lean_array_uget(v_as_2618_, v_i_2619_);
v_lib_2639_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2676_ == 0)
{
lean_object* v_unused_2677_; 
v_unused_2677_ = lean_ctor_get(v___x_2638_, 1);
lean_dec(v_unused_2677_);
v___x_2641_ = v___x_2638_;
v_isShared_2642_ = v_isSharedCheck_2676_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_lib_2639_);
lean_dec(v___x_2638_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2676_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v_pkg_2643_; lean_object* v_name_2644_; uint8_t v___x_2645_; 
v_pkg_2643_ = lean_ctor_get(v_lib_2639_, 0);
v_name_2644_ = lean_ctor_get(v_lib_2639_, 1);
lean_inc(v_name_2644_);
v___x_2645_ = l_Lean_NameSet_contains(v_fst_2636_, v_name_2644_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2673_; 
lean_inc(v_snd_2637_);
lean_inc(v_fst_2636_);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_b_2621_);
if (v_isSharedCheck_2673_ == 0)
{
lean_object* v_unused_2674_; lean_object* v_unused_2675_; 
v_unused_2674_ = lean_ctor_get(v_b_2621_, 1);
lean_dec(v_unused_2674_);
v_unused_2675_ = lean_ctor_get(v_b_2621_, 0);
lean_dec(v_unused_2675_);
v___x_2647_ = v_b_2621_;
v_isShared_2648_ = v_isSharedCheck_2673_;
goto v_resetjp_2646_;
}
else
{
lean_dec(v_b_2621_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2673_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v_keyName_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; 
v_keyName_2649_ = lean_ctor_get(v_pkg_2643_, 2);
v___x_2650_ = l_Lake_LeanLib_sharedFacet;
lean_inc(v_name_2644_);
lean_inc(v_keyName_2649_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 3);
lean_ctor_set(v___x_2641_, 1, v_name_2644_);
lean_ctor_set(v___x_2641_, 0, v_keyName_2649_);
v___x_2652_ = v___x_2641_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_keyName_2649_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_name_2644_);
v___x_2652_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2653_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_2654_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2652_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
lean_ctor_set(v___x_2654_, 2, v_lib_2639_);
lean_ctor_set(v___x_2654_, 3, v___x_2650_);
lean_inc_ref(v___y_2622_);
lean_inc_ref(v___y_2626_);
lean_inc(v___y_2625_);
lean_inc(v___y_2624_);
lean_inc(v___y_2623_);
v___x_2655_ = lean_apply_7(v___y_2622_, v___x_2654_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, lean_box(0));
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v_a_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
v_a_2657_ = lean_ctor_get(v___x_2655_, 1);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2655_, 2);
v___x_2658_ = lean_array_push(v_snd_2637_, v_a_2656_);
v___x_2659_ = l_Lean_NameSet_insert(v_fst_2636_, v_name_2644_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 1, v___x_2658_);
lean_ctor_set(v___x_2647_, 0, v___x_2659_);
v___x_2661_ = v___x_2647_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2662_, 1, v___x_2658_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
v_a_2630_ = v___x_2661_;
v_a_2631_ = v_a_2657_;
goto v___jp_2629_;
}
}
else
{
lean_object* v_a_2663_; lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_del_object(v___x_2647_);
lean_dec(v_name_2644_);
lean_dec(v_snd_2637_);
lean_dec(v_fst_2636_);
lean_dec_ref(v___y_2622_);
v_a_2663_ = lean_ctor_get(v___x_2655_, 0);
v_a_2664_ = lean_ctor_get(v___x_2655_, 1);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2655_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_inc(v_a_2663_);
lean_dec(v___x_2655_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2663_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
}
else
{
lean_dec(v_name_2644_);
lean_del_object(v___x_2641_);
lean_dec_ref(v_lib_2639_);
v_a_2630_ = v_b_2621_;
v_a_2631_ = v___y_2627_;
goto v___jp_2629_;
}
}
}
else
{
lean_object* v___x_2678_; 
lean_dec_ref(v___y_2622_);
v___x_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2678_, 0, v_b_2621_);
lean_ctor_set(v___x_2678_, 1, v___y_2627_);
return v___x_2678_;
}
v___jp_2629_:
{
size_t v___x_2632_; size_t v___x_2633_; 
v___x_2632_ = ((size_t)1ULL);
v___x_2633_ = lean_usize_add(v_i_2619_, v___x_2632_);
v_i_2619_ = v___x_2633_;
v_b_2621_ = v_a_2630_;
v___y_2627_ = v_a_2631_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6___boxed(lean_object* v_as_2679_, lean_object* v_i_2680_, lean_object* v_stop_2681_, lean_object* v_b_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
size_t v_i_boxed_2690_; size_t v_stop_boxed_2691_; lean_object* v_res_2692_; 
v_i_boxed_2690_ = lean_unbox_usize(v_i_2680_);
lean_dec(v_i_2680_);
v_stop_boxed_2691_ = lean_unbox_usize(v_stop_2681_);
lean_dec(v_stop_2681_);
v_res_2692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_as_2679_, v_i_boxed_2690_, v_stop_boxed_2691_, v_b_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v_as_2679_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(lean_object* v___x_2693_, lean_object* v_as_2694_, size_t v_i_2695_, size_t v_stop_2696_, lean_object* v_b_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
uint8_t v___x_2705_; 
v___x_2705_ = lean_usize_dec_eq(v_i_2695_, v_stop_2696_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_array_uget_borrowed(v_as_2694_, v_i_2695_);
lean_inc_ref(v___y_2698_);
lean_inc(v___x_2706_);
lean_inc_ref(v___x_2693_);
v___x_2707_ = l_Lake_Target_fetchIn___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__1(v___x_2693_, v___x_2706_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v_a_2709_; lean_object* v___x_2710_; size_t v___x_2711_; size_t v___x_2712_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
v_a_2709_ = lean_ctor_get(v___x_2707_, 1);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2707_, 2);
v___x_2710_ = lean_array_push(v_b_2697_, v_a_2708_);
v___x_2711_ = ((size_t)1ULL);
v___x_2712_ = lean_usize_add(v_i_2695_, v___x_2711_);
v_i_2695_ = v___x_2712_;
v_b_2697_ = v___x_2710_;
v___y_2703_ = v_a_2709_;
goto _start;
}
else
{
lean_object* v_a_2714_; lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec_ref(v___y_2698_);
lean_dec_ref(v_b_2697_);
lean_dec_ref(v___x_2693_);
v_a_2714_ = lean_ctor_get(v___x_2707_, 0);
v_a_2715_ = lean_ctor_get(v___x_2707_, 1);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2707_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_inc(v_a_2714_);
lean_dec(v___x_2707_);
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
lean_dec_ref(v___y_2698_);
lean_dec_ref(v___x_2693_);
v___x_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2723_, 0, v_b_2697_);
lean_ctor_set(v___x_2723_, 1, v___y_2703_);
return v___x_2723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4___boxed(lean_object* v___x_2724_, lean_object* v_as_2725_, lean_object* v_i_2726_, lean_object* v_stop_2727_, lean_object* v_b_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
size_t v_i_boxed_2736_; size_t v_stop_boxed_2737_; lean_object* v_res_2738_; 
v_i_boxed_2736_ = lean_unbox_usize(v_i_2726_);
lean_dec(v_i_2726_);
v_stop_boxed_2737_ = lean_unbox_usize(v_stop_2727_);
lean_dec(v_stop_2727_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v___x_2724_, v_as_2725_, v_i_boxed_2736_, v_stop_boxed_2737_, v_b_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v_as_2725_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(lean_object* v___x_2739_, lean_object* v_as_2740_, size_t v_i_2741_, size_t v_stop_2742_, lean_object* v_b_2743_){
_start:
{
lean_object* v___y_2745_; uint8_t v___x_2749_; 
v___x_2749_ = lean_usize_dec_eq(v_i_2741_, v_stop_2742_);
if (v___x_2749_ == 0)
{
lean_object* v_toConfigDecl_2750_; lean_object* v_name_2751_; lean_object* v_kind_2752_; lean_object* v_config_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
v_toConfigDecl_2750_ = lean_array_uget_borrowed(v_as_2740_, v_i_2741_);
v_name_2751_ = lean_ctor_get(v_toConfigDecl_2750_, 1);
v_kind_2752_ = lean_ctor_get(v_toConfigDecl_2750_, 2);
v_config_2753_ = lean_ctor_get(v_toConfigDecl_2750_, 3);
v___x_2754_ = l_Lake_ExternLib_keyword;
v___x_2755_ = lean_name_eq(v_kind_2752_, v___x_2754_);
if (v___x_2755_ == 0)
{
v___y_2745_ = v_b_2743_;
goto v___jp_2744_;
}
else
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
lean_inc(v_config_2753_);
lean_inc(v_name_2751_);
lean_inc_ref(v___x_2739_);
v___x_2756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2739_);
lean_ctor_set(v___x_2756_, 1, v_name_2751_);
lean_ctor_set(v___x_2756_, 2, v_config_2753_);
v___x_2757_ = lean_array_push(v_b_2743_, v___x_2756_);
v___y_2745_ = v___x_2757_;
goto v___jp_2744_;
}
}
else
{
lean_dec_ref(v___x_2739_);
return v_b_2743_;
}
v___jp_2744_:
{
size_t v___x_2746_; size_t v___x_2747_; 
v___x_2746_ = ((size_t)1ULL);
v___x_2747_ = lean_usize_add(v_i_2741_, v___x_2746_);
v_i_2741_ = v___x_2747_;
v_b_2743_ = v___y_2745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3___boxed(lean_object* v___x_2758_, lean_object* v_as_2759_, lean_object* v_i_2760_, lean_object* v_stop_2761_, lean_object* v_b_2762_){
_start:
{
size_t v_i_boxed_2763_; size_t v_stop_boxed_2764_; lean_object* v_res_2765_; 
v_i_boxed_2763_ = lean_unbox_usize(v_i_2760_);
lean_dec(v_i_2760_);
v_stop_boxed_2764_ = lean_unbox_usize(v_stop_2761_);
lean_dec(v_stop_2761_);
v_res_2765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v___x_2758_, v_as_2759_, v_i_boxed_2763_, v_stop_boxed_2764_, v_b_2762_);
lean_dec_ref(v_as_2759_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(lean_object* v_as_2766_, size_t v_i_2767_, size_t v_stop_2768_, lean_object* v_b_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
uint8_t v___x_2777_; 
v___x_2777_ = lean_usize_dec_eq(v_i_2767_, v_stop_2768_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; lean_object* v_lib_2779_; lean_object* v_config_2780_; lean_object* v_nativeFacets_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; size_t v_sz_2785_; size_t v___x_2786_; lean_object* v___x_2787_; 
v___x_2778_ = lean_array_uget_borrowed(v_as_2766_, v_i_2767_);
v_lib_2779_ = lean_ctor_get(v___x_2778_, 0);
v_config_2780_ = lean_ctor_get(v_lib_2779_, 2);
v_nativeFacets_2781_ = lean_ctor_get(v_config_2780_, 8);
v___x_2782_ = 1;
v___x_2783_ = lean_box(v___x_2782_);
lean_inc_ref(v_nativeFacets_2781_);
v___x_2784_ = lean_apply_1(v_nativeFacets_2781_, v___x_2783_);
v_sz_2785_ = lean_array_size(v___x_2784_);
v___x_2786_ = ((size_t)0ULL);
lean_inc_ref(v___y_2770_);
lean_inc(v___x_2778_);
v___x_2787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___at___00Lake_LeanLib_staticFacetConfig_spec__0_spec__0(v___x_2778_, v_sz_2785_, v___x_2786_, v___x_2784_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v_a_2789_; lean_object* v___x_2790_; size_t v___x_2791_; size_t v___x_2792_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
v_a_2789_ = lean_ctor_get(v___x_2787_, 1);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2787_, 2);
v___x_2790_ = l_Array_append___redArg(v_b_2769_, v_a_2788_);
lean_dec(v_a_2788_);
v___x_2791_ = ((size_t)1ULL);
v___x_2792_ = lean_usize_add(v_i_2767_, v___x_2791_);
v_i_2767_ = v___x_2792_;
v_b_2769_ = v___x_2790_;
v___y_2775_ = v_a_2789_;
goto _start;
}
else
{
lean_dec_ref(v___y_2770_);
lean_dec_ref(v_b_2769_);
return v___x_2787_;
}
}
else
{
lean_object* v___x_2794_; 
lean_dec_ref(v___y_2770_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v_b_2769_);
lean_ctor_set(v___x_2794_, 1, v___y_2775_);
return v___x_2794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9___boxed(lean_object* v_as_2795_, lean_object* v_i_2796_, lean_object* v_stop_2797_, lean_object* v_b_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
size_t v_i_boxed_2806_; size_t v_stop_boxed_2807_; lean_object* v_res_2808_; 
v_i_boxed_2806_ = lean_unbox_usize(v_i_2796_);
lean_dec(v_i_2796_);
v_stop_boxed_2807_ = lean_unbox_usize(v_stop_2797_);
lean_dec(v_stop_2797_);
v_res_2808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_as_2795_, v_i_boxed_2806_, v_stop_boxed_2807_, v_b_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec(v___y_2800_);
lean_dec_ref(v_as_2795_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(lean_object* v_self_2809_, lean_object* v_dir_2810_, lean_object* v___x_2811_, lean_object* v_targetDecls_2812_, lean_object* v_pkg_2813_, lean_object* v_name_2814_, lean_object* v___x_2815_, lean_object* v_config_2816_, lean_object* v_config_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v_a_2826_; lean_object* v_a_2827_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v_a_2837_; lean_object* v_a_2838_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v_a_2898_; lean_object* v_a_2899_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v_snd_2931_; lean_object* v_a_2932_; lean_object* v___y_2944_; lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v_a_2954_; lean_object* v_a_2955_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___x_2994_; 
lean_inc_ref(v___y_2818_);
lean_inc_ref(v___y_2822_);
lean_inc(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc(v___x_2811_);
v___x_2994_ = lean_apply_7(v___y_2818_, v___x_2815_, v___x_2811_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, lean_box(0));
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v_a_2996_; lean_object* v___x_2997_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
v_a_2996_ = lean_ctor_get(v___x_2994_, 1);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2994_, 2);
v___x_2997_ = l_Lake_Job_await___redArg(v_a_2995_, v_a_2996_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v_a_2999_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v_a_3010_; lean_object* v_a_3011_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v_a_3045_; lean_object* v_a_3046_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
v_a_2999_ = lean_ctor_get(v___x_2997_, 1);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___x_2997_, 2);
v___x_3070_ = lean_unsigned_to_nat(0u);
v___x_3071_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildStatic___lam__6___closed__2));
v___x_3072_ = lean_array_get_size(v_a_2998_);
v___x_3073_ = lean_nat_dec_lt(v___x_3070_, v___x_3072_);
if (v___x_3073_ == 0)
{
v_a_3045_ = v___x_3071_;
v_a_3046_ = v_a_2999_;
goto v___jp_3044_;
}
else
{
size_t v___x_3074_; size_t v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = ((size_t)0ULL);
v___x_3075_ = lean_usize_of_nat(v___x_3072_);
lean_inc_ref(v___y_2818_);
v___x_3076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__9(v_a_2998_, v___x_3074_, v___x_3075_, v___x_3071_, v___y_2818_, v___x_2811_, v___y_2820_, v___y_2821_, v___y_2822_, v_a_2999_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; lean_object* v_a_3078_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
v_a_3078_ = lean_ctor_get(v___x_3076_, 1);
lean_inc(v_a_3078_);
lean_dec_ref_known(v___x_3076_, 2);
v_a_3045_ = v_a_3077_;
v_a_3046_ = v_a_3078_;
goto v___jp_3044_;
}
else
{
lean_object* v_a_3079_; lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec(v_a_2998_);
lean_dec_ref(v___y_2818_);
lean_dec_ref(v_config_2816_);
lean_dec(v_name_2814_);
lean_dec_ref(v_pkg_2813_);
lean_dec(v___x_2811_);
lean_dec_ref(v_dir_2810_);
lean_dec_ref(v_self_2809_);
v_a_3079_ = lean_ctor_get(v___x_3076_, 0);
v_a_3080_ = lean_ctor_get(v___x_3076_, 1);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3076_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_inc(v_a_3079_);
lean_dec(v___x_3076_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3079_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
v___jp_3000_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3012_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__5;
v___x_3013_ = lean_array_get_size(v_a_2998_);
v___x_3014_ = lean_nat_dec_lt(v___y_3006_, v___x_3013_);
if (v___x_3014_ == 0)
{
lean_dec(v_a_2998_);
v___y_2944_ = v___y_3001_;
v___y_2945_ = v___y_3002_;
v___y_2946_ = v_a_3010_;
v___y_2947_ = v___y_3003_;
v___y_2948_ = v___y_3004_;
v___y_2949_ = v___y_3005_;
v___y_2950_ = v___y_3006_;
v___y_2951_ = v___y_3007_;
v___y_2952_ = v___y_3008_;
v___y_2953_ = v___y_3009_;
v_a_2954_ = v___x_3012_;
v_a_2955_ = v_a_3011_;
goto v___jp_2943_;
}
else
{
uint8_t v___x_3015_; 
v___x_3015_ = lean_nat_dec_le(v___x_3013_, v___x_3013_);
if (v___x_3015_ == 0)
{
if (v___x_3014_ == 0)
{
lean_dec(v_a_2998_);
v___y_2944_ = v___y_3001_;
v___y_2945_ = v___y_3002_;
v___y_2946_ = v_a_3010_;
v___y_2947_ = v___y_3003_;
v___y_2948_ = v___y_3004_;
v___y_2949_ = v___y_3005_;
v___y_2950_ = v___y_3006_;
v___y_2951_ = v___y_3007_;
v___y_2952_ = v___y_3008_;
v___y_2953_ = v___y_3009_;
v_a_2954_ = v___x_3012_;
v_a_2955_ = v_a_3011_;
goto v___jp_2943_;
}
else
{
size_t v___x_3016_; size_t v___x_3017_; lean_object* v___x_3018_; 
v___x_3016_ = ((size_t)0ULL);
v___x_3017_ = lean_usize_of_nat(v___x_3013_);
lean_inc_ref(v___y_2818_);
v___x_3018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_2998_, v___x_3016_, v___x_3017_, v___x_3012_, v___y_2818_, v___x_2811_, v___y_2820_, v___y_2821_, v___y_2822_, v_a_3011_);
lean_dec(v_a_2998_);
v___y_2979_ = v___y_3001_;
v___y_2980_ = v___y_3002_;
v___y_2981_ = v_a_3010_;
v___y_2982_ = v___y_3003_;
v___y_2983_ = v___y_3004_;
v___y_2984_ = v___y_3006_;
v___y_2985_ = v___y_3005_;
v___y_2986_ = v___y_3009_;
v___y_2987_ = v___y_3008_;
v___y_2988_ = v___y_3007_;
v___y_2989_ = v___x_3018_;
goto v___jp_2978_;
}
}
else
{
size_t v___x_3019_; size_t v___x_3020_; lean_object* v___x_3021_; 
v___x_3019_ = ((size_t)0ULL);
v___x_3020_ = lean_usize_of_nat(v___x_3013_);
lean_inc_ref(v___y_2818_);
v___x_3021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__7(v_a_2998_, v___x_3019_, v___x_3020_, v___x_3012_, v___y_2818_, v___x_2811_, v___y_2820_, v___y_2821_, v___y_2822_, v_a_3011_);
lean_dec(v_a_2998_);
v___y_2979_ = v___y_3001_;
v___y_2980_ = v___y_3002_;
v___y_2981_ = v_a_3010_;
v___y_2982_ = v___y_3003_;
v___y_2983_ = v___y_3004_;
v___y_2984_ = v___y_3006_;
v___y_2985_ = v___y_3005_;
v___y_2986_ = v___y_3009_;
v___y_2987_ = v___y_3008_;
v___y_2988_ = v___y_3007_;
v___y_2989_ = v___x_3021_;
goto v___jp_2978_;
}
}
}
v___jp_3022_:
{
if (lean_obj_tag(v___y_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v_a_3034_; 
v_a_3033_ = lean_ctor_get(v___y_3032_, 0);
lean_inc(v_a_3033_);
v_a_3034_ = lean_ctor_get(v___y_3032_, 1);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___y_3032_, 2);
v___y_3001_ = v___y_3023_;
v___y_3002_ = v___y_3024_;
v___y_3003_ = v___y_3025_;
v___y_3004_ = v___y_3026_;
v___y_3005_ = v___y_3028_;
v___y_3006_ = v___y_3027_;
v___y_3007_ = v___y_3031_;
v___y_3008_ = v___y_3030_;
v___y_3009_ = v___y_3029_;
v_a_3010_ = v_a_3033_;
v_a_3011_ = v_a_3034_;
goto v___jp_3000_;
}
else
{
lean_object* v_a_3035_; lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec_ref(v___y_3031_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v_a_2998_);
lean_dec_ref(v___y_2818_);
lean_dec(v_name_2814_);
lean_dec_ref(v_pkg_2813_);
lean_dec(v___x_2811_);
lean_dec_ref(v_dir_2810_);
lean_dec_ref(v_self_2809_);
v_a_3035_ = lean_ctor_get(v___y_3032_, 0);
v_a_3036_ = lean_ctor_get(v___y_3032_, 1);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___y_3032_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___y_3032_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_inc(v_a_3035_);
lean_dec(v___y_3032_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3035_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
v___jp_3044_:
{
lean_object* v_toLeanConfig_3047_; lean_object* v_toLeanConfig_3048_; lean_object* v_buildDir_3049_; lean_object* v_nativeLibDir_3050_; lean_object* v_moreLinkObjs_3051_; lean_object* v_moreLinkLibs_3052_; lean_object* v_moreLinkArgs_3053_; lean_object* v_weakLinkArgs_3054_; lean_object* v_moreLinkObjs_3055_; lean_object* v_moreLinkLibs_3056_; lean_object* v_moreLinkArgs_3057_; lean_object* v_weakLinkArgs_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v_toLeanConfig_3047_ = lean_ctor_get(v_config_2816_, 1);
lean_inc_ref(v_toLeanConfig_3047_);
v_toLeanConfig_3048_ = lean_ctor_get(v_config_2817_, 0);
v_buildDir_3049_ = lean_ctor_get(v_config_2816_, 5);
lean_inc_ref(v_buildDir_3049_);
v_nativeLibDir_3050_ = lean_ctor_get(v_config_2816_, 7);
lean_inc_ref(v_nativeLibDir_3050_);
lean_dec_ref(v_config_2816_);
v_moreLinkObjs_3051_ = lean_ctor_get(v_toLeanConfig_3047_, 6);
lean_inc_ref(v_moreLinkObjs_3051_);
v_moreLinkLibs_3052_ = lean_ctor_get(v_toLeanConfig_3047_, 7);
lean_inc_ref(v_moreLinkLibs_3052_);
v_moreLinkArgs_3053_ = lean_ctor_get(v_toLeanConfig_3047_, 8);
lean_inc_ref(v_moreLinkArgs_3053_);
v_weakLinkArgs_3054_ = lean_ctor_get(v_toLeanConfig_3047_, 9);
lean_inc_ref(v_weakLinkArgs_3054_);
lean_dec_ref(v_toLeanConfig_3047_);
v_moreLinkObjs_3055_ = lean_ctor_get(v_toLeanConfig_3048_, 6);
v_moreLinkLibs_3056_ = lean_ctor_get(v_toLeanConfig_3048_, 7);
v_moreLinkArgs_3057_ = lean_ctor_get(v_toLeanConfig_3048_, 8);
v_weakLinkArgs_3058_ = lean_ctor_get(v_toLeanConfig_3048_, 9);
v___x_3059_ = l_Array_append___redArg(v_moreLinkObjs_3051_, v_moreLinkObjs_3055_);
v___x_3060_ = lean_unsigned_to_nat(0u);
v___x_3061_ = lean_array_get_size(v___x_3059_);
v___x_3062_ = lean_nat_dec_lt(v___x_3060_, v___x_3061_);
if (v___x_3062_ == 0)
{
lean_dec_ref(v___x_3059_);
v___y_3001_ = v_moreLinkLibs_3052_;
v___y_3002_ = v_buildDir_3049_;
v___y_3003_ = v_moreLinkArgs_3057_;
v___y_3004_ = v_weakLinkArgs_3054_;
v___y_3005_ = v_moreLinkLibs_3056_;
v___y_3006_ = v___x_3060_;
v___y_3007_ = v_moreLinkArgs_3053_;
v___y_3008_ = v_weakLinkArgs_3058_;
v___y_3009_ = v_nativeLibDir_3050_;
v_a_3010_ = v_a_3045_;
v_a_3011_ = v_a_3046_;
goto v___jp_3000_;
}
else
{
uint8_t v___x_3063_; 
v___x_3063_ = lean_nat_dec_le(v___x_3061_, v___x_3061_);
if (v___x_3063_ == 0)
{
if (v___x_3062_ == 0)
{
lean_dec_ref(v___x_3059_);
v___y_3001_ = v_moreLinkLibs_3052_;
v___y_3002_ = v_buildDir_3049_;
v___y_3003_ = v_moreLinkArgs_3057_;
v___y_3004_ = v_weakLinkArgs_3054_;
v___y_3005_ = v_moreLinkLibs_3056_;
v___y_3006_ = v___x_3060_;
v___y_3007_ = v_moreLinkArgs_3053_;
v___y_3008_ = v_weakLinkArgs_3058_;
v___y_3009_ = v_nativeLibDir_3050_;
v_a_3010_ = v_a_3045_;
v_a_3011_ = v_a_3046_;
goto v___jp_3000_;
}
else
{
size_t v___x_3064_; size_t v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = ((size_t)0ULL);
v___x_3065_ = lean_usize_of_nat(v___x_3061_);
lean_inc_ref(v___y_2818_);
lean_inc_ref(v_pkg_2813_);
v___x_3066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2813_, v___x_3059_, v___x_3064_, v___x_3065_, v_a_3045_, v___y_2818_, v___x_2811_, v___y_2820_, v___y_2821_, v___y_2822_, v_a_3046_);
lean_dec_ref(v___x_3059_);
v___y_3023_ = v_moreLinkLibs_3052_;
v___y_3024_ = v_buildDir_3049_;
v___y_3025_ = v_moreLinkArgs_3057_;
v___y_3026_ = v_weakLinkArgs_3054_;
v___y_3027_ = v___x_3060_;
v___y_3028_ = v_moreLinkLibs_3056_;
v___y_3029_ = v_nativeLibDir_3050_;
v___y_3030_ = v_weakLinkArgs_3058_;
v___y_3031_ = v_moreLinkArgs_3053_;
v___y_3032_ = v___x_3066_;
goto v___jp_3022_;
}
}
else
{
size_t v___x_3067_; size_t v___x_3068_; lean_object* v___x_3069_; 
v___x_3067_ = ((size_t)0ULL);
v___x_3068_ = lean_usize_of_nat(v___x_3061_);
lean_inc_ref(v___y_2818_);
lean_inc_ref(v_pkg_2813_);
v___x_3069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__8(v_pkg_2813_, v___x_3059_, v___x_3067_, v___x_3068_, v_a_3045_, v___y_2818_, v___x_2811_, v___y_2820_, v___y_2821_, v___y_2822_, v_a_3046_);
lean_dec_ref(v___x_3059_);
v___y_3023_ = v_moreLinkLibs_3052_;
v___y_3024_ = v_buildDir_3049_;
v___y_3025_ = v_moreLinkArgs_3057_;
v___y_3026_ = v_weakLinkArgs_3054_;
v___y_3027_ = v___x_3060_;
v___y_3028_ = v_moreLinkLibs_3056_;
v___y_3029_ = v_nativeLibDir_3050_;
v___y_3030_ = v_weakLinkArgs_3058_;
v___y_3031_ = v_moreLinkArgs_3053_;
v___y_3032_ = v___x_3069_;
goto v___jp_3022_;
}
}
}
}
else
{
lean_object* v_a_3088_; lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec_ref(v___y_2818_);
lean_dec_ref(v_config_2816_);
lean_dec(v_name_2814_);
lean_dec_ref(v_pkg_2813_);
lean_dec(v___x_2811_);
lean_dec_ref(v_dir_2810_);
lean_dec_ref(v_self_2809_);
v_a_3088_ = lean_ctor_get(v___x_2997_, 0);
v_a_3089_ = lean_ctor_get(v___x_2997_, 1);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_2997_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_inc(v_a_3088_);
lean_dec(v___x_2997_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3088_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec_ref(v___y_2818_);
lean_dec_ref(v_config_2816_);
lean_dec(v_name_2814_);
lean_dec_ref(v_pkg_2813_);
lean_dec(v___x_2811_);
lean_dec_ref(v_dir_2810_);
lean_dec_ref(v_self_2809_);
v_a_3097_ = lean_ctor_get(v___x_2994_, 0);
v_a_3098_ = lean_ctor_get(v___x_2994_, 1);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_2994_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_inc(v_a_3097_);
lean_dec(v___x_2994_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3097_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
v___jp_2825_:
{
lean_object* v___x_2828_; 
v___x_2828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2828_, 0, v_a_2826_);
lean_ctor_set(v___x_2828_, 1, v_a_2827_);
return v___x_2828_;
}
v___jp_2829_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; uint8_t v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
lean_inc_ref(v_self_2809_);
v___x_2839_ = l_Lake_LeanLib_libName(v_self_2809_);
v___x_2840_ = l_System_FilePath_normalize(v___y_2830_);
v___x_2841_ = l_Lake_joinRelative(v_dir_2810_, v___x_2840_);
v___x_2842_ = l_System_FilePath_normalize(v___y_2836_);
v___x_2843_ = l_Lake_joinRelative(v___x_2841_, v___x_2842_);
v___x_2844_ = 0;
v___x_2845_ = l_Lake_nameToSharedLib(v___x_2839_, v___x_2844_);
v___x_2846_ = l_Lake_joinRelative(v___x_2843_, v___x_2845_);
v___x_2847_ = l_Array_append___redArg(v___y_2833_, v___y_2835_);
v___x_2848_ = l_Array_append___redArg(v___y_2834_, v___y_2832_);
v___x_2849_ = l_Lake_LeanLib_isPlugin(v_self_2809_);
v___x_2850_ = l_System_Platform_isWindows;
v___x_2851_ = lean_box(0);
v___x_2852_ = lean_obj_once(&l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2, &l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2_once, _init_l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__2);
v___x_2853_ = l_Lake_buildLeanSharedLib(v___x_2839_, v___x_2846_, v___y_2831_, v_a_2837_, v___x_2847_, v___x_2848_, v___x_2849_, v___x_2850_, v___x_2851_, v___y_2818_, v___x_2811_, v___y_2820_, v___y_2821_, v___y_2822_, v___x_2852_);
lean_dec(v___x_2811_);
lean_dec_ref(v___y_2831_);
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
lean_ctor_set(v___x_2854_, 1, v_a_2838_);
return v___x_2854_;
}
v___jp_2855_:
{
if (lean_obj_tag(v___y_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v_a_2865_; 
v_a_2864_ = lean_ctor_get(v___y_2863_, 0);
lean_inc(v_a_2864_);
v_a_2865_ = lean_ctor_get(v___y_2863_, 1);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___y_2863_, 2);
v___y_2830_ = v___y_2856_;
v___y_2831_ = v___y_2857_;
v___y_2832_ = v___y_2858_;
v___y_2833_ = v___y_2859_;
v___y_2834_ = v___y_2862_;
v___y_2835_ = v___y_2861_;
v___y_2836_ = v___y_2860_;
v_a_2837_ = v_a_2864_;
v_a_2838_ = v_a_2865_;
goto v___jp_2829_;
}
else
{
lean_object* v_a_2866_; lean_object* v_a_2867_; 
lean_dec_ref(v___y_2862_);
lean_dec_ref(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec_ref(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec_ref(v___y_2818_);
lean_dec(v___x_2811_);
lean_dec_ref(v_dir_2810_);
lean_dec_ref(v_self_2809_);
v_a_2866_ = lean_ctor_get(v___y_2863_, 0);
lean_inc(v_a_2866_);
v_a_2867_ = lean_ctor_get(v___y_2863_, 1);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___y_2863_, 2);
v_a_2826_ = v_a_2866_;
v_a_2827_ = v_a_2867_;
goto v___jp_2825_;
}
}
v___jp_2868_:
{
lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2880_ = lean_array_get_size(v___y_2879_);
v___x_2881_ = lean_nat_dec_lt(v___y_2875_, v___x_2880_);
if (v___x_2881_ == 0)
{
lean_dec_ref(v___y_2879_);
v___y_2830_ = v___y_2870_;
v___y_2831_ = v___y_2871_;
v___y_2832_ = v___y_2872_;
v___y_2833_ = v___y_2874_;
v___y_2834_ = v___y_2878_;
v___y_2835_ = v___y_2877_;
v___y_2836_ = v___y_2876_;
v_a_2837_ = v___y_2873_;
v_a_2838_ = v___y_2869_;
goto v___jp_2829_;
}
else
{
uint8_t v___x_2882_; 
v___x_2882_ = lean_nat_dec_le(v___x_2880_, v___x_2880_);
if (v___x_2882_ == 0)
{
if (v___x_2881_ == 0)
{
lean_dec_ref(v___y_2879_);
v___y_2830_ = v___y_2870_;
v___y_2831_ = v___y_2871_;
v___y_2832_ = v___y_2872_;
v___y_2833_ = v___y_2874_;
v___y_2834_ = v___y_2878_;
v___y_2835_ = v___y_2877_;
v___y_2836_ = v___y_2876_;
v_a_2837_ = v___y_2873_;
v_a_2838_ = v___y_2869_;
goto v___jp_2829_;
}
else
{
size_t v___x_2883_; size_t v___x_2884_; lean_object* v___x_2885_; 
v___x_2883_ = ((size_t)0ULL);
v___x_2884_ = lean_usize_of_nat(v___x_2880_);
lean_inc_ref(v___y_2818_);
v___x_2885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2879_, v___x_2883_, v___x_2884_, v___y_2873_, v___y_2818_, v___x_2811_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2869_);
lean_dec_ref(v___y_2879_);
v___y_2856_ = v___y_2870_;
v___y_2857_ = v___y_2871_;
v___y_2858_ = v___y_2872_;
v___y_2859_ = v___y_2874_;
v___y_2860_ = v___y_2876_;
v___y_2861_ = v___y_2877_;
v___y_2862_ = v___y_2878_;
v___y_2863_ = v___x_2885_;
goto v___jp_2855_;
}
}
else
{
size_t v___x_2886_; size_t v___x_2887_; lean_object* v___x_2888_; 
v___x_2886_ = ((size_t)0ULL);
v___x_2887_ = lean_usize_of_nat(v___x_2880_);
lean_inc_ref(v___y_2818_);
v___x_2888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__2(v___y_2879_, v___x_2886_, v___x_2887_, v___y_2873_, v___y_2818_, v___x_2811_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2869_);
lean_dec_ref(v___y_2879_);
v___y_2856_ = v___y_2870_;
v___y_2857_ = v___y_2871_;
v___y_2858_ = v___y_2872_;
v___y_2859_ = v___y_2874_;
v___y_2860_ = v___y_2876_;
v___y_2861_ = v___y_2877_;
v___y_2862_ = v___y_2878_;
v___y_2863_ = v___x_2888_;
goto v___jp_2855_;
}
}
}
v___jp_2889_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; 
v___x_2900_ = lean_mk_empty_array_with_capacity(v___y_2894_);
v___x_2901_ = lean_array_get_size(v_targetDecls_2812_);
v___x_2902_ = lean_nat_dec_lt(v___y_2894_, v___x_2901_);
if (v___x_2902_ == 0)
{
lean_dec_ref(v_pkg_2813_);
v___y_2869_ = v_a_2899_;
v___y_2870_ = v___y_2890_;
v___y_2871_ = v___y_2891_;
v___y_2872_ = v___y_2892_;
v___y_2873_ = v_a_2898_;
v___y_2874_ = v___y_2893_;
v___y_2875_ = v___y_2894_;
v___y_2876_ = v___y_2897_;
v___y_2877_ = v___y_2896_;
v___y_2878_ = v___y_2895_;
v___y_2879_ = v___x_2900_;
goto v___jp_2868_;
}
else
{
size_t v___x_2903_; size_t v___x_2904_; lean_object* v___x_2905_; 
v___x_2903_ = ((size_t)0ULL);
v___x_2904_ = lean_usize_of_nat(v___x_2901_);
v___x_2905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__3(v_pkg_2813_, v_targetDecls_2812_, v___x_2903_, v___x_2904_, v___x_2900_);
v___y_2869_ = v_a_2899_;
v___y_2870_ = v___y_2890_;
v___y_2871_ = v___y_2891_;
v___y_2872_ = v___y_2892_;
v___y_2873_ = v_a_2898_;
v___y_2874_ = v___y_2893_;
v___y_2875_ = v___y_2894_;
v___y_2876_ = v___y_2897_;
v___y_2877_ = v___y_2896_;
v___y_2878_ = v___y_2895_;
v___y_2879_ = v___x_2905_;
goto v___jp_2868_;
}
}
v___jp_2906_:
{
if (lean_obj_tag(v___y_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v_a_2917_; 
v_a_2916_ = lean_ctor_get(v___y_2915_, 0);
lean_inc(v_a_2916_);
v_a_2917_ = lean_ctor_get(v___y_2915_, 1);
lean_inc(v_a_2917_);
lean_dec_ref_known(v___y_2915_, 2);
v___y_2890_ = v___y_2907_;
v___y_2891_ = v___y_2908_;
v___y_2892_ = v___y_2909_;
v___y_2893_ = v___y_2910_;
v___y_2894_ = v___y_2911_;
v___y_2895_ = v___y_2914_;
v___y_2896_ = v___y_2913_;
v___y_2897_ = v___y_2912_;
v_a_2898_ = v_a_2916_;
v_a_2899_ = v_a_2917_;
goto v___jp_2889_;
}
else
{
lean_object* v_a_2918_; lean_object* v_a_2919_; 
lean_dec_ref(v___y_2914_);
lean_dec_ref(v___y_2912_);
lean_dec_ref(v___y_2910_);
lean_dec_ref(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec_ref(v___y_2818_);
lean_dec_ref(v_pkg_2813_);
lean_dec(v___x_2811_);
lean_dec_ref(v_dir_2810_);
lean_dec_ref(v_self_2809_);
v_a_2918_ = lean_ctor_get(v___y_2915_, 0);
lean_inc(v_a_2918_);
v_a_2919_ = lean_ctor_get(v___y_2915_, 1);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___y_2915_, 2);
v_a_2826_ = v_a_2918_;
v_a_2827_ = v_a_2919_;
goto v___jp_2825_;
}
}
v___jp_2920_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; uint8_t v___x_2935_; 
v___x_2933_ = l_Array_append___redArg(v___y_2921_, v___y_2927_);
v___x_2934_ = lean_array_get_size(v___x_2933_);
v___x_2935_ = lean_nat_dec_lt(v___y_2926_, v___x_2934_);
if (v___x_2935_ == 0)
{
lean_dec_ref(v___x_2933_);
v___y_2890_ = v___y_2922_;
v___y_2891_ = v___y_2923_;
v___y_2892_ = v___y_2924_;
v___y_2893_ = v___y_2925_;
v___y_2894_ = v___y_2926_;
v___y_2895_ = v___y_2930_;
v___y_2896_ = v___y_2929_;
v___y_2897_ = v___y_2928_;
v_a_2898_ = v_snd_2931_;
v_a_2899_ = v_a_2932_;
goto v___jp_2889_;
}
else
{
uint8_t v___x_2936_; 
v___x_2936_ = lean_nat_dec_le(v___x_2934_, v___x_2934_);
if (v___x_2936_ == 0)
{
if (v___x_2935_ == 0)
{
lean_dec_ref(v___x_2933_);
v___y_2890_ = v___y_2922_;
v___y_2891_ = v___y_2923_;
v___y_2892_ = v___y_2924_;
v___y_2893_ = v___y_2925_;
v___y_2894_ = v___y_2926_;
v___y_2895_ = v___y_2930_;
v___y_2896_ = v___y_2929_;
v___y_2897_ = v___y_2928_;
v_a_2898_ = v_snd_2931_;
v_a_2899_ = v_a_2932_;
goto v___jp_2889_;
}
else
{
size_t v___x_2937_; size_t v___x_2938_; lean_object* v___x_2939_; 
v___x_2937_ = ((size_t)0ULL);
v___x_2938_ = lean_usize_of_nat(v___x_2934_);
lean_inc_ref(v___y_2818_);
lean_inc_ref(v_pkg_2813_);
v___x_2939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2813_, v___x_2933_, v___x_2937_, v___x_2938_, v_snd_2931_, v___y_2818_, v___x_2811_, v___y_2820_, v___y_2821_, v___y_2822_, v_a_2932_);
lean_dec_ref(v___x_2933_);
v___y_2907_ = v___y_2922_;
v___y_2908_ = v___y_2923_;
v___y_2909_ = v___y_2924_;
v___y_2910_ = v___y_2925_;
v___y_2911_ = v___y_2926_;
v___y_2912_ = v___y_2928_;
v___y_2913_ = v___y_2929_;
v___y_2914_ = v___y_2930_;
v___y_2915_ = v___x_2939_;
goto v___jp_2906_;
}
}
else
{
size_t v___x_2940_; size_t v___x_2941_; lean_object* v___x_2942_; 
v___x_2940_ = ((size_t)0ULL);
v___x_2941_ = lean_usize_of_nat(v___x_2934_);
lean_inc_ref(v___y_2818_);
lean_inc_ref(v_pkg_2813_);
v___x_2942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__4(v_pkg_2813_, v___x_2933_, v___x_2940_, v___x_2941_, v_snd_2931_, v___y_2818_, v___x_2811_, v___y_2820_, v___y_2821_, v___y_2822_, v_a_2932_);
lean_dec_ref(v___x_2933_);
v___y_2907_ = v___y_2922_;
v___y_2908_ = v___y_2923_;
v___y_2909_ = v___y_2924_;
v___y_2910_ = v___y_2925_;
v___y_2911_ = v___y_2926_;
v___y_2912_ = v___y_2928_;
v___y_2913_ = v___y_2929_;
v___y_2914_ = v___y_2930_;
v___y_2915_ = v___x_2942_;
goto v___jp_2906_;
}
}
}
v___jp_2943_:
{
lean_object* v_toArray_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2976_; 
v_toArray_2956_ = lean_ctor_get(v_a_2954_, 1);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_a_2954_);
if (v_isSharedCheck_2976_ == 0)
{
lean_object* v_unused_2977_; 
v_unused_2977_ = lean_ctor_get(v_a_2954_, 0);
lean_dec(v_unused_2977_);
v___x_2958_ = v_a_2954_;
v_isShared_2959_ = v_isSharedCheck_2976_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_toArray_2956_);
lean_dec(v_a_2954_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2976_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2960_ = lean_mk_empty_array_with_capacity(v___y_2950_);
v___x_2961_ = lean_array_get_size(v_toArray_2956_);
v___x_2962_ = lean_nat_dec_lt(v___y_2950_, v___x_2961_);
if (v___x_2962_ == 0)
{
lean_del_object(v___x_2958_);
lean_dec_ref(v_toArray_2956_);
lean_dec(v_name_2814_);
v___y_2921_ = v___y_2944_;
v___y_2922_ = v___y_2945_;
v___y_2923_ = v___y_2946_;
v___y_2924_ = v___y_2947_;
v___y_2925_ = v___y_2948_;
v___y_2926_ = v___y_2950_;
v___y_2927_ = v___y_2949_;
v___y_2928_ = v___y_2953_;
v___y_2929_ = v___y_2952_;
v___y_2930_ = v___y_2951_;
v_snd_2931_ = v___x_2960_;
v_a_2932_ = v_a_2955_;
goto v___jp_2920_;
}
else
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2963_ = l_Lean_NameSet_empty;
v___x_2964_ = l_Lean_NameSet_insert(v___x_2963_, v_name_2814_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 1, v___x_2960_);
lean_ctor_set(v___x_2958_, 0, v___x_2964_);
v___x_2966_ = v___x_2958_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2964_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v___x_2960_);
v___x_2966_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
size_t v___x_2967_; size_t v___x_2968_; lean_object* v___x_2969_; 
v___x_2967_ = ((size_t)0ULL);
v___x_2968_ = lean_usize_of_nat(v___x_2961_);
lean_inc_ref(v___y_2818_);
v___x_2969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared_spec__6(v_toArray_2956_, v___x_2967_, v___x_2968_, v___x_2966_, v___y_2818_, v___x_2811_, v___y_2820_, v___y_2821_, v___y_2822_, v_a_2955_);
lean_dec_ref(v_toArray_2956_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v_a_2971_; lean_object* v_snd_2972_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
v_a_2971_ = lean_ctor_get(v___x_2969_, 1);
lean_inc(v_a_2971_);
lean_dec_ref_known(v___x_2969_, 2);
v_snd_2972_ = lean_ctor_get(v_a_2970_, 1);
lean_inc(v_snd_2972_);
lean_dec(v_a_2970_);
v___y_2921_ = v___y_2944_;
v___y_2922_ = v___y_2945_;
v___y_2923_ = v___y_2946_;
v___y_2924_ = v___y_2947_;
v___y_2925_ = v___y_2948_;
v___y_2926_ = v___y_2950_;
v___y_2927_ = v___y_2949_;
v___y_2928_ = v___y_2953_;
v___y_2929_ = v___y_2952_;
v___y_2930_ = v___y_2951_;
v_snd_2931_ = v_snd_2972_;
v_a_2932_ = v_a_2971_;
goto v___jp_2920_;
}
else
{
lean_object* v_a_2973_; lean_object* v_a_2974_; 
lean_dec_ref(v___y_2953_);
lean_dec_ref(v___y_2951_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v___y_2946_);
lean_dec_ref(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec_ref(v___y_2818_);
lean_dec_ref(v_pkg_2813_);
lean_dec(v___x_2811_);
lean_dec_ref(v_dir_2810_);
lean_dec_ref(v_self_2809_);
v_a_2973_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2973_);
v_a_2974_ = lean_ctor_get(v___x_2969_, 1);
lean_inc(v_a_2974_);
lean_dec_ref_known(v___x_2969_, 2);
v_a_2826_ = v_a_2973_;
v_a_2827_ = v_a_2974_;
goto v___jp_2825_;
}
}
}
}
}
v___jp_2978_:
{
if (lean_obj_tag(v___y_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v_a_2991_; 
v_a_2990_ = lean_ctor_get(v___y_2989_, 0);
lean_inc(v_a_2990_);
v_a_2991_ = lean_ctor_get(v___y_2989_, 1);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___y_2989_, 2);
v___y_2944_ = v___y_2979_;
v___y_2945_ = v___y_2980_;
v___y_2946_ = v___y_2981_;
v___y_2947_ = v___y_2982_;
v___y_2948_ = v___y_2983_;
v___y_2949_ = v___y_2985_;
v___y_2950_ = v___y_2984_;
v___y_2951_ = v___y_2988_;
v___y_2952_ = v___y_2987_;
v___y_2953_ = v___y_2986_;
v_a_2954_ = v_a_2990_;
v_a_2955_ = v_a_2991_;
goto v___jp_2943_;
}
else
{
lean_object* v_a_2992_; lean_object* v_a_2993_; 
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2986_);
lean_dec_ref(v___y_2983_);
lean_dec_ref(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec_ref(v___y_2818_);
lean_dec(v_name_2814_);
lean_dec_ref(v_pkg_2813_);
lean_dec(v___x_2811_);
lean_dec_ref(v_dir_2810_);
lean_dec_ref(v_self_2809_);
v_a_2992_ = lean_ctor_get(v___y_2989_, 0);
lean_inc(v_a_2992_);
v_a_2993_ = lean_ctor_get(v___y_2989_, 1);
lean_inc(v_a_2993_);
lean_dec_ref_known(v___y_2989_, 2);
v_a_2826_ = v_a_2992_;
v_a_2827_ = v_a_2993_;
goto v___jp_2825_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed(lean_object* v_self_3106_, lean_object* v_dir_3107_, lean_object* v___x_3108_, lean_object* v_targetDecls_3109_, lean_object* v_pkg_3110_, lean_object* v_name_3111_, lean_object* v___x_3112_, lean_object* v_config_3113_, lean_object* v_config_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0(v_self_3106_, v_dir_3107_, v___x_3108_, v_targetDecls_3109_, v_pkg_3110_, v_name_3111_, v___x_3112_, v_config_3113_, v_config_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec(v_config_3114_);
lean_dec_ref(v_targetDecls_3109_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(lean_object* v_self_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v_pkg_3132_; lean_object* v_name_3133_; lean_object* v_config_3134_; lean_object* v_keyName_3135_; lean_object* v_dir_3136_; lean_object* v_config_3137_; lean_object* v_targetDecls_3138_; lean_object* v___x_3139_; uint8_t v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___f_3149_; uint8_t v___x_3150_; lean_object* v___x_3151_; 
v_pkg_3132_ = lean_ctor_get(v_self_3124_, 0);
lean_inc_ref_n(v_pkg_3132_, 2);
v_name_3133_ = lean_ctor_get(v_self_3124_, 1);
lean_inc_n(v_name_3133_, 3);
v_config_3134_ = lean_ctor_get(v_self_3124_, 2);
lean_inc(v_config_3134_);
v_keyName_3135_ = lean_ctor_get(v_pkg_3132_, 2);
v_dir_3136_ = lean_ctor_get(v_pkg_3132_, 4);
lean_inc_ref(v_dir_3136_);
v_config_3137_ = lean_ctor_get(v_pkg_3132_, 6);
lean_inc_ref(v_config_3137_);
v_targetDecls_3138_ = lean_ctor_get(v_pkg_3132_, 15);
lean_inc_ref(v_targetDecls_3138_);
v___x_3139_ = l_Lake_instDataKindDynlib;
v___x_3140_ = 1;
v___x_3141_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3133_, v___x_3140_);
v___x_3142_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___closed__0));
v___x_3143_ = lean_string_append(v___x_3141_, v___x_3142_);
v___x_3144_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_3135_);
v___x_3145_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3145_, 0, v_keyName_3135_);
lean_ctor_set(v___x_3145_, 1, v_name_3133_);
v___x_3146_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3124_);
v___x_3147_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3145_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
lean_ctor_set(v___x_3147_, 2, v_self_3124_);
lean_ctor_set(v___x_3147_, 3, v___x_3144_);
v___x_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3148_, 0, v_pkg_3132_);
v___f_3149_ = lean_alloc_closure((void*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3149_, 0, v_self_3124_);
lean_closure_set(v___f_3149_, 1, v_dir_3136_);
lean_closure_set(v___f_3149_, 2, v___x_3148_);
lean_closure_set(v___f_3149_, 3, v_targetDecls_3138_);
lean_closure_set(v___f_3149_, 4, v_pkg_3132_);
lean_closure_set(v___f_3149_, 5, v_name_3133_);
lean_closure_set(v___f_3149_, 6, v___x_3147_);
lean_closure_set(v___f_3149_, 7, v_config_3137_);
lean_closure_set(v___f_3149_, 8, v_config_3134_);
v___x_3150_ = 0;
v___x_3151_ = l_Lake_ensureJob___redArg(v___x_3139_, v___f_3149_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3176_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_a_3153_ = lean_ctor_get(v___x_3151_, 1);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3155_ = v___x_3151_;
v_isShared_3156_ = v_isSharedCheck_3176_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3176_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v_task_3157_; lean_object* v_kind_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3174_; 
v_task_3157_ = lean_ctor_get(v_a_3152_, 0);
v_kind_3158_ = lean_ctor_get(v_a_3152_, 1);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_a_3152_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v_a_3152_, 2);
lean_dec(v_unused_3175_);
v___x_3160_ = v_a_3152_;
v_isShared_3161_ = v_isSharedCheck_3174_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_kind_3158_);
lean_inc(v_task_3157_);
lean_dec(v_a_3152_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3174_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v_registeredJobs_3162_; lean_object* v_job_3164_; 
v_registeredJobs_3162_ = lean_ctor_get(v_a_3129_, 4);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 2, v___x_3143_);
v_job_3164_ = v___x_3160_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_task_3157_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v_kind_3158_);
lean_ctor_set(v_reuseFailAlloc_3173_, 2, v___x_3143_);
v_job_3164_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3171_; 
lean_ctor_set_uint8(v_job_3164_, sizeof(void*)*3, v___x_3150_);
v___x_3165_ = lean_st_ref_take(v_registeredJobs_3162_);
lean_inc_ref(v_job_3164_);
v___x_3166_ = l_Lake_Job_toOpaque___redArg(v_job_3164_);
v___x_3167_ = lean_array_push(v___x_3165_, v___x_3166_);
v___x_3168_ = lean_st_ref_put(v_registeredJobs_3162_, v___x_3167_);
v___x_3169_ = l_Lake_Job_renew___redArg(v_job_3164_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v___x_3169_);
v___x_3171_ = v___x_3155_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3169_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_a_3153_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3143_);
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared___boxed(lean_object* v_self_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildShared(v_self_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_);
lean_dec_ref(v_a_3182_);
lean_dec(v_a_3181_);
lean_dec(v_a_3180_);
lean_dec(v_a_3179_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(uint8_t v_fmt_3186_, lean_object* v_a_3187_){
_start:
{
if (v_fmt_3186_ == 0)
{
lean_object* v_path_3188_; 
v_path_3188_ = lean_ctor_get(v_a_3187_, 0);
lean_inc_ref(v_path_3188_);
return v_path_3188_;
}
else
{
lean_object* v_path_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v_path_3189_ = lean_ctor_get(v_a_3187_, 0);
lean_inc_ref(v_path_3189_);
v___x_3190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3190_, 0, v_path_3189_);
v___x_3191_ = l_Lean_Json_compress(v___x_3190_);
return v___x_3191_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0___boxed(lean_object* v_fmt_3192_, lean_object* v_a_3193_){
_start:
{
uint8_t v_fmt_boxed_3194_; lean_object* v_res_3195_; 
v_fmt_boxed_3194_ = lean_unbox(v_fmt_3192_);
v_res_3195_ = l_Lake_formatQuery___at___00Lake_LeanLib_sharedFacetConfig_spec__0(v_fmt_boxed_3194_, v_a_3193_);
lean_dec_ref(v_a_3193_);
return v_res_3195_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3198_; uint8_t v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___f_3198_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__0));
v___x_3199_ = 1;
v___x_3200_ = l_Lake_instDataKindDynlib;
v___x_3201_ = ((lean_object*)(l_Lake_LeanLib_sharedFacetConfig___closed__1));
v___x_3202_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3203_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
lean_ctor_set(v___x_3203_, 1, v___x_3201_);
lean_ctor_set(v___x_3203_, 2, v___x_3200_);
lean_ctor_set(v___x_3203_, 3, v___f_3198_);
lean_ctor_set_uint8(v___x_3203_, sizeof(void*)*4, v___x_3199_);
lean_ctor_set_uint8(v___x_3203_, sizeof(void*)*4 + 1, v___x_3199_);
return v___x_3203_;
}
}
static lean_object* _init_l_Lake_LeanLib_sharedFacetConfig(void){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = lean_obj_once(&l_Lake_LeanLib_sharedFacetConfig___closed__2, &l_Lake_LeanLib_sharedFacetConfig___closed__2_once, _init_l_Lake_LeanLib_sharedFacetConfig___closed__2);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(lean_object* v___x_3205_, lean_object* v_as_3206_, size_t v_sz_3207_, size_t v_i_3208_, lean_object* v_b_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
uint8_t v___x_3217_; 
v___x_3217_ = lean_usize_dec_lt(v_i_3208_, v_sz_3207_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; 
lean_dec_ref(v___y_3210_);
lean_dec_ref(v___x_3205_);
v___x_3218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3218_, 0, v_b_3209_);
lean_ctor_set(v___x_3218_, 1, v___y_3215_);
return v___x_3218_;
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3220_; 
v_a_3219_ = lean_array_uget_borrowed(v_as_3206_, v_i_3208_);
lean_inc_ref(v___y_3210_);
lean_inc_n(v_a_3219_, 2);
lean_inc_ref(v___x_3205_);
v___x_3220_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(v___x_3205_, v_a_3219_, v_a_3219_, v___x_3217_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v_a_3222_; lean_object* v_snd_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; size_t v___x_3226_; size_t v___x_3227_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
v_a_3222_ = lean_ctor_get(v___x_3220_, 1);
lean_inc(v_a_3222_);
lean_dec_ref_known(v___x_3220_, 2);
v_snd_3223_ = lean_ctor_get(v_a_3221_, 1);
lean_inc(v_snd_3223_);
lean_dec(v_a_3221_);
v___x_3224_ = l_Lake_Job_toOpaque___redArg(v_snd_3223_);
v___x_3225_ = l_Lake_Job_mix___redArg(v_b_3209_, v___x_3224_);
v___x_3226_ = ((size_t)1ULL);
v___x_3227_ = lean_usize_add(v_i_3208_, v___x_3226_);
v_i_3208_ = v___x_3227_;
v_b_3209_ = v___x_3225_;
v___y_3215_ = v_a_3222_;
goto _start;
}
else
{
lean_object* v_a_3229_; lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec_ref(v___y_3210_);
lean_dec_ref(v_b_3209_);
lean_dec_ref(v___x_3205_);
v_a_3229_ = lean_ctor_get(v___x_3220_, 0);
v_a_3230_ = lean_ctor_get(v___x_3220_, 1);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3220_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_inc(v_a_3229_);
lean_dec(v___x_3220_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3229_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1___boxed(lean_object* v___x_3238_, lean_object* v_as_3239_, lean_object* v_sz_3240_, lean_object* v_i_3241_, lean_object* v_b_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
size_t v_sz_boxed_3250_; size_t v_i_boxed_3251_; lean_object* v_res_3252_; 
v_sz_boxed_3250_ = lean_unbox_usize(v_sz_3240_);
lean_dec(v_sz_3240_);
v_i_boxed_3251_ = lean_unbox_usize(v_i_3241_);
lean_dec(v_i_3241_);
v_res_3252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v___x_3238_, v_as_3239_, v_sz_boxed_3250_, v_i_boxed_3251_, v_b_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v_as_3239_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(lean_object* v___x_3253_, lean_object* v_as_3254_, size_t v_sz_3255_, size_t v_i_3256_, lean_object* v_b_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
uint8_t v___x_3265_; 
v___x_3265_ = lean_usize_dec_lt(v_i_3256_, v_sz_3255_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; 
lean_dec_ref(v___y_3258_);
lean_dec_ref(v___x_3253_);
v___x_3266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3266_, 0, v_b_3257_);
lean_ctor_set(v___x_3266_, 1, v___y_3263_);
return v___x_3266_;
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3268_; 
v_a_3267_ = lean_array_uget_borrowed(v_as_3254_, v_i_3256_);
lean_inc_ref(v___y_3258_);
lean_inc(v_a_3267_);
lean_inc_ref(v___x_3253_);
v___x_3268_ = l_Lake_Package_fetchTargetJob(v___x_3253_, v_a_3267_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v_a_3270_; lean_object* v___x_3271_; size_t v___x_3272_; size_t v___x_3273_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
v_a_3270_ = lean_ctor_get(v___x_3268_, 1);
lean_inc(v_a_3270_);
lean_dec_ref_known(v___x_3268_, 2);
v___x_3271_ = l_Lake_Job_mix___redArg(v_b_3257_, v_a_3269_);
v___x_3272_ = ((size_t)1ULL);
v___x_3273_ = lean_usize_add(v_i_3256_, v___x_3272_);
v_i_3256_ = v___x_3273_;
v_b_3257_ = v___x_3271_;
v___y_3263_ = v_a_3270_;
goto _start;
}
else
{
lean_object* v_a_3275_; lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
lean_dec_ref(v___y_3258_);
lean_dec_ref(v_b_3257_);
lean_dec_ref(v___x_3253_);
v_a_3275_ = lean_ctor_get(v___x_3268_, 0);
v_a_3276_ = lean_ctor_get(v___x_3268_, 1);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3268_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_inc(v_a_3275_);
lean_dec(v___x_3268_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3275_);
lean_ctor_set(v_reuseFailAlloc_3282_, 1, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0___boxed(lean_object* v___x_3284_, lean_object* v_as_3285_, lean_object* v_sz_3286_, lean_object* v_i_3287_, lean_object* v_b_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
size_t v_sz_boxed_3296_; size_t v_i_boxed_3297_; lean_object* v_res_3298_; 
v_sz_boxed_3296_ = lean_unbox_usize(v_sz_3286_);
lean_dec(v_sz_3286_);
v_i_boxed_3297_ = lean_unbox_usize(v_i_3287_);
lean_dec(v_i_3287_);
v_res_3298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v___x_3284_, v_as_3285_, v_sz_boxed_3296_, v_i_boxed_3297_, v_b_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v_as_3285_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(lean_object* v_self_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v_pkg_3309_; lean_object* v_name_3310_; lean_object* v_config_3311_; lean_object* v_baseName_3312_; lean_object* v_keyName_3313_; uint8_t v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; uint8_t v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v_job_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_pkg_3309_ = lean_ctor_get(v_self_3301_, 0);
lean_inc_ref_n(v_pkg_3309_, 2);
v_name_3310_ = lean_ctor_get(v_self_3301_, 1);
lean_inc(v_name_3310_);
v_config_3311_ = lean_ctor_get(v_self_3301_, 2);
lean_inc(v_config_3311_);
lean_dec_ref(v_self_3301_);
v_baseName_3312_ = lean_ctor_get(v_pkg_3309_, 1);
v_keyName_3313_ = lean_ctor_get(v_pkg_3309_, 2);
v___x_3314_ = 1;
lean_inc(v_baseName_3312_);
v___x_3315_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3312_, v___x_3314_);
v___x_3316_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__0));
v___x_3317_ = lean_string_append(v___x_3315_, v___x_3316_);
v___x_3318_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3310_, v___x_3314_);
v___x_3319_ = lean_string_append(v___x_3317_, v___x_3318_);
lean_dec_ref(v___x_3318_);
v___x_3320_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___closed__1));
v___x_3321_ = lean_string_append(v___x_3319_, v___x_3320_);
v___x_3322_ = lean_box(0);
v___x_3323_ = lean_box(0);
v___x_3324_ = lean_unsigned_to_nat(0u);
v___x_3325_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildLean___closed__0));
v___x_3326_ = 0;
v___x_3327_ = 0;
v___x_3328_ = l_Lake_BuildTrace_nil(v___x_3321_);
v___x_3329_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3329_, 0, v___x_3325_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
lean_ctor_set(v___x_3329_, 2, v___x_3324_);
lean_ctor_set_uint8(v___x_3329_, sizeof(void*)*3, v___x_3326_);
lean_ctor_set_uint8(v___x_3329_, sizeof(void*)*3 + 1, v___x_3327_);
v___x_3330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3322_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = lean_task_pure(v___x_3330_);
v___x_3332_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recCollectLocalModules___lam__0___closed__0));
v_job_3333_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_3333_, 0, v___x_3331_);
lean_ctor_set(v_job_3333_, 1, v___x_3323_);
lean_ctor_set(v_job_3333_, 2, v___x_3332_);
lean_ctor_set_uint8(v_job_3333_, sizeof(void*)*3, v___x_3327_);
v___x_3334_ = l_Lake_Package_extraDepFacet;
lean_inc(v_keyName_3313_);
v___x_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3335_, 0, v_keyName_3313_);
v___x_3336_ = l_Lake_Package_keyword;
v___x_3337_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3335_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
lean_ctor_set(v___x_3337_, 2, v_pkg_3309_);
lean_ctor_set(v___x_3337_, 3, v___x_3334_);
lean_inc_ref(v_a_3302_);
lean_inc_ref(v_a_3306_);
lean_inc(v_a_3305_);
lean_inc(v_a_3304_);
lean_inc(v_a_3303_);
v___x_3338_ = lean_apply_7(v_a_3302_, v___x_3337_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, lean_box(0));
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v_a_3339_; lean_object* v_a_3340_; lean_object* v_needs_3341_; lean_object* v_extraDepTargets_3342_; lean_object* v___x_3343_; size_t v_sz_3344_; size_t v___x_3345_; lean_object* v___x_3346_; 
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
v_a_3340_ = lean_ctor_get(v___x_3338_, 1);
lean_inc(v_a_3340_);
lean_dec_ref_known(v___x_3338_, 2);
v_needs_3341_ = lean_ctor_get(v_config_3311_, 5);
lean_inc_ref(v_needs_3341_);
v_extraDepTargets_3342_ = lean_ctor_get(v_config_3311_, 6);
lean_inc_ref(v_extraDepTargets_3342_);
lean_dec(v_config_3311_);
v___x_3343_ = l_Lake_Job_mix___redArg(v_job_3333_, v_a_3339_);
v_sz_3344_ = lean_array_size(v_extraDepTargets_3342_);
v___x_3345_ = ((size_t)0ULL);
lean_inc_ref(v_a_3302_);
lean_inc_ref(v_pkg_3309_);
v___x_3346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__0(v_pkg_3309_, v_extraDepTargets_3342_, v_sz_3344_, v___x_3345_, v___x_3343_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3340_);
lean_dec_ref(v_extraDepTargets_3342_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; lean_object* v_a_3348_; size_t v_sz_3349_; lean_object* v___x_3350_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
v_a_3348_ = lean_ctor_get(v___x_3346_, 1);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3346_, 2);
v_sz_3349_ = lean_array_size(v_needs_3341_);
v___x_3350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets_spec__1(v_pkg_3309_, v_needs_3341_, v_sz_3349_, v___x_3345_, v_a_3347_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3348_);
lean_dec_ref(v_needs_3341_);
return v___x_3350_;
}
else
{
lean_dec_ref(v_needs_3341_);
lean_dec_ref(v_pkg_3309_);
lean_dec_ref(v_a_3302_);
return v___x_3346_;
}
}
else
{
lean_dec_ref_known(v_job_3333_, 3);
lean_dec(v_config_3311_);
lean_dec_ref(v_pkg_3309_);
lean_dec_ref(v_a_3302_);
return v___x_3338_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets___boxed(lean_object* v_self_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildExtraDepTargets(v_self_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_);
lean_dec_ref(v_a_3356_);
lean_dec(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec(v_a_3353_);
return v_res_3359_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3361_; uint8_t v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___f_3361_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3362_ = 1;
v___x_3363_ = l_Lake_instDataKindUnit;
v___x_3364_ = ((lean_object*)(l_Lake_LeanLib_extraDepFacetConfig___closed__0));
v___x_3365_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3366_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
lean_ctor_set(v___x_3366_, 1, v___x_3364_);
lean_ctor_set(v___x_3366_, 2, v___x_3363_);
lean_ctor_set(v___x_3366_, 3, v___f_3361_);
lean_ctor_set_uint8(v___x_3366_, sizeof(void*)*4, v___x_3362_);
lean_ctor_set_uint8(v___x_3366_, sizeof(void*)*4 + 1, v___x_3362_);
return v___x_3366_;
}
}
static lean_object* _init_l_Lake_LeanLib_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_3367_; 
v___x_3367_ = lean_obj_once(&l_Lake_LeanLib_extraDepFacetConfig___closed__1, &l_Lake_LeanLib_extraDepFacetConfig___closed__1_once, _init_l_Lake_LeanLib_extraDepFacetConfig___closed__1);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(lean_object* v_self_3368_, size_t v_sz_3369_, size_t v_i_3370_, lean_object* v_bs_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
uint8_t v___x_3379_; 
v___x_3379_ = lean_usize_dec_lt(v_i_3370_, v_sz_3369_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; 
lean_dec_ref(v___y_3372_);
lean_dec_ref(v_self_3368_);
v___x_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3380_, 0, v_bs_3371_);
lean_ctor_set(v___x_3380_, 1, v___y_3377_);
return v___x_3380_;
}
else
{
lean_object* v_pkg_3381_; lean_object* v_name_3382_; lean_object* v_keyName_3383_; lean_object* v_v_3384_; lean_object* v___x_3385_; lean_object* v_bs_x27_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v_pkg_3381_ = lean_ctor_get(v_self_3368_, 0);
v_name_3382_ = lean_ctor_get(v_self_3368_, 1);
v_keyName_3383_ = lean_ctor_get(v_pkg_3381_, 2);
v_v_3384_ = lean_array_uget(v_bs_3371_, v_i_3370_);
v___x_3385_ = lean_unsigned_to_nat(0u);
v_bs_x27_3386_ = lean_array_uset(v_bs_3371_, v_i_3370_, v___x_3385_);
lean_inc(v_name_3382_);
lean_inc(v_keyName_3383_);
v___x_3387_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3387_, 0, v_keyName_3383_);
lean_ctor_set(v___x_3387_, 1, v_name_3382_);
v___x_3388_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
lean_inc_ref(v_self_3368_);
v___x_3389_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3387_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
lean_ctor_set(v___x_3389_, 2, v_self_3368_);
lean_ctor_set(v___x_3389_, 3, v_v_3384_);
lean_inc_ref(v___y_3372_);
lean_inc_ref(v___y_3376_);
lean_inc(v___y_3375_);
lean_inc(v___y_3374_);
lean_inc(v___y_3373_);
v___x_3390_ = lean_apply_7(v___y_3372_, v___x_3389_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, lean_box(0));
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v_a_3392_; lean_object* v___x_3393_; size_t v___x_3394_; size_t v___x_3395_; lean_object* v___x_3396_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
v_a_3392_ = lean_ctor_get(v___x_3390_, 1);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3390_, 2);
v___x_3393_ = l_Lake_Job_toOpaque___redArg(v_a_3391_);
v___x_3394_ = ((size_t)1ULL);
v___x_3395_ = lean_usize_add(v_i_3370_, v___x_3394_);
v___x_3396_ = lean_array_uset(v_bs_x27_3386_, v_i_3370_, v___x_3393_);
v_i_3370_ = v___x_3395_;
v_bs_3371_ = v___x_3396_;
v___y_3377_ = v_a_3392_;
goto _start;
}
else
{
lean_object* v_a_3398_; lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec_ref(v_bs_x27_3386_);
lean_dec_ref(v___y_3372_);
lean_dec_ref(v_self_3368_);
v_a_3398_ = lean_ctor_get(v___x_3390_, 0);
v_a_3399_ = lean_ctor_get(v___x_3390_, 1);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3390_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_inc(v_a_3398_);
lean_dec(v___x_3390_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3398_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0___boxed(lean_object* v_self_3407_, lean_object* v_sz_3408_, lean_object* v_i_3409_, lean_object* v_bs_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
size_t v_sz_boxed_3418_; size_t v_i_boxed_3419_; lean_object* v_res_3420_; 
v_sz_boxed_3418_ = lean_unbox_usize(v_sz_3408_);
lean_dec(v_sz_3408_);
v_i_boxed_3419_ = lean_unbox_usize(v_i_3409_);
lean_dec(v_i_3409_);
v_res_3420_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3407_, v_sz_boxed_3418_, v_i_boxed_3419_, v_bs_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec(v___y_3412_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(lean_object* v_self_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_){
_start:
{
lean_object* v_config_3430_; lean_object* v_defaultFacets_3431_; size_t v_sz_3432_; size_t v___x_3433_; lean_object* v___x_3434_; 
v_config_3430_ = lean_ctor_get(v_self_3422_, 2);
v_defaultFacets_3431_ = lean_ctor_get(v_config_3430_, 7);
lean_inc_ref(v_defaultFacets_3431_);
v_sz_3432_ = lean_array_size(v_defaultFacets_3431_);
v___x_3433_ = ((size_t)0ULL);
v___x_3434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets_spec__0(v_self_3422_, v_sz_3432_, v___x_3433_, v_defaultFacets_3431_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3445_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_a_3436_ = lean_ctor_get(v___x_3434_, 1);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3438_ = v___x_3434_;
v_isShared_3439_ = v_isSharedCheck_3445_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3445_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3443_; 
v___x_3440_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___closed__0));
v___x_3441_ = l_Lake_Job_mixArray___redArg(v_a_3435_, v___x_3440_);
lean_dec(v_a_3435_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3441_);
v___x_3443_ = v___x_3438_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_a_3436_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
v_a_3446_ = lean_ctor_get(v___x_3434_, 0);
v_a_3447_ = lean_ctor_get(v___x_3434_, 1);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3434_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_inc(v_a_3446_);
lean_dec(v___x_3434_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3446_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets___boxed(lean_object* v_self_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l___private_Lake_Build_Library_0__Lake_LeanLib_recBuildDefaultFacets(v_self_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
lean_dec_ref(v_a_3460_);
lean_dec(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec(v_a_3457_);
return v_res_3463_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3465_; uint8_t v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v___f_3465_ = ((lean_object*)(l_Lake_LeanLib_leanArtsFacetConfig___closed__0));
v___x_3466_ = 1;
v___x_3467_ = l_Lake_instDataKindUnit;
v___x_3468_ = ((lean_object*)(l_Lake_LeanLib_defaultFacetConfig___closed__0));
v___x_3469_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig___closed__2));
v___x_3470_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
lean_ctor_set(v___x_3470_, 1, v___x_3468_);
lean_ctor_set(v___x_3470_, 2, v___x_3467_);
lean_ctor_set(v___x_3470_, 3, v___f_3465_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*4, v___x_3466_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*4 + 1, v___x_3466_);
return v___x_3470_;
}
}
static lean_object* _init_l_Lake_LeanLib_defaultFacetConfig(void){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = lean_obj_once(&l_Lake_LeanLib_defaultFacetConfig___closed__1, &l_Lake_LeanLib_defaultFacetConfig___closed__1_once, _init_l_Lake_LeanLib_defaultFacetConfig___closed__1);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(lean_object* v_k_3472_, lean_object* v_v_3473_, lean_object* v_t_3474_){
_start:
{
if (lean_obj_tag(v_t_3474_) == 0)
{
lean_object* v_size_3475_; lean_object* v_k_3476_; lean_object* v_v_3477_; lean_object* v_l_3478_; lean_object* v_r_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3759_; 
v_size_3475_ = lean_ctor_get(v_t_3474_, 0);
v_k_3476_ = lean_ctor_get(v_t_3474_, 1);
v_v_3477_ = lean_ctor_get(v_t_3474_, 2);
v_l_3478_ = lean_ctor_get(v_t_3474_, 3);
v_r_3479_ = lean_ctor_get(v_t_3474_, 4);
v_isSharedCheck_3759_ = !lean_is_exclusive(v_t_3474_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3481_ = v_t_3474_;
v_isShared_3482_ = v_isSharedCheck_3759_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_r_3479_);
lean_inc(v_l_3478_);
lean_inc(v_v_3477_);
lean_inc(v_k_3476_);
lean_inc(v_size_3475_);
lean_dec(v_t_3474_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3759_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
uint8_t v___x_3483_; 
v___x_3483_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3472_, v_k_3476_);
switch(v___x_3483_)
{
case 0:
{
lean_object* v_impl_3484_; lean_object* v___x_3485_; 
lean_dec(v_size_3475_);
v_impl_3484_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3472_, v_v_3473_, v_l_3478_);
v___x_3485_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3479_) == 0)
{
lean_object* v_size_3486_; lean_object* v_size_3487_; lean_object* v_k_3488_; lean_object* v_v_3489_; lean_object* v_l_3490_; lean_object* v_r_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
v_size_3486_ = lean_ctor_get(v_r_3479_, 0);
v_size_3487_ = lean_ctor_get(v_impl_3484_, 0);
lean_inc(v_size_3487_);
v_k_3488_ = lean_ctor_get(v_impl_3484_, 1);
lean_inc(v_k_3488_);
v_v_3489_ = lean_ctor_get(v_impl_3484_, 2);
lean_inc(v_v_3489_);
v_l_3490_ = lean_ctor_get(v_impl_3484_, 3);
lean_inc(v_l_3490_);
v_r_3491_ = lean_ctor_get(v_impl_3484_, 4);
lean_inc(v_r_3491_);
v___x_3492_ = lean_unsigned_to_nat(3u);
v___x_3493_ = lean_nat_mul(v___x_3492_, v_size_3486_);
v___x_3494_ = lean_nat_dec_lt(v___x_3493_, v_size_3487_);
lean_dec(v___x_3493_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3498_; 
lean_dec(v_r_3491_);
lean_dec(v_l_3490_);
lean_dec(v_v_3489_);
lean_dec(v_k_3488_);
v___x_3495_ = lean_nat_add(v___x_3485_, v_size_3487_);
lean_dec(v_size_3487_);
v___x_3496_ = lean_nat_add(v___x_3495_, v_size_3486_);
lean_dec(v___x_3495_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 3, v_impl_3484_);
lean_ctor_set(v___x_3481_, 0, v___x_3496_);
v___x_3498_ = v___x_3481_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3496_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3499_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3499_, 3, v_impl_3484_);
lean_ctor_set(v_reuseFailAlloc_3499_, 4, v_r_3479_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
else
{
lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3565_; 
v_isSharedCheck_3565_ = !lean_is_exclusive(v_impl_3484_);
if (v_isSharedCheck_3565_ == 0)
{
lean_object* v_unused_3566_; lean_object* v_unused_3567_; lean_object* v_unused_3568_; lean_object* v_unused_3569_; lean_object* v_unused_3570_; 
v_unused_3566_ = lean_ctor_get(v_impl_3484_, 4);
lean_dec(v_unused_3566_);
v_unused_3567_ = lean_ctor_get(v_impl_3484_, 3);
lean_dec(v_unused_3567_);
v_unused_3568_ = lean_ctor_get(v_impl_3484_, 2);
lean_dec(v_unused_3568_);
v_unused_3569_ = lean_ctor_get(v_impl_3484_, 1);
lean_dec(v_unused_3569_);
v_unused_3570_ = lean_ctor_get(v_impl_3484_, 0);
lean_dec(v_unused_3570_);
v___x_3501_ = v_impl_3484_;
v_isShared_3502_ = v_isSharedCheck_3565_;
goto v_resetjp_3500_;
}
else
{
lean_dec(v_impl_3484_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3565_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v_size_3503_; lean_object* v_size_3504_; lean_object* v_k_3505_; lean_object* v_v_3506_; lean_object* v_l_3507_; lean_object* v_r_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; 
v_size_3503_ = lean_ctor_get(v_l_3490_, 0);
v_size_3504_ = lean_ctor_get(v_r_3491_, 0);
v_k_3505_ = lean_ctor_get(v_r_3491_, 1);
v_v_3506_ = lean_ctor_get(v_r_3491_, 2);
v_l_3507_ = lean_ctor_get(v_r_3491_, 3);
v_r_3508_ = lean_ctor_get(v_r_3491_, 4);
v___x_3509_ = lean_unsigned_to_nat(2u);
v___x_3510_ = lean_nat_mul(v___x_3509_, v_size_3503_);
v___x_3511_ = lean_nat_dec_lt(v_size_3504_, v___x_3510_);
lean_dec(v___x_3510_);
if (v___x_3511_ == 0)
{
lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3540_; 
lean_inc(v_r_3508_);
lean_inc(v_l_3507_);
lean_inc(v_v_3506_);
lean_inc(v_k_3505_);
v_isSharedCheck_3540_ = !lean_is_exclusive(v_r_3491_);
if (v_isSharedCheck_3540_ == 0)
{
lean_object* v_unused_3541_; lean_object* v_unused_3542_; lean_object* v_unused_3543_; lean_object* v_unused_3544_; lean_object* v_unused_3545_; 
v_unused_3541_ = lean_ctor_get(v_r_3491_, 4);
lean_dec(v_unused_3541_);
v_unused_3542_ = lean_ctor_get(v_r_3491_, 3);
lean_dec(v_unused_3542_);
v_unused_3543_ = lean_ctor_get(v_r_3491_, 2);
lean_dec(v_unused_3543_);
v_unused_3544_ = lean_ctor_get(v_r_3491_, 1);
lean_dec(v_unused_3544_);
v_unused_3545_ = lean_ctor_get(v_r_3491_, 0);
lean_dec(v_unused_3545_);
v___x_3513_ = v_r_3491_;
v_isShared_3514_ = v_isSharedCheck_3540_;
goto v_resetjp_3512_;
}
else
{
lean_dec(v_r_3491_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3540_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___x_3528_; lean_object* v___y_3530_; 
v___x_3515_ = lean_nat_add(v___x_3485_, v_size_3487_);
lean_dec(v_size_3487_);
v___x_3516_ = lean_nat_add(v___x_3515_, v_size_3486_);
lean_dec(v___x_3515_);
v___x_3528_ = lean_nat_add(v___x_3485_, v_size_3503_);
if (lean_obj_tag(v_l_3507_) == 0)
{
lean_object* v_size_3538_; 
v_size_3538_ = lean_ctor_get(v_l_3507_, 0);
lean_inc(v_size_3538_);
v___y_3530_ = v_size_3538_;
goto v___jp_3529_;
}
else
{
lean_object* v___x_3539_; 
v___x_3539_ = lean_unsigned_to_nat(0u);
v___y_3530_ = v___x_3539_;
goto v___jp_3529_;
}
v___jp_3517_:
{
lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3521_ = lean_nat_add(v___y_3518_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec(v___y_3518_);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 4, v_r_3479_);
lean_ctor_set(v___x_3513_, 3, v_r_3508_);
lean_ctor_set(v___x_3513_, 2, v_v_3477_);
lean_ctor_set(v___x_3513_, 1, v_k_3476_);
lean_ctor_set(v___x_3513_, 0, v___x_3521_);
v___x_3523_ = v___x_3513_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3521_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3527_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3527_, 3, v_r_3508_);
lean_ctor_set(v_reuseFailAlloc_3527_, 4, v_r_3479_);
v___x_3523_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
lean_object* v___x_3525_; 
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 4, v___x_3523_);
lean_ctor_set(v___x_3501_, 3, v___y_3519_);
lean_ctor_set(v___x_3501_, 2, v_v_3506_);
lean_ctor_set(v___x_3501_, 1, v_k_3505_);
lean_ctor_set(v___x_3501_, 0, v___x_3516_);
v___x_3525_ = v___x_3501_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3516_);
lean_ctor_set(v_reuseFailAlloc_3526_, 1, v_k_3505_);
lean_ctor_set(v_reuseFailAlloc_3526_, 2, v_v_3506_);
lean_ctor_set(v_reuseFailAlloc_3526_, 3, v___y_3519_);
lean_ctor_set(v_reuseFailAlloc_3526_, 4, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
v___jp_3529_:
{
lean_object* v___x_3531_; lean_object* v___x_3533_; 
v___x_3531_ = lean_nat_add(v___x_3528_, v___y_3530_);
lean_dec(v___y_3530_);
lean_dec(v___x_3528_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 4, v_l_3507_);
lean_ctor_set(v___x_3481_, 3, v_l_3490_);
lean_ctor_set(v___x_3481_, 2, v_v_3489_);
lean_ctor_set(v___x_3481_, 1, v_k_3488_);
lean_ctor_set(v___x_3481_, 0, v___x_3531_);
v___x_3533_ = v___x_3481_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3531_);
lean_ctor_set(v_reuseFailAlloc_3537_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3537_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3537_, 3, v_l_3490_);
lean_ctor_set(v_reuseFailAlloc_3537_, 4, v_l_3507_);
v___x_3533_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
lean_object* v___x_3534_; 
v___x_3534_ = lean_nat_add(v___x_3485_, v_size_3486_);
if (lean_obj_tag(v_r_3508_) == 0)
{
lean_object* v_size_3535_; 
v_size_3535_ = lean_ctor_get(v_r_3508_, 0);
lean_inc(v_size_3535_);
v___y_3518_ = v___x_3534_;
v___y_3519_ = v___x_3533_;
v___y_3520_ = v_size_3535_;
goto v___jp_3517_;
}
else
{
lean_object* v___x_3536_; 
v___x_3536_ = lean_unsigned_to_nat(0u);
v___y_3518_ = v___x_3534_;
v___y_3519_ = v___x_3533_;
v___y_3520_ = v___x_3536_;
goto v___jp_3517_;
}
}
}
}
}
else
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3551_; 
lean_del_object(v___x_3481_);
v___x_3546_ = lean_nat_add(v___x_3485_, v_size_3487_);
lean_dec(v_size_3487_);
v___x_3547_ = lean_nat_add(v___x_3546_, v_size_3486_);
lean_dec(v___x_3546_);
v___x_3548_ = lean_nat_add(v___x_3485_, v_size_3486_);
v___x_3549_ = lean_nat_add(v___x_3548_, v_size_3504_);
lean_dec(v___x_3548_);
lean_inc_ref(v_r_3479_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 4, v_r_3479_);
lean_ctor_set(v___x_3501_, 3, v_r_3491_);
lean_ctor_set(v___x_3501_, 2, v_v_3477_);
lean_ctor_set(v___x_3501_, 1, v_k_3476_);
lean_ctor_set(v___x_3501_, 0, v___x_3549_);
v___x_3551_ = v___x_3501_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3564_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3564_, 3, v_r_3491_);
lean_ctor_set(v_reuseFailAlloc_3564_, 4, v_r_3479_);
v___x_3551_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
v_isSharedCheck_3558_ = !lean_is_exclusive(v_r_3479_);
if (v_isSharedCheck_3558_ == 0)
{
lean_object* v_unused_3559_; lean_object* v_unused_3560_; lean_object* v_unused_3561_; lean_object* v_unused_3562_; lean_object* v_unused_3563_; 
v_unused_3559_ = lean_ctor_get(v_r_3479_, 4);
lean_dec(v_unused_3559_);
v_unused_3560_ = lean_ctor_get(v_r_3479_, 3);
lean_dec(v_unused_3560_);
v_unused_3561_ = lean_ctor_get(v_r_3479_, 2);
lean_dec(v_unused_3561_);
v_unused_3562_ = lean_ctor_get(v_r_3479_, 1);
lean_dec(v_unused_3562_);
v_unused_3563_ = lean_ctor_get(v_r_3479_, 0);
lean_dec(v_unused_3563_);
v___x_3553_ = v_r_3479_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_dec(v_r_3479_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 4, v___x_3551_);
lean_ctor_set(v___x_3553_, 3, v_l_3490_);
lean_ctor_set(v___x_3553_, 2, v_v_3489_);
lean_ctor_set(v___x_3553_, 1, v_k_3488_);
lean_ctor_set(v___x_3553_, 0, v___x_3547_);
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3547_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_k_3488_);
lean_ctor_set(v_reuseFailAlloc_3557_, 2, v_v_3489_);
lean_ctor_set(v_reuseFailAlloc_3557_, 3, v_l_3490_);
lean_ctor_set(v_reuseFailAlloc_3557_, 4, v___x_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3571_; 
v_l_3571_ = lean_ctor_get(v_impl_3484_, 3);
lean_inc(v_l_3571_);
if (lean_obj_tag(v_l_3571_) == 0)
{
lean_object* v_r_3572_; lean_object* v_k_3573_; lean_object* v_v_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3585_; 
v_r_3572_ = lean_ctor_get(v_impl_3484_, 4);
v_k_3573_ = lean_ctor_get(v_impl_3484_, 1);
v_v_3574_ = lean_ctor_get(v_impl_3484_, 2);
v_isSharedCheck_3585_ = !lean_is_exclusive(v_impl_3484_);
if (v_isSharedCheck_3585_ == 0)
{
lean_object* v_unused_3586_; lean_object* v_unused_3587_; 
v_unused_3586_ = lean_ctor_get(v_impl_3484_, 3);
lean_dec(v_unused_3586_);
v_unused_3587_ = lean_ctor_get(v_impl_3484_, 0);
lean_dec(v_unused_3587_);
v___x_3576_ = v_impl_3484_;
v_isShared_3577_ = v_isSharedCheck_3585_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_r_3572_);
lean_inc(v_v_3574_);
lean_inc(v_k_3573_);
lean_dec(v_impl_3484_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3585_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3578_; lean_object* v___x_3580_; 
v___x_3578_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3572_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 3, v_r_3572_);
lean_ctor_set(v___x_3576_, 2, v_v_3477_);
lean_ctor_set(v___x_3576_, 1, v_k_3476_);
lean_ctor_set(v___x_3576_, 0, v___x_3485_);
v___x_3580_ = v___x_3576_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3584_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3584_, 3, v_r_3572_);
lean_ctor_set(v_reuseFailAlloc_3584_, 4, v_r_3572_);
v___x_3580_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
lean_object* v___x_3582_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 4, v___x_3580_);
lean_ctor_set(v___x_3481_, 3, v_l_3571_);
lean_ctor_set(v___x_3481_, 2, v_v_3574_);
lean_ctor_set(v___x_3481_, 1, v_k_3573_);
lean_ctor_set(v___x_3481_, 0, v___x_3578_);
v___x_3582_ = v___x_3481_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v_k_3573_);
lean_ctor_set(v_reuseFailAlloc_3583_, 2, v_v_3574_);
lean_ctor_set(v_reuseFailAlloc_3583_, 3, v_l_3571_);
lean_ctor_set(v_reuseFailAlloc_3583_, 4, v___x_3580_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
else
{
lean_object* v_r_3588_; 
v_r_3588_ = lean_ctor_get(v_impl_3484_, 4);
lean_inc(v_r_3588_);
if (lean_obj_tag(v_r_3588_) == 0)
{
lean_object* v_k_3589_; lean_object* v_v_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3613_; 
v_k_3589_ = lean_ctor_get(v_impl_3484_, 1);
v_v_3590_ = lean_ctor_get(v_impl_3484_, 2);
v_isSharedCheck_3613_ = !lean_is_exclusive(v_impl_3484_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; lean_object* v_unused_3615_; lean_object* v_unused_3616_; 
v_unused_3614_ = lean_ctor_get(v_impl_3484_, 4);
lean_dec(v_unused_3614_);
v_unused_3615_ = lean_ctor_get(v_impl_3484_, 3);
lean_dec(v_unused_3615_);
v_unused_3616_ = lean_ctor_get(v_impl_3484_, 0);
lean_dec(v_unused_3616_);
v___x_3592_ = v_impl_3484_;
v_isShared_3593_ = v_isSharedCheck_3613_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_v_3590_);
lean_inc(v_k_3589_);
lean_dec(v_impl_3484_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3613_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v_k_3594_; lean_object* v_v_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3609_; 
v_k_3594_ = lean_ctor_get(v_r_3588_, 1);
v_v_3595_ = lean_ctor_get(v_r_3588_, 2);
v_isSharedCheck_3609_ = !lean_is_exclusive(v_r_3588_);
if (v_isSharedCheck_3609_ == 0)
{
lean_object* v_unused_3610_; lean_object* v_unused_3611_; lean_object* v_unused_3612_; 
v_unused_3610_ = lean_ctor_get(v_r_3588_, 4);
lean_dec(v_unused_3610_);
v_unused_3611_ = lean_ctor_get(v_r_3588_, 3);
lean_dec(v_unused_3611_);
v_unused_3612_ = lean_ctor_get(v_r_3588_, 0);
lean_dec(v_unused_3612_);
v___x_3597_ = v_r_3588_;
v_isShared_3598_ = v_isSharedCheck_3609_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_v_3595_);
lean_inc(v_k_3594_);
lean_dec(v_r_3588_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3609_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3599_; lean_object* v___x_3601_; 
v___x_3599_ = lean_unsigned_to_nat(3u);
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 4, v_l_3571_);
lean_ctor_set(v___x_3597_, 3, v_l_3571_);
lean_ctor_set(v___x_3597_, 2, v_v_3590_);
lean_ctor_set(v___x_3597_, 1, v_k_3589_);
lean_ctor_set(v___x_3597_, 0, v___x_3485_);
v___x_3601_ = v___x_3597_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_k_3589_);
lean_ctor_set(v_reuseFailAlloc_3608_, 2, v_v_3590_);
lean_ctor_set(v_reuseFailAlloc_3608_, 3, v_l_3571_);
lean_ctor_set(v_reuseFailAlloc_3608_, 4, v_l_3571_);
v___x_3601_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3603_; 
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 4, v_l_3571_);
lean_ctor_set(v___x_3592_, 2, v_v_3477_);
lean_ctor_set(v___x_3592_, 1, v_k_3476_);
lean_ctor_set(v___x_3592_, 0, v___x_3485_);
v___x_3603_ = v___x_3592_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3607_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3607_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3607_, 3, v_l_3571_);
lean_ctor_set(v_reuseFailAlloc_3607_, 4, v_l_3571_);
v___x_3603_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
lean_object* v___x_3605_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 4, v___x_3603_);
lean_ctor_set(v___x_3481_, 3, v___x_3601_);
lean_ctor_set(v___x_3481_, 2, v_v_3595_);
lean_ctor_set(v___x_3481_, 1, v_k_3594_);
lean_ctor_set(v___x_3481_, 0, v___x_3599_);
v___x_3605_ = v___x_3481_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3599_);
lean_ctor_set(v_reuseFailAlloc_3606_, 1, v_k_3594_);
lean_ctor_set(v_reuseFailAlloc_3606_, 2, v_v_3595_);
lean_ctor_set(v_reuseFailAlloc_3606_, 3, v___x_3601_);
lean_ctor_set(v_reuseFailAlloc_3606_, 4, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
}
else
{
lean_object* v___x_3617_; lean_object* v___x_3619_; 
v___x_3617_ = lean_unsigned_to_nat(2u);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 4, v_r_3588_);
lean_ctor_set(v___x_3481_, 3, v_impl_3484_);
lean_ctor_set(v___x_3481_, 0, v___x_3617_);
v___x_3619_ = v___x_3481_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3617_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3620_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3620_, 3, v_impl_3484_);
lean_ctor_set(v_reuseFailAlloc_3620_, 4, v_r_3588_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3622_; 
lean_dec(v_v_3477_);
lean_dec(v_k_3476_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 2, v_v_3473_);
lean_ctor_set(v___x_3481_, 1, v_k_3472_);
v___x_3622_ = v___x_3481_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_size_3475_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_k_3472_);
lean_ctor_set(v_reuseFailAlloc_3623_, 2, v_v_3473_);
lean_ctor_set(v_reuseFailAlloc_3623_, 3, v_l_3478_);
lean_ctor_set(v_reuseFailAlloc_3623_, 4, v_r_3479_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
default: 
{
lean_object* v_impl_3624_; lean_object* v___x_3625_; 
lean_dec(v_size_3475_);
v_impl_3624_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3472_, v_v_3473_, v_r_3479_);
v___x_3625_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3478_) == 0)
{
lean_object* v_size_3626_; lean_object* v_size_3627_; lean_object* v_k_3628_; lean_object* v_v_3629_; lean_object* v_l_3630_; lean_object* v_r_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; 
v_size_3626_ = lean_ctor_get(v_l_3478_, 0);
v_size_3627_ = lean_ctor_get(v_impl_3624_, 0);
lean_inc(v_size_3627_);
v_k_3628_ = lean_ctor_get(v_impl_3624_, 1);
lean_inc(v_k_3628_);
v_v_3629_ = lean_ctor_get(v_impl_3624_, 2);
lean_inc(v_v_3629_);
v_l_3630_ = lean_ctor_get(v_impl_3624_, 3);
lean_inc(v_l_3630_);
v_r_3631_ = lean_ctor_get(v_impl_3624_, 4);
lean_inc(v_r_3631_);
v___x_3632_ = lean_unsigned_to_nat(3u);
v___x_3633_ = lean_nat_mul(v___x_3632_, v_size_3626_);
v___x_3634_ = lean_nat_dec_lt(v___x_3633_, v_size_3627_);
lean_dec(v___x_3633_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3638_; 
lean_dec(v_r_3631_);
lean_dec(v_l_3630_);
lean_dec(v_v_3629_);
lean_dec(v_k_3628_);
v___x_3635_ = lean_nat_add(v___x_3625_, v_size_3626_);
v___x_3636_ = lean_nat_add(v___x_3635_, v_size_3627_);
lean_dec(v_size_3627_);
lean_dec(v___x_3635_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 4, v_impl_3624_);
lean_ctor_set(v___x_3481_, 0, v___x_3636_);
v___x_3638_ = v___x_3481_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3639_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3639_, 3, v_l_3478_);
lean_ctor_set(v_reuseFailAlloc_3639_, 4, v_impl_3624_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
else
{
lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3703_; 
v_isSharedCheck_3703_ = !lean_is_exclusive(v_impl_3624_);
if (v_isSharedCheck_3703_ == 0)
{
lean_object* v_unused_3704_; lean_object* v_unused_3705_; lean_object* v_unused_3706_; lean_object* v_unused_3707_; lean_object* v_unused_3708_; 
v_unused_3704_ = lean_ctor_get(v_impl_3624_, 4);
lean_dec(v_unused_3704_);
v_unused_3705_ = lean_ctor_get(v_impl_3624_, 3);
lean_dec(v_unused_3705_);
v_unused_3706_ = lean_ctor_get(v_impl_3624_, 2);
lean_dec(v_unused_3706_);
v_unused_3707_ = lean_ctor_get(v_impl_3624_, 1);
lean_dec(v_unused_3707_);
v_unused_3708_ = lean_ctor_get(v_impl_3624_, 0);
lean_dec(v_unused_3708_);
v___x_3641_ = v_impl_3624_;
v_isShared_3642_ = v_isSharedCheck_3703_;
goto v_resetjp_3640_;
}
else
{
lean_dec(v_impl_3624_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3703_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v_size_3643_; lean_object* v_k_3644_; lean_object* v_v_3645_; lean_object* v_l_3646_; lean_object* v_r_3647_; lean_object* v_size_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; uint8_t v___x_3651_; 
v_size_3643_ = lean_ctor_get(v_l_3630_, 0);
v_k_3644_ = lean_ctor_get(v_l_3630_, 1);
v_v_3645_ = lean_ctor_get(v_l_3630_, 2);
v_l_3646_ = lean_ctor_get(v_l_3630_, 3);
v_r_3647_ = lean_ctor_get(v_l_3630_, 4);
v_size_3648_ = lean_ctor_get(v_r_3631_, 0);
v___x_3649_ = lean_unsigned_to_nat(2u);
v___x_3650_ = lean_nat_mul(v___x_3649_, v_size_3648_);
v___x_3651_ = lean_nat_dec_lt(v_size_3643_, v___x_3650_);
lean_dec(v___x_3650_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3679_; 
lean_inc(v_r_3647_);
lean_inc(v_l_3646_);
lean_inc(v_v_3645_);
lean_inc(v_k_3644_);
v_isSharedCheck_3679_ = !lean_is_exclusive(v_l_3630_);
if (v_isSharedCheck_3679_ == 0)
{
lean_object* v_unused_3680_; lean_object* v_unused_3681_; lean_object* v_unused_3682_; lean_object* v_unused_3683_; lean_object* v_unused_3684_; 
v_unused_3680_ = lean_ctor_get(v_l_3630_, 4);
lean_dec(v_unused_3680_);
v_unused_3681_ = lean_ctor_get(v_l_3630_, 3);
lean_dec(v_unused_3681_);
v_unused_3682_ = lean_ctor_get(v_l_3630_, 2);
lean_dec(v_unused_3682_);
v_unused_3683_ = lean_ctor_get(v_l_3630_, 1);
lean_dec(v_unused_3683_);
v_unused_3684_ = lean_ctor_get(v_l_3630_, 0);
lean_dec(v_unused_3684_);
v___x_3653_ = v_l_3630_;
v_isShared_3654_ = v_isSharedCheck_3679_;
goto v_resetjp_3652_;
}
else
{
lean_dec(v_l_3630_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3679_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3669_; 
v___x_3655_ = lean_nat_add(v___x_3625_, v_size_3626_);
v___x_3656_ = lean_nat_add(v___x_3655_, v_size_3627_);
lean_dec(v_size_3627_);
if (lean_obj_tag(v_l_3646_) == 0)
{
lean_object* v_size_3677_; 
v_size_3677_ = lean_ctor_get(v_l_3646_, 0);
lean_inc(v_size_3677_);
v___y_3669_ = v_size_3677_;
goto v___jp_3668_;
}
else
{
lean_object* v___x_3678_; 
v___x_3678_ = lean_unsigned_to_nat(0u);
v___y_3669_ = v___x_3678_;
goto v___jp_3668_;
}
v___jp_3657_:
{
lean_object* v___x_3661_; lean_object* v___x_3663_; 
v___x_3661_ = lean_nat_add(v___y_3658_, v___y_3660_);
lean_dec(v___y_3660_);
lean_dec(v___y_3658_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 4, v_r_3631_);
lean_ctor_set(v___x_3653_, 3, v_r_3647_);
lean_ctor_set(v___x_3653_, 2, v_v_3629_);
lean_ctor_set(v___x_3653_, 1, v_k_3628_);
lean_ctor_set(v___x_3653_, 0, v___x_3661_);
v___x_3663_ = v___x_3653_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3661_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_k_3628_);
lean_ctor_set(v_reuseFailAlloc_3667_, 2, v_v_3629_);
lean_ctor_set(v_reuseFailAlloc_3667_, 3, v_r_3647_);
lean_ctor_set(v_reuseFailAlloc_3667_, 4, v_r_3631_);
v___x_3663_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3665_; 
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 4, v___x_3663_);
lean_ctor_set(v___x_3641_, 3, v___y_3659_);
lean_ctor_set(v___x_3641_, 2, v_v_3645_);
lean_ctor_set(v___x_3641_, 1, v_k_3644_);
lean_ctor_set(v___x_3641_, 0, v___x_3656_);
v___x_3665_ = v___x_3641_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3656_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_k_3644_);
lean_ctor_set(v_reuseFailAlloc_3666_, 2, v_v_3645_);
lean_ctor_set(v_reuseFailAlloc_3666_, 3, v___y_3659_);
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
v___jp_3668_:
{
lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3670_ = lean_nat_add(v___x_3655_, v___y_3669_);
lean_dec(v___y_3669_);
lean_dec(v___x_3655_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 4, v_l_3646_);
lean_ctor_set(v___x_3481_, 0, v___x_3670_);
v___x_3672_ = v___x_3481_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3670_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_l_3478_);
lean_ctor_set(v_reuseFailAlloc_3676_, 4, v_l_3646_);
v___x_3672_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3673_; 
v___x_3673_ = lean_nat_add(v___x_3625_, v_size_3648_);
if (lean_obj_tag(v_r_3647_) == 0)
{
lean_object* v_size_3674_; 
v_size_3674_ = lean_ctor_get(v_r_3647_, 0);
lean_inc(v_size_3674_);
v___y_3658_ = v___x_3673_;
v___y_3659_ = v___x_3672_;
v___y_3660_ = v_size_3674_;
goto v___jp_3657_;
}
else
{
lean_object* v___x_3675_; 
v___x_3675_ = lean_unsigned_to_nat(0u);
v___y_3658_ = v___x_3673_;
v___y_3659_ = v___x_3672_;
v___y_3660_ = v___x_3675_;
goto v___jp_3657_;
}
}
}
}
}
else
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3689_; 
lean_del_object(v___x_3481_);
v___x_3685_ = lean_nat_add(v___x_3625_, v_size_3626_);
v___x_3686_ = lean_nat_add(v___x_3685_, v_size_3627_);
lean_dec(v_size_3627_);
v___x_3687_ = lean_nat_add(v___x_3685_, v_size_3643_);
lean_dec(v___x_3685_);
lean_inc_ref(v_l_3478_);
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 4, v_l_3630_);
lean_ctor_set(v___x_3641_, 3, v_l_3478_);
lean_ctor_set(v___x_3641_, 2, v_v_3477_);
lean_ctor_set(v___x_3641_, 1, v_k_3476_);
lean_ctor_set(v___x_3641_, 0, v___x_3687_);
v___x_3689_ = v___x_3641_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3687_);
lean_ctor_set(v_reuseFailAlloc_3702_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3702_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3702_, 3, v_l_3478_);
lean_ctor_set(v_reuseFailAlloc_3702_, 4, v_l_3630_);
v___x_3689_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
v_isSharedCheck_3696_ = !lean_is_exclusive(v_l_3478_);
if (v_isSharedCheck_3696_ == 0)
{
lean_object* v_unused_3697_; lean_object* v_unused_3698_; lean_object* v_unused_3699_; lean_object* v_unused_3700_; lean_object* v_unused_3701_; 
v_unused_3697_ = lean_ctor_get(v_l_3478_, 4);
lean_dec(v_unused_3697_);
v_unused_3698_ = lean_ctor_get(v_l_3478_, 3);
lean_dec(v_unused_3698_);
v_unused_3699_ = lean_ctor_get(v_l_3478_, 2);
lean_dec(v_unused_3699_);
v_unused_3700_ = lean_ctor_get(v_l_3478_, 1);
lean_dec(v_unused_3700_);
v_unused_3701_ = lean_ctor_get(v_l_3478_, 0);
lean_dec(v_unused_3701_);
v___x_3691_ = v_l_3478_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_dec(v_l_3478_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 4, v_r_3631_);
lean_ctor_set(v___x_3691_, 3, v___x_3689_);
lean_ctor_set(v___x_3691_, 2, v_v_3629_);
lean_ctor_set(v___x_3691_, 1, v_k_3628_);
lean_ctor_set(v___x_3691_, 0, v___x_3686_);
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3686_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v_k_3628_);
lean_ctor_set(v_reuseFailAlloc_3695_, 2, v_v_3629_);
lean_ctor_set(v_reuseFailAlloc_3695_, 3, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3695_, 4, v_r_3631_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3709_; 
v_l_3709_ = lean_ctor_get(v_impl_3624_, 3);
lean_inc(v_l_3709_);
if (lean_obj_tag(v_l_3709_) == 0)
{
lean_object* v_r_3710_; lean_object* v_k_3711_; lean_object* v_v_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3735_; 
v_r_3710_ = lean_ctor_get(v_impl_3624_, 4);
v_k_3711_ = lean_ctor_get(v_impl_3624_, 1);
v_v_3712_ = lean_ctor_get(v_impl_3624_, 2);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_impl_3624_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; lean_object* v_unused_3737_; 
v_unused_3736_ = lean_ctor_get(v_impl_3624_, 3);
lean_dec(v_unused_3736_);
v_unused_3737_ = lean_ctor_get(v_impl_3624_, 0);
lean_dec(v_unused_3737_);
v___x_3714_ = v_impl_3624_;
v_isShared_3715_ = v_isSharedCheck_3735_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_r_3710_);
lean_inc(v_v_3712_);
lean_inc(v_k_3711_);
lean_dec(v_impl_3624_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3735_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v_k_3716_; lean_object* v_v_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3731_; 
v_k_3716_ = lean_ctor_get(v_l_3709_, 1);
v_v_3717_ = lean_ctor_get(v_l_3709_, 2);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_l_3709_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; lean_object* v_unused_3733_; lean_object* v_unused_3734_; 
v_unused_3732_ = lean_ctor_get(v_l_3709_, 4);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_l_3709_, 3);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_l_3709_, 0);
lean_dec(v_unused_3734_);
v___x_3719_ = v_l_3709_;
v_isShared_3720_ = v_isSharedCheck_3731_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_v_3717_);
lean_inc(v_k_3716_);
lean_dec(v_l_3709_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3731_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3721_; lean_object* v___x_3723_; 
v___x_3721_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3710_, 2);
if (v_isShared_3720_ == 0)
{
lean_ctor_set(v___x_3719_, 4, v_r_3710_);
lean_ctor_set(v___x_3719_, 3, v_r_3710_);
lean_ctor_set(v___x_3719_, 2, v_v_3477_);
lean_ctor_set(v___x_3719_, 1, v_k_3476_);
lean_ctor_set(v___x_3719_, 0, v___x_3625_);
v___x_3723_ = v___x_3719_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3625_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3730_, 3, v_r_3710_);
lean_ctor_set(v_reuseFailAlloc_3730_, 4, v_r_3710_);
v___x_3723_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3725_; 
lean_inc(v_r_3710_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 3, v_r_3710_);
lean_ctor_set(v___x_3714_, 0, v___x_3625_);
v___x_3725_ = v___x_3714_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3625_);
lean_ctor_set(v_reuseFailAlloc_3729_, 1, v_k_3711_);
lean_ctor_set(v_reuseFailAlloc_3729_, 2, v_v_3712_);
lean_ctor_set(v_reuseFailAlloc_3729_, 3, v_r_3710_);
lean_ctor_set(v_reuseFailAlloc_3729_, 4, v_r_3710_);
v___x_3725_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3727_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 4, v___x_3725_);
lean_ctor_set(v___x_3481_, 3, v___x_3723_);
lean_ctor_set(v___x_3481_, 2, v_v_3717_);
lean_ctor_set(v___x_3481_, 1, v_k_3716_);
lean_ctor_set(v___x_3481_, 0, v___x_3721_);
v___x_3727_ = v___x_3481_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_k_3716_);
lean_ctor_set(v_reuseFailAlloc_3728_, 2, v_v_3717_);
lean_ctor_set(v_reuseFailAlloc_3728_, 3, v___x_3723_);
lean_ctor_set(v_reuseFailAlloc_3728_, 4, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
}
else
{
lean_object* v_r_3738_; 
v_r_3738_ = lean_ctor_get(v_impl_3624_, 4);
lean_inc(v_r_3738_);
if (lean_obj_tag(v_r_3738_) == 0)
{
lean_object* v_k_3739_; lean_object* v_v_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3751_; 
v_k_3739_ = lean_ctor_get(v_impl_3624_, 1);
v_v_3740_ = lean_ctor_get(v_impl_3624_, 2);
v_isSharedCheck_3751_ = !lean_is_exclusive(v_impl_3624_);
if (v_isSharedCheck_3751_ == 0)
{
lean_object* v_unused_3752_; lean_object* v_unused_3753_; lean_object* v_unused_3754_; 
v_unused_3752_ = lean_ctor_get(v_impl_3624_, 4);
lean_dec(v_unused_3752_);
v_unused_3753_ = lean_ctor_get(v_impl_3624_, 3);
lean_dec(v_unused_3753_);
v_unused_3754_ = lean_ctor_get(v_impl_3624_, 0);
lean_dec(v_unused_3754_);
v___x_3742_ = v_impl_3624_;
v_isShared_3743_ = v_isSharedCheck_3751_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_v_3740_);
lean_inc(v_k_3739_);
lean_dec(v_impl_3624_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3751_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3744_; lean_object* v___x_3746_; 
v___x_3744_ = lean_unsigned_to_nat(3u);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 4, v_l_3709_);
lean_ctor_set(v___x_3742_, 2, v_v_3477_);
lean_ctor_set(v___x_3742_, 1, v_k_3476_);
lean_ctor_set(v___x_3742_, 0, v___x_3625_);
v___x_3746_ = v___x_3742_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3625_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3750_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3750_, 3, v_l_3709_);
lean_ctor_set(v_reuseFailAlloc_3750_, 4, v_l_3709_);
v___x_3746_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
lean_object* v___x_3748_; 
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 4, v_r_3738_);
lean_ctor_set(v___x_3481_, 3, v___x_3746_);
lean_ctor_set(v___x_3481_, 2, v_v_3740_);
lean_ctor_set(v___x_3481_, 1, v_k_3739_);
lean_ctor_set(v___x_3481_, 0, v___x_3744_);
v___x_3748_ = v___x_3481_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3744_);
lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_k_3739_);
lean_ctor_set(v_reuseFailAlloc_3749_, 2, v_v_3740_);
lean_ctor_set(v_reuseFailAlloc_3749_, 3, v___x_3746_);
lean_ctor_set(v_reuseFailAlloc_3749_, 4, v_r_3738_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
else
{
lean_object* v___x_3755_; lean_object* v___x_3757_; 
v___x_3755_ = lean_unsigned_to_nat(2u);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 4, v_impl_3624_);
lean_ctor_set(v___x_3481_, 3, v_r_3738_);
lean_ctor_set(v___x_3481_, 0, v___x_3755_);
v___x_3757_ = v___x_3481_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3755_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_k_3476_);
lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_v_3477_);
lean_ctor_set(v_reuseFailAlloc_3758_, 3, v_r_3738_);
lean_ctor_set(v_reuseFailAlloc_3758_, 4, v_impl_3624_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
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
lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3760_ = lean_unsigned_to_nat(1u);
v___x_3761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3760_);
lean_ctor_set(v___x_3761_, 1, v_k_3472_);
lean_ctor_set(v___x_3761_, 2, v_v_3473_);
lean_ctor_set(v___x_3761_, 3, v_t_3474_);
lean_ctor_set(v___x_3761_, 4, v_t_3474_);
return v___x_3761_;
}
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3762_ = lean_box(1);
v___x_3763_ = l_Lake_LeanLib_defaultFacetConfig;
v___x_3764_ = l_Lake_LeanLib_defaultFacet;
v___x_3765_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3764_, v___x_3763_, v___x_3762_);
return v___x_3765_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
v___x_3766_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__0, &l_Lake_LeanLib_initFacetConfigs___closed__0_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__0);
v___x_3767_ = ((lean_object*)(l___private_Lake_Build_Library_0__Lake_LeanLib_modulesFacetConfig));
v___x_3768_ = l_Lake_LeanLib_modulesFacet;
v___x_3769_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3768_, v___x_3767_, v___x_3766_);
return v___x_3769_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3770_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__1, &l_Lake_LeanLib_initFacetConfigs___closed__1_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__1);
v___x_3771_ = l_Lake_LeanLib_leanArtsFacetConfig;
v___x_3772_ = l_Lake_LeanLib_leanArtsFacet;
v___x_3773_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3772_, v___x_3771_, v___x_3770_);
return v___x_3773_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3774_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__2, &l_Lake_LeanLib_initFacetConfigs___closed__2_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__2);
v___x_3775_ = l_Lake_LeanLib_staticFacetConfig;
v___x_3776_ = l_Lake_LeanLib_staticFacet;
v___x_3777_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3776_, v___x_3775_, v___x_3774_);
return v___x_3777_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3778_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__3, &l_Lake_LeanLib_initFacetConfigs___closed__3_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__3);
v___x_3779_ = l_Lake_LeanLib_staticExportFacetConfig;
v___x_3780_ = l_Lake_LeanLib_staticExportFacet;
v___x_3781_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3780_, v___x_3779_, v___x_3778_);
return v___x_3781_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3782_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__4, &l_Lake_LeanLib_initFacetConfigs___closed__4_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__4);
v___x_3783_ = l_Lake_LeanLib_sharedFacetConfig;
v___x_3784_ = l_Lake_LeanLib_sharedFacet;
v___x_3785_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3784_, v___x_3783_, v___x_3782_);
return v___x_3785_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3786_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__5, &l_Lake_LeanLib_initFacetConfigs___closed__5_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__5);
v___x_3787_ = l_Lake_LeanLib_extraDepFacetConfig;
v___x_3788_ = l_Lake_LeanLib_extraDepFacet;
v___x_3789_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v___x_3788_, v___x_3787_, v___x_3786_);
return v___x_3789_;
}
}
static lean_object* _init_l_Lake_LeanLib_initFacetConfigs(void){
_start:
{
lean_object* v___x_3790_; 
v___x_3790_ = lean_obj_once(&l_Lake_LeanLib_initFacetConfigs___closed__6, &l_Lake_LeanLib_initFacetConfigs___closed__6_once, _init_l_Lake_LeanLib_initFacetConfigs___closed__6);
return v___x_3790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3791_, lean_object* v_k_3792_, lean_object* v_v_3793_, lean_object* v_t_3794_, lean_object* v_hl_3795_){
_start:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_LeanLib_initFacetConfigs_spec__0___redArg(v_k_3792_, v_v_3793_, v_t_3794_);
return v___x_3796_;
}
}
static lean_object* _init_l_Lake_initLibraryFacetConfigs(void){
_start:
{
lean_object* v___x_3797_; 
v___x_3797_ = l_Lake_LeanLib_initFacetConfigs;
return v___x_3797_;
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
