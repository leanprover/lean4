// Lean compiler output
// Module: Lake.Build.Package
// Imports: public import Lake.Config.FacetConfig public import Lake.Build.Job.Monad public import Lake.Build.Infos import Lake.Util.Git import Lake.Util.Url import Lake.Build.Common import Lake.Build.Targets import Lake.Build.Job.Register import Lake.Reservoir
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_Verbosity_ctorIdx(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lake_Package_optReservoirBarrelFacet;
lean_object* l_Lake_Name_eraseHead(lean_object*);
extern lean_object* l_Lake_Package_optGitHubReleaseFacet;
extern lean_object* l_Lake_instDataKindUnit;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_task_pure(lean_object*);
extern lean_object* l_Lake_Package_optBuildCacheFacet;
extern lean_object* l_Lake_Package_keyword;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_add___redArg(lean_object*, lean_object*);
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_uriEncode(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*);
extern uint64_t l_Lake_Hash_nil;
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lake_readTraceFile(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_io_metadata(lean_object*);
uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
lean_object* l_Lake_OutputStatus_ctorIdx(uint8_t);
lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildMetadata_writeFile(lean_object*, lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern lean_object* l_Lake_Package_transDepsFacet;
lean_object* l_Lake_Job_await___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lake_Package_depsFacet;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_Package_findTargetDecl_x3f(lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_keyword;
lean_object* l_Lake_LeanExeConfig_toLeanLibConfig___redArg(lean_object*);
extern lean_object* l_Lake_Module_transImportsFacet;
extern lean_object* l_Lake_Module_keyword;
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lake_LeanLib_modulesFacet;
extern lean_object* l_Lake_Package_defaultModulesFacet;
lean_object* l_Lake_Package_fetchTargetJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_mix___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_Package_extraDepFacet;
extern lean_object* l_Lake_instDataKindBool;
extern lean_object* l_Lake_Package_buildCacheFacet;
extern lean_object* l_Lake_Reservoir_lakeHeaders;
extern lean_object* l_Lake_Package_reservoirBarrelFacet;
lean_object* l_Lake_GitRepo_findTag_x3f(lean_object*, lean_object*);
extern lean_object* l_Lake_Git_defaultRemote;
lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instQueryJsonUnit___lam__0(lean_object*);
lean_object* l_instToStringBool___lam__0___boxed(lean_object*);
extern lean_object* l_Lake_Package_gitHubReleaseFacet;
lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object*);
lean_object* l_Lake_formatQuery___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instQueryTextUnit___lam__0(lean_object*);
lean_object* l_Lake_Job_async___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobM_runSpawnM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_FetchM_runJobM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__2_value;
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3;
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Package_depsFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_depsFacetConfig___closed__0 = (const lean_object*)&l_Lake_Package_depsFacetConfig___closed__0_value;
static const lean_closure_object l_Lake_Package_depsFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_depsFacetConfig___closed__1 = (const lean_object*)&l_Lake_Package_depsFacetConfig___closed__1_value;
static lean_once_cell_t l_Lake_Package_depsFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_depsFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_depsFacetConfig;
static lean_once_cell_t l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0;
static lean_once_cell_t l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1;
static const lean_array_object l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2 = (const lean_object*)&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2_value;
static lean_once_cell_t l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0;
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1;
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2;
static const lean_ctor_object l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___boxed__const__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Package_defaultModulesFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_defaultModulesFacetConfig___closed__0 = (const lean_object*)&l_Lake_Package_defaultModulesFacetConfig___closed__0_value;
static const lean_closure_object l_Lake_Package_defaultModulesFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_defaultModulesFacetConfig___closed__1 = (const lean_object*)&l_Lake_Package_defaultModulesFacetConfig___closed__1_value;
static lean_once_cell_t l_Lake_Package_defaultModulesFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_defaultModulesFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_defaultModulesFacetConfig;
static const lean_closure_object l_Lake_Package_transDepsFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_transDepsFacetConfig___closed__0 = (const lean_object*)&l_Lake_Package_transDepsFacetConfig___closed__0_value;
static lean_once_cell_t l_Lake_Package_transDepsFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_transDepsFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_transDepsFacetConfig;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0 = (const lean_object*)&l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0_value;
static const lean_string_object l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1 = (const lean_object*)&l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Package_optBuildCacheFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_optBuildCacheFacetConfig___closed__0 = (const lean_object*)&l_Lake_Package_optBuildCacheFacetConfig___closed__0_value;
static const lean_closure_object l_Lake_Package_optBuildCacheFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_optBuildCacheFacetConfig___closed__1 = (const lean_object*)&l_Lake_Package_optBuildCacheFacetConfig___closed__1_value;
static lean_once_cell_t l_Lake_Package_optBuildCacheFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_optBuildCacheFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_optBuildCacheFacetConfig;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "leanprover"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "leanprover-community"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " (run with '-v' for details)"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " (see '"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "' for details)"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "building from source; failed to fetch Reservoir build"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "building from source; failed to fetch GitHub release"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2;
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ":extraDep"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Package_extraDepFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Package_extraDepFacetConfig___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_extraDepFacetConfig___closed__0 = (const lean_object*)&l_Lake_Package_extraDepFacetConfig___closed__0_value;
static const lean_closure_object l_Lake_Package_extraDepFacetConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Package_extraDepFacetConfig___closed__1 = (const lean_object*)&l_Lake_Package_extraDepFacetConfig___closed__1_value;
static lean_once_cell_t l_Lake_Package_extraDepFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_extraDepFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "/barrel\?rev="};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "&toolchain="};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "Lean toolchain not known; Reservoir only hosts builds for known toolchains"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3_value;
static const lean_ctor_object l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "failed to resolve HEAD revision"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__5 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__5_value;
static const lean_ctor_object l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "package has no Reservoir scope"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__7 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__7_value;
static const lean_ctor_object l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "no release tag found for revision"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "/releases/download/"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " '"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "release repository URL not known; the package may need to set 'releaseRepo'"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__5 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__5_value;
static const lean_ctor_object l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "target is out-of-date and needs to be rebuilt"};
static const lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__0 = (const lean_object*)&l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1 = (const lean_object*)&l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1_value;
static const lean_string_object l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nobuild"};
static const lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2 = (const lean_object*)&l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "<hash>"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2_value;
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3;
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0_value;
static const lean_closure_object l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1_value;
static const lean_ctor_object l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__0_value),((lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__1_value)}};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2_value;
static const lean_closure_object l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__2_value)} };
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "failed to fetch "};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instQueryTextUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__0_value;
static const lean_closure_object l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instQueryJsonUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__1_value;
static const lean_ctor_object l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__0_value),((lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__1_value)}};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__2_value;
static const lean_closure_object l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__2_value)} };
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "failed to fetch build cache"};
static const lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0 = (const lean_object*)&l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Package_buildCacheFacetConfig___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_buildCacheFacetConfig___closed__0;
static lean_once_cell_t l_Lake_Package_buildCacheFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_buildCacheFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig;
static const lean_string_object l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "build.barrel"};
static const lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0 = (const lean_object*)&l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Package_optBarrelFacetConfig___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_optBarrelFacetConfig___closed__0;
static lean_once_cell_t l_Lake_Package_optBarrelFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_optBarrelFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig;
static const lean_string_object l_Lake_Package_barrelFacetConfig___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "failed to fetch Reservoir build"};
static const lean_object* l_Lake_Package_barrelFacetConfig___lam__1___closed__0 = (const lean_object*)&l_Lake_Package_barrelFacetConfig___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Package_barrelFacetConfig___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_barrelFacetConfig___closed__0;
static lean_once_cell_t l_Lake_Package_barrelFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_barrelFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_Package_optGitHubReleaseFacetConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___closed__0 = (const lean_object*)&l_Lake_Package_optGitHubReleaseFacetConfig___closed__0_value;
static lean_once_cell_t l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___closed__1;
static lean_once_cell_t l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig;
static const lean_string_object l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "failed to fetch GitHub release"};
static const lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0 = (const lean_object*)&l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___closed__0;
static lean_once_cell_t l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_gitHubReleaseFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig;
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Package_initFacetConfigs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_initFacetConfigs___closed__0;
static lean_once_cell_t l_Lake_Package_initFacetConfigs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_initFacetConfigs___closed__1;
static lean_once_cell_t l_Lake_Package_initFacetConfigs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_initFacetConfigs___closed__2;
static lean_once_cell_t l_Lake_Package_initFacetConfigs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_initFacetConfigs___closed__3;
static lean_once_cell_t l_Lake_Package_initFacetConfigs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_initFacetConfigs___closed__4;
static lean_once_cell_t l_Lake_Package_initFacetConfigs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_initFacetConfigs___closed__5;
static lean_once_cell_t l_Lake_Package_initFacetConfigs___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_initFacetConfigs___closed__6;
static lean_once_cell_t l_Lake_Package_initFacetConfigs___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_initFacetConfigs___closed__7;
static lean_once_cell_t l_Lake_Package_initFacetConfigs___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_initFacetConfigs___closed__8;
static lean_once_cell_t l_Lake_Package_initFacetConfigs___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_initFacetConfigs___closed__9;
LEAN_EXPORT lean_object* l_Lake_Package_initFacetConfigs;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initPackageFacetConfigs;
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__2));
v___x_6_ = l_Lake_BuildTrace_nil(v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__4(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; uint8_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_9_ = 0;
v___x_10_ = 0;
v___x_11_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_12_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_8_);
lean_ctor_set(v___x_12_, 2, v___x_7_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*3, v___x_10_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*3 + 1, v___x_9_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*3 + 2, v___x_9_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg(lean_object* v_self_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_depPkgs_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_depPkgs_16_ = lean_ctor_get(v_self_13_, 14);
v___x_17_ = lean_box(0);
v___x_18_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_19_ = 0;
v___x_20_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__4);
lean_inc_ref(v_depPkgs_16_);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v_depPkgs_16_);
lean_ctor_set(v___x_21_, 1, v___x_20_);
v___x_22_ = lean_task_pure(v___x_21_);
v___x_23_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_23_, 0, v___x_22_);
lean_ctor_set(v___x_23_, 1, v___x_17_);
lean_ctor_set(v___x_23_, 2, v___x_18_);
lean_ctor_set_uint8(v___x_23_, sizeof(void*)*3, v___x_19_);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v_a_14_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___boxed(lean_object* v_self_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg(v_self_25_, v_a_26_);
lean_dec_ref(v_self_25_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps(lean_object* v_self_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg(v_self_29_, v_a_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___boxed(lean_object* v_self_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps(v_self_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
lean_dec(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec_ref(v_self_38_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(size_t v_sz_47_, size_t v_i_48_, lean_object* v_bs_49_){
_start:
{
uint8_t v___x_50_; 
v___x_50_ = lean_usize_dec_lt(v_i_48_, v_sz_47_);
if (v___x_50_ == 0)
{
return v_bs_49_;
}
else
{
lean_object* v_v_51_; lean_object* v_keyName_52_; lean_object* v___x_53_; lean_object* v_bs_x27_54_; lean_object* v___x_55_; lean_object* v___x_56_; size_t v___x_57_; size_t v___x_58_; lean_object* v___x_59_; 
v_v_51_ = lean_array_uget_borrowed(v_bs_49_, v_i_48_);
v_keyName_52_ = lean_ctor_get(v_v_51_, 2);
lean_inc(v_keyName_52_);
v___x_53_ = lean_unsigned_to_nat(0u);
v_bs_x27_54_ = lean_array_uset(v_bs_49_, v_i_48_, v___x_53_);
v___x_55_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_52_, v___x_50_);
v___x_56_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
v___x_57_ = ((size_t)1ULL);
v___x_58_ = lean_usize_add(v_i_48_, v___x_57_);
v___x_59_ = lean_array_uset(v_bs_x27_54_, v_i_48_, v___x_56_);
v_i_48_ = v___x_58_;
v_bs_49_ = v___x_59_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1___boxed(lean_object* v_sz_61_, lean_object* v_i_62_, lean_object* v_bs_63_){
_start:
{
size_t v_sz_boxed_64_; size_t v_i_boxed_65_; lean_object* v_res_66_; 
v_sz_boxed_64_ = lean_unbox_usize(v_sz_61_);
lean_dec(v_sz_61_);
v_i_boxed_65_ = lean_unbox_usize(v_i_62_);
lean_dec(v_i_62_);
v_res_66_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(v_sz_boxed_64_, v_i_boxed_65_, v_bs_63_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(lean_object* v_as_68_, size_t v_i_69_, size_t v_stop_70_, lean_object* v_b_71_){
_start:
{
uint8_t v___x_72_; 
v___x_72_ = lean_usize_dec_eq(v_i_69_, v_stop_70_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v_baseName_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; size_t v___x_79_; size_t v___x_80_; 
v___x_73_ = lean_array_uget_borrowed(v_as_68_, v_i_69_);
v_baseName_74_ = lean_ctor_get(v___x_73_, 1);
lean_inc(v_baseName_74_);
v___x_75_ = l_Lean_Name_toString(v_baseName_74_, v___x_72_);
v___x_76_ = lean_string_append(v_b_71_, v___x_75_);
lean_dec_ref(v___x_75_);
v___x_77_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0));
v___x_78_ = lean_string_append(v___x_76_, v___x_77_);
v___x_79_ = ((size_t)1ULL);
v___x_80_ = lean_usize_add(v_i_69_, v___x_79_);
v_i_69_ = v___x_80_;
v_b_71_ = v___x_78_;
goto _start;
}
else
{
return v_b_71_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_82_, lean_object* v_i_83_, lean_object* v_stop_84_, lean_object* v_b_85_){
_start:
{
size_t v_i_boxed_86_; size_t v_stop_boxed_87_; lean_object* v_res_88_; 
v_i_boxed_86_ = lean_unbox_usize(v_i_83_);
lean_dec(v_i_83_);
v_stop_boxed_87_ = lean_unbox_usize(v_stop_84_);
lean_dec(v_stop_84_);
v_res_88_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(v_as_82_, v_i_boxed_86_, v_stop_boxed_87_, v_b_85_);
lean_dec_ref(v_as_82_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0(uint8_t v_fmt_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___y_92_; 
if (v_fmt_89_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_99_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_array_get_size(v_a_90_);
v___x_102_ = lean_nat_dec_lt(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_dec_ref(v_a_90_);
v___y_92_ = v___x_99_;
goto v___jp_91_;
}
else
{
size_t v___x_103_; size_t v___x_104_; lean_object* v___x_105_; 
v___x_103_ = ((size_t)0ULL);
v___x_104_ = lean_usize_of_nat(v___x_101_);
v___x_105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(v_a_90_, v___x_103_, v___x_104_, v___x_99_);
lean_dec_ref(v_a_90_);
v___y_92_ = v___x_105_;
goto v___jp_91_;
}
}
else
{
size_t v_sz_106_; size_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_sz_106_ = lean_array_size(v_a_90_);
v___x_107_ = ((size_t)0ULL);
v___x_108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(v_sz_106_, v___x_107_, v_a_90_);
v___x_109_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
v___x_110_ = l_Lean_Json_compress(v___x_109_);
return v___x_110_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_string_utf8_byte_size(v___y_92_);
lean_inc_ref(v___y_92_);
v___x_96_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_96_, 0, v___y_92_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
lean_ctor_set(v___x_96_, 2, v___x_95_);
v___x_97_ = l_String_Slice_Pos_prevn(v___x_96_, v___x_95_, v___x_93_);
lean_dec_ref_known(v___x_96_, 3);
v___x_98_ = lean_string_utf8_extract_fast(v___y_92_, v___x_94_, v___x_97_);
lean_dec(v___x_97_);
lean_dec_ref(v___y_92_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0___boxed(lean_object* v_fmt_111_, lean_object* v_a_112_){
_start:
{
uint8_t v_fmt_boxed_113_; lean_object* v_res_114_; 
v_fmt_boxed_113_ = lean_unbox(v_fmt_111_);
v_res_114_ = l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0(v_fmt_boxed_113_, v_a_112_);
return v_res_114_;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__2(void){
_start:
{
uint8_t v___x_117_; lean_object* v___f_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_117_ = 1;
v___f_118_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__0));
v___x_119_ = 0;
v___x_120_ = lean_box(0);
v___x_121_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__1));
v___x_122_ = l_Lake_Package_keyword;
v___x_123_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_120_);
lean_ctor_set(v___x_123_, 3, v___f_118_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*4, v___x_119_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*4 + 1, v___x_117_);
return v___x_123_;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_obj_once(&l_Lake_Package_depsFacetConfig___closed__2, &l_Lake_Package_depsFacetConfig___closed__2_once, _init_l_Lake_Package_depsFacetConfig___closed__2);
return v___x_124_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_box(0);
v___x_126_ = lean_unsigned_to_nat(16u);
v___x_127_ = lean_mk_array(v___x_126_, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0);
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
return v___x_130_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2));
v___x_134_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2(void){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3);
return v___x_136_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(lean_object* v_a_137_, lean_object* v_x_138_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
uint8_t v___x_139_; 
v___x_139_ = 0;
return v___x_139_;
}
else
{
lean_object* v_key_140_; lean_object* v_tail_141_; lean_object* v_wsIdx_142_; lean_object* v_wsIdx_143_; uint8_t v___x_144_; 
v_key_140_ = lean_ctor_get(v_x_138_, 0);
v_tail_141_ = lean_ctor_get(v_x_138_, 2);
v_wsIdx_142_ = lean_ctor_get(v_key_140_, 0);
v_wsIdx_143_ = lean_ctor_get(v_a_137_, 0);
v___x_144_ = lean_nat_dec_eq(v_wsIdx_142_, v_wsIdx_143_);
if (v___x_144_ == 0)
{
v_x_138_ = v_tail_141_;
goto _start;
}
else
{
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_a_146_, lean_object* v_x_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_146_, v_x_147_);
lean_dec(v_x_147_);
lean_dec_ref(v_a_146_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(lean_object* v_m_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_buckets_152_; lean_object* v_keyName_153_; lean_object* v___x_154_; uint64_t v___y_156_; 
v_buckets_152_ = lean_ctor_get(v_m_150_, 1);
v_keyName_153_ = lean_ctor_get(v_a_151_, 2);
v___x_154_ = lean_array_get_size(v_buckets_152_);
if (lean_obj_tag(v_keyName_153_) == 0)
{
uint64_t v___x_170_; 
v___x_170_ = 1723ULL;
v___y_156_ = v___x_170_;
goto v___jp_155_;
}
else
{
uint64_t v_hash_171_; 
v_hash_171_ = lean_ctor_get_uint64(v_keyName_153_, sizeof(void*)*2);
v___y_156_ = v_hash_171_;
goto v___jp_155_;
}
v___jp_155_:
{
uint64_t v___x_157_; uint64_t v___x_158_; uint64_t v_fold_159_; uint64_t v___x_160_; uint64_t v___x_161_; uint64_t v___x_162_; size_t v___x_163_; size_t v___x_164_; size_t v___x_165_; size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_157_ = 32ULL;
v___x_158_ = lean_uint64_shift_right(v___y_156_, v___x_157_);
v_fold_159_ = lean_uint64_xor(v___y_156_, v___x_158_);
v___x_160_ = 16ULL;
v___x_161_ = lean_uint64_shift_right(v_fold_159_, v___x_160_);
v___x_162_ = lean_uint64_xor(v_fold_159_, v___x_161_);
v___x_163_ = lean_uint64_to_usize(v___x_162_);
v___x_164_ = lean_usize_of_nat(v___x_154_);
v___x_165_ = ((size_t)1ULL);
v___x_166_ = lean_usize_sub(v___x_164_, v___x_165_);
v___x_167_ = lean_usize_land(v___x_163_, v___x_166_);
v___x_168_ = lean_array_uget_borrowed(v_buckets_152_, v___x_167_);
v___x_169_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_151_, v___x_168_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(lean_object* v_m_172_, lean_object* v_a_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_172_, v_a_173_);
lean_dec_ref(v_a_173_);
lean_dec_ref(v_m_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(lean_object* v_x_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
return v_x_176_;
}
else
{
lean_object* v_key_178_; lean_object* v_value_179_; lean_object* v_tail_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_207_; 
v_key_178_ = lean_ctor_get(v_x_177_, 0);
v_value_179_ = lean_ctor_get(v_x_177_, 1);
v_tail_180_ = lean_ctor_get(v_x_177_, 2);
v_isSharedCheck_207_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_207_ == 0)
{
v___x_182_ = v_x_177_;
v_isShared_183_ = v_isSharedCheck_207_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_tail_180_);
lean_inc(v_value_179_);
lean_inc(v_key_178_);
lean_dec(v_x_177_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_207_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_keyName_184_; lean_object* v___x_185_; uint64_t v___y_187_; 
v_keyName_184_ = lean_ctor_get(v_key_178_, 2);
v___x_185_ = lean_array_get_size(v_x_176_);
if (lean_obj_tag(v_keyName_184_) == 0)
{
uint64_t v___x_205_; 
v___x_205_ = 1723ULL;
v___y_187_ = v___x_205_;
goto v___jp_186_;
}
else
{
uint64_t v_hash_206_; 
v_hash_206_ = lean_ctor_get_uint64(v_keyName_184_, sizeof(void*)*2);
v___y_187_ = v_hash_206_;
goto v___jp_186_;
}
v___jp_186_:
{
uint64_t v___x_188_; uint64_t v___x_189_; uint64_t v_fold_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v___x_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; size_t v___x_197_; size_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_188_ = 32ULL;
v___x_189_ = lean_uint64_shift_right(v___y_187_, v___x_188_);
v_fold_190_ = lean_uint64_xor(v___y_187_, v___x_189_);
v___x_191_ = 16ULL;
v___x_192_ = lean_uint64_shift_right(v_fold_190_, v___x_191_);
v___x_193_ = lean_uint64_xor(v_fold_190_, v___x_192_);
v___x_194_ = lean_uint64_to_usize(v___x_193_);
v___x_195_ = lean_usize_of_nat(v___x_185_);
v___x_196_ = ((size_t)1ULL);
v___x_197_ = lean_usize_sub(v___x_195_, v___x_196_);
v___x_198_ = lean_usize_land(v___x_194_, v___x_197_);
v___x_199_ = lean_array_uget_borrowed(v_x_176_, v___x_198_);
lean_inc(v___x_199_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 2, v___x_199_);
v___x_201_ = v___x_182_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_key_178_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_value_179_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v___x_199_);
v___x_201_ = v_reuseFailAlloc_204_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; 
v___x_202_ = lean_array_uset(v_x_176_, v___x_198_, v___x_201_);
v_x_176_ = v___x_202_;
v_x_177_ = v_tail_180_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_i_208_, lean_object* v_source_209_, lean_object* v_target_210_){
_start:
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = lean_array_get_size(v_source_209_);
v___x_212_ = lean_nat_dec_lt(v_i_208_, v___x_211_);
if (v___x_212_ == 0)
{
lean_dec_ref(v_source_209_);
lean_dec(v_i_208_);
return v_target_210_;
}
else
{
lean_object* v_es_213_; lean_object* v___x_214_; lean_object* v_source_215_; lean_object* v_target_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_es_213_ = lean_array_fget(v_source_209_, v_i_208_);
v___x_214_ = lean_box(0);
v_source_215_ = lean_array_fset(v_source_209_, v_i_208_, v___x_214_);
v_target_216_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(v_target_210_, v_es_213_);
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = lean_nat_add(v_i_208_, v___x_217_);
lean_dec(v_i_208_);
v_i_208_ = v___x_218_;
v_source_209_ = v_source_215_;
v_target_210_ = v_target_216_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(lean_object* v_data_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_nbuckets_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_221_ = lean_array_get_size(v_data_220_);
v___x_222_ = lean_unsigned_to_nat(2u);
v_nbuckets_223_ = lean_nat_mul(v___x_221_, v___x_222_);
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_box(0);
v___x_226_ = lean_mk_array(v_nbuckets_223_, v___x_225_);
v___x_227_ = lean_array_propagate_mark(v_data_220_, v___x_226_);
v___x_228_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v___x_224_, v_data_220_, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(lean_object* v_m_229_, lean_object* v_a_230_, lean_object* v_b_231_){
_start:
{
lean_object* v_size_232_; lean_object* v_buckets_233_; lean_object* v_keyName_234_; lean_object* v___x_235_; uint64_t v___y_237_; 
v_size_232_ = lean_ctor_get(v_m_229_, 0);
v_buckets_233_ = lean_ctor_get(v_m_229_, 1);
v_keyName_234_ = lean_ctor_get(v_a_230_, 2);
v___x_235_ = lean_array_get_size(v_buckets_233_);
if (lean_obj_tag(v_keyName_234_) == 0)
{
uint64_t v___x_274_; 
v___x_274_ = 1723ULL;
v___y_237_ = v___x_274_;
goto v___jp_236_;
}
else
{
uint64_t v_hash_275_; 
v_hash_275_ = lean_ctor_get_uint64(v_keyName_234_, sizeof(void*)*2);
v___y_237_ = v_hash_275_;
goto v___jp_236_;
}
v___jp_236_:
{
uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v_fold_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; lean_object* v_bkt_249_; uint8_t v___x_250_; 
v___x_238_ = 32ULL;
v___x_239_ = lean_uint64_shift_right(v___y_237_, v___x_238_);
v_fold_240_ = lean_uint64_xor(v___y_237_, v___x_239_);
v___x_241_ = 16ULL;
v___x_242_ = lean_uint64_shift_right(v_fold_240_, v___x_241_);
v___x_243_ = lean_uint64_xor(v_fold_240_, v___x_242_);
v___x_244_ = lean_uint64_to_usize(v___x_243_);
v___x_245_ = lean_usize_of_nat(v___x_235_);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_sub(v___x_245_, v___x_246_);
v___x_248_ = lean_usize_land(v___x_244_, v___x_247_);
v_bkt_249_ = lean_array_uget_borrowed(v_buckets_233_, v___x_248_);
v___x_250_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_230_, v_bkt_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_271_; 
lean_inc_ref(v_buckets_233_);
lean_inc(v_size_232_);
v_isSharedCheck_271_ = !lean_is_exclusive(v_m_229_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; lean_object* v_unused_273_; 
v_unused_272_ = lean_ctor_get(v_m_229_, 1);
lean_dec(v_unused_272_);
v_unused_273_ = lean_ctor_get(v_m_229_, 0);
lean_dec(v_unused_273_);
v___x_252_ = v_m_229_;
v_isShared_253_ = v_isSharedCheck_271_;
goto v_resetjp_251_;
}
else
{
lean_dec(v_m_229_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_271_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v_size_x27_255_; lean_object* v___x_256_; lean_object* v_buckets_x27_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_254_ = lean_unsigned_to_nat(1u);
v_size_x27_255_ = lean_nat_add(v_size_232_, v___x_254_);
lean_dec(v_size_232_);
lean_inc(v_bkt_249_);
v___x_256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_256_, 0, v_a_230_);
lean_ctor_set(v___x_256_, 1, v_b_231_);
lean_ctor_set(v___x_256_, 2, v_bkt_249_);
v_buckets_x27_257_ = lean_array_uset(v_buckets_233_, v___x_248_, v___x_256_);
v___x_258_ = lean_unsigned_to_nat(4u);
v___x_259_ = lean_nat_mul(v_size_x27_255_, v___x_258_);
v___x_260_ = lean_unsigned_to_nat(3u);
v___x_261_ = lean_nat_div(v___x_259_, v___x_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_array_get_size(v_buckets_x27_257_);
v___x_263_ = lean_nat_dec_le(v___x_261_, v___x_262_);
lean_dec(v___x_261_);
if (v___x_263_ == 0)
{
lean_object* v_val_264_; lean_object* v___x_266_; 
v_val_264_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_buckets_x27_257_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v_val_264_);
lean_ctor_set(v___x_252_, 0, v_size_x27_255_);
v___x_266_ = v___x_252_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_size_x27_255_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_val_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
else
{
lean_object* v___x_269_; 
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v_buckets_x27_257_);
lean_ctor_set(v___x_252_, 0, v_size_x27_255_);
v___x_269_ = v___x_252_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_size_x27_255_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_buckets_x27_257_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_dec(v_b_231_);
lean_dec_ref(v_a_230_);
return v_m_229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(lean_object* v_self_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_toHashSet_278_; lean_object* v_toArray_279_; uint8_t v___x_280_; 
v_toHashSet_278_ = lean_ctor_get(v_self_276_, 0);
v_toArray_279_ = lean_ctor_get(v_self_276_, 1);
v___x_280_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_toHashSet_278_, v_a_277_);
if (v___x_280_ == 0)
{
lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_290_; 
lean_inc_ref(v_toArray_279_);
lean_inc_ref(v_toHashSet_278_);
v_isSharedCheck_290_ = !lean_is_exclusive(v_self_276_);
if (v_isSharedCheck_290_ == 0)
{
lean_object* v_unused_291_; lean_object* v_unused_292_; 
v_unused_291_ = lean_ctor_get(v_self_276_, 1);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_self_276_, 0);
lean_dec(v_unused_292_);
v___x_282_ = v_self_276_;
v_isShared_283_ = v_isSharedCheck_290_;
goto v_resetjp_281_;
}
else
{
lean_dec(v_self_276_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_290_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_284_ = lean_box(0);
lean_inc_ref(v_a_277_);
v___x_285_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_toHashSet_278_, v_a_277_, v___x_284_);
v___x_286_ = lean_array_push(v_toArray_279_, v_a_277_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v___x_286_);
lean_ctor_set(v___x_282_, 0, v___x_285_);
v___x_288_ = v___x_282_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
else
{
lean_dec_ref(v_a_277_);
return v_self_276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(lean_object* v_as_293_, size_t v_i_294_, size_t v_stop_295_, lean_object* v_b_296_){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = lean_usize_dec_eq(v_i_294_, v_stop_295_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; size_t v___x_300_; size_t v___x_301_; 
v___x_298_ = lean_array_uget_borrowed(v_as_293_, v_i_294_);
lean_inc(v___x_298_);
v___x_299_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v_b_296_, v___x_298_);
v___x_300_ = ((size_t)1ULL);
v___x_301_ = lean_usize_add(v_i_294_, v___x_300_);
v_i_294_ = v___x_301_;
v_b_296_ = v___x_299_;
goto _start;
}
else
{
return v_b_296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1___boxed(lean_object* v_as_303_, lean_object* v_i_304_, lean_object* v_stop_305_, lean_object* v_b_306_){
_start:
{
size_t v_i_boxed_307_; size_t v_stop_boxed_308_; lean_object* v_res_309_; 
v_i_boxed_307_ = lean_unbox_usize(v_i_304_);
lean_dec(v_i_304_);
v_stop_boxed_308_ = lean_unbox_usize(v_stop_305_);
lean_dec(v_stop_305_);
v_res_309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_as_303_, v_i_boxed_307_, v_stop_boxed_308_, v_b_306_);
lean_dec_ref(v_as_303_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(lean_object* v_as_310_, size_t v_i_311_, size_t v_stop_312_, lean_object* v_b_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = lean_usize_dec_eq(v_i_311_, v_stop_312_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v_keyName_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_322_ = lean_array_uget_borrowed(v_as_310_, v_i_311_);
v_keyName_323_ = lean_ctor_get(v___x_322_, 2);
v___x_324_ = l_Lake_Package_transDepsFacet;
lean_inc(v_keyName_323_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v_keyName_323_);
v___x_326_ = l_Lake_Package_keyword;
lean_inc(v___x_322_);
v___x_327_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
lean_ctor_set(v___x_327_, 2, v___x_322_);
lean_ctor_set(v___x_327_, 3, v___x_324_);
lean_inc_ref(v___y_314_);
lean_inc_ref(v___y_318_);
lean_inc(v___y_317_);
lean_inc(v___y_316_);
lean_inc(v___y_315_);
v___x_328_ = lean_apply_7(v___y_314_, v___x_327_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, lean_box(0));
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v_a_330_; lean_object* v___x_331_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
v_a_330_ = lean_ctor_get(v___x_328_, 1);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_328_, 2);
v___x_331_ = l_Lake_Job_await___redArg(v_a_329_, v_a_330_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v_a_333_; lean_object* v___y_335_; lean_object* v___x_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
v_a_333_ = lean_ctor_get(v___x_331_, 1);
lean_inc(v_a_333_);
lean_dec_ref_known(v___x_331_, 2);
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = lean_array_get_size(v_a_332_);
v___x_342_ = lean_nat_dec_lt(v___x_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_dec(v_a_332_);
v___y_335_ = v_b_313_;
goto v___jp_334_;
}
else
{
uint8_t v___x_343_; 
v___x_343_ = lean_nat_dec_le(v___x_341_, v___x_341_);
if (v___x_343_ == 0)
{
if (v___x_342_ == 0)
{
lean_dec(v_a_332_);
v___y_335_ = v_b_313_;
goto v___jp_334_;
}
else
{
size_t v___x_344_; size_t v___x_345_; lean_object* v___x_346_; 
v___x_344_ = ((size_t)0ULL);
v___x_345_ = lean_usize_of_nat(v___x_341_);
v___x_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_332_, v___x_344_, v___x_345_, v_b_313_);
lean_dec(v_a_332_);
v___y_335_ = v___x_346_;
goto v___jp_334_;
}
}
else
{
size_t v___x_347_; size_t v___x_348_; lean_object* v___x_349_; 
v___x_347_ = ((size_t)0ULL);
v___x_348_ = lean_usize_of_nat(v___x_341_);
v___x_349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_332_, v___x_347_, v___x_348_, v_b_313_);
lean_dec(v_a_332_);
v___y_335_ = v___x_349_;
goto v___jp_334_;
}
}
v___jp_334_:
{
lean_object* v___x_336_; size_t v___x_337_; size_t v___x_338_; 
lean_inc(v___x_322_);
v___x_336_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v___y_335_, v___x_322_);
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_add(v_i_311_, v___x_337_);
v_i_311_ = v___x_338_;
v_b_313_ = v___x_336_;
v___y_319_ = v_a_333_;
goto _start;
}
}
else
{
lean_object* v_a_350_; lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec_ref(v___y_314_);
lean_dec_ref(v_b_313_);
v_a_350_ = lean_ctor_get(v___x_331_, 0);
v_a_351_ = lean_ctor_get(v___x_331_, 1);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_331_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_inc(v_a_350_);
lean_dec(v___x_331_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_350_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_object* v_a_359_; lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec_ref(v___y_314_);
lean_dec_ref(v_b_313_);
v_a_359_ = lean_ctor_get(v___x_328_, 0);
v_a_360_ = lean_ctor_get(v___x_328_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_328_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_inc(v_a_359_);
lean_dec(v___x_328_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_359_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
else
{
lean_object* v___x_368_; 
lean_dec_ref(v___y_314_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v_b_313_);
lean_ctor_set(v___x_368_, 1, v___y_319_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3___boxed(lean_object* v_as_369_, lean_object* v_i_370_, lean_object* v_stop_371_, lean_object* v_b_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
size_t v_i_boxed_380_; size_t v_stop_boxed_381_; lean_object* v_res_382_; 
v_i_boxed_380_ = lean_unbox_usize(v_i_370_);
lean_dec(v_i_370_);
v_stop_boxed_381_ = lean_unbox_usize(v_stop_371_);
lean_dec(v_stop_371_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_as_369_, v_i_boxed_380_, v_stop_boxed_381_, v_b_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v_as_369_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(lean_object* v___x_383_, lean_object* v___x_384_, lean_object* v___x_385_, lean_object* v___x_386_, lean_object* v_depPkgs_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_a_396_; lean_object* v_a_397_; lean_object* v___y_417_; uint8_t v___x_429_; 
v___x_429_ = lean_nat_dec_lt(v___x_383_, v___x_385_);
if (v___x_429_ == 0)
{
lean_dec_ref(v___y_388_);
v_a_396_ = v___x_386_;
v_a_397_ = v___y_393_;
goto v___jp_395_;
}
else
{
uint8_t v___x_430_; 
v___x_430_ = lean_nat_dec_le(v___x_385_, v___x_385_);
if (v___x_430_ == 0)
{
if (v___x_429_ == 0)
{
lean_dec_ref(v___y_388_);
v_a_396_ = v___x_386_;
v_a_397_ = v___y_393_;
goto v___jp_395_;
}
else
{
size_t v___x_431_; size_t v___x_432_; lean_object* v___x_433_; 
v___x_431_ = ((size_t)0ULL);
v___x_432_ = lean_usize_of_nat(v___x_385_);
v___x_433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_387_, v___x_431_, v___x_432_, v___x_386_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
v___y_417_ = v___x_433_;
goto v___jp_416_;
}
}
else
{
size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
v___x_434_ = ((size_t)0ULL);
v___x_435_ = lean_usize_of_nat(v___x_385_);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_387_, v___x_434_, v___x_435_, v___x_386_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
v___y_417_ = v___x_436_;
goto v___jp_416_;
}
}
v___jp_395_:
{
lean_object* v_toArray_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_414_; 
v_toArray_398_ = lean_ctor_get(v_a_396_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_a_396_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v_a_396_, 0);
lean_dec(v_unused_415_);
v___x_400_ = v_a_396_;
v_isShared_401_ = v_isSharedCheck_414_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_toArray_398_);
lean_dec(v_a_396_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_414_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; uint8_t v___x_404_; uint8_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_402_ = lean_mk_empty_array_with_capacity(v___x_383_);
v___x_403_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_404_ = 0;
v___x_405_ = 0;
v___x_406_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_407_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_407_, 0, v___x_402_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_ctor_set(v___x_407_, 2, v___x_383_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*3, v___x_404_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*3 + 1, v___x_405_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*3 + 2, v___x_405_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v___x_407_);
lean_ctor_set(v___x_400_, 0, v_toArray_398_);
v___x_409_ = v___x_400_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_toArray_398_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v___x_407_);
v___x_409_ = v_reuseFailAlloc_413_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = lean_task_pure(v___x_409_);
v___x_411_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v___x_384_);
lean_ctor_set(v___x_411_, 2, v___x_403_);
lean_ctor_set_uint8(v___x_411_, sizeof(void*)*3, v___x_405_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_a_397_);
return v___x_412_;
}
}
}
v___jp_416_:
{
if (lean_obj_tag(v___y_417_) == 0)
{
lean_object* v_a_418_; lean_object* v_a_419_; 
v_a_418_ = lean_ctor_get(v___y_417_, 0);
lean_inc(v_a_418_);
v_a_419_ = lean_ctor_get(v___y_417_, 1);
lean_inc(v_a_419_);
lean_dec_ref_known(v___y_417_, 2);
v_a_396_ = v_a_418_;
v_a_397_ = v_a_419_;
goto v___jp_395_;
}
else
{
lean_object* v_a_420_; lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_428_; 
lean_dec(v___x_384_);
lean_dec(v___x_383_);
v_a_420_ = lean_ctor_get(v___y_417_, 0);
v_a_421_ = lean_ctor_get(v___y_417_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v___y_417_);
if (v_isSharedCheck_428_ == 0)
{
v___x_423_ = v___y_417_;
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_inc(v_a_420_);
lean_dec(v___y_417_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_428_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_426_; 
if (v_isShared_424_ == 0)
{
v___x_426_ = v___x_423_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_a_420_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_a_421_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed(lean_object* v___x_437_, lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v_depPkgs_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(v___x_437_, v___x_438_, v___x_439_, v___x_440_, v_depPkgs_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v_depPkgs_441_);
lean_dec(v___x_439_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(lean_object* v_self_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_depPkgs_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___f_463_; lean_object* v___x_464_; 
v_depPkgs_458_ = lean_ctor_get(v_self_450_, 14);
lean_inc_ref(v_depPkgs_458_);
lean_dec_ref(v_self_450_);
v___x_459_ = lean_box(0);
v___x_460_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2;
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_array_get_size(v_depPkgs_458_);
v___f_463_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed), 12, 5);
lean_closure_set(v___f_463_, 0, v___x_461_);
lean_closure_set(v___f_463_, 1, v___x_459_);
lean_closure_set(v___f_463_, 2, v___x_462_);
lean_closure_set(v___f_463_, 3, v___x_460_);
lean_closure_set(v___f_463_, 4, v_depPkgs_458_);
v___x_464_ = l_Lake_ensureJob___redArg(v___x_459_, v___f_463_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___boxed(lean_object* v_self_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(v_self_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_);
lean_dec_ref(v_a_470_);
lean_dec(v_a_469_);
lean_dec(v_a_468_);
lean_dec(v_a_467_);
return v_res_473_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object* v_00_u03b2_474_, lean_object* v_m_475_, lean_object* v_a_476_){
_start:
{
uint8_t v___x_477_; 
v___x_477_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_475_, v_a_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_478_, lean_object* v_m_479_, lean_object* v_a_480_){
_start:
{
uint8_t v_res_481_; lean_object* v_r_482_; 
v_res_481_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(v_00_u03b2_478_, v_m_479_, v_a_480_);
lean_dec_ref(v_a_480_);
lean_dec_ref(v_m_479_);
v_r_482_ = lean_box(v_res_481_);
return v_r_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1(lean_object* v_00_u03b2_483_, lean_object* v_m_484_, lean_object* v_a_485_, lean_object* v_b_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_m_484_, v_a_485_, v_b_486_);
return v___x_487_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_488_, lean_object* v_a_489_, lean_object* v_x_490_){
_start:
{
uint8_t v___x_491_; 
v___x_491_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_489_, v_x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_492_, lean_object* v_a_493_, lean_object* v_x_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(v_00_u03b2_492_, v_a_493_, v_x_494_);
lean_dec(v_x_494_);
lean_dec_ref(v_a_493_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_497_, lean_object* v_data_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_data_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_500_, lean_object* v_i_501_, lean_object* v_source_502_, lean_object* v_target_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v_i_501_, v_source_502_, v_target_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(v_x_506_, v_x_507_);
return v___x_508_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(lean_object* v_a_509_, lean_object* v_x_510_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
uint8_t v___x_511_; 
v___x_511_ = 0;
return v___x_511_;
}
else
{
lean_object* v_key_512_; lean_object* v_tail_513_; lean_object* v_name_514_; lean_object* v_name_515_; uint8_t v___x_516_; 
v_key_512_ = lean_ctor_get(v_x_510_, 0);
v_tail_513_ = lean_ctor_get(v_x_510_, 2);
v_name_514_ = lean_ctor_get(v_key_512_, 1);
v_name_515_ = lean_ctor_get(v_a_509_, 1);
v___x_516_ = lean_name_eq(v_name_514_, v_name_515_);
if (v___x_516_ == 0)
{
v_x_510_ = v_tail_513_;
goto _start;
}
else
{
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg___boxed(lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_518_, v_x_519_);
lean_dec(v_x_519_);
lean_dec_ref(v_a_518_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(lean_object* v_m_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_buckets_524_; lean_object* v_name_525_; lean_object* v___x_526_; uint64_t v___y_528_; 
v_buckets_524_ = lean_ctor_get(v_m_522_, 1);
v_name_525_ = lean_ctor_get(v_a_523_, 1);
v___x_526_ = lean_array_get_size(v_buckets_524_);
if (lean_obj_tag(v_name_525_) == 0)
{
uint64_t v___x_542_; 
v___x_542_ = 1723ULL;
v___y_528_ = v___x_542_;
goto v___jp_527_;
}
else
{
uint64_t v_hash_543_; 
v_hash_543_ = lean_ctor_get_uint64(v_name_525_, sizeof(void*)*2);
v___y_528_ = v_hash_543_;
goto v___jp_527_;
}
v___jp_527_:
{
uint64_t v___x_529_; uint64_t v___x_530_; uint64_t v_fold_531_; uint64_t v___x_532_; uint64_t v___x_533_; uint64_t v___x_534_; size_t v___x_535_; size_t v___x_536_; size_t v___x_537_; size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_529_ = 32ULL;
v___x_530_ = lean_uint64_shift_right(v___y_528_, v___x_529_);
v_fold_531_ = lean_uint64_xor(v___y_528_, v___x_530_);
v___x_532_ = 16ULL;
v___x_533_ = lean_uint64_shift_right(v_fold_531_, v___x_532_);
v___x_534_ = lean_uint64_xor(v_fold_531_, v___x_533_);
v___x_535_ = lean_uint64_to_usize(v___x_534_);
v___x_536_ = lean_usize_of_nat(v___x_526_);
v___x_537_ = ((size_t)1ULL);
v___x_538_ = lean_usize_sub(v___x_536_, v___x_537_);
v___x_539_ = lean_usize_land(v___x_535_, v___x_538_);
v___x_540_ = lean_array_uget_borrowed(v_buckets_524_, v___x_539_);
v___x_541_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_523_, v___x_540_);
return v___x_541_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg___boxed(lean_object* v_m_544_, lean_object* v_a_545_){
_start:
{
uint8_t v_res_546_; lean_object* v_r_547_; 
v_res_546_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(v_m_544_, v_a_545_);
lean_dec_ref(v_a_545_);
lean_dec_ref(v_m_544_);
v_r_547_ = lean_box(v_res_546_);
return v_r_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
if (lean_obj_tag(v_x_549_) == 0)
{
return v_x_548_;
}
else
{
lean_object* v_key_550_; lean_object* v_value_551_; lean_object* v_tail_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_579_; 
v_key_550_ = lean_ctor_get(v_x_549_, 0);
v_value_551_ = lean_ctor_get(v_x_549_, 1);
v_tail_552_ = lean_ctor_get(v_x_549_, 2);
v_isSharedCheck_579_ = !lean_is_exclusive(v_x_549_);
if (v_isSharedCheck_579_ == 0)
{
v___x_554_ = v_x_549_;
v_isShared_555_ = v_isSharedCheck_579_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_tail_552_);
lean_inc(v_value_551_);
lean_inc(v_key_550_);
lean_dec(v_x_549_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_579_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v_name_556_; lean_object* v___x_557_; uint64_t v___y_559_; 
v_name_556_ = lean_ctor_get(v_key_550_, 1);
v___x_557_ = lean_array_get_size(v_x_548_);
if (lean_obj_tag(v_name_556_) == 0)
{
uint64_t v___x_577_; 
v___x_577_ = 1723ULL;
v___y_559_ = v___x_577_;
goto v___jp_558_;
}
else
{
uint64_t v_hash_578_; 
v_hash_578_ = lean_ctor_get_uint64(v_name_556_, sizeof(void*)*2);
v___y_559_ = v_hash_578_;
goto v___jp_558_;
}
v___jp_558_:
{
uint64_t v___x_560_; uint64_t v___x_561_; uint64_t v_fold_562_; uint64_t v___x_563_; uint64_t v___x_564_; uint64_t v___x_565_; size_t v___x_566_; size_t v___x_567_; size_t v___x_568_; size_t v___x_569_; size_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_560_ = 32ULL;
v___x_561_ = lean_uint64_shift_right(v___y_559_, v___x_560_);
v_fold_562_ = lean_uint64_xor(v___y_559_, v___x_561_);
v___x_563_ = 16ULL;
v___x_564_ = lean_uint64_shift_right(v_fold_562_, v___x_563_);
v___x_565_ = lean_uint64_xor(v_fold_562_, v___x_564_);
v___x_566_ = lean_uint64_to_usize(v___x_565_);
v___x_567_ = lean_usize_of_nat(v___x_557_);
v___x_568_ = ((size_t)1ULL);
v___x_569_ = lean_usize_sub(v___x_567_, v___x_568_);
v___x_570_ = lean_usize_land(v___x_566_, v___x_569_);
v___x_571_ = lean_array_uget_borrowed(v_x_548_, v___x_570_);
lean_inc(v___x_571_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 2, v___x_571_);
v___x_573_ = v___x_554_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_key_550_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_value_551_);
lean_ctor_set(v_reuseFailAlloc_576_, 2, v___x_571_);
v___x_573_ = v_reuseFailAlloc_576_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; 
v___x_574_ = lean_array_uset(v_x_548_, v___x_570_, v___x_573_);
v_x_548_ = v___x_574_;
v_x_549_ = v_tail_552_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3___redArg(lean_object* v_i_580_, lean_object* v_source_581_, lean_object* v_target_582_){
_start:
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_array_get_size(v_source_581_);
v___x_584_ = lean_nat_dec_lt(v_i_580_, v___x_583_);
if (v___x_584_ == 0)
{
lean_dec_ref(v_source_581_);
lean_dec(v_i_580_);
return v_target_582_;
}
else
{
lean_object* v_es_585_; lean_object* v___x_586_; lean_object* v_source_587_; lean_object* v_target_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_es_585_ = lean_array_fget(v_source_581_, v_i_580_);
v___x_586_ = lean_box(0);
v_source_587_ = lean_array_fset(v_source_581_, v_i_580_, v___x_586_);
v_target_588_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6___redArg(v_target_582_, v_es_585_);
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_add(v_i_580_, v___x_589_);
lean_dec(v_i_580_);
v_i_580_ = v___x_590_;
v_source_581_ = v_source_587_;
v_target_582_ = v_target_588_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2___redArg(lean_object* v_data_592_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v_nbuckets_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_593_ = lean_array_get_size(v_data_592_);
v___x_594_ = lean_unsigned_to_nat(2u);
v_nbuckets_595_ = lean_nat_mul(v___x_593_, v___x_594_);
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_box(0);
v___x_598_ = lean_mk_array(v_nbuckets_595_, v___x_597_);
v___x_599_ = lean_array_propagate_mark(v_data_592_, v___x_598_);
v___x_600_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3___redArg(v___x_596_, v_data_592_, v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1___redArg(lean_object* v_m_601_, lean_object* v_a_602_, lean_object* v_b_603_){
_start:
{
lean_object* v_size_604_; lean_object* v_buckets_605_; lean_object* v_name_606_; lean_object* v___x_607_; uint64_t v___y_609_; 
v_size_604_ = lean_ctor_get(v_m_601_, 0);
v_buckets_605_ = lean_ctor_get(v_m_601_, 1);
v_name_606_ = lean_ctor_get(v_a_602_, 1);
v___x_607_ = lean_array_get_size(v_buckets_605_);
if (lean_obj_tag(v_name_606_) == 0)
{
uint64_t v___x_646_; 
v___x_646_ = 1723ULL;
v___y_609_ = v___x_646_;
goto v___jp_608_;
}
else
{
uint64_t v_hash_647_; 
v_hash_647_ = lean_ctor_get_uint64(v_name_606_, sizeof(void*)*2);
v___y_609_ = v_hash_647_;
goto v___jp_608_;
}
v___jp_608_:
{
uint64_t v___x_610_; uint64_t v___x_611_; uint64_t v_fold_612_; uint64_t v___x_613_; uint64_t v___x_614_; uint64_t v___x_615_; size_t v___x_616_; size_t v___x_617_; size_t v___x_618_; size_t v___x_619_; size_t v___x_620_; lean_object* v_bkt_621_; uint8_t v___x_622_; 
v___x_610_ = 32ULL;
v___x_611_ = lean_uint64_shift_right(v___y_609_, v___x_610_);
v_fold_612_ = lean_uint64_xor(v___y_609_, v___x_611_);
v___x_613_ = 16ULL;
v___x_614_ = lean_uint64_shift_right(v_fold_612_, v___x_613_);
v___x_615_ = lean_uint64_xor(v_fold_612_, v___x_614_);
v___x_616_ = lean_uint64_to_usize(v___x_615_);
v___x_617_ = lean_usize_of_nat(v___x_607_);
v___x_618_ = ((size_t)1ULL);
v___x_619_ = lean_usize_sub(v___x_617_, v___x_618_);
v___x_620_ = lean_usize_land(v___x_616_, v___x_619_);
v_bkt_621_ = lean_array_uget_borrowed(v_buckets_605_, v___x_620_);
v___x_622_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_602_, v_bkt_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_643_; 
lean_inc_ref(v_buckets_605_);
lean_inc(v_size_604_);
v_isSharedCheck_643_ = !lean_is_exclusive(v_m_601_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; lean_object* v_unused_645_; 
v_unused_644_ = lean_ctor_get(v_m_601_, 1);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_m_601_, 0);
lean_dec(v_unused_645_);
v___x_624_ = v_m_601_;
v_isShared_625_ = v_isSharedCheck_643_;
goto v_resetjp_623_;
}
else
{
lean_dec(v_m_601_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_643_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v_size_x27_627_; lean_object* v___x_628_; lean_object* v_buckets_x27_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_626_ = lean_unsigned_to_nat(1u);
v_size_x27_627_ = lean_nat_add(v_size_604_, v___x_626_);
lean_dec(v_size_604_);
lean_inc(v_bkt_621_);
v___x_628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_628_, 0, v_a_602_);
lean_ctor_set(v___x_628_, 1, v_b_603_);
lean_ctor_set(v___x_628_, 2, v_bkt_621_);
v_buckets_x27_629_ = lean_array_uset(v_buckets_605_, v___x_620_, v___x_628_);
v___x_630_ = lean_unsigned_to_nat(4u);
v___x_631_ = lean_nat_mul(v_size_x27_627_, v___x_630_);
v___x_632_ = lean_unsigned_to_nat(3u);
v___x_633_ = lean_nat_div(v___x_631_, v___x_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_array_get_size(v_buckets_x27_629_);
v___x_635_ = lean_nat_dec_le(v___x_633_, v___x_634_);
lean_dec(v___x_633_);
if (v___x_635_ == 0)
{
lean_object* v_val_636_; lean_object* v___x_638_; 
v_val_636_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2___redArg(v_buckets_x27_629_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v_val_636_);
lean_ctor_set(v___x_624_, 0, v_size_x27_627_);
v___x_638_ = v___x_624_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_size_x27_627_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_val_636_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
else
{
lean_object* v___x_641_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 1, v_buckets_x27_629_);
lean_ctor_set(v___x_624_, 0, v_size_x27_627_);
v___x_641_ = v___x_624_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_size_x27_627_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_buckets_x27_629_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
else
{
lean_dec(v_b_603_);
lean_dec_ref(v_a_602_);
return v_m_601_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(lean_object* v_as_648_, size_t v_sz_649_, size_t v_i_650_, lean_object* v_b_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_a_655_; lean_object* v_a_656_; uint8_t v___x_660_; 
v___x_660_ = lean_usize_dec_lt(v_i_650_, v_sz_649_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v_b_651_);
lean_ctor_set(v___x_661_, 1, v___y_652_);
return v___x_661_;
}
else
{
lean_object* v_fst_662_; lean_object* v_snd_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_678_; 
v_fst_662_ = lean_ctor_get(v_b_651_, 0);
v_snd_663_ = lean_ctor_get(v_b_651_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v_b_651_);
if (v_isSharedCheck_678_ == 0)
{
v___x_665_ = v_b_651_;
v_isShared_666_ = v_isSharedCheck_678_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_snd_663_);
lean_inc(v_fst_662_);
lean_dec(v_b_651_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_678_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_a_667_; uint8_t v___x_668_; 
v_a_667_ = lean_array_uget_borrowed(v_as_648_, v_i_650_);
v___x_668_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(v_snd_663_, v_a_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_669_ = lean_box(0);
lean_inc_n(v_a_667_, 2);
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1___redArg(v_snd_663_, v_a_667_, v___x_669_);
v___x_671_ = lean_array_push(v_fst_662_, v_a_667_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_670_);
lean_ctor_set(v___x_665_, 0, v___x_671_);
v___x_673_ = v___x_665_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v___x_670_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
v_a_655_ = v___x_673_;
v_a_656_ = v___y_652_;
goto v___jp_654_;
}
}
else
{
lean_object* v___x_676_; 
if (v_isShared_666_ == 0)
{
v___x_676_ = v___x_665_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_fst_662_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_snd_663_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
v_a_655_ = v___x_676_;
v_a_656_ = v___y_652_;
goto v___jp_654_;
}
}
}
}
v___jp_654_:
{
size_t v___x_657_; size_t v___x_658_; 
v___x_657_ = ((size_t)1ULL);
v___x_658_ = lean_usize_add(v_i_650_, v___x_657_);
v_i_650_ = v___x_658_;
v_b_651_ = v_a_655_;
v___y_652_ = v_a_656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg___boxed(lean_object* v_as_679_, lean_object* v_sz_680_, lean_object* v_i_681_, lean_object* v_b_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
size_t v_sz_boxed_685_; size_t v_i_boxed_686_; lean_object* v_res_687_; 
v_sz_boxed_685_ = lean_unbox_usize(v_sz_680_);
lean_dec(v_sz_680_);
v_i_boxed_686_ = lean_unbox_usize(v_i_681_);
lean_dec(v_i_681_);
v_res_687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(v_as_679_, v_sz_boxed_685_, v_i_boxed_686_, v_b_682_, v___y_683_);
lean_dec_ref(v_as_679_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3(lean_object* v_self_693_, lean_object* v_as_694_, size_t v_sz_695_, size_t v_i_696_, lean_object* v_b_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_a_706_; lean_object* v_a_707_; uint8_t v___x_709_; 
v___x_709_ = lean_usize_dec_lt(v_i_696_, v_sz_695_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
lean_dec_ref(v___y_698_);
lean_dec_ref(v_self_693_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_b_697_);
lean_ctor_set(v___x_710_, 1, v___y_703_);
return v___x_710_;
}
else
{
lean_object* v_fst_711_; lean_object* v_snd_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_812_; 
v_fst_711_ = lean_ctor_get(v_b_697_, 0);
v_snd_712_ = lean_ctor_get(v_b_697_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v_b_697_);
if (v_isSharedCheck_812_ == 0)
{
v___x_714_ = v_b_697_;
v_isShared_715_ = v_isSharedCheck_812_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_snd_712_);
lean_inc(v_fst_711_);
lean_dec(v_b_697_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_812_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_targetMods_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v_mods_746_; lean_object* v_a_747_; lean_object* v___x_783_; 
v_mods_746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__0));
v_a_747_ = lean_array_uget_borrowed(v_as_694_, v_i_696_);
v___x_783_ = l_Lake_Package_findTargetDecl_x3f(v_a_747_, v_self_693_);
if (lean_obj_tag(v___x_783_) == 0)
{
goto v___jp_748_;
}
else
{
lean_object* v_val_784_; lean_object* v_name_785_; lean_object* v_kind_786_; lean_object* v_config_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_810_; 
v_val_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v___x_783_, 1);
v_name_785_ = lean_ctor_get(v_val_784_, 1);
v_kind_786_ = lean_ctor_get(v_val_784_, 2);
v_config_787_ = lean_ctor_get(v_val_784_, 3);
v_isSharedCheck_810_ = !lean_is_exclusive(v_val_784_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v_val_784_, 0);
lean_dec(v_unused_811_);
v___x_789_ = v_val_784_;
v_isShared_790_ = v_isSharedCheck_810_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_config_787_);
lean_inc(v_kind_786_);
lean_inc(v_name_785_);
lean_dec(v_val_784_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_810_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__2));
v___x_792_ = lean_name_eq(v_kind_786_, v___x_791_);
lean_dec(v_kind_786_);
if (v___x_792_ == 0)
{
lean_del_object(v___x_789_);
lean_dec(v_config_787_);
lean_dec(v_name_785_);
goto v___jp_748_;
}
else
{
lean_object* v_keyName_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
v_keyName_793_ = lean_ctor_get(v_self_693_, 2);
lean_inc(v_name_785_);
lean_inc_ref(v_self_693_);
v___x_794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_794_, 0, v_self_693_);
lean_ctor_set(v___x_794_, 1, v_name_785_);
lean_ctor_set(v___x_794_, 2, v_config_787_);
v___x_795_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_793_);
v___x_796_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_796_, 0, v_keyName_793_);
lean_ctor_set(v___x_796_, 1, v_name_785_);
if (v_isShared_790_ == 0)
{
lean_ctor_set_tag(v___x_789_, 1);
lean_ctor_set(v___x_789_, 3, v___x_795_);
lean_ctor_set(v___x_789_, 2, v___x_794_);
lean_ctor_set(v___x_789_, 1, v___x_791_);
lean_ctor_set(v___x_789_, 0, v___x_796_);
v___x_798_ = v___x_789_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_809_, 2, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_809_, 3, v___x_795_);
v___x_798_ = v_reuseFailAlloc_809_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; 
lean_inc_ref(v___y_698_);
lean_inc_ref(v___y_702_);
lean_inc(v___y_701_);
lean_inc(v___y_700_);
lean_inc(v___y_699_);
v___x_799_ = lean_apply_7(v___y_698_, v___x_798_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, lean_box(0));
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v_a_801_; lean_object* v___x_802_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
v_a_801_ = lean_ctor_get(v___x_799_, 1);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_799_, 2);
v___x_802_ = l_Lake_Job_await___redArg(v_a_800_, v_a_801_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v_a_804_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
v_a_804_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_802_, 2);
lean_inc_ref(v___y_698_);
v_targetMods_717_ = v_a_803_;
v___y_718_ = v___y_698_;
v___y_719_ = v___y_699_;
v___y_720_ = v___y_700_;
v___y_721_ = v___y_701_;
v___y_722_ = v___y_702_;
v___y_723_ = v_a_804_;
goto v___jp_716_;
}
else
{
lean_object* v_a_805_; lean_object* v_a_806_; 
lean_del_object(v___x_714_);
lean_dec(v_snd_712_);
lean_dec(v_fst_711_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v_self_693_);
v_a_805_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_805_);
v_a_806_ = lean_ctor_get(v___x_802_, 1);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_802_, 2);
v_a_706_ = v_a_805_;
v_a_707_ = v_a_806_;
goto v___jp_705_;
}
}
else
{
lean_object* v_a_807_; lean_object* v_a_808_; 
lean_del_object(v___x_714_);
lean_dec(v_snd_712_);
lean_dec(v_fst_711_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v_self_693_);
v_a_807_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_807_);
v_a_808_ = lean_ctor_get(v___x_799_, 1);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_799_, 2);
v_a_706_ = v_a_807_;
v_a_707_ = v_a_808_;
goto v___jp_705_;
}
}
}
}
}
v___jp_716_:
{
lean_object* v___x_725_; 
lean_dec_ref(v___y_718_);
if (v_isShared_715_ == 0)
{
v___x_725_ = v___x_714_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_fst_711_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_snd_712_);
v___x_725_ = v_reuseFailAlloc_745_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
size_t v_sz_726_; size_t v___x_727_; lean_object* v___x_728_; 
v_sz_726_ = lean_array_size(v_targetMods_717_);
v___x_727_ = ((size_t)0ULL);
v___x_728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(v_targetMods_717_, v_sz_726_, v___x_727_, v___x_725_, v___y_723_);
lean_dec_ref(v_targetMods_717_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v_a_730_; lean_object* v_fst_731_; lean_object* v_snd_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_742_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
v_a_730_ = lean_ctor_get(v___x_728_, 1);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_728_, 2);
v_fst_731_ = lean_ctor_get(v_a_729_, 0);
v_snd_732_ = lean_ctor_get(v_a_729_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_a_729_);
if (v_isSharedCheck_742_ == 0)
{
v___x_734_ = v_a_729_;
v_isShared_735_ = v_isSharedCheck_742_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_snd_732_);
lean_inc(v_fst_731_);
lean_dec(v_a_729_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_742_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_fst_731_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_snd_732_);
v___x_737_ = v_reuseFailAlloc_741_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
size_t v___x_738_; size_t v___x_739_; 
v___x_738_ = ((size_t)1ULL);
v___x_739_ = lean_usize_add(v_i_696_, v___x_738_);
v_i_696_ = v___x_739_;
v_b_697_ = v___x_737_;
v___y_703_ = v_a_730_;
goto _start;
}
}
}
else
{
lean_object* v_a_743_; lean_object* v_a_744_; 
lean_dec_ref(v___y_698_);
lean_dec_ref(v_self_693_);
v_a_743_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_743_);
v_a_744_ = lean_ctor_get(v___x_728_, 1);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_728_, 2);
v_a_706_ = v_a_743_;
v_a_707_ = v_a_744_;
goto v___jp_705_;
}
}
}
v___jp_748_:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lake_Package_findTargetDecl_x3f(v_a_747_, v_self_693_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_inc_ref(v___y_698_);
v_targetMods_717_ = v_mods_746_;
v___y_718_ = v___y_698_;
v___y_719_ = v___y_699_;
v___y_720_ = v___y_700_;
v___y_721_ = v___y_701_;
v___y_722_ = v___y_702_;
v___y_723_ = v___y_703_;
goto v___jp_716_;
}
else
{
lean_object* v_val_750_; lean_object* v_name_751_; lean_object* v_kind_752_; lean_object* v_config_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_781_; 
v_val_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_val_750_);
lean_dec_ref_known(v___x_749_, 1);
v_name_751_ = lean_ctor_get(v_val_750_, 1);
v_kind_752_ = lean_ctor_get(v_val_750_, 2);
v_config_753_ = lean_ctor_get(v_val_750_, 3);
v_isSharedCheck_781_ = !lean_is_exclusive(v_val_750_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v_val_750_, 0);
lean_dec(v_unused_782_);
v___x_755_ = v_val_750_;
v_isShared_756_ = v_isSharedCheck_781_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_config_753_);
lean_inc(v_kind_752_);
lean_inc(v_name_751_);
lean_dec(v_val_750_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_781_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = l_Lake_LeanExe_keyword;
v___x_758_ = lean_name_eq(v_kind_752_, v___x_757_);
lean_dec(v_kind_752_);
if (v___x_758_ == 0)
{
lean_del_object(v___x_755_);
lean_dec(v_config_753_);
lean_dec(v_name_751_);
lean_inc_ref(v___y_698_);
v_targetMods_717_ = v_mods_746_;
v___y_718_ = v___y_698_;
v___y_719_ = v___y_699_;
v___y_720_ = v___y_700_;
v___y_721_ = v___y_701_;
v___y_722_ = v___y_702_;
v___y_723_ = v___y_703_;
goto v___jp_716_;
}
else
{
lean_object* v_root_759_; lean_object* v_keyName_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v_root_759_ = lean_ctor_get(v_config_753_, 2);
lean_inc_n(v_root_759_, 2);
v_keyName_760_ = lean_ctor_get(v_self_693_, 2);
v___x_761_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_753_);
lean_dec(v_config_753_);
lean_inc_ref(v_self_693_);
v___x_762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_762_, 0, v_self_693_);
lean_ctor_set(v___x_762_, 1, v_name_751_);
lean_ctor_set(v___x_762_, 2, v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v_root_759_);
v___x_764_ = l_Lake_Module_transImportsFacet;
lean_inc(v_keyName_760_);
v___x_765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_765_, 0, v_keyName_760_);
lean_ctor_set(v___x_765_, 1, v_root_759_);
v___x_766_ = l_Lake_Module_keyword;
lean_inc_ref(v___x_763_);
if (v_isShared_756_ == 0)
{
lean_ctor_set_tag(v___x_755_, 1);
lean_ctor_set(v___x_755_, 3, v___x_764_);
lean_ctor_set(v___x_755_, 2, v___x_763_);
lean_ctor_set(v___x_755_, 1, v___x_766_);
lean_ctor_set(v___x_755_, 0, v___x_765_);
v___x_768_ = v___x_755_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_780_, 2, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_780_, 3, v___x_764_);
v___x_768_ = v_reuseFailAlloc_780_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; 
lean_inc_ref(v___y_698_);
lean_inc_ref(v___y_702_);
lean_inc(v___y_701_);
lean_inc(v___y_700_);
lean_inc(v___y_699_);
v___x_769_ = lean_apply_7(v___y_698_, v___x_768_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, lean_box(0));
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v_a_771_; lean_object* v___x_772_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
v_a_771_ = lean_ctor_get(v___x_769_, 1);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_769_, 2);
v___x_772_ = l_Lake_Job_await___redArg(v_a_770_, v_a_771_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v_a_774_; lean_object* v___x_775_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
v_a_774_ = lean_ctor_get(v___x_772_, 1);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_772_, 2);
v___x_775_ = lean_array_push(v_a_773_, v___x_763_);
lean_inc_ref(v___y_698_);
v_targetMods_717_ = v___x_775_;
v___y_718_ = v___y_698_;
v___y_719_ = v___y_699_;
v___y_720_ = v___y_700_;
v___y_721_ = v___y_701_;
v___y_722_ = v___y_702_;
v___y_723_ = v_a_774_;
goto v___jp_716_;
}
else
{
lean_object* v_a_776_; lean_object* v_a_777_; 
lean_dec_ref_known(v___x_763_, 2);
lean_del_object(v___x_714_);
lean_dec(v_snd_712_);
lean_dec(v_fst_711_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v_self_693_);
v_a_776_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_776_);
v_a_777_ = lean_ctor_get(v___x_772_, 1);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_772_, 2);
v_a_706_ = v_a_776_;
v_a_707_ = v_a_777_;
goto v___jp_705_;
}
}
else
{
lean_object* v_a_778_; lean_object* v_a_779_; 
lean_dec_ref_known(v___x_763_, 2);
lean_del_object(v___x_714_);
lean_dec(v_snd_712_);
lean_dec(v_fst_711_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v_self_693_);
v_a_778_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_778_);
v_a_779_ = lean_ctor_get(v___x_769_, 1);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_769_, 2);
v_a_706_ = v_a_778_;
v_a_707_ = v_a_779_;
goto v___jp_705_;
}
}
}
}
}
}
}
}
v___jp_705_:
{
lean_object* v___x_708_; 
v___x_708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_708_, 0, v_a_706_);
lean_ctor_set(v___x_708_, 1, v_a_707_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___boxed(lean_object* v_self_813_, lean_object* v_as_814_, lean_object* v_sz_815_, lean_object* v_i_816_, lean_object* v_b_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
size_t v_sz_boxed_825_; size_t v_i_boxed_826_; lean_object* v_res_827_; 
v_sz_boxed_825_ = lean_unbox_usize(v_sz_815_);
lean_dec(v_sz_815_);
v_i_boxed_826_ = lean_unbox_usize(v_i_816_);
lean_dec(v_i_816_);
v_res_827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3(v_self_813_, v_as_814_, v_sz_boxed_825_, v_i_boxed_826_, v_b_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v_as_814_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0(lean_object* v_self_828_, lean_object* v_defaultTargets_829_, size_t v_sz_830_, size_t v___x_831_, lean_object* v___x_832_, lean_object* v___x_833_, lean_object* v___x_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3(v_self_828_, v_defaultTargets_829_, v_sz_830_, v___x_831_, v___x_832_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_868_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_a_844_ = lean_ctor_get(v___x_842_, 1);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_868_ == 0)
{
v___x_846_ = v___x_842_;
v_isShared_847_ = v_isSharedCheck_868_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_868_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v_fst_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_866_; 
v_fst_848_ = lean_ctor_get(v_a_843_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v_a_843_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; 
v_unused_867_ = lean_ctor_get(v_a_843_, 1);
lean_dec(v_unused_867_);
v___x_850_ = v_a_843_;
v_isShared_851_ = v_isSharedCheck_866_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_fst_848_);
lean_dec(v_a_843_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_866_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_852_ = lean_mk_empty_array_with_capacity(v___x_833_);
v___x_853_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_854_ = 0;
v___x_855_ = 0;
v___x_856_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_857_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_857_, 0, v___x_852_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
lean_ctor_set(v___x_857_, 2, v___x_833_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*3, v___x_854_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*3 + 1, v___x_855_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*3 + 2, v___x_855_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v___x_857_);
lean_ctor_set(v___x_846_, 0, v_fst_848_);
v___x_859_ = v___x_846_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_fst_848_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v___x_857_);
v___x_859_ = v_reuseFailAlloc_865_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_860_ = lean_task_pure(v___x_859_);
v___x_861_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v___x_834_);
lean_ctor_set(v___x_861_, 2, v___x_853_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*3, v___x_855_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v_a_844_);
lean_ctor_set(v___x_850_, 0, v___x_861_);
v___x_863_ = v___x_850_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_a_844_);
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
else
{
lean_object* v_a_869_; lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec(v___x_834_);
lean_dec(v___x_833_);
v_a_869_ = lean_ctor_get(v___x_842_, 0);
v_a_870_ = lean_ctor_get(v___x_842_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_842_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_inc(v_a_869_);
lean_dec(v___x_842_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_869_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0___boxed(lean_object* v_self_878_, lean_object* v_defaultTargets_879_, lean_object* v_sz_880_, lean_object* v___x_881_, lean_object* v___x_882_, lean_object* v___x_883_, lean_object* v___x_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
size_t v_sz_boxed_892_; size_t v___x_15377__boxed_893_; lean_object* v_res_894_; 
v_sz_boxed_892_ = lean_unbox_usize(v_sz_880_);
lean_dec(v_sz_880_);
v___x_15377__boxed_893_ = lean_unbox_usize(v___x_881_);
lean_dec(v___x_881_);
v_res_894_ = l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0(v_self_878_, v_defaultTargets_879_, v_sz_boxed_892_, v___x_15377__boxed_893_, v___x_882_, v___x_883_, v___x_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v_defaultTargets_879_);
return v_res_894_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = lean_box(0);
v___x_896_ = lean_unsigned_to_nat(16u);
v___x_897_ = lean_mk_array(v___x_896_, v___x_895_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v_seen_900_; 
v___x_898_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0);
v___x_899_ = lean_unsigned_to_nat(0u);
v_seen_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_seen_900_, 0, v___x_899_);
lean_ctor_set(v_seen_900_, 1, v___x_898_);
return v_seen_900_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2(void){
_start:
{
lean_object* v_seen_901_; lean_object* v_mods_902_; lean_object* v___x_903_; 
v_seen_901_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1, &l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1);
v_mods_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__0));
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v_mods_902_);
lean_ctor_set(v___x_903_, 1, v_seen_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules(lean_object* v_self_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_defaultTargets_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; size_t v_sz_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___f_921_; lean_object* v___x_922_; 
v_defaultTargets_914_ = lean_ctor_get(v_self_906_, 17);
lean_inc_ref(v_defaultTargets_914_);
v___x_915_ = lean_unsigned_to_nat(0u);
v___x_916_ = lean_box(0);
v___x_917_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2);
v_sz_918_ = lean_array_size(v_defaultTargets_914_);
v___x_919_ = lean_box_usize(v_sz_918_);
v___x_920_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___boxed__const__1));
v___f_921_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0___boxed), 14, 7);
lean_closure_set(v___f_921_, 0, v_self_906_);
lean_closure_set(v___f_921_, 1, v_defaultTargets_914_);
lean_closure_set(v___f_921_, 2, v___x_919_);
lean_closure_set(v___f_921_, 3, v___x_920_);
lean_closure_set(v___f_921_, 4, v___x_917_);
lean_closure_set(v___f_921_, 5, v___x_915_);
lean_closure_set(v___f_921_, 6, v___x_916_);
v___x_922_ = l_Lake_ensureJob___redArg(v___x_916_, v___f_921_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___boxed(lean_object* v_self_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules(v_self_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec(v_a_926_);
lean_dec(v_a_925_);
return v_res_931_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0(lean_object* v_00_u03b2_932_, lean_object* v_m_933_, lean_object* v_a_934_){
_start:
{
uint8_t v___x_935_; 
v___x_935_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(v_m_933_, v_a_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___boxed(lean_object* v_00_u03b2_936_, lean_object* v_m_937_, lean_object* v_a_938_){
_start:
{
uint8_t v_res_939_; lean_object* v_r_940_; 
v_res_939_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0(v_00_u03b2_936_, v_m_937_, v_a_938_);
lean_dec_ref(v_a_938_);
lean_dec_ref(v_m_937_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1(lean_object* v_00_u03b2_941_, lean_object* v_m_942_, lean_object* v_a_943_, lean_object* v_b_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1___redArg(v_m_942_, v_a_943_, v_b_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2(lean_object* v_as_946_, size_t v_sz_947_, size_t v_i_948_, lean_object* v_b_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(v_as_946_, v_sz_947_, v_i_948_, v_b_949_, v___y_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___boxed(lean_object* v_as_958_, lean_object* v_sz_959_, lean_object* v_i_960_, lean_object* v_b_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
size_t v_sz_boxed_969_; size_t v_i_boxed_970_; lean_object* v_res_971_; 
v_sz_boxed_969_ = lean_unbox_usize(v_sz_959_);
lean_dec(v_sz_959_);
v_i_boxed_970_ = lean_unbox_usize(v_i_960_);
lean_dec(v_i_960_);
v_res_971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2(v_as_958_, v_sz_boxed_969_, v_i_boxed_970_, v_b_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec_ref(v_as_958_);
return v_res_971_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0(lean_object* v_00_u03b2_972_, lean_object* v_a_973_, lean_object* v_x_974_){
_start:
{
uint8_t v___x_975_; 
v___x_975_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_973_, v_x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___boxed(lean_object* v_00_u03b2_976_, lean_object* v_a_977_, lean_object* v_x_978_){
_start:
{
uint8_t v_res_979_; lean_object* v_r_980_; 
v_res_979_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0(v_00_u03b2_976_, v_a_977_, v_x_978_);
lean_dec(v_x_978_);
lean_dec_ref(v_a_977_);
v_r_980_ = lean_box(v_res_979_);
return v_r_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2(lean_object* v_00_u03b2_981_, lean_object* v_data_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2___redArg(v_data_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_984_, lean_object* v_i_985_, lean_object* v_source_986_, lean_object* v_target_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3___redArg(v_i_985_, v_source_986_, v_target_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6___redArg(v_x_990_, v_x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0(lean_object* v_as_993_, size_t v_i_994_, size_t v_stop_995_, lean_object* v_b_996_){
_start:
{
uint8_t v___x_997_; 
v___x_997_ = lean_usize_dec_eq(v_i_994_, v_stop_995_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; lean_object* v_name_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; size_t v___x_1005_; size_t v___x_1006_; 
v___x_998_ = lean_array_uget_borrowed(v_as_993_, v_i_994_);
v_name_999_ = lean_ctor_get(v___x_998_, 1);
v___x_1000_ = 1;
lean_inc(v_name_999_);
v___x_1001_ = l_Lean_Name_toString(v_name_999_, v___x_1000_);
v___x_1002_ = lean_string_append(v_b_996_, v___x_1001_);
lean_dec_ref(v___x_1001_);
v___x_1003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0));
v___x_1004_ = lean_string_append(v___x_1002_, v___x_1003_);
v___x_1005_ = ((size_t)1ULL);
v___x_1006_ = lean_usize_add(v_i_994_, v___x_1005_);
v_i_994_ = v___x_1006_;
v_b_996_ = v___x_1004_;
goto _start;
}
else
{
return v_b_996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_1008_, lean_object* v_i_1009_, lean_object* v_stop_1010_, lean_object* v_b_1011_){
_start:
{
size_t v_i_boxed_1012_; size_t v_stop_boxed_1013_; lean_object* v_res_1014_; 
v_i_boxed_1012_ = lean_unbox_usize(v_i_1009_);
lean_dec(v_i_1009_);
v_stop_boxed_1013_ = lean_unbox_usize(v_stop_1010_);
lean_dec(v_stop_1010_);
v_res_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0(v_as_1008_, v_i_boxed_1012_, v_stop_boxed_1013_, v_b_1011_);
lean_dec_ref(v_as_1008_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2(size_t v_sz_1015_, size_t v_i_1016_, lean_object* v_bs_1017_){
_start:
{
uint8_t v___x_1018_; 
v___x_1018_ = lean_usize_dec_lt(v_i_1016_, v_sz_1015_);
if (v___x_1018_ == 0)
{
return v_bs_1017_;
}
else
{
lean_object* v_v_1019_; lean_object* v_name_1020_; lean_object* v___x_1021_; lean_object* v_bs_x27_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; size_t v___x_1025_; size_t v___x_1026_; lean_object* v___x_1027_; 
v_v_1019_ = lean_array_uget_borrowed(v_bs_1017_, v_i_1016_);
v_name_1020_ = lean_ctor_get(v_v_1019_, 1);
lean_inc(v_name_1020_);
v___x_1021_ = lean_unsigned_to_nat(0u);
v_bs_x27_1022_ = lean_array_uset(v_bs_1017_, v_i_1016_, v___x_1021_);
v___x_1023_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1020_, v___x_1018_);
v___x_1024_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
v___x_1025_ = ((size_t)1ULL);
v___x_1026_ = lean_usize_add(v_i_1016_, v___x_1025_);
v___x_1027_ = lean_array_uset(v_bs_x27_1022_, v_i_1016_, v___x_1024_);
v_i_1016_ = v___x_1026_;
v_bs_1017_ = v___x_1027_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_1029_, lean_object* v_i_1030_, lean_object* v_bs_1031_){
_start:
{
size_t v_sz_boxed_1032_; size_t v_i_boxed_1033_; lean_object* v_res_1034_; 
v_sz_boxed_1032_ = lean_unbox_usize(v_sz_1029_);
lean_dec(v_sz_1029_);
v_i_boxed_1033_ = lean_unbox_usize(v_i_1030_);
lean_dec(v_i_1030_);
v_res_1034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_1032_, v_i_boxed_1033_, v_bs_1031_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1(lean_object* v_a_1035_){
_start:
{
size_t v_sz_1036_; size_t v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_sz_1036_ = lean_array_size(v_a_1035_);
v___x_1037_ = ((size_t)0ULL);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2(v_sz_1036_, v___x_1037_, v_a_1035_);
v___x_1039_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0(uint8_t v_fmt_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___y_1043_; 
if (v_fmt_1040_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1050_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = lean_array_get_size(v_a_1041_);
v___x_1053_ = lean_nat_dec_lt(v___x_1051_, v___x_1052_);
if (v___x_1053_ == 0)
{
lean_dec_ref(v_a_1041_);
v___y_1043_ = v___x_1050_;
goto v___jp_1042_;
}
else
{
size_t v___x_1054_; size_t v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = ((size_t)0ULL);
v___x_1055_ = lean_usize_of_nat(v___x_1052_);
v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0(v_a_1041_, v___x_1054_, v___x_1055_, v___x_1050_);
lean_dec_ref(v_a_1041_);
v___y_1043_ = v___x_1056_;
goto v___jp_1042_;
}
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = l_Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1(v_a_1041_);
v___x_1058_ = l_Lean_Json_compress(v___x_1057_);
return v___x_1058_;
}
v___jp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1044_ = lean_unsigned_to_nat(1u);
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = lean_string_utf8_byte_size(v___y_1043_);
lean_inc_ref(v___y_1043_);
v___x_1047_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1047_, 0, v___y_1043_);
lean_ctor_set(v___x_1047_, 1, v___x_1045_);
lean_ctor_set(v___x_1047_, 2, v___x_1046_);
v___x_1048_ = l_String_Slice_Pos_prevn(v___x_1047_, v___x_1046_, v___x_1044_);
lean_dec_ref_known(v___x_1047_, 3);
v___x_1049_ = lean_string_utf8_extract_fast(v___y_1043_, v___x_1045_, v___x_1048_);
lean_dec(v___x_1048_);
lean_dec_ref(v___y_1043_);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0___boxed(lean_object* v_fmt_1059_, lean_object* v_a_1060_){
_start:
{
uint8_t v_fmt_boxed_1061_; lean_object* v_res_1062_; 
v_fmt_boxed_1061_ = lean_unbox(v_fmt_1059_);
v_res_1062_ = l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0(v_fmt_boxed_1061_, v_a_1060_);
return v_res_1062_;
}
}
static lean_object* _init_l_Lake_Package_defaultModulesFacetConfig___closed__2(void){
_start:
{
uint8_t v___x_1065_; lean_object* v___f_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1065_ = 1;
v___f_1066_ = ((lean_object*)(l_Lake_Package_defaultModulesFacetConfig___closed__0));
v___x_1067_ = 0;
v___x_1068_ = lean_box(0);
v___x_1069_ = ((lean_object*)(l_Lake_Package_defaultModulesFacetConfig___closed__1));
v___x_1070_ = l_Lake_Package_keyword;
v___x_1071_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_1069_);
lean_ctor_set(v___x_1071_, 2, v___x_1068_);
lean_ctor_set(v___x_1071_, 3, v___f_1066_);
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*4, v___x_1067_);
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*4 + 1, v___x_1065_);
return v___x_1071_;
}
}
static lean_object* _init_l_Lake_Package_defaultModulesFacetConfig(void){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = lean_obj_once(&l_Lake_Package_defaultModulesFacetConfig___closed__2, &l_Lake_Package_defaultModulesFacetConfig___closed__2_once, _init_l_Lake_Package_defaultModulesFacetConfig___closed__2);
return v___x_1072_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_1074_; lean_object* v___f_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1074_ = 1;
v___f_1075_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__0));
v___x_1076_ = 0;
v___x_1077_ = lean_box(0);
v___x_1078_ = ((lean_object*)(l_Lake_Package_transDepsFacetConfig___closed__0));
v___x_1079_ = l_Lake_Package_keyword;
v___x_1080_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v___x_1078_);
lean_ctor_set(v___x_1080_, 2, v___x_1077_);
lean_ctor_set(v___x_1080_, 3, v___f_1075_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*4, v___x_1076_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*4 + 1, v___x_1074_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig(void){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_obj_once(&l_Lake_Package_transDepsFacetConfig___closed__1, &l_Lake_Package_transDepsFacetConfig___closed__1_once, _init_l_Lake_Package_transDepsFacetConfig___closed__1);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object* v_self_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_config_1090_; uint8_t v_preferReleaseBuild_1091_; 
v_config_1090_ = lean_ctor_get(v_self_1082_, 6);
v_preferReleaseBuild_1091_ = lean_ctor_get_uint8(v_config_1090_, sizeof(void*)*28 + 2);
if (v_preferReleaseBuild_1091_ == 0)
{
lean_object* v_keyName_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_keyName_1092_ = lean_ctor_get(v_self_1082_, 2);
v___x_1093_ = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(v_keyName_1092_);
v___x_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_keyName_1092_);
v___x_1095_ = l_Lake_Package_keyword;
v___x_1096_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
lean_ctor_set(v___x_1096_, 2, v_self_1082_);
lean_ctor_set(v___x_1096_, 3, v___x_1093_);
lean_inc_ref(v_a_1087_);
lean_inc(v_a_1086_);
lean_inc(v_a_1085_);
lean_inc(v_a_1084_);
v___x_1097_ = lean_apply_7(v_a_1083_, v___x_1096_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, lean_box(0));
return v___x_1097_;
}
else
{
lean_object* v_keyName_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_keyName_1098_ = lean_ctor_get(v_self_1082_, 2);
v___x_1099_ = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(v_keyName_1098_);
v___x_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1100_, 0, v_keyName_1098_);
v___x_1101_ = l_Lake_Package_keyword;
v___x_1102_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
lean_ctor_set(v___x_1102_, 2, v_self_1082_);
lean_ctor_set(v___x_1102_, 3, v___x_1099_);
lean_inc_ref(v_a_1087_);
lean_inc(v_a_1086_);
lean_inc(v_a_1085_);
lean_inc(v_a_1084_);
v___x_1103_ = lean_apply_7(v_a_1083_, v___x_1102_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, lean_box(0));
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___boxed(lean_object* v_self_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(v_self_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec(v_a_1106_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t v_fmt_1115_, uint8_t v_a_1116_){
_start:
{
if (v_fmt_1115_ == 0)
{
if (v_a_1116_ == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0));
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; 
v___x_1118_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1));
return v___x_1118_;
}
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1119_, 0, v_a_1116_);
v___x_1120_ = l_Lean_Json_compress(v___x_1119_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object* v_fmt_1121_, lean_object* v_a_1122_){
_start:
{
uint8_t v_fmt_boxed_1123_; uint8_t v_a_boxed_1124_; lean_object* v_res_1125_; 
v_fmt_boxed_1123_ = lean_unbox(v_fmt_1121_);
v_a_boxed_1124_ = lean_unbox(v_a_1122_);
v_res_1125_ = l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(v_fmt_boxed_1123_, v_a_boxed_1124_);
return v_res_1125_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1128_; uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___f_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___f_1128_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_1129_ = 1;
v___x_1130_ = l_Lake_instDataKindBool;
v___f_1131_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__0));
v___x_1132_ = l_Lake_Package_keyword;
v___x_1133_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
lean_ctor_set(v___x_1133_, 1, v___f_1131_);
lean_ctor_set(v___x_1133_, 2, v___x_1130_);
lean_ctor_set(v___x_1133_, 3, v___f_1128_);
lean_ctor_set_uint8(v___x_1133_, sizeof(void*)*4, v___x_1129_);
lean_ctor_set_uint8(v___x_1133_, sizeof(void*)*4 + 1, v___x_1129_);
return v___x_1133_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig(void){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_obj_once(&l_Lake_Package_optBuildCacheFacetConfig___closed__2, &l_Lake_Package_optBuildCacheFacetConfig___closed__2_once, _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(lean_object* v_self_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___y_1146_; uint8_t v___y_1147_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1170_; uint8_t v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v_toContext_1177_; lean_object* v_lakeEnv_1178_; uint8_t v_noCache_1179_; lean_object* v_toolchain_1180_; uint8_t v_a_1182_; lean_object* v_a_1183_; 
v_toContext_1177_ = lean_ctor_get(v_a_1142_, 1);
v_lakeEnv_1178_ = lean_ctor_get(v_toContext_1177_, 0);
v_noCache_1179_ = lean_ctor_get_uint8(v_lakeEnv_1178_, sizeof(void*)*20);
v_toolchain_1180_ = lean_ctor_get(v_lakeEnv_1178_, 19);
if (v_noCache_1179_ == 0)
{
uint8_t v___x_1198_; 
v___x_1198_ = 1;
v_a_1182_ = v___x_1198_;
v_a_1183_ = v_a_1143_;
goto v___jp_1181_;
}
else
{
uint8_t v___x_1199_; 
v___x_1199_ = 0;
v_a_1182_ = v___x_1199_;
v_a_1183_ = v_a_1143_;
goto v___jp_1181_;
}
v___jp_1145_:
{
uint8_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1148_ = 1;
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_unsigned_to_nat(0u);
v___x_1151_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1152_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1153_ = 0;
v___x_1154_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_1155_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1155_, 0, v___x_1151_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
lean_ctor_set(v___x_1155_, 2, v___x_1150_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3, v___x_1153_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 1, v___y_1147_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 2, v___y_1147_);
v___x_1156_ = lean_box(v___x_1148_);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v___x_1155_);
v___x_1158_ = lean_task_pure(v___x_1157_);
v___x_1159_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v___x_1149_);
lean_ctor_set(v___x_1159_, 2, v___x_1152_);
lean_ctor_set_uint8(v___x_1159_, sizeof(void*)*3, v___y_1147_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v___y_1146_);
return v___x_1160_;
}
v___jp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1164_ = l_Lake_Package_optBuildCacheFacet;
v___x_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___y_1163_);
v___x_1166_ = l_Lake_Package_keyword;
v___x_1167_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
lean_ctor_set(v___x_1167_, 2, v_self_1137_);
lean_ctor_set(v___x_1167_, 3, v___x_1164_);
lean_inc_ref(v_a_1142_);
lean_inc(v_a_1141_);
lean_inc(v_a_1140_);
lean_inc(v_a_1139_);
v___x_1168_ = lean_apply_7(v_a_1138_, v___x_1167_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v___y_1162_, lean_box(0));
return v___x_1168_;
}
v___jp_1169_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1174_ = lean_string_utf8_byte_size(v___y_1170_);
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = lean_nat_dec_eq(v___x_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
v___y_1162_ = v___y_1173_;
v___y_1163_ = v___y_1172_;
goto v___jp_1161_;
}
else
{
lean_dec(v___y_1172_);
lean_dec_ref(v_a_1138_);
lean_dec_ref(v_self_1137_);
v___y_1146_ = v___y_1173_;
v___y_1147_ = v___y_1171_;
goto v___jp_1145_;
}
}
v___jp_1181_:
{
lean_object* v_config_1184_; lean_object* v_keyName_1185_; lean_object* v_dir_1186_; lean_object* v_scope_1187_; lean_object* v_buildDir_1188_; uint8_t v_preferReleaseBuild_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v_config_1184_ = lean_ctor_get(v_self_1137_, 6);
v_keyName_1185_ = lean_ctor_get(v_self_1137_, 2);
v_dir_1186_ = lean_ctor_get(v_self_1137_, 4);
v_scope_1187_ = lean_ctor_get(v_self_1137_, 10);
v_buildDir_1188_ = lean_ctor_get(v_config_1184_, 5);
v_preferReleaseBuild_1189_ = lean_ctor_get_uint8(v_config_1184_, sizeof(void*)*28 + 2);
lean_inc_ref(v_buildDir_1188_);
v___x_1190_ = l_System_FilePath_normalize(v_buildDir_1188_);
lean_inc_ref(v_dir_1186_);
v___x_1191_ = l_Lake_joinRelative(v_dir_1186_, v___x_1190_);
v___x_1192_ = l_System_FilePath_pathExists(v___x_1191_);
lean_dec_ref(v___x_1191_);
if (v_a_1182_ == 0)
{
lean_dec_ref(v_a_1138_);
lean_dec_ref(v_self_1137_);
v___y_1146_ = v_a_1183_;
v___y_1147_ = v_a_1182_;
goto v___jp_1145_;
}
else
{
if (v___x_1192_ == 0)
{
if (v_preferReleaseBuild_1189_ == 0)
{
lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0));
v___x_1194_ = lean_string_dec_eq(v_scope_1187_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1));
v___x_1196_ = lean_string_dec_eq(v_scope_1187_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_dec_ref(v_a_1138_);
lean_dec_ref(v_self_1137_);
v___y_1146_ = v_a_1183_;
v___y_1147_ = v___x_1196_;
goto v___jp_1145_;
}
else
{
lean_inc(v_keyName_1185_);
v___y_1170_ = v_toolchain_1180_;
v___y_1171_ = v_preferReleaseBuild_1189_;
v___y_1172_ = v_keyName_1185_;
v___y_1173_ = v_a_1183_;
goto v___jp_1169_;
}
}
else
{
lean_inc(v_keyName_1185_);
v___y_1170_ = v_toolchain_1180_;
v___y_1171_ = v_preferReleaseBuild_1189_;
v___y_1172_ = v_keyName_1185_;
v___y_1173_ = v_a_1183_;
goto v___jp_1169_;
}
}
else
{
lean_inc(v_keyName_1185_);
v___y_1162_ = v_a_1183_;
v___y_1163_ = v_keyName_1185_;
goto v___jp_1161_;
}
}
else
{
uint8_t v___x_1197_; 
lean_dec_ref(v_a_1138_);
lean_dec_ref(v_self_1137_);
v___x_1197_ = 0;
v___y_1146_ = v_a_1183_;
v___y_1147_ = v___x_1197_;
goto v___jp_1145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___boxed(lean_object* v_self_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec(v_a_1202_);
return v_res_1208_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0(void){
_start:
{
uint8_t v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = 2;
v___x_1210_ = l_Lake_Verbosity_ctorIdx(v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object* v_self_1215_, lean_object* v_facet_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v_toBuildConfig_1220_; uint8_t v_verbosity_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v_toBuildConfig_1220_ = lean_ctor_get(v_a_1217_, 0);
v_verbosity_1221_ = lean_ctor_get_uint8(v_toBuildConfig_1220_, sizeof(void*)*5 + 4);
v___x_1222_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1221_);
v___x_1223_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_1224_ = lean_nat_dec_eq(v___x_1222_, v___x_1223_);
lean_dec(v___x_1222_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_dec(v_facet_1216_);
lean_dec_ref(v_self_1215_);
v___x_1225_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v_a_1218_);
return v___x_1226_;
}
else
{
lean_object* v_baseName_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v_baseName_1227_ = lean_ctor_get(v_self_1215_, 1);
lean_inc(v_baseName_1227_);
lean_dec_ref(v_self_1215_);
v___x_1228_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1229_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1227_, v___x_1224_);
v___x_1230_ = lean_string_append(v___x_1228_, v___x_1229_);
lean_dec_ref(v___x_1229_);
v___x_1231_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1232_ = lean_string_append(v___x_1230_, v___x_1231_);
v___x_1233_ = l_Lake_Name_eraseHead(v_facet_1216_);
v___x_1234_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1233_, v___x_1224_);
v___x_1235_ = lean_string_append(v___x_1232_, v___x_1234_);
lean_dec_ref(v___x_1234_);
v___x_1236_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_1237_ = lean_string_append(v___x_1235_, v___x_1236_);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
lean_ctor_set(v___x_1238_, 1, v_a_1218_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* v_self_1239_, lean_object* v_facet_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(v_self_1239_, v_facet_1240_, v_a_1241_, v_a_1242_);
lean_dec_ref(v_a_1241_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* v_self_1245_, lean_object* v_facet_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_toBuildConfig_1254_; uint8_t v_verbosity_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v_toBuildConfig_1254_ = lean_ctor_get(v_a_1251_, 0);
v_verbosity_1255_ = lean_ctor_get_uint8(v_toBuildConfig_1254_, sizeof(void*)*5 + 4);
v___x_1256_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1255_);
v___x_1257_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_1258_ = lean_nat_dec_eq(v___x_1256_, v___x_1257_);
lean_dec(v___x_1256_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec(v_facet_1246_);
lean_dec_ref(v_self_1245_);
v___x_1259_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v_a_1252_);
return v___x_1260_;
}
else
{
lean_object* v_baseName_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_baseName_1261_ = lean_ctor_get(v_self_1245_, 1);
lean_inc(v_baseName_1261_);
lean_dec_ref(v_self_1245_);
v___x_1262_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1263_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1261_, v___x_1258_);
v___x_1264_ = lean_string_append(v___x_1262_, v___x_1263_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1266_ = lean_string_append(v___x_1264_, v___x_1265_);
v___x_1267_ = l_Lake_Name_eraseHead(v_facet_1246_);
v___x_1268_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1267_, v___x_1258_);
v___x_1269_ = lean_string_append(v___x_1266_, v___x_1268_);
lean_dec_ref(v___x_1268_);
v___x_1270_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_1271_ = lean_string_append(v___x_1269_, v___x_1270_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v_a_1252_);
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* v_self_1273_, lean_object* v_facet_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(v_self_1273_, v_facet_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
return v_res_1282_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_1286_ = l_Lake_Name_eraseHead(v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_1288_ = l_Lake_Name_eraseHead(v___x_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(lean_object* v_self_1289_, uint8_t v_success_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_a_1299_; lean_object* v_a_1300_; lean_object* v_a_1322_; lean_object* v_a_1323_; 
if (v_success_1290_ == 0)
{
lean_object* v_config_1344_; uint8_t v_preferReleaseBuild_1345_; 
v_config_1344_ = lean_ctor_get(v_self_1289_, 6);
v_preferReleaseBuild_1345_ = lean_ctor_get_uint8(v_config_1344_, sizeof(void*)*28 + 2);
if (v_preferReleaseBuild_1345_ == 0)
{
lean_object* v_toBuildConfig_1346_; lean_object* v_baseName_1347_; uint8_t v_verbosity_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v_toBuildConfig_1346_ = lean_ctor_get(v___y_1295_, 0);
v_baseName_1347_ = lean_ctor_get(v_self_1289_, 1);
lean_inc(v_baseName_1347_);
lean_dec_ref(v_self_1289_);
v_verbosity_1348_ = lean_ctor_get_uint8(v_toBuildConfig_1346_, sizeof(void*)*5 + 4);
v___x_1349_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1348_);
v___x_1350_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_1351_ = lean_nat_dec_eq(v___x_1349_, v___x_1350_);
lean_dec(v___x_1349_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
lean_dec(v_baseName_1347_);
v___x_1352_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_1299_ = v___x_1352_;
v_a_1300_ = v___y_1296_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1353_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1354_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1347_, v___x_1351_);
v___x_1355_ = lean_string_append(v___x_1353_, v___x_1354_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1357_ = lean_string_append(v___x_1355_, v___x_1356_);
v___x_1358_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2);
v___x_1359_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1358_, v___x_1351_);
v___x_1360_ = lean_string_append(v___x_1357_, v___x_1359_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_1362_ = lean_string_append(v___x_1360_, v___x_1361_);
v_a_1299_ = v___x_1362_;
v_a_1300_ = v___y_1296_;
goto v___jp_1298_;
}
}
else
{
lean_object* v_toBuildConfig_1363_; lean_object* v_baseName_1364_; uint8_t v_verbosity_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_toBuildConfig_1363_ = lean_ctor_get(v___y_1295_, 0);
v_baseName_1364_ = lean_ctor_get(v_self_1289_, 1);
lean_inc(v_baseName_1364_);
lean_dec_ref(v_self_1289_);
v_verbosity_1365_ = lean_ctor_get_uint8(v_toBuildConfig_1363_, sizeof(void*)*5 + 4);
v___x_1366_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1365_);
v___x_1367_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_1368_ = lean_nat_dec_eq(v___x_1366_, v___x_1367_);
lean_dec(v___x_1366_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
lean_dec(v_baseName_1364_);
v___x_1369_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_1322_ = v___x_1369_;
v_a_1323_ = v___y_1296_;
goto v___jp_1321_;
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1370_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1371_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1364_, v___x_1368_);
v___x_1372_ = lean_string_append(v___x_1370_, v___x_1371_);
lean_dec_ref(v___x_1371_);
v___x_1373_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1374_ = lean_string_append(v___x_1372_, v___x_1373_);
v___x_1375_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
v___x_1376_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1375_, v___x_1368_);
v___x_1377_ = lean_string_append(v___x_1374_, v___x_1376_);
lean_dec_ref(v___x_1376_);
v___x_1378_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_1379_ = lean_string_append(v___x_1377_, v___x_1378_);
v_a_1322_ = v___x_1379_;
v_a_1323_ = v___y_1296_;
goto v___jp_1321_;
}
}
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_dec_ref(v_self_1289_);
v___x_1380_ = lean_box(0);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
lean_ctor_set(v___x_1381_, 1, v___y_1296_);
return v___x_1381_;
}
v___jp_1298_:
{
lean_object* v_log_1301_; uint8_t v_action_1302_; uint8_t v_wantsRebuild_1303_; uint8_t v_canceled_1304_; lean_object* v_trace_1305_; lean_object* v_buildTime_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1320_; 
v_log_1301_ = lean_ctor_get(v_a_1300_, 0);
v_action_1302_ = lean_ctor_get_uint8(v_a_1300_, sizeof(void*)*3);
v_wantsRebuild_1303_ = lean_ctor_get_uint8(v_a_1300_, sizeof(void*)*3 + 1);
v_canceled_1304_ = lean_ctor_get_uint8(v_a_1300_, sizeof(void*)*3 + 2);
v_trace_1305_ = lean_ctor_get(v_a_1300_, 1);
v_buildTime_1306_ = lean_ctor_get(v_a_1300_, 2);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_a_1300_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1308_ = v_a_1300_;
v_isShared_1309_ = v_isSharedCheck_1320_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_buildTime_1306_);
lean_inc(v_trace_1305_);
lean_inc(v_log_1301_);
lean_dec(v_a_1300_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1320_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v___x_1310_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0));
v___x_1311_ = lean_string_append(v___x_1310_, v_a_1299_);
lean_dec_ref(v_a_1299_);
v___x_1312_ = 0;
v___x_1313_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1313_, 0, v___x_1311_);
lean_ctor_set_uint8(v___x_1313_, sizeof(void*)*1, v___x_1312_);
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_array_push(v_log_1301_, v___x_1313_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1315_);
v___x_1317_ = v___x_1308_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_trace_1305_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_buildTime_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*3, v_action_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*3 + 1, v_wantsRebuild_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*3 + 2, v_canceled_1304_);
v___x_1317_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1314_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
return v___x_1318_;
}
}
}
v___jp_1321_:
{
lean_object* v_log_1324_; uint8_t v_action_1325_; uint8_t v_wantsRebuild_1326_; uint8_t v_canceled_1327_; lean_object* v_trace_1328_; lean_object* v_buildTime_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1343_; 
v_log_1324_ = lean_ctor_get(v_a_1323_, 0);
v_action_1325_ = lean_ctor_get_uint8(v_a_1323_, sizeof(void*)*3);
v_wantsRebuild_1326_ = lean_ctor_get_uint8(v_a_1323_, sizeof(void*)*3 + 1);
v_canceled_1327_ = lean_ctor_get_uint8(v_a_1323_, sizeof(void*)*3 + 2);
v_trace_1328_ = lean_ctor_get(v_a_1323_, 1);
v_buildTime_1329_ = lean_ctor_get(v_a_1323_, 2);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_a_1323_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1331_ = v_a_1323_;
v_isShared_1332_ = v_isSharedCheck_1343_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_buildTime_1329_);
lean_inc(v_trace_1328_);
lean_inc(v_log_1324_);
lean_dec(v_a_1323_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1343_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1333_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1));
v___x_1334_ = lean_string_append(v___x_1333_, v_a_1322_);
lean_dec_ref(v_a_1322_);
v___x_1335_ = 2;
v___x_1336_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*1, v___x_1335_);
v___x_1337_ = lean_box(0);
v___x_1338_ = lean_array_push(v_log_1324_, v___x_1336_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1338_);
v___x_1340_ = v___x_1331_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_trace_1328_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_buildTime_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*3, v_action_1325_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*3 + 1, v_wantsRebuild_1326_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*3 + 2, v_canceled_1327_);
v___x_1340_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1337_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
return v___x_1341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* v_self_1382_, lean_object* v_success_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v_success_boxed_1391_; lean_object* v_res_1392_; 
v_success_boxed_1391_ = lean_unbox(v_success_1383_);
v_res_1392_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(v_self_1382_, v_success_boxed_1391_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* v_self_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_){
_start:
{
lean_object* v___f_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_inc_ref(v_self_1393_);
v___f_1401_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(v___f_1401_, 0, v_self_1393_);
v___x_1402_ = l_Lake_instDataKindUnit;
lean_inc_ref(v_a_1394_);
v___x_1403_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1416_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
v_a_1405_ = lean_ctor_get(v___x_1403_, 1);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1407_ = v___x_1403_;
v_isShared_1408_ = v_isSharedCheck_1416_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_inc(v_a_1404_);
lean_dec(v___x_1403_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1416_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; uint8_t v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = 0;
v___x_1411_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_1412_ = l_Lake_Job_mapM___redArg(v___x_1402_, v_a_1404_, v___f_1401_, v___x_1409_, v___x_1410_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v___x_1411_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 0, v___x_1412_);
v___x_1414_ = v___x_1407_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_a_1405_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_dec_ref(v___f_1401_);
lean_dec_ref(v_a_1394_);
v_a_1417_ = lean_ctor_get(v___x_1403_, 0);
v_a_1418_ = lean_ctor_get(v___x_1403_, 1);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1403_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_inc(v_a_1417_);
lean_dec(v___x_1403_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1417_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(lean_object* v_self_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec(v_a_1429_);
lean_dec(v_a_1428_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* v_self_1435_, lean_object* v_as_1436_, size_t v_sz_1437_, size_t v_i_1438_, lean_object* v_b_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
uint8_t v___x_1447_; 
v___x_1447_ = lean_usize_dec_lt(v_i_1438_, v_sz_1437_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; 
lean_dec_ref(v___y_1440_);
lean_dec_ref(v_self_1435_);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v_b_1439_);
lean_ctor_set(v___x_1448_, 1, v___y_1445_);
return v___x_1448_;
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1450_; 
v_a_1449_ = lean_array_uget_borrowed(v_as_1436_, v_i_1438_);
lean_inc_ref(v___y_1440_);
lean_inc(v_a_1449_);
lean_inc_ref(v_self_1435_);
v___x_1450_ = l_Lake_Package_fetchTargetJob(v_self_1435_, v_a_1449_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v_a_1452_; lean_object* v___x_1453_; size_t v___x_1454_; size_t v___x_1455_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
v_a_1452_ = lean_ctor_get(v___x_1450_, 1);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1450_, 2);
v___x_1453_ = l_Lake_Job_mix___redArg(v_b_1439_, v_a_1451_);
v___x_1454_ = ((size_t)1ULL);
v___x_1455_ = lean_usize_add(v_i_1438_, v___x_1454_);
v_i_1438_ = v___x_1455_;
v_b_1439_ = v___x_1453_;
v___y_1445_ = v_a_1452_;
goto _start;
}
else
{
lean_object* v_a_1457_; lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v___y_1440_);
lean_dec_ref(v_b_1439_);
lean_dec_ref(v_self_1435_);
v_a_1457_ = lean_ctor_get(v___x_1450_, 0);
v_a_1458_ = lean_ctor_get(v___x_1450_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1450_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_inc(v_a_1457_);
lean_dec(v___x_1450_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* v_self_1466_, lean_object* v_as_1467_, lean_object* v_sz_1468_, lean_object* v_i_1469_, lean_object* v_b_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
size_t v_sz_boxed_1478_; size_t v_i_boxed_1479_; lean_object* v_res_1480_; 
v_sz_boxed_1478_ = lean_unbox_usize(v_sz_1468_);
lean_dec(v_sz_1468_);
v_i_boxed_1479_ = lean_unbox_usize(v_i_1469_);
lean_dec(v_i_1469_);
v_res_1480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1466_, v_as_1467_, v_sz_boxed_1478_, v_i_boxed_1479_, v_b_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v_as_1467_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object* v_config_1481_, lean_object* v_self_1482_, lean_object* v_____r_1483_, lean_object* v_job_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_extraDepTargets_1492_; size_t v_sz_1493_; size_t v___x_1494_; lean_object* v___x_1495_; 
v_extraDepTargets_1492_ = lean_ctor_get(v_config_1481_, 2);
v_sz_1493_ = lean_array_size(v_extraDepTargets_1492_);
v___x_1494_ = ((size_t)0ULL);
v___x_1495_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1482_, v_extraDepTargets_1492_, v_sz_1493_, v___x_1494_, v_job_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object* v_config_1496_, lean_object* v_self_1497_, lean_object* v_____r_1498_, lean_object* v_job_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(v_config_1496_, v_self_1497_, v_____r_1498_, v_job_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v_config_1496_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(uint8_t v___x_1508_, lean_object* v_self_1509_, lean_object* v_job_1510_, lean_object* v___f_1511_, lean_object* v___x_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
if (v___x_1508_ == 0)
{
lean_object* v___x_1520_; 
lean_inc_ref(v___y_1513_);
v___x_1520_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1509_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v_a_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
v_a_1522_ = lean_ctor_get(v___x_1520_, 1);
lean_inc(v_a_1522_);
lean_dec_ref_known(v___x_1520_, 2);
v___x_1523_ = l_Lake_Job_add___redArg(v_job_1510_, v_a_1521_);
lean_inc_ref(v___y_1517_);
lean_inc(v___y_1516_);
lean_inc(v___y_1515_);
lean_inc(v___y_1514_);
v___x_1524_ = lean_apply_9(v___f_1511_, v___x_1512_, v___x_1523_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v_a_1522_, lean_box(0));
return v___x_1524_;
}
else
{
lean_dec_ref(v___y_1513_);
lean_dec_ref(v___f_1511_);
lean_dec_ref(v_job_1510_);
return v___x_1520_;
}
}
else
{
lean_object* v___x_1525_; 
lean_dec_ref(v_self_1509_);
lean_inc_ref(v___y_1517_);
lean_inc(v___y_1516_);
lean_inc(v___y_1515_);
lean_inc(v___y_1514_);
v___x_1525_ = lean_apply_9(v___f_1511_, v___x_1512_, v_job_1510_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, lean_box(0));
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* v___x_1526_, lean_object* v_self_1527_, lean_object* v_job_1528_, lean_object* v___f_1529_, lean_object* v___x_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_){
_start:
{
uint8_t v___x_4126__boxed_1538_; lean_object* v_res_1539_; 
v___x_4126__boxed_1538_ = lean_unbox(v___x_1526_);
v_res_1539_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(v___x_4126__boxed_1538_, v_self_1527_, v_job_1528_, v___f_1529_, v___x_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
lean_dec_ref(v___y_1535_);
lean_dec(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec(v___y_1532_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object* v_self_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_wsIdx_1550_; lean_object* v_baseName_1551_; lean_object* v_config_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v_job_1573_; uint8_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___y_1576_; lean_object* v___x_1577_; 
v_wsIdx_1550_ = lean_ctor_get(v_self_1542_, 0);
v_baseName_1551_ = lean_ctor_get(v_self_1542_, 1);
v_config_1552_ = lean_ctor_get(v_self_1542_, 6);
lean_inc_ref(v_self_1542_);
lean_inc_ref(v_config_1552_);
v___f_1553_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1553_, 0, v_config_1552_);
lean_closure_set(v___f_1553_, 1, v_self_1542_);
v___x_1554_ = l_Lake_instDataKindUnit;
v___x_1555_ = 1;
lean_inc(v_baseName_1551_);
v___x_1556_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1551_, v___x_1555_);
v___x_1557_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0));
lean_inc_ref(v___x_1556_);
v___x_1558_ = lean_string_append(v___x_1556_, v___x_1557_);
v___x_1559_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1));
v___x_1560_ = lean_string_append(v___x_1559_, v___x_1556_);
lean_dec_ref(v___x_1556_);
v___x_1561_ = lean_string_append(v___x_1560_, v___x_1557_);
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_unsigned_to_nat(0u);
v___x_1565_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1566_ = 0;
v___x_1567_ = 0;
v___x_1568_ = l_Lake_BuildTrace_nil(v___x_1561_);
v___x_1569_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1569_, 0, v___x_1565_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
lean_ctor_set(v___x_1569_, 2, v___x_1564_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*3, v___x_1566_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*3 + 1, v___x_1567_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*3 + 2, v___x_1567_);
v___x_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1562_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = lean_task_pure(v___x_1570_);
v___x_1572_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_job_1573_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_1573_, 0, v___x_1571_);
lean_ctor_set(v_job_1573_, 1, v___x_1563_);
lean_ctor_set(v_job_1573_, 2, v___x_1572_);
lean_ctor_set_uint8(v_job_1573_, sizeof(void*)*3, v___x_1567_);
v___x_1574_ = lean_nat_dec_eq(v_wsIdx_1550_, v___x_1564_);
v___x_1575_ = lean_box(v___x_1574_);
v___y_1576_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 12, 5);
lean_closure_set(v___y_1576_, 0, v___x_1575_);
lean_closure_set(v___y_1576_, 1, v_self_1542_);
lean_closure_set(v___y_1576_, 2, v_job_1573_);
lean_closure_set(v___y_1576_, 3, v___f_1553_);
lean_closure_set(v___y_1576_, 4, v___x_1562_);
v___x_1577_ = l_Lake_ensureJob___redArg(v___x_1554_, v___y_1576_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1602_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_a_1579_ = lean_ctor_get(v___x_1577_, 1);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1581_ = v___x_1577_;
v_isShared_1582_ = v_isSharedCheck_1602_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1602_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v_task_1583_; lean_object* v_kind_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1600_; 
v_task_1583_ = lean_ctor_get(v_a_1578_, 0);
v_kind_1584_ = lean_ctor_get(v_a_1578_, 1);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_a_1578_);
if (v_isSharedCheck_1600_ == 0)
{
lean_object* v_unused_1601_; 
v_unused_1601_ = lean_ctor_get(v_a_1578_, 2);
lean_dec(v_unused_1601_);
v___x_1586_ = v_a_1578_;
v_isShared_1587_ = v_isSharedCheck_1600_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_kind_1584_);
lean_inc(v_task_1583_);
lean_dec(v_a_1578_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1600_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v_registeredJobs_1588_; lean_object* v_job_1590_; 
v_registeredJobs_1588_ = lean_ctor_get(v_a_1547_, 4);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 2, v___x_1558_);
v_job_1590_ = v___x_1586_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_task_1583_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_kind_1584_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v___x_1558_);
v_job_1590_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
lean_ctor_set_uint8(v_job_1590_, sizeof(void*)*3, v___x_1567_);
v___x_1591_ = lean_st_ref_take(v_registeredJobs_1588_);
lean_inc_ref(v_job_1590_);
v___x_1592_ = l_Lake_Job_toOpaque___redArg(v_job_1590_);
v___x_1593_ = lean_array_push(v___x_1591_, v___x_1592_);
v___x_1594_ = lean_st_ref_put(v_registeredJobs_1588_, v___x_1593_);
v___x_1595_ = l_Lake_Job_renew___redArg(v_job_1590_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1595_);
v___x_1597_ = v___x_1581_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_a_1579_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1558_);
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(lean_object* v_self_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(v_self_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec(v_a_1605_);
return v_res_1611_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_box(0);
v___x_1613_ = l_Lean_Json_compress(v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t v_fmt_1614_){
_start:
{
if (v_fmt_1614_ == 0)
{
lean_object* v___x_1615_; 
v___x_1615_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
return v___x_1615_;
}
else
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
return v___x_1616_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_1617_){
_start:
{
uint8_t v_fmt_boxed_1618_; lean_object* v_res_1619_; 
v_fmt_boxed_1618_ = lean_unbox(v_fmt_1617_);
v_res_1619_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_boxed_1618_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(uint8_t v_fmt_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_1620_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object* v_fmt_1623_, lean_object* v_a_1624_){
_start:
{
uint8_t v_fmt_boxed_1625_; lean_object* v_res_1626_; 
v_fmt_boxed_1625_ = lean_unbox(v_fmt_1623_);
v_res_1626_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(v_fmt_boxed_1625_, v_a_1624_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v___y_1627_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
uint8_t v___y_67__boxed_1632_; lean_object* v_res_1633_; 
v___y_67__boxed_1632_ = lean_unbox(v___y_1630_);
v_res_1633_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_67__boxed_1632_, v___y_1631_);
return v_res_1633_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1636_; uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___f_1636_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_1637_ = 1;
v___x_1638_ = l_Lake_instDataKindUnit;
v___x_1639_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__1));
v___x_1640_ = l_Lake_Package_keyword;
v___x_1641_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
lean_ctor_set(v___x_1641_, 1, v___x_1639_);
lean_ctor_set(v___x_1641_, 2, v___x_1638_);
lean_ctor_set(v___x_1641_, 3, v___f_1636_);
lean_ctor_set_uint8(v___x_1641_, sizeof(void*)*4, v___x_1637_);
lean_ctor_set_uint8(v___x_1641_, sizeof(void*)*4 + 1, v___x_1637_);
return v___x_1641_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = lean_obj_once(&l_Lake_Package_extraDepFacetConfig___closed__2, &l_Lake_Package_extraDepFacetConfig___closed__2_once, _init_l_Lake_Package_extraDepFacetConfig___closed__2);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object* v_self_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v_origName_1662_; lean_object* v_dir_1663_; lean_object* v_scope_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v_origName_1662_ = lean_ctor_get(v_self_1658_, 3);
lean_inc(v_origName_1662_);
v_dir_1663_ = lean_ctor_get(v_self_1658_, 4);
lean_inc_ref(v_dir_1663_);
v_scope_1664_ = lean_ctor_get(v_self_1658_, 10);
lean_inc_ref(v_scope_1664_);
lean_dec_ref(v_self_1658_);
v___x_1665_ = lean_string_utf8_byte_size(v_scope_1664_);
v___x_1666_ = lean_unsigned_to_nat(0u);
v___x_1667_ = lean_nat_dec_eq(v___x_1665_, v___x_1666_);
if (v___x_1667_ == 0)
{
lean_object* v_log_1668_; uint8_t v_action_1669_; uint8_t v_wantsRebuild_1670_; uint8_t v_canceled_1671_; lean_object* v_trace_1672_; lean_object* v_buildTime_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_log_1668_ = lean_ctor_get(v_a_1660_, 0);
v_action_1669_ = lean_ctor_get_uint8(v_a_1660_, sizeof(void*)*3);
v_wantsRebuild_1670_ = lean_ctor_get_uint8(v_a_1660_, sizeof(void*)*3 + 1);
v_canceled_1671_ = lean_ctor_get_uint8(v_a_1660_, sizeof(void*)*3 + 2);
v_trace_1672_ = lean_ctor_get(v_a_1660_, 1);
v_buildTime_1673_ = lean_ctor_get(v_a_1660_, 2);
v___x_1674_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
v___x_1675_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1674_, v_dir_1663_);
if (lean_obj_tag(v___x_1675_) == 1)
{
lean_object* v_toContext_1676_; lean_object* v_lakeEnv_1677_; lean_object* v_val_1678_; lean_object* v_toolchain_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v_toContext_1676_ = lean_ctor_get(v_a_1659_, 1);
v_lakeEnv_1677_ = lean_ctor_get(v_toContext_1676_, 0);
v_val_1678_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_val_1678_);
lean_dec_ref_known(v___x_1675_, 1);
v_toolchain_1679_ = lean_ctor_get(v_lakeEnv_1677_, 19);
v___x_1680_ = lean_string_utf8_byte_size(v_toolchain_1679_);
v___x_1681_ = lean_nat_dec_eq(v___x_1680_, v___x_1666_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1682_ = l_Lean_Name_toString(v_origName_1662_, v___x_1667_);
lean_inc_ref(v_lakeEnv_1677_);
v___x_1683_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_1677_, v_scope_1664_, v___x_1682_);
lean_dec_ref(v___x_1682_);
lean_dec_ref(v_scope_1664_);
v___x_1684_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1));
v___x_1685_ = lean_string_append(v___x_1683_, v___x_1684_);
v___x_1686_ = lean_string_append(v___x_1685_, v_val_1678_);
lean_dec(v_val_1678_);
v___x_1687_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2));
v___x_1688_ = lean_string_append(v___x_1686_, v___x_1687_);
v___x_1689_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1690_ = l_Lake_uriEncode(v_toolchain_1679_, v___x_1689_);
v___x_1691_ = lean_string_append(v___x_1688_, v___x_1690_);
lean_dec_ref(v___x_1690_);
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v_a_1660_);
return v___x_1692_;
}
else
{
lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1703_; 
lean_inc(v_buildTime_1673_);
lean_inc_ref(v_trace_1672_);
lean_inc_ref(v_log_1668_);
lean_dec(v_val_1678_);
lean_dec_ref(v_scope_1664_);
lean_dec(v_origName_1662_);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_a_1660_);
if (v_isSharedCheck_1703_ == 0)
{
lean_object* v_unused_1704_; lean_object* v_unused_1705_; lean_object* v_unused_1706_; 
v_unused_1704_ = lean_ctor_get(v_a_1660_, 2);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_a_1660_, 1);
lean_dec(v_unused_1705_);
v_unused_1706_ = lean_ctor_get(v_a_1660_, 0);
lean_dec(v_unused_1706_);
v___x_1694_ = v_a_1660_;
v_isShared_1695_ = v_isSharedCheck_1703_;
goto v_resetjp_1693_;
}
else
{
lean_dec(v_a_1660_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1703_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1696_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4));
v___x_1697_ = lean_array_get_size(v_log_1668_);
v___x_1698_ = lean_array_push(v_log_1668_, v___x_1696_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1698_);
v___x_1700_ = v___x_1694_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_trace_1672_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v_buildTime_1673_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*3, v_action_1669_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*3 + 1, v_wantsRebuild_1670_);
lean_ctor_set_uint8(v_reuseFailAlloc_1702_, sizeof(void*)*3 + 2, v_canceled_1671_);
v___x_1700_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1697_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
return v___x_1701_;
}
}
}
}
else
{
lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1717_; 
lean_inc(v_buildTime_1673_);
lean_inc_ref(v_trace_1672_);
lean_inc_ref(v_log_1668_);
lean_dec(v___x_1675_);
lean_dec_ref(v_scope_1664_);
lean_dec(v_origName_1662_);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_a_1660_);
if (v_isSharedCheck_1717_ == 0)
{
lean_object* v_unused_1718_; lean_object* v_unused_1719_; lean_object* v_unused_1720_; 
v_unused_1718_ = lean_ctor_get(v_a_1660_, 2);
lean_dec(v_unused_1718_);
v_unused_1719_ = lean_ctor_get(v_a_1660_, 1);
lean_dec(v_unused_1719_);
v_unused_1720_ = lean_ctor_get(v_a_1660_, 0);
lean_dec(v_unused_1720_);
v___x_1708_ = v_a_1660_;
v_isShared_1709_ = v_isSharedCheck_1717_;
goto v_resetjp_1707_;
}
else
{
lean_dec(v_a_1660_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1717_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1710_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6));
v___x_1711_ = lean_array_get_size(v_log_1668_);
v___x_1712_ = lean_array_push(v_log_1668_, v___x_1710_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1712_);
v___x_1714_ = v___x_1708_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_trace_1672_);
lean_ctor_set(v_reuseFailAlloc_1716_, 2, v_buildTime_1673_);
lean_ctor_set_uint8(v_reuseFailAlloc_1716_, sizeof(void*)*3, v_action_1669_);
lean_ctor_set_uint8(v_reuseFailAlloc_1716_, sizeof(void*)*3 + 1, v_wantsRebuild_1670_);
lean_ctor_set_uint8(v_reuseFailAlloc_1716_, sizeof(void*)*3 + 2, v_canceled_1671_);
v___x_1714_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1711_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
return v___x_1715_;
}
}
}
}
else
{
lean_object* v_log_1721_; uint8_t v_action_1722_; uint8_t v_wantsRebuild_1723_; uint8_t v_canceled_1724_; lean_object* v_trace_1725_; lean_object* v_buildTime_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1737_; 
lean_dec_ref(v_scope_1664_);
lean_dec_ref(v_dir_1663_);
lean_dec(v_origName_1662_);
v_log_1721_ = lean_ctor_get(v_a_1660_, 0);
v_action_1722_ = lean_ctor_get_uint8(v_a_1660_, sizeof(void*)*3);
v_wantsRebuild_1723_ = lean_ctor_get_uint8(v_a_1660_, sizeof(void*)*3 + 1);
v_canceled_1724_ = lean_ctor_get_uint8(v_a_1660_, sizeof(void*)*3 + 2);
v_trace_1725_ = lean_ctor_get(v_a_1660_, 1);
v_buildTime_1726_ = lean_ctor_get(v_a_1660_, 2);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_a_1660_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1728_ = v_a_1660_;
v_isShared_1729_ = v_isSharedCheck_1737_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_buildTime_1726_);
lean_inc(v_trace_1725_);
lean_inc(v_log_1721_);
lean_dec(v_a_1660_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1737_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1734_; 
v___x_1730_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8));
v___x_1731_ = lean_array_get_size(v_log_1721_);
v___x_1732_ = lean_array_push(v_log_1721_, v___x_1730_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1732_);
v___x_1734_ = v___x_1728_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_trace_1725_);
lean_ctor_set(v_reuseFailAlloc_1736_, 2, v_buildTime_1726_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*3, v_action_1722_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*3 + 1, v_wantsRebuild_1723_);
lean_ctor_set_uint8(v_reuseFailAlloc_1736_, sizeof(void*)*3 + 2, v_canceled_1724_);
v___x_1734_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; 
v___x_1735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1731_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
return v___x_1735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___boxed(lean_object* v_self_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1738_, v_a_1739_, v_a_1740_);
lean_dec_ref(v_a_1739_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object* v_self_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1743_, v_a_1748_, v_a_1749_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object* v_self_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(v_self_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
lean_dec_ref(v_a_1757_);
lean_dec(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object* v_self_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_rev_1774_; lean_object* v_log_1775_; uint8_t v_action_1776_; uint8_t v_wantsRebuild_1777_; uint8_t v_canceled_1778_; lean_object* v_trace_1779_; lean_object* v_buildTime_1780_; lean_object* v_dir_1789_; lean_object* v_config_1790_; lean_object* v_remoteUrl_1791_; lean_object* v_buildArchive_1792_; uint8_t v___y_1794_; uint8_t v___y_1795_; lean_object* v___y_1796_; uint8_t v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v_val_1800_; lean_object* v___y_1820_; lean_object* v_releaseRepo_1842_; 
v_dir_1789_ = lean_ctor_get(v_self_1770_, 4);
lean_inc_ref(v_dir_1789_);
v_config_1790_ = lean_ctor_get(v_self_1770_, 6);
lean_inc_ref(v_config_1790_);
v_remoteUrl_1791_ = lean_ctor_get(v_self_1770_, 11);
lean_inc_ref(v_remoteUrl_1791_);
v_buildArchive_1792_ = lean_ctor_get(v_self_1770_, 21);
lean_inc_ref(v_buildArchive_1792_);
lean_dec_ref(v_self_1770_);
v_releaseRepo_1842_ = lean_ctor_get(v_config_1790_, 10);
lean_inc(v_releaseRepo_1842_);
lean_dec_ref(v_config_1790_);
if (lean_obj_tag(v_releaseRepo_1842_) == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v___x_1843_ = lean_string_utf8_byte_size(v_remoteUrl_1791_);
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = lean_nat_dec_eq(v___x_1843_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v_remoteUrl_1791_);
v___y_1820_ = v___x_1846_;
goto v___jp_1819_;
}
else
{
lean_dec_ref(v_remoteUrl_1791_);
v___y_1820_ = v_releaseRepo_1842_;
goto v___jp_1819_;
}
}
else
{
lean_dec_ref(v_remoteUrl_1791_);
v___y_1820_ = v_releaseRepo_1842_;
goto v___jp_1819_;
}
v___jp_1773_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1781_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0));
v___x_1782_ = lean_string_append(v___x_1781_, v_rev_1774_);
lean_dec_ref(v_rev_1774_);
v___x_1783_ = 3;
v___x_1784_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set_uint8(v___x_1784_, sizeof(void*)*1, v___x_1783_);
v___x_1785_ = lean_array_get_size(v_log_1775_);
v___x_1786_ = lean_array_push(v_log_1775_, v___x_1784_);
v___x_1787_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
lean_ctor_set(v___x_1787_, 1, v_trace_1779_);
lean_ctor_set(v___x_1787_, 2, v_buildTime_1780_);
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*3, v_action_1776_);
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*3 + 1, v_wantsRebuild_1777_);
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*3 + 2, v_canceled_1778_);
v___x_1788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1785_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
return v___x_1788_;
}
v___jp_1793_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
lean_inc_ref(v_dir_1789_);
v___x_1802_ = l_Lake_GitRepo_findTag_x3f(v___x_1801_, v_dir_1789_);
if (lean_obj_tag(v___x_1802_) == 1)
{
lean_object* v_val_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
lean_dec_ref(v_dir_1789_);
v_val_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_val_1803_);
lean_dec_ref_known(v___x_1802_, 1);
v___x_1804_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1804_, 0, v___y_1796_);
lean_ctor_set(v___x_1804_, 1, v___y_1798_);
lean_ctor_set(v___x_1804_, 2, v___y_1799_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3, v___y_1797_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 1, v___y_1794_);
lean_ctor_set_uint8(v___x_1804_, sizeof(void*)*3 + 2, v___y_1795_);
v___x_1805_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1));
v___x_1806_ = lean_string_append(v_val_1800_, v___x_1805_);
v___x_1807_ = lean_string_append(v___x_1806_, v_val_1803_);
lean_dec(v_val_1803_);
v___x_1808_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2));
v___x_1809_ = lean_string_append(v___x_1807_, v___x_1808_);
v___x_1810_ = lean_string_append(v___x_1809_, v_buildArchive_1792_);
lean_dec_ref(v_buildArchive_1792_);
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
lean_ctor_set(v___x_1811_, 1, v___x_1804_);
return v___x_1811_;
}
else
{
lean_object* v___x_1812_; 
lean_dec(v___x_1802_);
lean_dec_ref(v_val_1800_);
lean_dec_ref(v_buildArchive_1792_);
v___x_1812_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1801_, v_dir_1789_);
if (lean_obj_tag(v___x_1812_) == 1)
{
lean_object* v_val_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_val_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_val_1813_);
lean_dec_ref_known(v___x_1812_, 1);
v___x_1814_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3));
v___x_1815_ = lean_string_append(v___x_1814_, v_val_1813_);
lean_dec(v_val_1813_);
v___x_1816_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4));
v___x_1817_ = lean_string_append(v___x_1815_, v___x_1816_);
v_rev_1774_ = v___x_1817_;
v_log_1775_ = v___y_1796_;
v_action_1776_ = v___y_1797_;
v_wantsRebuild_1777_ = v___y_1794_;
v_canceled_1778_ = v___y_1795_;
v_trace_1779_ = v___y_1798_;
v_buildTime_1780_ = v___y_1799_;
goto v___jp_1773_;
}
else
{
lean_object* v___x_1818_; 
lean_dec(v___x_1812_);
v___x_1818_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_rev_1774_ = v___x_1818_;
v_log_1775_ = v___y_1796_;
v_action_1776_ = v___y_1797_;
v_wantsRebuild_1777_ = v___y_1794_;
v_canceled_1778_ = v___y_1795_;
v_trace_1779_ = v___y_1798_;
v_buildTime_1780_ = v___y_1799_;
goto v___jp_1773_;
}
}
}
v___jp_1819_:
{
lean_object* v_log_1821_; uint8_t v_action_1822_; uint8_t v_wantsRebuild_1823_; uint8_t v_canceled_1824_; lean_object* v_trace_1825_; lean_object* v_buildTime_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1841_; 
v_log_1821_ = lean_ctor_get(v_a_1771_, 0);
v_action_1822_ = lean_ctor_get_uint8(v_a_1771_, sizeof(void*)*3);
v_wantsRebuild_1823_ = lean_ctor_get_uint8(v_a_1771_, sizeof(void*)*3 + 1);
v_canceled_1824_ = lean_ctor_get_uint8(v_a_1771_, sizeof(void*)*3 + 2);
v_trace_1825_ = lean_ctor_get(v_a_1771_, 1);
v_buildTime_1826_ = lean_ctor_get(v_a_1771_, 2);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_a_1771_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1828_ = v_a_1771_;
v_isShared_1829_ = v_isSharedCheck_1841_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_buildTime_1826_);
lean_inc(v_trace_1825_);
lean_inc(v_log_1821_);
lean_dec(v_a_1771_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1841_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_dir_1789_);
v___x_1831_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v___x_1830_, v_dir_1789_);
if (lean_obj_tag(v___y_1820_) == 0)
{
if (lean_obj_tag(v___x_1831_) == 1)
{
lean_object* v_val_1832_; 
lean_del_object(v___x_1828_);
v_val_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_val_1832_);
lean_dec_ref_known(v___x_1831_, 1);
v___y_1794_ = v_wantsRebuild_1823_;
v___y_1795_ = v_canceled_1824_;
v___y_1796_ = v_log_1821_;
v___y_1797_ = v_action_1822_;
v___y_1798_ = v_trace_1825_;
v___y_1799_ = v_buildTime_1826_;
v_val_1800_ = v_val_1832_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
lean_dec(v___x_1831_);
lean_dec_ref(v_buildArchive_1792_);
lean_dec_ref(v_dir_1789_);
v___x_1833_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6));
v___x_1834_ = lean_array_get_size(v_log_1821_);
v___x_1835_ = lean_array_push(v_log_1821_, v___x_1833_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1835_);
v___x_1837_ = v___x_1828_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_trace_1825_);
lean_ctor_set(v_reuseFailAlloc_1839_, 2, v_buildTime_1826_);
lean_ctor_set_uint8(v_reuseFailAlloc_1839_, sizeof(void*)*3, v_action_1822_);
lean_ctor_set_uint8(v_reuseFailAlloc_1839_, sizeof(void*)*3 + 1, v_wantsRebuild_1823_);
lean_ctor_set_uint8(v_reuseFailAlloc_1839_, sizeof(void*)*3 + 2, v_canceled_1824_);
v___x_1837_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1834_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
return v___x_1838_;
}
}
}
else
{
lean_object* v_val_1840_; 
lean_dec(v___x_1831_);
lean_del_object(v___x_1828_);
v_val_1840_ = lean_ctor_get(v___y_1820_, 0);
lean_inc(v_val_1840_);
lean_dec_ref_known(v___y_1820_, 1);
v___y_1794_ = v_wantsRebuild_1823_;
v___y_1795_ = v_canceled_1824_;
v___y_1796_ = v_log_1821_;
v___y_1797_ = v_action_1822_;
v___y_1798_ = v_trace_1825_;
v___y_1799_ = v_buildTime_1826_;
v_val_1800_ = v_val_1840_;
goto v___jp_1793_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(lean_object* v_self_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1847_, v_a_1848_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object* v_self_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1851_, v_a_1857_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object* v_self_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(v_self_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec(v_a_1863_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(lean_object* v_val_1869_, lean_object* v_a_x3f_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_log_1873_; uint8_t v_action_1874_; uint8_t v_wantsRebuild_1875_; uint8_t v_canceled_1876_; lean_object* v_trace_1877_; lean_object* v_buildTime_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1890_; 
v_log_1873_ = lean_ctor_get(v___y_1871_, 0);
v_action_1874_ = lean_ctor_get_uint8(v___y_1871_, sizeof(void*)*3);
v_wantsRebuild_1875_ = lean_ctor_get_uint8(v___y_1871_, sizeof(void*)*3 + 1);
v_canceled_1876_ = lean_ctor_get_uint8(v___y_1871_, sizeof(void*)*3 + 2);
v_trace_1877_ = lean_ctor_get(v___y_1871_, 1);
v_buildTime_1878_ = lean_ctor_get(v___y_1871_, 2);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___y_1871_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1880_ = v___y_1871_;
v_isShared_1881_ = v_isSharedCheck_1890_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_buildTime_1878_);
lean_inc(v_trace_1877_);
lean_inc(v_log_1873_);
lean_dec(v___y_1871_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1890_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1882_ = lean_io_mono_ms_now();
v___x_1883_ = lean_nat_sub(v___x_1882_, v_val_1869_);
lean_dec(v___x_1882_);
v___x_1884_ = lean_box(0);
v___x_1885_ = lean_nat_add(v_buildTime_1878_, v___x_1883_);
lean_dec(v___x_1883_);
lean_dec(v_buildTime_1878_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 2, v___x_1885_);
v___x_1887_ = v___x_1880_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_log_1873_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_trace_1877_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v___x_1885_);
lean_ctor_set_uint8(v_reuseFailAlloc_1889_, sizeof(void*)*3, v_action_1874_);
lean_ctor_set_uint8(v_reuseFailAlloc_1889_, sizeof(void*)*3 + 1, v_wantsRebuild_1875_);
lean_ctor_set_uint8(v_reuseFailAlloc_1889_, sizeof(void*)*3 + 2, v_canceled_1876_);
v___x_1887_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; 
v___x_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1884_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
return v___x_1888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0___boxed(lean_object* v_val_1891_, lean_object* v_a_x3f_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v_val_1891_, v_a_x3f_1892_, v___y_1893_);
lean_dec(v_a_x3f_1892_);
lean_dec(v_val_1891_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(lean_object* v_url_1901_, lean_object* v_archiveFile_1902_, lean_object* v_headers_1903_, lean_object* v_depTrace_1904_, lean_object* v_traceFile_1905_, uint8_t v_action_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v_a_1911_; lean_object* v_a_1912_; lean_object* v_log_1915_; uint8_t v_action_1916_; uint8_t v_wantsRebuild_1917_; uint8_t v_canceled_1918_; lean_object* v_trace_1919_; lean_object* v_buildTime_1920_; lean_object* v_toBuildConfig_1926_; lean_object* v_log_1927_; uint8_t v_action_1928_; uint8_t v_wantsRebuild_1929_; uint8_t v_canceled_1930_; lean_object* v_trace_1931_; lean_object* v_buildTime_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_2022_; 
v_toBuildConfig_1926_ = lean_ctor_get(v_a_1907_, 0);
v_log_1927_ = lean_ctor_get(v_a_1908_, 0);
v_action_1928_ = lean_ctor_get_uint8(v_a_1908_, sizeof(void*)*3);
v_wantsRebuild_1929_ = lean_ctor_get_uint8(v_a_1908_, sizeof(void*)*3 + 1);
v_canceled_1930_ = lean_ctor_get_uint8(v_a_1908_, sizeof(void*)*3 + 2);
v_trace_1931_ = lean_ctor_get(v_a_1908_, 1);
v_buildTime_1932_ = lean_ctor_get(v_a_1908_, 2);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_a_1908_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_1934_ = v_a_1908_;
v_isShared_1935_ = v_isSharedCheck_2022_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_buildTime_1932_);
lean_inc(v_trace_1931_);
lean_inc(v_log_1927_);
lean_dec(v_a_1908_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_2022_;
goto v_resetjp_1933_;
}
v___jp_1910_:
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_a_1911_);
lean_ctor_set(v___x_1913_, 1, v_a_1912_);
return v___x_1913_;
}
v___jp_1914_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1921_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1));
v___x_1922_ = lean_array_get_size(v_log_1915_);
v___x_1923_ = lean_array_push(v_log_1915_, v___x_1921_);
v___x_1924_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v_trace_1919_);
lean_ctor_set(v___x_1924_, 2, v_buildTime_1920_);
lean_ctor_set_uint8(v___x_1924_, sizeof(void*)*3, v_action_1916_);
lean_ctor_set_uint8(v___x_1924_, sizeof(void*)*3 + 1, v_wantsRebuild_1917_);
lean_ctor_set_uint8(v___x_1924_, sizeof(void*)*3 + 2, v_canceled_1918_);
v___x_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1922_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
return v___x_1925_;
}
v_resetjp_1933_:
{
uint8_t v_noBuild_1936_; uint8_t v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_noBuild_1936_ = lean_ctor_get_uint8(v_toBuildConfig_1926_, sizeof(void*)*5 + 2);
v___x_1937_ = l_Lake_JobAction_merge(v_action_1928_, v_action_1906_);
v___x_1938_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2));
lean_inc_ref(v_traceFile_1905_);
v___x_1939_ = l_System_FilePath_addExtension(v_traceFile_1905_, v___x_1938_);
if (v_noBuild_1936_ == 0)
{
lean_object* v___x_1940_; lean_object* v_a_1942_; lean_object* v_a_1943_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1940_ = lean_io_mono_ms_now();
v___x_1947_ = lean_array_get_size(v_log_1927_);
v___x_1948_ = l_Lake_download(v_url_1901_, v_archiveFile_1902_, v_headers_1903_, v_log_1927_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v_a_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
v_a_1950_ = lean_ctor_get(v___x_1948_, 1);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___x_1948_, 2);
v___x_1951_ = lean_array_get_size(v_a_1950_);
v___x_1952_ = l_Array_extract___redArg(v_a_1950_, v___x_1947_, v___x_1951_);
v___x_1953_ = lean_box(0);
v___x_1954_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1904_, v___x_1953_, v___x_1952_);
v___x_1955_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1905_, v___x_1954_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1992_; 
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v___x_1955_, 0);
lean_dec(v_unused_1993_);
v___x_1957_ = v___x_1955_;
v_isShared_1958_ = v_isSharedCheck_1992_;
goto v_resetjp_1956_;
}
else
{
lean_dec(v___x_1955_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1992_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lake_removeFileIfExists(v___x_1939_);
lean_dec_ref(v___x_1939_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1982_; 
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v___x_1959_, 0);
lean_dec(v_unused_1983_);
v___x_1961_ = v___x_1959_;
v_isShared_1962_ = v_isSharedCheck_1982_;
goto v_resetjp_1960_;
}
else
{
lean_dec(v___x_1959_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1982_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v_a_1950_);
v___x_1964_ = v___x_1934_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1950_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_trace_1931_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_buildTime_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*3 + 1, v_wantsRebuild_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*3 + 2, v_canceled_1930_);
v___x_1964_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1966_; 
lean_ctor_set_uint8(v___x_1964_, sizeof(void*)*3, v___x_1937_);
lean_inc(v_a_1949_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v_a_1949_);
v___x_1966_ = v___x_1961_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1949_);
v___x_1966_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1968_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set_tag(v___x_1957_, 1);
lean_ctor_set(v___x_1957_, 0, v___x_1966_);
v___x_1968_ = v___x_1957_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
v___x_1969_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1940_, v___x_1968_, v___x_1964_);
lean_dec_ref(v___x_1968_);
lean_dec(v___x_1940_);
v_a_1970_ = lean_ctor_get(v___x_1969_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1977_ == 0)
{
lean_object* v_unused_1978_; 
v_unused_1978_ = lean_ctor_get(v___x_1969_, 0);
lean_dec(v_unused_1978_);
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v_a_1949_);
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1949_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
lean_del_object(v___x_1957_);
lean_dec(v_a_1949_);
v_a_1984_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___x_1959_, 1);
v___x_1985_ = lean_io_error_to_string(v_a_1984_);
v___x_1986_ = 3;
v___x_1987_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1987_, 0, v___x_1985_);
lean_ctor_set_uint8(v___x_1987_, sizeof(void*)*1, v___x_1986_);
v___x_1988_ = lean_array_push(v_a_1950_, v___x_1987_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v___x_1988_);
v___x_1990_ = v___x_1934_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_trace_1931_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_buildTime_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_1991_, sizeof(void*)*3 + 1, v_wantsRebuild_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_1991_, sizeof(void*)*3 + 2, v_canceled_1930_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*3, v___x_1937_);
v_a_1942_ = v___x_1951_;
v_a_1943_ = v___x_1990_;
goto v___jp_1941_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
lean_dec(v_a_1949_);
lean_dec_ref(v___x_1939_);
v_a_1994_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1995_ = lean_io_error_to_string(v_a_1994_);
v___x_1996_ = 3;
v___x_1997_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1997_, 0, v___x_1995_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*1, v___x_1996_);
v___x_1998_ = lean_array_push(v_a_1950_, v___x_1997_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v___x_1998_);
v___x_2000_ = v___x_1934_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_trace_1931_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v_buildTime_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_2001_, sizeof(void*)*3 + 1, v_wantsRebuild_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_2001_, sizeof(void*)*3 + 2, v_canceled_1930_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*3, v___x_1937_);
v_a_1942_ = v___x_1951_;
v_a_1943_ = v___x_2000_;
goto v___jp_1941_;
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v_a_2003_; lean_object* v___x_2005_; 
lean_dec_ref(v___x_1939_);
lean_dec_ref(v_traceFile_1905_);
v_a_2002_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_2002_);
v_a_2003_ = lean_ctor_get(v___x_1948_, 1);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_1948_, 2);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v_a_2003_);
v___x_2005_ = v___x_1934_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2003_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_trace_1931_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_buildTime_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*3 + 1, v_wantsRebuild_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*3 + 2, v_canceled_1930_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*3, v___x_1937_);
v_a_1942_ = v_a_2002_;
v_a_1943_ = v___x_2005_;
goto v___jp_1941_;
}
}
v___jp_1941_:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v_a_1946_; 
v___x_1944_ = lean_box(0);
v___x_1945_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1940_, v___x_1944_, v_a_1943_);
lean_dec(v___x_1940_);
v_a_1946_ = lean_ctor_get(v___x_1945_, 1);
lean_inc(v_a_1946_);
lean_dec_ref(v___x_1945_);
v_a_1911_ = v_a_1942_;
v_a_1912_ = v_a_1946_;
goto v___jp_1910_;
}
}
else
{
uint8_t v___x_2007_; 
lean_dec_ref(v_archiveFile_1902_);
lean_dec_ref(v_url_1901_);
v___x_2007_ = l_System_FilePath_pathExists(v_traceFile_1905_);
lean_dec_ref(v_traceFile_1905_);
if (v___x_2007_ == 0)
{
lean_dec_ref(v___x_1939_);
lean_del_object(v___x_1934_);
v_log_1915_ = v_log_1927_;
v_action_1916_ = v___x_1937_;
v_wantsRebuild_1917_ = v_noBuild_1936_;
v_canceled_1918_ = v_canceled_1930_;
v_trace_1919_ = v_trace_1931_;
v_buildTime_1920_ = v_buildTime_1932_;
goto v___jp_1914_;
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2008_ = lean_box(0);
v___x_2009_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_2010_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1904_, v___x_2008_, v___x_2009_);
v___x_2011_ = l_Lake_BuildMetadata_writeFile(v___x_1939_, v___x_2010_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_dec_ref_known(v___x_2011_, 1);
lean_del_object(v___x_1934_);
v_log_1915_ = v_log_1927_;
v_action_1916_ = v___x_1937_;
v_wantsRebuild_1917_ = v_noBuild_1936_;
v_canceled_1918_ = v_canceled_1930_;
v_trace_1919_ = v_trace_1931_;
v_buildTime_1920_ = v_buildTime_1932_;
goto v___jp_1914_;
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2019_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v___x_2013_ = lean_io_error_to_string(v_a_2012_);
v___x_2014_ = 3;
v___x_2015_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2015_, 0, v___x_2013_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*1, v___x_2014_);
v___x_2016_ = lean_array_get_size(v_log_1927_);
v___x_2017_ = lean_array_push(v_log_1927_, v___x_2015_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v___x_2017_);
v___x_2019_ = v___x_1934_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_trace_1931_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v_buildTime_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_2021_, sizeof(void*)*3 + 2, v_canceled_1930_);
v___x_2019_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
lean_object* v___x_2020_; 
lean_ctor_set_uint8(v___x_2019_, sizeof(void*)*3, v___x_1937_);
lean_ctor_set_uint8(v___x_2019_, sizeof(void*)*3 + 1, v_noBuild_1936_);
v___x_2020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2016_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
return v___x_2020_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___boxed(lean_object* v_url_2023_, lean_object* v_archiveFile_2024_, lean_object* v_headers_2025_, lean_object* v_depTrace_2026_, lean_object* v_traceFile_2027_, lean_object* v_action_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
uint8_t v_action_boxed_2032_; lean_object* v_res_2033_; 
v_action_boxed_2032_ = lean_unbox(v_action_2028_);
v_res_2033_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2023_, v_archiveFile_2024_, v_headers_2025_, v_depTrace_2026_, v_traceFile_2027_, v_action_boxed_2032_, v_a_2029_, v_a_2030_);
lean_dec_ref(v_a_2029_);
lean_dec_ref(v_depTrace_2026_);
lean_dec_ref(v_headers_2025_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(lean_object* v_url_2034_, lean_object* v_archiveFile_2035_, lean_object* v_headers_2036_, lean_object* v_a_2037_, lean_object* v_depTrace_2038_, lean_object* v_traceFile_2039_, uint8_t v_action_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2034_, v_archiveFile_2035_, v_headers_2036_, v_depTrace_2038_, v_traceFile_2039_, v_action_2040_, v_a_2044_, v_a_2045_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___boxed(lean_object* v_url_2048_, lean_object* v_archiveFile_2049_, lean_object* v_headers_2050_, lean_object* v_a_2051_, lean_object* v_depTrace_2052_, lean_object* v_traceFile_2053_, lean_object* v_action_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
uint8_t v_action_boxed_2061_; lean_object* v_res_2062_; 
v_action_boxed_2061_ = lean_unbox(v_action_2054_);
v_res_2062_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(v_url_2048_, v_archiveFile_2049_, v_headers_2050_, v_a_2051_, v_depTrace_2052_, v_traceFile_2053_, v_action_boxed_2061_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
lean_dec_ref(v_a_2058_);
lean_dec(v_a_2057_);
lean_dec(v_a_2056_);
lean_dec(v_a_2055_);
lean_dec_ref(v_depTrace_2052_);
lean_dec_ref(v_a_2051_);
lean_dec_ref(v_headers_2050_);
return v_res_2062_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(lean_object* v_x_2063_, lean_object* v_x_2064_){
_start:
{
if (lean_obj_tag(v_x_2063_) == 0)
{
if (lean_obj_tag(v_x_2064_) == 0)
{
uint8_t v___x_2065_; 
v___x_2065_ = 1;
return v___x_2065_;
}
else
{
uint8_t v___x_2066_; 
v___x_2066_ = 0;
return v___x_2066_;
}
}
else
{
if (lean_obj_tag(v_x_2064_) == 0)
{
uint8_t v___x_2067_; 
v___x_2067_ = 0;
return v___x_2067_;
}
else
{
lean_object* v_val_2068_; lean_object* v_val_2069_; uint64_t v___x_2070_; uint64_t v___x_2071_; uint8_t v___x_2072_; 
v_val_2068_ = lean_ctor_get(v_x_2063_, 0);
v_val_2069_ = lean_ctor_get(v_x_2064_, 0);
v___x_2070_ = lean_unbox_uint64(v_val_2068_);
v___x_2071_ = lean_unbox_uint64(v_val_2069_);
v___x_2072_ = lean_uint64_dec_eq(v___x_2070_, v___x_2071_);
return v___x_2072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2073_, lean_object* v_x_2074_){
_start:
{
uint8_t v_res_2075_; lean_object* v_r_2076_; 
v_res_2075_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v_x_2073_, v_x_2074_);
lean_dec(v_x_2074_);
lean_dec(v_x_2073_);
v_r_2076_ = lean_box(v_res_2075_);
return v_r_2076_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object* v_info_2077_, lean_object* v_self_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = lean_io_metadata(v_info_2077_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v_modified_2082_; uint8_t v___x_2083_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___x_2080_, 1);
v_modified_2082_ = lean_ctor_get(v_a_2081_, 1);
lean_inc_ref(v_modified_2082_);
lean_dec(v_a_2081_);
v___x_2083_ = l_IO_FS_instOrdSystemTime_ord(v_self_2078_, v_modified_2082_);
lean_dec_ref(v_modified_2082_);
if (v___x_2083_ == 0)
{
uint8_t v___x_2084_; 
v___x_2084_ = 1;
return v___x_2084_;
}
else
{
uint8_t v___x_2085_; 
v___x_2085_ = 0;
return v___x_2085_;
}
}
else
{
uint8_t v___x_2086_; 
lean_dec_ref_known(v___x_2080_, 1);
v___x_2086_ = 0;
return v___x_2086_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object* v_info_2087_, lean_object* v_self_2088_, lean_object* v_a_2089_){
_start:
{
uint8_t v_res_2090_; lean_object* v_r_2091_; 
v_res_2090_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2087_, v_self_2088_);
lean_dec_ref(v_self_2088_);
lean_dec_ref(v_info_2087_);
v_r_2091_ = lean_box(v_res_2090_);
return v_r_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(lean_object* v_info_2092_, lean_object* v_depTrace_2093_, lean_object* v_depHash_2094_, lean_object* v_oldTrace_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
uint64_t v_hash_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v_hash_2099_ = lean_ctor_get_uint64(v_depTrace_2093_, sizeof(void*)*3);
v___x_2100_ = lean_box_uint64(v_hash_2099_);
v___x_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
v___x_2102_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v___x_2101_, v_depHash_2094_);
lean_dec_ref_known(v___x_2101_, 1);
if (v___x_2102_ == 0)
{
lean_object* v_toBuildConfig_2103_; uint8_t v_oldMode_2104_; 
v_toBuildConfig_2103_ = lean_ctor_get(v_a_2096_, 0);
v_oldMode_2104_ = lean_ctor_get_uint8(v_toBuildConfig_2103_, sizeof(void*)*5);
if (v_oldMode_2104_ == 0)
{
uint8_t v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = 0;
v___x_2106_ = lean_box(v___x_2105_);
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
lean_ctor_set(v___x_2107_, 1, v_a_2097_);
return v___x_2107_;
}
else
{
uint8_t v___x_2108_; 
v___x_2108_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2092_, v_oldTrace_2095_);
if (v___x_2108_ == 0)
{
uint8_t v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = 0;
v___x_2110_ = lean_box(v___x_2109_);
v___x_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
lean_ctor_set(v___x_2111_, 1, v_a_2097_);
return v___x_2111_;
}
else
{
uint8_t v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = 1;
v___x_2113_ = lean_box(v___x_2112_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v_a_2097_);
return v___x_2114_;
}
}
}
else
{
uint8_t v___x_2115_; 
v___x_2115_ = l_System_FilePath_pathExists(v_info_2092_);
if (v___x_2115_ == 0)
{
uint8_t v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = 0;
v___x_2117_ = lean_box(v___x_2116_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v_a_2097_);
return v___x_2118_;
}
else
{
uint8_t v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2119_ = 2;
v___x_2120_ = lean_box(v___x_2119_);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
lean_ctor_set(v___x_2121_, 1, v_a_2097_);
return v___x_2121_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(lean_object* v_info_2122_, lean_object* v_depTrace_2123_, lean_object* v_depHash_2124_, lean_object* v_oldTrace_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2122_, v_depTrace_2123_, v_depHash_2124_, v_oldTrace_2125_, v_a_2126_, v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec_ref(v_oldTrace_2125_);
lean_dec(v_depHash_2124_);
lean_dec_ref(v_depTrace_2123_);
lean_dec_ref(v_info_2122_);
return v_res_2129_;
}
}
static lean_object* _init_l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0(void){
_start:
{
uint8_t v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = 0;
v___x_2131_ = l_Lake_OutputStatus_ctorIdx(v___x_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(lean_object* v_a_2132_, lean_object* v_info_2133_, lean_object* v_depTrace_2134_, lean_object* v_savedTrace_2135_, lean_object* v_oldTrace_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
if (lean_obj_tag(v_savedTrace_2135_) == 2)
{
lean_object* v_data_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2195_; 
v_data_2143_ = lean_ctor_get(v_savedTrace_2135_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v_savedTrace_2135_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2145_ = v_savedTrace_2135_;
v_isShared_2146_ = v_isSharedCheck_2195_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_data_2143_);
lean_dec(v_savedTrace_2135_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2195_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
uint64_t v_depHash_2147_; lean_object* v_log_2148_; lean_object* v___x_2149_; lean_object* v___x_2151_; 
v_depHash_2147_ = lean_ctor_get_uint64(v_data_2143_, sizeof(void*)*3);
v_log_2148_ = lean_ctor_get(v_data_2143_, 2);
lean_inc_ref(v_log_2148_);
lean_dec_ref(v_data_2143_);
v___x_2149_ = lean_box_uint64(v_depHash_2147_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set_tag(v___x_2145_, 1);
lean_ctor_set(v___x_2145_, 0, v___x_2149_);
v___x_2151_ = v___x_2145_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2152_; lean_object* v_a_2153_; lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2193_; 
v___x_2152_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2133_, v_depTrace_2134_, v___x_2151_, v_oldTrace_2136_, v_a_2140_, v_a_2141_);
lean_dec_ref(v___x_2151_);
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_a_2154_ = lean_ctor_get(v___x_2152_, 1);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2156_ = v___x_2152_;
v_isShared_2157_ = v_isSharedCheck_2193_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2193_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___y_2159_; uint8_t v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v___x_2163_ = lean_unbox(v_a_2153_);
v___x_2164_ = l_Lake_OutputStatus_ctorIdx(v___x_2163_);
v___x_2165_ = lean_obj_once(&l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0, &l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0_once, _init_l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0);
v___x_2166_ = lean_nat_dec_eq(v___x_2164_, v___x_2165_);
lean_dec(v___x_2164_);
if (v___x_2166_ == 0)
{
lean_object* v_log_2167_; uint8_t v_action_2168_; uint8_t v_wantsRebuild_2169_; uint8_t v_canceled_2170_; lean_object* v_trace_2171_; lean_object* v_buildTime_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2192_; 
v_log_2167_ = lean_ctor_get(v_a_2154_, 0);
v_action_2168_ = lean_ctor_get_uint8(v_a_2154_, sizeof(void*)*3);
v_wantsRebuild_2169_ = lean_ctor_get_uint8(v_a_2154_, sizeof(void*)*3 + 1);
v_canceled_2170_ = lean_ctor_get_uint8(v_a_2154_, sizeof(void*)*3 + 2);
v_trace_2171_ = lean_ctor_get(v_a_2154_, 1);
v_buildTime_2172_ = lean_ctor_get(v_a_2154_, 2);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_a_2154_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2174_ = v_a_2154_;
v_isShared_2175_ = v_isSharedCheck_2192_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_buildTime_2172_);
lean_inc(v_trace_2171_);
lean_inc(v_log_2167_);
lean_dec(v_a_2154_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2192_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
uint8_t v___x_2176_; uint8_t v___x_2177_; lean_object* v___x_2179_; 
v___x_2176_ = 2;
v___x_2177_ = l_Lake_JobAction_merge(v_action_2168_, v___x_2176_);
if (v_isShared_2175_ == 0)
{
v___x_2179_ = v___x_2174_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_log_2167_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_trace_2171_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_buildTime_2172_);
lean_ctor_set_uint8(v_reuseFailAlloc_2191_, sizeof(void*)*3 + 1, v_wantsRebuild_2169_);
lean_ctor_set_uint8(v_reuseFailAlloc_2191_, sizeof(void*)*3 + 2, v_canceled_2170_);
v___x_2179_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2180_; 
lean_ctor_set_uint8(v___x_2179_, sizeof(void*)*3, v___x_2177_);
v___x_2180_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_2148_, v_a_2132_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v___x_2179_);
lean_dec_ref(v_log_2148_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 1);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 2);
v___y_2159_ = v_a_2181_;
goto v___jp_2158_;
}
else
{
lean_object* v_a_2182_; lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_del_object(v___x_2156_);
lean_dec(v_a_2153_);
v_a_2182_ = lean_ctor_get(v___x_2180_, 0);
v_a_2183_ = lean_ctor_get(v___x_2180_, 1);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2180_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_inc(v_a_2182_);
lean_dec(v___x_2180_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2182_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_2148_);
v___y_2159_ = v_a_2154_;
goto v___jp_2158_;
}
v___jp_2158_:
{
lean_object* v___x_2161_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 1, v___y_2159_);
v___x_2161_ = v___x_2156_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2153_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___y_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_2196_; uint8_t v_oldMode_2197_; 
lean_dec(v_savedTrace_2135_);
v_toBuildConfig_2196_ = lean_ctor_get(v_a_2140_, 0);
v_oldMode_2197_ = lean_ctor_get_uint8(v_toBuildConfig_2196_, sizeof(void*)*5);
if (v_oldMode_2197_ == 0)
{
uint8_t v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = 0;
v___x_2199_ = lean_box(v___x_2198_);
v___x_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
lean_ctor_set(v___x_2200_, 1, v_a_2141_);
return v___x_2200_;
}
else
{
uint8_t v___x_2201_; 
v___x_2201_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2133_, v_oldTrace_2136_);
if (v___x_2201_ == 0)
{
uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = 0;
v___x_2203_ = lean_box(v___x_2202_);
v___x_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set(v___x_2204_, 1, v_a_2141_);
return v___x_2204_;
}
else
{
uint8_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = 1;
v___x_2206_ = lean_box(v___x_2205_);
v___x_2207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set(v___x_2207_, 1, v_a_2141_);
return v___x_2207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object* v_a_2208_, lean_object* v_info_2209_, lean_object* v_depTrace_2210_, lean_object* v_savedTrace_2211_, lean_object* v_oldTrace_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_2208_, v_info_2209_, v_depTrace_2210_, v_savedTrace_2211_, v_oldTrace_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec(v_a_2213_);
lean_dec_ref(v_oldTrace_2212_);
lean_dec_ref(v_depTrace_2210_);
lean_dec_ref(v_info_2209_);
lean_dec_ref(v_a_2208_);
return v_res_2219_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = lean_unsigned_to_nat(0u);
v___x_2225_ = lean_nat_to_int(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4(void){
_start:
{
uint32_t v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = 0;
v___x_2227_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3);
v___x_2228_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set_uint32(v___x_2228_, sizeof(void*)*1, v___x_2226_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(lean_object* v_self_2229_, lean_object* v_url_2230_, lean_object* v_archiveFile_2231_, lean_object* v_headers_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v___y_2241_; lean_object* v___y_2242_; uint8_t v___y_2243_; lean_object* v___y_2244_; uint8_t v___y_2245_; lean_object* v___y_2246_; uint8_t v___y_2247_; uint8_t v_a_2273_; lean_object* v_a_2274_; lean_object* v_a_2290_; lean_object* v_a_2291_; lean_object* v_log_2293_; uint8_t v_action_2294_; uint8_t v_wantsRebuild_2295_; uint8_t v_canceled_2296_; lean_object* v_trace_2297_; lean_object* v_buildTime_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2338_; 
v_log_2293_ = lean_ctor_get(v_a_2238_, 0);
v_action_2294_ = lean_ctor_get_uint8(v_a_2238_, sizeof(void*)*3);
v_wantsRebuild_2295_ = lean_ctor_get_uint8(v_a_2238_, sizeof(void*)*3 + 1);
v_canceled_2296_ = lean_ctor_get_uint8(v_a_2238_, sizeof(void*)*3 + 2);
v_trace_2297_ = lean_ctor_get(v_a_2238_, 1);
v_buildTime_2298_ = lean_ctor_get(v_a_2238_, 2);
v_isSharedCheck_2338_ = !lean_is_exclusive(v_a_2238_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2300_ = v_a_2238_;
v_isShared_2301_ = v_isSharedCheck_2338_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_buildTime_2298_);
lean_inc(v_trace_2297_);
lean_inc(v_log_2293_);
lean_dec(v_a_2238_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2338_;
goto v_resetjp_2299_;
}
v___jp_2240_:
{
uint8_t v___x_2248_; uint8_t v___x_2249_; uint8_t v___x_2250_; lean_object* v___x_2251_; 
v___x_2248_ = 1;
v___x_2249_ = 3;
v___x_2250_ = l_Lake_JobAction_merge(v___y_2247_, v___x_2249_);
v___x_2251_ = l_Lake_untar(v_archiveFile_2231_, v___y_2241_, v___x_2248_, v___y_2242_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2261_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_a_2253_ = lean_ctor_get(v___x_2251_, 1);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2255_ = v___x_2251_;
v_isShared_2256_ = v_isSharedCheck_2261_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2261_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2257_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2257_, 0, v_a_2253_);
lean_ctor_set(v___x_2257_, 1, v___y_2244_);
lean_ctor_set(v___x_2257_, 2, v___y_2246_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*3, v___x_2250_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*3 + 1, v___y_2245_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*3 + 2, v___y_2243_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 1, v___x_2257_);
v___x_2259_ = v___x_2255_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2252_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2271_; 
v_a_2262_ = lean_ctor_get(v___x_2251_, 0);
v_a_2263_ = lean_ctor_get(v___x_2251_, 1);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2265_ = v___x_2251_;
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_inc(v_a_2262_);
lean_dec(v___x_2251_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2267_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2267_, 0, v_a_2263_);
lean_ctor_set(v___x_2267_, 1, v___y_2244_);
lean_ctor_set(v___x_2267_, 2, v___y_2246_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*3, v___x_2250_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*3 + 1, v___y_2245_);
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*3 + 2, v___y_2243_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 1, v___x_2267_);
v___x_2269_ = v___x_2265_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2262_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
v___jp_2272_:
{
lean_object* v_config_2275_; lean_object* v_dir_2276_; lean_object* v_buildDir_2277_; lean_object* v_log_2278_; uint8_t v_action_2279_; uint8_t v_wantsRebuild_2280_; uint8_t v_canceled_2281_; lean_object* v_trace_2282_; lean_object* v_buildTime_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v_config_2275_ = lean_ctor_get(v_self_2229_, 6);
lean_inc_ref(v_config_2275_);
v_dir_2276_ = lean_ctor_get(v_self_2229_, 4);
lean_inc_ref(v_dir_2276_);
lean_dec_ref(v_self_2229_);
v_buildDir_2277_ = lean_ctor_get(v_config_2275_, 5);
lean_inc_ref(v_buildDir_2277_);
lean_dec_ref(v_config_2275_);
v_log_2278_ = lean_ctor_get(v_a_2274_, 0);
v_action_2279_ = lean_ctor_get_uint8(v_a_2274_, sizeof(void*)*3);
v_wantsRebuild_2280_ = lean_ctor_get_uint8(v_a_2274_, sizeof(void*)*3 + 1);
v_canceled_2281_ = lean_ctor_get_uint8(v_a_2274_, sizeof(void*)*3 + 2);
v_trace_2282_ = lean_ctor_get(v_a_2274_, 1);
v_buildTime_2283_ = lean_ctor_get(v_a_2274_, 2);
v___x_2284_ = l_System_FilePath_normalize(v_buildDir_2277_);
v___x_2285_ = l_Lake_joinRelative(v_dir_2276_, v___x_2284_);
v___x_2286_ = l_System_FilePath_pathExists(v___x_2285_);
if (v_a_2273_ == 0)
{
lean_inc(v_buildTime_2283_);
lean_inc_ref(v_trace_2282_);
lean_inc_ref(v_log_2278_);
lean_dec_ref(v_a_2274_);
v___y_2241_ = v___x_2285_;
v___y_2242_ = v_log_2278_;
v___y_2243_ = v_canceled_2281_;
v___y_2244_ = v_trace_2282_;
v___y_2245_ = v_wantsRebuild_2280_;
v___y_2246_ = v_buildTime_2283_;
v___y_2247_ = v_action_2279_;
goto v___jp_2240_;
}
else
{
if (v___x_2286_ == 0)
{
lean_inc(v_buildTime_2283_);
lean_inc_ref(v_trace_2282_);
lean_inc_ref(v_log_2278_);
lean_dec_ref(v_a_2274_);
v___y_2241_ = v___x_2285_;
v___y_2242_ = v_log_2278_;
v___y_2243_ = v_canceled_2281_;
v___y_2244_ = v_trace_2282_;
v___y_2245_ = v_wantsRebuild_2280_;
v___y_2246_ = v_buildTime_2283_;
v___y_2247_ = v_action_2279_;
goto v___jp_2240_;
}
else
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
lean_dec_ref(v___x_2285_);
lean_dec_ref(v_archiveFile_2231_);
v___x_2287_ = lean_box(0);
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v_a_2274_);
return v___x_2288_;
}
}
}
v___jp_2289_:
{
lean_object* v___x_2292_; 
v___x_2292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2292_, 0, v_a_2290_);
lean_ctor_set(v___x_2292_, 1, v_a_2291_);
return v___x_2292_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; uint64_t v___x_2303_; uint64_t v___x_2304_; uint64_t v_depTrace_2305_; lean_object* v___x_2306_; lean_object* v_traceFile_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; 
v___x_2302_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0));
v___x_2303_ = l_Lake_Hash_nil;
v___x_2304_ = lean_string_hash(v_url_2230_);
v_depTrace_2305_ = lean_uint64_mix_hash(v___x_2303_, v___x_2304_);
v___x_2306_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1));
lean_inc_ref(v_archiveFile_2231_);
v_traceFile_2307_ = l_System_FilePath_addExtension(v_archiveFile_2231_, v___x_2306_);
v___x_2308_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2));
v___x_2309_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
v___x_2310_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2302_);
lean_ctor_set(v___x_2310_, 2, v___x_2309_);
lean_ctor_set_uint64(v___x_2310_, sizeof(void*)*3, v_depTrace_2305_);
v___x_2311_ = 4;
lean_inc_ref(v_traceFile_2307_);
v___x_2312_ = l_Lake_readTraceFile(v_traceFile_2307_, v_log_2293_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v_a_2314_; lean_object* v___x_2316_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
v_a_2314_ = lean_ctor_get(v___x_2312_, 1);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2312_, 2);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v_a_2314_);
v___x_2316_ = v___x_2300_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2314_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_trace_2297_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_buildTime_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*3, v_action_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*3 + 1, v_wantsRebuild_2295_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*3 + 2, v_canceled_2296_);
v___x_2316_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_2233_, v_archiveFile_2231_, v___x_2310_, v_a_2313_, v___x_2309_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v___x_2316_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v_a_2319_; uint8_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
v_a_2319_ = lean_ctor_get(v___x_2317_, 1);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2317_, 2);
v___x_2320_ = lean_unbox(v_a_2318_);
lean_dec(v_a_2318_);
v___x_2321_ = l_Lake_OutputStatus_ctorIdx(v___x_2320_);
v___x_2322_ = lean_obj_once(&l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0, &l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0_once, _init_l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0);
v___x_2323_ = lean_nat_dec_eq(v___x_2321_, v___x_2322_);
lean_dec(v___x_2321_);
if (v___x_2323_ == 0)
{
uint8_t v___x_2324_; 
lean_dec_ref_known(v___x_2310_, 3);
lean_dec_ref(v_traceFile_2307_);
lean_dec_ref(v_url_2230_);
v___x_2324_ = 1;
v_a_2273_ = v___x_2324_;
v_a_2274_ = v_a_2319_;
goto v___jp_2272_;
}
else
{
uint8_t v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = 0;
lean_inc_ref(v_archiveFile_2231_);
v___x_2326_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2230_, v_archiveFile_2231_, v_headers_2232_, v___x_2310_, v_traceFile_2307_, v___x_2311_, v_a_2237_, v_a_2319_);
lean_dec_ref_known(v___x_2310_, 3);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 1);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2326_, 2);
v_a_2273_ = v___x_2325_;
v_a_2274_ = v_a_2327_;
goto v___jp_2272_;
}
else
{
lean_object* v_a_2328_; lean_object* v_a_2329_; 
lean_dec_ref(v_archiveFile_2231_);
lean_dec_ref(v_self_2229_);
v_a_2328_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2328_);
v_a_2329_ = lean_ctor_get(v___x_2326_, 1);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2326_, 2);
v_a_2290_ = v_a_2328_;
v_a_2291_ = v_a_2329_;
goto v___jp_2289_;
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v_a_2331_; 
lean_dec_ref_known(v___x_2310_, 3);
lean_dec_ref(v_traceFile_2307_);
lean_dec_ref(v_archiveFile_2231_);
lean_dec_ref(v_url_2230_);
lean_dec_ref(v_self_2229_);
v_a_2330_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2330_);
v_a_2331_ = lean_ctor_get(v___x_2317_, 1);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2317_, 2);
v_a_2290_ = v_a_2330_;
v_a_2291_ = v_a_2331_;
goto v___jp_2289_;
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v_a_2334_; lean_object* v___x_2336_; 
lean_dec_ref_known(v___x_2310_, 3);
lean_dec_ref(v_traceFile_2307_);
lean_dec_ref(v_archiveFile_2231_);
lean_dec_ref(v_url_2230_);
lean_dec_ref(v_self_2229_);
v_a_2333_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2333_);
v_a_2334_ = lean_ctor_get(v___x_2312_, 1);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2312_, 2);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v_a_2334_);
v___x_2336_ = v___x_2300_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2334_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v_trace_2297_);
lean_ctor_set(v_reuseFailAlloc_2337_, 2, v_buildTime_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2337_, sizeof(void*)*3, v_action_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2337_, sizeof(void*)*3 + 1, v_wantsRebuild_2295_);
lean_ctor_set_uint8(v_reuseFailAlloc_2337_, sizeof(void*)*3 + 2, v_canceled_2296_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
v_a_2290_ = v_a_2333_;
v_a_2291_ = v___x_2336_;
goto v___jp_2289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object* v_self_2339_, lean_object* v_url_2340_, lean_object* v_archiveFile_2341_, lean_object* v_headers_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_self_2339_, v_url_2340_, v_archiveFile_2341_, v_headers_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
lean_dec_ref(v_headers_2342_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object* v_a_2351_, lean_object* v_info_2352_, lean_object* v_depTrace_2353_, lean_object* v_depHash_2354_, lean_object* v_oldTrace_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2352_, v_depTrace_2353_, v_depHash_2354_, v_oldTrace_2355_, v_a_2359_, v_a_2360_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object* v_a_2363_, lean_object* v_info_2364_, lean_object* v_depTrace_2365_, lean_object* v_depHash_2366_, lean_object* v_oldTrace_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_2363_, v_info_2364_, v_depTrace_2365_, v_depHash_2366_, v_oldTrace_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
lean_dec_ref(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec(v_a_2369_);
lean_dec(v_a_2368_);
lean_dec_ref(v_oldTrace_2367_);
lean_dec(v_depHash_2366_);
lean_dec_ref(v_depTrace_2365_);
lean_dec_ref(v_info_2364_);
lean_dec_ref(v_a_2363_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_getUrl_2375_, lean_object* v_pkg_2376_, lean_object* v_archiveFile_2377_, lean_object* v_headers_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
uint8_t v_r_2387_; lean_object* v___y_2388_; lean_object* v_a_2392_; lean_object* v___x_2409_; 
lean_inc_ref(v___y_2383_);
lean_inc(v___y_2382_);
lean_inc(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc_ref(v_pkg_2376_);
v___x_2409_ = lean_apply_8(v_getUrl_2375_, v_pkg_2376_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, lean_box(0));
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v_a_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
v_a_2411_ = lean_ctor_get(v___x_2409_, 1);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2409_, 2);
lean_inc_ref(v_pkg_2376_);
v___x_2412_ = lean_apply_1(v_archiveFile_2377_, v_pkg_2376_);
v___x_2413_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2376_, v_a_2410_, v___x_2412_, v_headers_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v_a_2411_);
lean_dec_ref(v___y_2379_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; uint8_t v___x_2415_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 1);
lean_inc(v_a_2414_);
lean_dec_ref_known(v___x_2413_, 2);
v___x_2415_ = 1;
v_r_2387_ = v___x_2415_;
v___y_2388_ = v_a_2414_;
goto v___jp_2386_;
}
else
{
lean_object* v_a_2416_; 
v_a_2416_ = lean_ctor_get(v___x_2413_, 1);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2413_, 2);
v_a_2392_ = v_a_2416_;
goto v___jp_2391_;
}
}
else
{
lean_object* v_a_2417_; 
lean_dec_ref(v___y_2379_);
lean_dec_ref(v_archiveFile_2377_);
lean_dec_ref(v_pkg_2376_);
v_a_2417_ = lean_ctor_get(v___x_2409_, 1);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2409_, 2);
v_a_2392_ = v_a_2417_;
goto v___jp_2391_;
}
v___jp_2386_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_box(v_r_2387_);
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
lean_ctor_set(v___x_2390_, 1, v___y_2388_);
return v___x_2390_;
}
v___jp_2391_:
{
lean_object* v_log_2393_; uint8_t v_action_2394_; uint8_t v_wantsRebuild_2395_; uint8_t v_canceled_2396_; lean_object* v_trace_2397_; lean_object* v_buildTime_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2408_; 
v_log_2393_ = lean_ctor_get(v_a_2392_, 0);
v_action_2394_ = lean_ctor_get_uint8(v_a_2392_, sizeof(void*)*3);
v_wantsRebuild_2395_ = lean_ctor_get_uint8(v_a_2392_, sizeof(void*)*3 + 1);
v_canceled_2396_ = lean_ctor_get_uint8(v_a_2392_, sizeof(void*)*3 + 2);
v_trace_2397_ = lean_ctor_get(v_a_2392_, 1);
v_buildTime_2398_ = lean_ctor_get(v_a_2392_, 2);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_a_2392_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2400_ = v_a_2392_;
v_isShared_2401_ = v_isSharedCheck_2408_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_buildTime_2398_);
lean_inc(v_trace_2397_);
lean_inc(v_log_2393_);
lean_dec(v_a_2392_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2408_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
uint8_t v___x_2402_; uint8_t v___x_2403_; lean_object* v___x_2405_; 
v___x_2402_ = 4;
v___x_2403_ = l_Lake_JobAction_merge(v_action_2394_, v___x_2402_);
if (v_isShared_2401_ == 0)
{
v___x_2405_ = v___x_2400_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_log_2393_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_trace_2397_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v_buildTime_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2407_, sizeof(void*)*3 + 1, v_wantsRebuild_2395_);
lean_ctor_set_uint8(v_reuseFailAlloc_2407_, sizeof(void*)*3 + 2, v_canceled_2396_);
v___x_2405_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
uint8_t v___x_2406_; 
lean_ctor_set_uint8(v___x_2405_, sizeof(void*)*3, v___x_2403_);
v___x_2406_ = 0;
v_r_2387_ = v___x_2406_;
v___y_2388_ = v___x_2405_;
goto v___jp_2386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_getUrl_2418_, lean_object* v_pkg_2419_, lean_object* v_archiveFile_2420_, lean_object* v_headers_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(v_getUrl_2418_, v_pkg_2419_, v_archiveFile_2420_, v_headers_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v_headers_2421_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* v_getUrl_2430_, lean_object* v_archiveFile_2431_, lean_object* v_headers_2432_, lean_object* v_facet_2433_, lean_object* v___x_2434_, lean_object* v_pkg_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_baseName_2443_; lean_object* v___f_2444_; uint8_t v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v_baseName_2443_ = lean_ctor_get(v_pkg_2435_, 1);
lean_inc(v_baseName_2443_);
v___f_2444_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2444_, 0, v_getUrl_2430_);
lean_closure_set(v___f_2444_, 1, v_pkg_2435_);
lean_closure_set(v___f_2444_, 2, v_archiveFile_2431_);
lean_closure_set(v___f_2444_, 3, v_headers_2432_);
v___x_2445_ = 1;
v___x_2446_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2443_, v___x_2445_);
v___x_2447_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2448_ = lean_string_append(v___x_2446_, v___x_2447_);
v___x_2449_ = l_Lake_Name_eraseHead(v_facet_2433_);
v___x_2450_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2449_, v___x_2445_);
v___x_2451_ = lean_string_append(v___x_2448_, v___x_2450_);
lean_dec_ref(v___x_2450_);
v___x_2452_ = lean_unsigned_to_nat(0u);
v___x_2453_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2434_);
v___x_2454_ = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(v___x_2454_, 0, lean_box(0));
lean_closure_set(v___x_2454_, 1, v___x_2434_);
lean_closure_set(v___x_2454_, 2, v___f_2444_);
lean_closure_set(v___x_2454_, 3, v___x_2452_);
lean_closure_set(v___x_2454_, 4, v___x_2453_);
v___x_2455_ = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM___boxed), 9, 2);
lean_closure_set(v___x_2455_, 0, lean_box(0));
lean_closure_set(v___x_2455_, 1, v___x_2454_);
v___x_2456_ = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM___boxed), 9, 2);
lean_closure_set(v___x_2456_, 0, lean_box(0));
lean_closure_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = l_Lake_ensureJob___redArg(v___x_2434_, v___x_2456_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2482_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_a_2459_ = lean_ctor_get(v___x_2457_, 1);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2461_ = v___x_2457_;
v_isShared_2462_ = v_isSharedCheck_2482_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2482_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v_task_2463_; lean_object* v_kind_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2480_; 
v_task_2463_ = lean_ctor_get(v_a_2458_, 0);
v_kind_2464_ = lean_ctor_get(v_a_2458_, 1);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_a_2458_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; 
v_unused_2481_ = lean_ctor_get(v_a_2458_, 2);
lean_dec(v_unused_2481_);
v___x_2466_ = v_a_2458_;
v_isShared_2467_ = v_isSharedCheck_2480_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_kind_2464_);
lean_inc(v_task_2463_);
lean_dec(v_a_2458_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2480_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v_registeredJobs_2468_; lean_object* v_job_2470_; 
v_registeredJobs_2468_ = lean_ctor_get(v___y_2440_, 4);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 2, v___x_2451_);
v_job_2470_ = v___x_2466_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_task_2463_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_kind_2464_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v___x_2451_);
v_job_2470_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
lean_ctor_set_uint8(v_job_2470_, sizeof(void*)*3, v___x_2445_);
v___x_2471_ = lean_st_ref_take(v_registeredJobs_2468_);
lean_inc_ref(v_job_2470_);
v___x_2472_ = l_Lake_Job_toOpaque___redArg(v_job_2470_);
v___x_2473_ = lean_array_push(v___x_2471_, v___x_2472_);
v___x_2474_ = lean_st_ref_put(v_registeredJobs_2468_, v___x_2473_);
v___x_2475_ = l_Lake_Job_renew___redArg(v_job_2470_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2475_);
v___x_2477_ = v___x_2461_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_a_2459_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2451_);
return v___x_2457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v_getUrl_2483_, lean_object* v_archiveFile_2484_, lean_object* v_headers_2485_, lean_object* v_facet_2486_, lean_object* v___x_2487_, lean_object* v_pkg_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_2483_, v_archiveFile_2484_, v_headers_2485_, v_facet_2486_, v___x_2487_, v_pkg_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec(v___y_2490_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object* v_facet_2504_, lean_object* v_archiveFile_2505_, lean_object* v_getUrl_2506_, lean_object* v_headers_2507_){
_start:
{
lean_object* v___x_2508_; lean_object* v___f_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2508_ = l_Lake_instDataKindBool;
v___f_2509_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2509_, 0, v_getUrl_2506_);
lean_closure_set(v___f_2509_, 1, v_archiveFile_2505_);
lean_closure_set(v___f_2509_, 2, v_headers_2507_);
lean_closure_set(v___f_2509_, 3, v_facet_2504_);
lean_closure_set(v___f_2509_, 4, v___x_2508_);
v___x_2510_ = l_Lake_Package_keyword;
v___x_2511_ = 1;
v___x_2512_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_2513_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2513_, 0, v___x_2510_);
lean_ctor_set(v___x_2513_, 1, v___f_2509_);
lean_ctor_set(v___x_2513_, 2, v___x_2508_);
lean_ctor_set(v___x_2513_, 3, v___x_2512_);
lean_ctor_set_uint8(v___x_2513_, sizeof(void*)*4, v___x_2511_);
lean_ctor_set_uint8(v___x_2513_, sizeof(void*)*4 + 1, v___x_2511_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* v_facet_2514_, lean_object* v_archiveFile_2515_, lean_object* v_getUrl_2516_, lean_object* v_headers_2517_, lean_object* v_inst_2518_){
_start:
{
lean_object* v___x_2519_; lean_object* v___f_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2519_ = l_Lake_instDataKindBool;
v___f_2520_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2520_, 0, v_getUrl_2516_);
lean_closure_set(v___f_2520_, 1, v_archiveFile_2515_);
lean_closure_set(v___f_2520_, 2, v_headers_2517_);
lean_closure_set(v___f_2520_, 3, v_facet_2514_);
lean_closure_set(v___f_2520_, 4, v___x_2519_);
v___x_2521_ = l_Lake_Package_keyword;
v___x_2522_ = 1;
v___x_2523_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_2524_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2524_, 0, v___x_2521_);
lean_ctor_set(v___x_2524_, 1, v___f_2520_);
lean_ctor_set(v___x_2524_, 2, v___x_2519_);
lean_ctor_set(v___x_2524_, 3, v___x_2523_);
lean_ctor_set_uint8(v___x_2524_, sizeof(void*)*4, v___x_2522_);
lean_ctor_set_uint8(v___x_2524_, sizeof(void*)*4 + 1, v___x_2522_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_what_2526_, lean_object* v_baseName_2527_, lean_object* v_optFacet_2528_, uint8_t v_success_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_a_2538_; lean_object* v_a_2539_; 
if (v_success_2529_ == 0)
{
lean_object* v_toBuildConfig_2561_; uint8_t v_verbosity_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v_toBuildConfig_2561_ = lean_ctor_get(v___y_2534_, 0);
v_verbosity_2562_ = lean_ctor_get_uint8(v_toBuildConfig_2561_, sizeof(void*)*5 + 4);
v___x_2563_ = l_Lake_Verbosity_ctorIdx(v_verbosity_2562_);
v___x_2564_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_2565_ = lean_nat_dec_eq(v___x_2563_, v___x_2564_);
lean_dec(v___x_2563_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; 
lean_dec(v_optFacet_2528_);
lean_dec(v_baseName_2527_);
v___x_2566_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_2538_ = v___x_2566_;
v_a_2539_ = v___y_2535_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2567_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2568_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2527_, v___x_2565_);
v___x_2569_ = lean_string_append(v___x_2567_, v___x_2568_);
lean_dec_ref(v___x_2568_);
v___x_2570_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2571_ = lean_string_append(v___x_2569_, v___x_2570_);
v___x_2572_ = l_Lake_Name_eraseHead(v_optFacet_2528_);
v___x_2573_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2572_, v___x_2565_);
v___x_2574_ = lean_string_append(v___x_2571_, v___x_2573_);
lean_dec_ref(v___x_2573_);
v___x_2575_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_2576_ = lean_string_append(v___x_2574_, v___x_2575_);
v_a_2538_ = v___x_2576_;
v_a_2539_ = v___y_2535_;
goto v___jp_2537_;
}
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_dec(v_optFacet_2528_);
lean_dec(v_baseName_2527_);
v___x_2577_ = lean_box(0);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
lean_ctor_set(v___x_2578_, 1, v___y_2535_);
return v___x_2578_;
}
v___jp_2537_:
{
lean_object* v_log_2540_; uint8_t v_action_2541_; uint8_t v_wantsRebuild_2542_; uint8_t v_canceled_2543_; lean_object* v_trace_2544_; lean_object* v_buildTime_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2560_; 
v_log_2540_ = lean_ctor_get(v_a_2539_, 0);
v_action_2541_ = lean_ctor_get_uint8(v_a_2539_, sizeof(void*)*3);
v_wantsRebuild_2542_ = lean_ctor_get_uint8(v_a_2539_, sizeof(void*)*3 + 1);
v_canceled_2543_ = lean_ctor_get_uint8(v_a_2539_, sizeof(void*)*3 + 2);
v_trace_2544_ = lean_ctor_get(v_a_2539_, 1);
v_buildTime_2545_ = lean_ctor_get(v_a_2539_, 2);
v_isSharedCheck_2560_ = !lean_is_exclusive(v_a_2539_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2547_ = v_a_2539_;
v_isShared_2548_ = v_isSharedCheck_2560_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_buildTime_2545_);
lean_inc(v_trace_2544_);
lean_inc(v_log_2540_);
lean_dec(v_a_2539_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2560_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2549_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0));
v___x_2550_ = lean_string_append(v___x_2549_, v_what_2526_);
v___x_2551_ = lean_string_append(v___x_2550_, v_a_2538_);
lean_dec_ref(v_a_2538_);
v___x_2552_ = 3;
v___x_2553_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2553_, 0, v___x_2551_);
lean_ctor_set_uint8(v___x_2553_, sizeof(void*)*1, v___x_2552_);
v___x_2554_ = lean_array_get_size(v_log_2540_);
v___x_2555_ = lean_array_push(v_log_2540_, v___x_2553_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v___x_2555_);
v___x_2557_ = v___x_2547_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_trace_2544_);
lean_ctor_set(v_reuseFailAlloc_2559_, 2, v_buildTime_2545_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*3, v_action_2541_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*3 + 1, v_wantsRebuild_2542_);
lean_ctor_set_uint8(v_reuseFailAlloc_2559_, sizeof(void*)*3 + 2, v_canceled_2543_);
v___x_2557_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2554_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
return v___x_2558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_what_2579_, lean_object* v_baseName_2580_, lean_object* v_optFacet_2581_, lean_object* v_success_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
uint8_t v_success_boxed_2590_; lean_object* v_res_2591_; 
v_success_boxed_2590_ = lean_unbox(v_success_2582_);
v_res_2591_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(v_what_2579_, v_baseName_2580_, v_optFacet_2581_, v_success_boxed_2590_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec_ref(v_what_2579_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object* v___x_2592_, lean_object* v___x_2593_, lean_object* v___f_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v___x_2602_; 
lean_inc_ref(v___y_2595_);
lean_inc_ref(v___y_2599_);
lean_inc(v___y_2598_);
lean_inc(v___y_2597_);
lean_inc(v___y_2596_);
v___x_2602_ = lean_apply_7(v___y_2595_, v___x_2592_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, lean_box(0));
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2615_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_a_2604_ = lean_ctor_get(v___x_2602_, 1);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2606_ = v___x_2602_;
v_isShared_2607_ = v_isSharedCheck_2615_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2615_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2608_; uint8_t v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2608_ = lean_unsigned_to_nat(0u);
v___x_2609_ = 0;
v___x_2610_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2611_ = l_Lake_Job_mapM___redArg(v___x_2593_, v_a_2603_, v___f_2594_, v___x_2608_, v___x_2609_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___x_2610_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v___x_2611_);
v___x_2613_ = v___x_2606_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_a_2604_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec_ref(v___y_2595_);
lean_dec_ref(v___f_2594_);
lean_dec(v___x_2593_);
v_a_2616_ = lean_ctor_get(v___x_2602_, 0);
v_a_2617_ = lean_ctor_get(v___x_2602_, 1);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2602_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_inc(v_a_2616_);
lean_dec(v___x_2602_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2616_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v___x_2625_, lean_object* v___x_2626_, lean_object* v___f_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(v___x_2625_, v___x_2626_, v___f_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec(v___y_2629_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object* v_what_2636_, lean_object* v_optFacet_2637_, lean_object* v_facet_2638_, lean_object* v___x_2639_, lean_object* v_pkg_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_baseName_2648_; lean_object* v_keyName_2649_; lean_object* v___f_2650_; uint8_t v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___f_2661_; uint8_t v___x_2662_; lean_object* v___x_2663_; 
v_baseName_2648_ = lean_ctor_get(v_pkg_2640_, 1);
v_keyName_2649_ = lean_ctor_get(v_pkg_2640_, 2);
lean_inc(v_optFacet_2637_);
lean_inc_n(v_baseName_2648_, 2);
v___f_2650_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2650_, 0, v_what_2636_);
lean_closure_set(v___f_2650_, 1, v_baseName_2648_);
lean_closure_set(v___f_2650_, 2, v_optFacet_2637_);
v___x_2651_ = 1;
v___x_2652_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2648_, v___x_2651_);
v___x_2653_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2654_ = lean_string_append(v___x_2652_, v___x_2653_);
v___x_2655_ = l_Lake_Name_eraseHead(v_facet_2638_);
v___x_2656_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2655_, v___x_2651_);
v___x_2657_ = lean_string_append(v___x_2654_, v___x_2656_);
lean_dec_ref(v___x_2656_);
lean_inc(v_keyName_2649_);
v___x_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2658_, 0, v_keyName_2649_);
v___x_2659_ = l_Lake_Package_keyword;
v___x_2660_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2658_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
lean_ctor_set(v___x_2660_, 2, v_pkg_2640_);
lean_ctor_set(v___x_2660_, 3, v_optFacet_2637_);
lean_inc(v___x_2639_);
v___f_2661_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2661_, 0, v___x_2660_);
lean_closure_set(v___f_2661_, 1, v___x_2639_);
lean_closure_set(v___f_2661_, 2, v___f_2650_);
v___x_2662_ = 0;
v___x_2663_ = l_Lake_ensureJob___redArg(v___x_2639_, v___f_2661_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2688_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
v_a_2665_ = lean_ctor_get(v___x_2663_, 1);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2667_ = v___x_2663_;
v_isShared_2668_ = v_isSharedCheck_2688_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_inc(v_a_2664_);
lean_dec(v___x_2663_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2688_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v_task_2669_; lean_object* v_kind_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2686_; 
v_task_2669_ = lean_ctor_get(v_a_2664_, 0);
v_kind_2670_ = lean_ctor_get(v_a_2664_, 1);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_a_2664_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; 
v_unused_2687_ = lean_ctor_get(v_a_2664_, 2);
lean_dec(v_unused_2687_);
v___x_2672_ = v_a_2664_;
v_isShared_2673_ = v_isSharedCheck_2686_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_kind_2670_);
lean_inc(v_task_2669_);
lean_dec(v_a_2664_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2686_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v_registeredJobs_2674_; lean_object* v_job_2676_; 
v_registeredJobs_2674_ = lean_ctor_get(v___y_2645_, 4);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 2, v___x_2657_);
v_job_2676_ = v___x_2672_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_task_2669_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_kind_2670_);
lean_ctor_set(v_reuseFailAlloc_2685_, 2, v___x_2657_);
v_job_2676_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
lean_ctor_set_uint8(v_job_2676_, sizeof(void*)*3, v___x_2662_);
v___x_2677_ = lean_st_ref_take(v_registeredJobs_2674_);
lean_inc_ref(v_job_2676_);
v___x_2678_ = l_Lake_Job_toOpaque___redArg(v_job_2676_);
v___x_2679_ = lean_array_push(v___x_2677_, v___x_2678_);
v___x_2680_ = lean_st_ref_put(v_registeredJobs_2674_, v___x_2679_);
v___x_2681_ = l_Lake_Job_renew___redArg(v_job_2676_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2681_);
v___x_2683_ = v___x_2667_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_a_2665_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2657_);
return v___x_2663_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object* v_what_2689_, lean_object* v_optFacet_2690_, lean_object* v_facet_2691_, lean_object* v___x_2692_, lean_object* v_pkg_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(v_what_2689_, v_optFacet_2690_, v_facet_2691_, v___x_2692_, v_pkg_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec(v___y_2695_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object* v_facet_2709_, lean_object* v_optFacet_2710_, lean_object* v_what_2711_){
_start:
{
lean_object* v___x_2712_; lean_object* v___f_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2712_ = l_Lake_instDataKindUnit;
v___f_2713_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2713_, 0, v_what_2711_);
lean_closure_set(v___f_2713_, 1, v_optFacet_2710_);
lean_closure_set(v___f_2713_, 2, v_facet_2709_);
lean_closure_set(v___f_2713_, 3, v___x_2712_);
v___x_2714_ = l_Lake_Package_keyword;
v___x_2715_ = 1;
v___x_2716_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2717_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2717_, 0, v___x_2714_);
lean_ctor_set(v___x_2717_, 1, v___f_2713_);
lean_ctor_set(v___x_2717_, 2, v___x_2712_);
lean_ctor_set(v___x_2717_, 3, v___x_2716_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*4, v___x_2715_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*4 + 1, v___x_2715_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* v_facet_2718_, lean_object* v_optFacet_2719_, lean_object* v_what_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_){
_start:
{
lean_object* v___x_2723_; lean_object* v___f_2724_; lean_object* v___x_2725_; uint8_t v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2723_ = l_Lake_instDataKindUnit;
v___f_2724_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2724_, 0, v_what_2720_);
lean_closure_set(v___f_2724_, 1, v_optFacet_2719_);
lean_closure_set(v___f_2724_, 2, v_facet_2718_);
lean_closure_set(v___f_2724_, 3, v___x_2723_);
v___x_2725_ = l_Lake_Package_keyword;
v___x_2726_ = 1;
v___x_2727_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2728_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2728_, 0, v___x_2725_);
lean_ctor_set(v___x_2728_, 1, v___f_2724_);
lean_ctor_set(v___x_2728_, 2, v___x_2723_);
lean_ctor_set(v___x_2728_, 3, v___x_2727_);
lean_ctor_set_uint8(v___x_2728_, sizeof(void*)*4, v___x_2726_);
lean_ctor_set_uint8(v___x_2728_, sizeof(void*)*4 + 1, v___x_2726_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* v_baseName_2730_, lean_object* v___x_2731_, uint8_t v_success_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_a_2741_; lean_object* v_a_2742_; 
if (v_success_2732_ == 0)
{
lean_object* v_toBuildConfig_2763_; uint8_t v_verbosity_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v_toBuildConfig_2763_ = lean_ctor_get(v___y_2737_, 0);
v_verbosity_2764_ = lean_ctor_get_uint8(v_toBuildConfig_2763_, sizeof(void*)*5 + 4);
v___x_2765_ = l_Lake_Verbosity_ctorIdx(v_verbosity_2764_);
v___x_2766_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_2767_ = lean_nat_dec_eq(v___x_2765_, v___x_2766_);
lean_dec(v___x_2765_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; 
lean_dec(v___x_2731_);
lean_dec(v_baseName_2730_);
v___x_2768_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_2741_ = v___x_2768_;
v_a_2742_ = v___y_2738_;
goto v___jp_2740_;
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2769_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2770_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2730_, v___x_2767_);
v___x_2771_ = lean_string_append(v___x_2769_, v___x_2770_);
lean_dec_ref(v___x_2770_);
v___x_2772_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2773_ = lean_string_append(v___x_2771_, v___x_2772_);
v___x_2774_ = l_Lake_Name_eraseHead(v___x_2731_);
v___x_2775_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2774_, v___x_2767_);
v___x_2776_ = lean_string_append(v___x_2773_, v___x_2775_);
lean_dec_ref(v___x_2775_);
v___x_2777_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_2778_ = lean_string_append(v___x_2776_, v___x_2777_);
v_a_2741_ = v___x_2778_;
v_a_2742_ = v___y_2738_;
goto v___jp_2740_;
}
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
lean_dec(v___x_2731_);
lean_dec(v_baseName_2730_);
v___x_2779_ = lean_box(0);
v___x_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2779_);
lean_ctor_set(v___x_2780_, 1, v___y_2738_);
return v___x_2780_;
}
v___jp_2740_:
{
lean_object* v_log_2743_; uint8_t v_action_2744_; uint8_t v_wantsRebuild_2745_; uint8_t v_canceled_2746_; lean_object* v_trace_2747_; lean_object* v_buildTime_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2762_; 
v_log_2743_ = lean_ctor_get(v_a_2742_, 0);
v_action_2744_ = lean_ctor_get_uint8(v_a_2742_, sizeof(void*)*3);
v_wantsRebuild_2745_ = lean_ctor_get_uint8(v_a_2742_, sizeof(void*)*3 + 1);
v_canceled_2746_ = lean_ctor_get_uint8(v_a_2742_, sizeof(void*)*3 + 2);
v_trace_2747_ = lean_ctor_get(v_a_2742_, 1);
v_buildTime_2748_ = lean_ctor_get(v_a_2742_, 2);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_a_2742_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2750_ = v_a_2742_;
v_isShared_2751_ = v_isSharedCheck_2762_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_buildTime_2748_);
lean_inc(v_trace_2747_);
lean_inc(v_log_2743_);
lean_dec(v_a_2742_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2762_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2752_ = ((lean_object*)(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0));
v___x_2753_ = lean_string_append(v___x_2752_, v_a_2741_);
lean_dec_ref(v_a_2741_);
v___x_2754_ = 3;
v___x_2755_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set_uint8(v___x_2755_, sizeof(void*)*1, v___x_2754_);
v___x_2756_ = lean_array_get_size(v_log_2743_);
v___x_2757_ = lean_array_push(v_log_2743_, v___x_2755_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2757_);
v___x_2759_ = v___x_2750_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2757_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_trace_2747_);
lean_ctor_set(v_reuseFailAlloc_2761_, 2, v_buildTime_2748_);
lean_ctor_set_uint8(v_reuseFailAlloc_2761_, sizeof(void*)*3, v_action_2744_);
lean_ctor_set_uint8(v_reuseFailAlloc_2761_, sizeof(void*)*3 + 1, v_wantsRebuild_2745_);
lean_ctor_set_uint8(v_reuseFailAlloc_2761_, sizeof(void*)*3 + 2, v_canceled_2746_);
v___x_2759_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2756_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
return v___x_2760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object* v_baseName_2781_, lean_object* v___x_2782_, lean_object* v_success_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
uint8_t v_success_boxed_2791_; lean_object* v_res_2792_; 
v_success_boxed_2791_ = lean_unbox(v_success_2783_);
v_res_2792_ = l_Lake_Package_buildCacheFacetConfig___lam__1(v_baseName_2781_, v___x_2782_, v_success_boxed_2791_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
return v_res_2792_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* v___x_2793_, lean_object* v___x_2794_, lean_object* v___x_2795_, lean_object* v_pkg_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v_baseName_2804_; lean_object* v_keyName_2805_; lean_object* v___f_2806_; uint8_t v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___f_2817_; uint8_t v___x_2818_; lean_object* v___x_2819_; 
v_baseName_2804_ = lean_ctor_get(v_pkg_2796_, 1);
v_keyName_2805_ = lean_ctor_get(v_pkg_2796_, 2);
lean_inc(v___x_2793_);
lean_inc_n(v_baseName_2804_, 2);
v___f_2806_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2806_, 0, v_baseName_2804_);
lean_closure_set(v___f_2806_, 1, v___x_2793_);
v___x_2807_ = 1;
v___x_2808_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2804_, v___x_2807_);
v___x_2809_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2810_ = lean_string_append(v___x_2808_, v___x_2809_);
v___x_2811_ = l_Lake_Name_eraseHead(v___x_2794_);
v___x_2812_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2811_, v___x_2807_);
v___x_2813_ = lean_string_append(v___x_2810_, v___x_2812_);
lean_dec_ref(v___x_2812_);
lean_inc(v_keyName_2805_);
v___x_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2814_, 0, v_keyName_2805_);
v___x_2815_ = l_Lake_Package_keyword;
v___x_2816_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2814_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
lean_ctor_set(v___x_2816_, 2, v_pkg_2796_);
lean_ctor_set(v___x_2816_, 3, v___x_2793_);
lean_inc(v___x_2795_);
v___f_2817_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2817_, 0, v___x_2816_);
lean_closure_set(v___f_2817_, 1, v___x_2795_);
lean_closure_set(v___f_2817_, 2, v___f_2806_);
v___x_2818_ = 0;
v___x_2819_ = l_Lake_ensureJob___redArg(v___x_2795_, v___f_2817_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2844_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
v_a_2821_ = lean_ctor_get(v___x_2819_, 1);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2823_ = v___x_2819_;
v_isShared_2824_ = v_isSharedCheck_2844_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_inc(v_a_2820_);
lean_dec(v___x_2819_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2844_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v_task_2825_; lean_object* v_kind_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2842_; 
v_task_2825_ = lean_ctor_get(v_a_2820_, 0);
v_kind_2826_ = lean_ctor_get(v_a_2820_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_a_2820_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; 
v_unused_2843_ = lean_ctor_get(v_a_2820_, 2);
lean_dec(v_unused_2843_);
v___x_2828_ = v_a_2820_;
v_isShared_2829_ = v_isSharedCheck_2842_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_kind_2826_);
lean_inc(v_task_2825_);
lean_dec(v_a_2820_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2842_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v_registeredJobs_2830_; lean_object* v_job_2832_; 
v_registeredJobs_2830_ = lean_ctor_get(v___y_2801_, 4);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 2, v___x_2813_);
v_job_2832_ = v___x_2828_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_task_2825_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_kind_2826_);
lean_ctor_set(v_reuseFailAlloc_2841_, 2, v___x_2813_);
v_job_2832_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2839_; 
lean_ctor_set_uint8(v_job_2832_, sizeof(void*)*3, v___x_2818_);
v___x_2833_ = lean_st_ref_take(v_registeredJobs_2830_);
lean_inc_ref(v_job_2832_);
v___x_2834_ = l_Lake_Job_toOpaque___redArg(v_job_2832_);
v___x_2835_ = lean_array_push(v___x_2833_, v___x_2834_);
v___x_2836_ = lean_st_ref_put(v_registeredJobs_2830_, v___x_2835_);
v___x_2837_ = l_Lake_Job_renew___redArg(v_job_2832_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2837_);
v___x_2839_ = v___x_2823_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_a_2821_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2813_);
return v___x_2819_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object* v___x_2845_, lean_object* v___x_2846_, lean_object* v___x_2847_, lean_object* v_pkg_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lake_Package_buildCacheFacetConfig___lam__2(v___x_2845_, v___x_2846_, v___x_2847_, v_pkg_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec(v___y_2850_);
return v_res_2856_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___f_2860_; 
v___x_2857_ = l_Lake_instDataKindUnit;
v___x_2858_ = l_Lake_Package_buildCacheFacet;
v___x_2859_ = l_Lake_Package_optBuildCacheFacet;
v___f_2860_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2860_, 0, v___x_2859_);
lean_closure_set(v___f_2860_, 1, v___x_2858_);
lean_closure_set(v___f_2860_, 2, v___x_2857_);
return v___f_2860_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2861_; uint8_t v___x_2862_; lean_object* v___x_2863_; lean_object* v___f_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___f_2861_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2862_ = 1;
v___x_2863_ = l_Lake_instDataKindUnit;
v___f_2864_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__0, &l_Lake_Package_buildCacheFacetConfig___closed__0_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__0);
v___x_2865_ = l_Lake_Package_keyword;
v___x_2866_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set(v___x_2866_, 1, v___f_2864_);
lean_ctor_set(v___x_2866_, 2, v___x_2863_);
lean_ctor_set(v___x_2866_, 3, v___f_2861_);
lean_ctor_set_uint8(v___x_2866_, sizeof(void*)*4, v___x_2862_);
lean_ctor_set_uint8(v___x_2866_, sizeof(void*)*4 + 1, v___x_2862_);
return v___x_2866_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig(void){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__1, &l_Lake_Package_buildCacheFacetConfig___closed__1_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__1);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* v_pkg_2869_, lean_object* v_dir_2870_, lean_object* v___x_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
uint8_t v_r_2880_; lean_object* v___y_2881_; lean_object* v_a_2885_; lean_object* v___x_2902_; 
lean_inc_ref(v_pkg_2869_);
v___x_2902_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_pkg_2869_, v___y_2876_, v___y_2877_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
v_a_2904_ = lean_ctor_get(v___x_2902_, 1);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2902_, 2);
v___x_2905_ = l_Lake_defaultLakeDir;
v___x_2906_ = l_Lake_joinRelative(v_dir_2870_, v___x_2905_);
v___x_2907_ = ((lean_object*)(l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0));
v___x_2908_ = l_Lake_joinRelative(v___x_2906_, v___x_2907_);
v___x_2909_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2869_, v_a_2903_, v___x_2908_, v___x_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v_a_2904_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; uint8_t v___x_2911_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 1);
lean_inc(v_a_2910_);
lean_dec_ref_known(v___x_2909_, 2);
v___x_2911_ = 1;
v_r_2880_ = v___x_2911_;
v___y_2881_ = v_a_2910_;
goto v___jp_2879_;
}
else
{
lean_object* v_a_2912_; 
v_a_2912_ = lean_ctor_get(v___x_2909_, 1);
lean_inc(v_a_2912_);
lean_dec_ref_known(v___x_2909_, 2);
v_a_2885_ = v_a_2912_;
goto v___jp_2884_;
}
}
else
{
lean_object* v_a_2913_; 
lean_dec_ref(v_dir_2870_);
lean_dec_ref(v_pkg_2869_);
v_a_2913_ = lean_ctor_get(v___x_2902_, 1);
lean_inc(v_a_2913_);
lean_dec_ref_known(v___x_2902_, 2);
v_a_2885_ = v_a_2913_;
goto v___jp_2884_;
}
v___jp_2879_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2882_ = lean_box(v_r_2880_);
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
lean_ctor_set(v___x_2883_, 1, v___y_2881_);
return v___x_2883_;
}
v___jp_2884_:
{
lean_object* v_log_2886_; uint8_t v_action_2887_; uint8_t v_wantsRebuild_2888_; uint8_t v_canceled_2889_; lean_object* v_trace_2890_; lean_object* v_buildTime_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2901_; 
v_log_2886_ = lean_ctor_get(v_a_2885_, 0);
v_action_2887_ = lean_ctor_get_uint8(v_a_2885_, sizeof(void*)*3);
v_wantsRebuild_2888_ = lean_ctor_get_uint8(v_a_2885_, sizeof(void*)*3 + 1);
v_canceled_2889_ = lean_ctor_get_uint8(v_a_2885_, sizeof(void*)*3 + 2);
v_trace_2890_ = lean_ctor_get(v_a_2885_, 1);
v_buildTime_2891_ = lean_ctor_get(v_a_2885_, 2);
v_isSharedCheck_2901_ = !lean_is_exclusive(v_a_2885_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2893_ = v_a_2885_;
v_isShared_2894_ = v_isSharedCheck_2901_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_buildTime_2891_);
lean_inc(v_trace_2890_);
lean_inc(v_log_2886_);
lean_dec(v_a_2885_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2901_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
uint8_t v___x_2895_; uint8_t v___x_2896_; lean_object* v___x_2898_; 
v___x_2895_ = 4;
v___x_2896_ = l_Lake_JobAction_merge(v_action_2887_, v___x_2895_);
if (v_isShared_2894_ == 0)
{
v___x_2898_ = v___x_2893_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_log_2886_);
lean_ctor_set(v_reuseFailAlloc_2900_, 1, v_trace_2890_);
lean_ctor_set(v_reuseFailAlloc_2900_, 2, v_buildTime_2891_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*3 + 1, v_wantsRebuild_2888_);
lean_ctor_set_uint8(v_reuseFailAlloc_2900_, sizeof(void*)*3 + 2, v_canceled_2889_);
v___x_2898_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
uint8_t v___x_2899_; 
lean_ctor_set_uint8(v___x_2898_, sizeof(void*)*3, v___x_2896_);
v___x_2899_ = 0;
v_r_2880_ = v___x_2899_;
v___y_2881_ = v___x_2898_;
goto v___jp_2879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* v_pkg_2914_, lean_object* v_dir_2915_, lean_object* v___x_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l_Lake_Package_optBarrelFacetConfig___lam__0(v_pkg_2914_, v_dir_2915_, v___x_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec_ref(v___x_2916_);
return v_res_2924_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* v___x_2925_, lean_object* v___f_2926_, lean_object* v___x_2927_, lean_object* v___x_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = l_Lake_Job_async___redArg(v___x_2925_, v___f_2926_, v___x_2927_, v___x_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
v___x_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
lean_ctor_set(v___x_2937_, 1, v___y_2934_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object* v___x_2938_, lean_object* v___f_2939_, lean_object* v___x_2940_, lean_object* v___x_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lake_Package_optBarrelFacetConfig___lam__1(v___x_2938_, v___f_2939_, v___x_2940_, v___x_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec(v___y_2944_);
lean_dec(v___y_2943_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* v___x_2950_, lean_object* v___x_2951_, lean_object* v___x_2952_, lean_object* v_pkg_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v_baseName_2961_; lean_object* v_dir_2962_; lean_object* v___f_2963_; uint8_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___f_2973_; lean_object* v___x_2974_; 
v_baseName_2961_ = lean_ctor_get(v_pkg_2953_, 1);
lean_inc(v_baseName_2961_);
v_dir_2962_ = lean_ctor_get(v_pkg_2953_, 4);
lean_inc_ref(v_dir_2962_);
v___f_2963_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2963_, 0, v_pkg_2953_);
lean_closure_set(v___f_2963_, 1, v_dir_2962_);
lean_closure_set(v___f_2963_, 2, v___x_2950_);
v___x_2964_ = 1;
v___x_2965_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2961_, v___x_2964_);
v___x_2966_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2967_ = lean_string_append(v___x_2965_, v___x_2966_);
v___x_2968_ = l_Lake_Name_eraseHead(v___x_2951_);
v___x_2969_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2968_, v___x_2964_);
v___x_2970_ = lean_string_append(v___x_2967_, v___x_2969_);
lean_dec_ref(v___x_2969_);
v___x_2971_ = lean_unsigned_to_nat(0u);
v___x_2972_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2952_);
v___f_2973_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2973_, 0, v___x_2952_);
lean_closure_set(v___f_2973_, 1, v___f_2963_);
lean_closure_set(v___f_2973_, 2, v___x_2971_);
lean_closure_set(v___f_2973_, 3, v___x_2972_);
v___x_2974_ = l_Lake_ensureJob___redArg(v___x_2952_, v___f_2973_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2999_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
v_a_2976_ = lean_ctor_get(v___x_2974_, 1);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2978_ = v___x_2974_;
v_isShared_2979_ = v_isSharedCheck_2999_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_inc(v_a_2975_);
lean_dec(v___x_2974_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2999_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v_task_2980_; lean_object* v_kind_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2997_; 
v_task_2980_ = lean_ctor_get(v_a_2975_, 0);
v_kind_2981_ = lean_ctor_get(v_a_2975_, 1);
v_isSharedCheck_2997_ = !lean_is_exclusive(v_a_2975_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; 
v_unused_2998_ = lean_ctor_get(v_a_2975_, 2);
lean_dec(v_unused_2998_);
v___x_2983_ = v_a_2975_;
v_isShared_2984_ = v_isSharedCheck_2997_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_kind_2981_);
lean_inc(v_task_2980_);
lean_dec(v_a_2975_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2997_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v_registeredJobs_2985_; lean_object* v_job_2987_; 
v_registeredJobs_2985_ = lean_ctor_get(v___y_2958_, 4);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 2, v___x_2970_);
v_job_2987_ = v___x_2983_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_task_2980_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v_kind_2981_);
lean_ctor_set(v_reuseFailAlloc_2996_, 2, v___x_2970_);
v_job_2987_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
lean_ctor_set_uint8(v_job_2987_, sizeof(void*)*3, v___x_2964_);
v___x_2988_ = lean_st_ref_take(v_registeredJobs_2985_);
lean_inc_ref(v_job_2987_);
v___x_2989_ = l_Lake_Job_toOpaque___redArg(v_job_2987_);
v___x_2990_ = lean_array_push(v___x_2988_, v___x_2989_);
v___x_2991_ = lean_st_ref_put(v_registeredJobs_2985_, v___x_2990_);
v___x_2992_ = l_Lake_Job_renew___redArg(v_job_2987_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_2992_);
v___x_2994_ = v___x_2978_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_a_2976_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2970_);
return v___x_2974_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object* v___x_3000_, lean_object* v___x_3001_, lean_object* v___x_3002_, lean_object* v_pkg_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_Lake_Package_optBarrelFacetConfig___lam__2(v___x_3000_, v___x_3001_, v___x_3002_, v_pkg_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3005_);
return v_res_3011_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___f_3015_; 
v___x_3012_ = l_Lake_instDataKindBool;
v___x_3013_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3014_ = l_Lake_Reservoir_lakeHeaders;
v___f_3015_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3015_, 0, v___x_3014_);
lean_closure_set(v___f_3015_, 1, v___x_3013_);
lean_closure_set(v___f_3015_, 2, v___x_3012_);
return v___f_3015_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___f_3016_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_3017_ = 1;
v___x_3018_ = l_Lake_instDataKindBool;
v___f_3019_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__0, &l_Lake_Package_optBarrelFacetConfig___closed__0_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__0);
v___x_3020_ = l_Lake_Package_keyword;
v___x_3021_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
lean_ctor_set(v___x_3021_, 1, v___f_3019_);
lean_ctor_set(v___x_3021_, 2, v___x_3018_);
lean_ctor_set(v___x_3021_, 3, v___f_3016_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*4, v___x_3017_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*4 + 1, v___x_3017_);
return v___x_3021_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig(void){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__1, &l_Lake_Package_optBarrelFacetConfig___closed__1_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__1);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* v_baseName_3024_, lean_object* v___x_3025_, uint8_t v_success_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_a_3035_; lean_object* v_a_3036_; 
if (v_success_3026_ == 0)
{
lean_object* v_toBuildConfig_3057_; uint8_t v_verbosity_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; uint8_t v___x_3061_; 
v_toBuildConfig_3057_ = lean_ctor_get(v___y_3031_, 0);
v_verbosity_3058_ = lean_ctor_get_uint8(v_toBuildConfig_3057_, sizeof(void*)*5 + 4);
v___x_3059_ = l_Lake_Verbosity_ctorIdx(v_verbosity_3058_);
v___x_3060_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_3061_ = lean_nat_dec_eq(v___x_3059_, v___x_3060_);
lean_dec(v___x_3059_);
if (v___x_3061_ == 0)
{
lean_object* v___x_3062_; 
lean_dec(v___x_3025_);
lean_dec(v_baseName_3024_);
v___x_3062_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_3035_ = v___x_3062_;
v_a_3036_ = v___y_3032_;
goto v___jp_3034_;
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3063_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3064_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3024_, v___x_3061_);
v___x_3065_ = lean_string_append(v___x_3063_, v___x_3064_);
lean_dec_ref(v___x_3064_);
v___x_3066_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3067_ = lean_string_append(v___x_3065_, v___x_3066_);
v___x_3068_ = l_Lake_Name_eraseHead(v___x_3025_);
v___x_3069_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3068_, v___x_3061_);
v___x_3070_ = lean_string_append(v___x_3067_, v___x_3069_);
lean_dec_ref(v___x_3069_);
v___x_3071_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_3072_ = lean_string_append(v___x_3070_, v___x_3071_);
v_a_3035_ = v___x_3072_;
v_a_3036_ = v___y_3032_;
goto v___jp_3034_;
}
}
else
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_dec(v___x_3025_);
lean_dec(v_baseName_3024_);
v___x_3073_ = lean_box(0);
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
lean_ctor_set(v___x_3074_, 1, v___y_3032_);
return v___x_3074_;
}
v___jp_3034_:
{
lean_object* v_log_3037_; uint8_t v_action_3038_; uint8_t v_wantsRebuild_3039_; uint8_t v_canceled_3040_; lean_object* v_trace_3041_; lean_object* v_buildTime_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3056_; 
v_log_3037_ = lean_ctor_get(v_a_3036_, 0);
v_action_3038_ = lean_ctor_get_uint8(v_a_3036_, sizeof(void*)*3);
v_wantsRebuild_3039_ = lean_ctor_get_uint8(v_a_3036_, sizeof(void*)*3 + 1);
v_canceled_3040_ = lean_ctor_get_uint8(v_a_3036_, sizeof(void*)*3 + 2);
v_trace_3041_ = lean_ctor_get(v_a_3036_, 1);
v_buildTime_3042_ = lean_ctor_get(v_a_3036_, 2);
v_isSharedCheck_3056_ = !lean_is_exclusive(v_a_3036_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3044_ = v_a_3036_;
v_isShared_3045_ = v_isSharedCheck_3056_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_buildTime_3042_);
lean_inc(v_trace_3041_);
lean_inc(v_log_3037_);
lean_dec(v_a_3036_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3056_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3053_; 
v___x_3046_ = ((lean_object*)(l_Lake_Package_barrelFacetConfig___lam__1___closed__0));
v___x_3047_ = lean_string_append(v___x_3046_, v_a_3035_);
lean_dec_ref(v_a_3035_);
v___x_3048_ = 3;
v___x_3049_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3049_, 0, v___x_3047_);
lean_ctor_set_uint8(v___x_3049_, sizeof(void*)*1, v___x_3048_);
v___x_3050_ = lean_array_get_size(v_log_3037_);
v___x_3051_ = lean_array_push(v_log_3037_, v___x_3049_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v___x_3051_);
v___x_3053_ = v___x_3044_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3051_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_trace_3041_);
lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_buildTime_3042_);
lean_ctor_set_uint8(v_reuseFailAlloc_3055_, sizeof(void*)*3, v_action_3038_);
lean_ctor_set_uint8(v_reuseFailAlloc_3055_, sizeof(void*)*3 + 1, v_wantsRebuild_3039_);
lean_ctor_set_uint8(v_reuseFailAlloc_3055_, sizeof(void*)*3 + 2, v_canceled_3040_);
v___x_3053_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3054_; 
v___x_3054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3050_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
return v___x_3054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object* v_baseName_3075_, lean_object* v___x_3076_, lean_object* v_success_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
uint8_t v_success_boxed_3085_; lean_object* v_res_3086_; 
v_success_boxed_3085_ = lean_unbox(v_success_3077_);
v_res_3086_ = l_Lake_Package_barrelFacetConfig___lam__1(v_baseName_3075_, v___x_3076_, v_success_boxed_3085_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* v___x_3087_, lean_object* v___x_3088_, lean_object* v___x_3089_, lean_object* v_pkg_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v_baseName_3098_; lean_object* v_keyName_3099_; lean_object* v___f_3100_; uint8_t v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___f_3111_; uint8_t v___x_3112_; lean_object* v___x_3113_; 
v_baseName_3098_ = lean_ctor_get(v_pkg_3090_, 1);
v_keyName_3099_ = lean_ctor_get(v_pkg_3090_, 2);
lean_inc(v___x_3087_);
lean_inc_n(v_baseName_3098_, 2);
v___f_3100_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3100_, 0, v_baseName_3098_);
lean_closure_set(v___f_3100_, 1, v___x_3087_);
v___x_3101_ = 1;
v___x_3102_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3098_, v___x_3101_);
v___x_3103_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3104_ = lean_string_append(v___x_3102_, v___x_3103_);
v___x_3105_ = l_Lake_Name_eraseHead(v___x_3088_);
v___x_3106_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3105_, v___x_3101_);
v___x_3107_ = lean_string_append(v___x_3104_, v___x_3106_);
lean_dec_ref(v___x_3106_);
lean_inc(v_keyName_3099_);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v_keyName_3099_);
v___x_3109_ = l_Lake_Package_keyword;
v___x_3110_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3108_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
lean_ctor_set(v___x_3110_, 2, v_pkg_3090_);
lean_ctor_set(v___x_3110_, 3, v___x_3087_);
lean_inc(v___x_3089_);
v___f_3111_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3111_, 0, v___x_3110_);
lean_closure_set(v___f_3111_, 1, v___x_3089_);
lean_closure_set(v___f_3111_, 2, v___f_3100_);
v___x_3112_ = 0;
v___x_3113_ = l_Lake_ensureJob___redArg(v___x_3089_, v___f_3111_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3138_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
v_a_3115_ = lean_ctor_get(v___x_3113_, 1);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3117_ = v___x_3113_;
v_isShared_3118_ = v_isSharedCheck_3138_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_inc(v_a_3114_);
lean_dec(v___x_3113_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3138_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v_task_3119_; lean_object* v_kind_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3136_; 
v_task_3119_ = lean_ctor_get(v_a_3114_, 0);
v_kind_3120_ = lean_ctor_get(v_a_3114_, 1);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_a_3114_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v_a_3114_, 2);
lean_dec(v_unused_3137_);
v___x_3122_ = v_a_3114_;
v_isShared_3123_ = v_isSharedCheck_3136_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_kind_3120_);
lean_inc(v_task_3119_);
lean_dec(v_a_3114_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3136_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v_registeredJobs_3124_; lean_object* v_job_3126_; 
v_registeredJobs_3124_ = lean_ctor_get(v___y_3095_, 4);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 2, v___x_3107_);
v_job_3126_ = v___x_3122_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_task_3119_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v_kind_3120_);
lean_ctor_set(v_reuseFailAlloc_3135_, 2, v___x_3107_);
v_job_3126_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3133_; 
lean_ctor_set_uint8(v_job_3126_, sizeof(void*)*3, v___x_3112_);
v___x_3127_ = lean_st_ref_take(v_registeredJobs_3124_);
lean_inc_ref(v_job_3126_);
v___x_3128_ = l_Lake_Job_toOpaque___redArg(v_job_3126_);
v___x_3129_ = lean_array_push(v___x_3127_, v___x_3128_);
v___x_3130_ = lean_st_ref_put(v_registeredJobs_3124_, v___x_3129_);
v___x_3131_ = l_Lake_Job_renew___redArg(v_job_3126_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 0, v___x_3131_);
v___x_3133_ = v___x_3117_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v_a_3115_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3107_);
return v___x_3113_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object* v___x_3139_, lean_object* v___x_3140_, lean_object* v___x_3141_, lean_object* v_pkg_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lake_Package_barrelFacetConfig___lam__2(v___x_3139_, v___x_3140_, v___x_3141_, v_pkg_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec(v___y_3144_);
return v_res_3150_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___f_3154_; 
v___x_3151_ = l_Lake_instDataKindUnit;
v___x_3152_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3153_ = l_Lake_Package_optReservoirBarrelFacet;
v___f_3154_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3154_, 0, v___x_3153_);
lean_closure_set(v___f_3154_, 1, v___x_3152_);
lean_closure_set(v___f_3154_, 2, v___x_3151_);
return v___f_3154_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3155_; uint8_t v___x_3156_; lean_object* v___x_3157_; lean_object* v___f_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___f_3155_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3156_ = 1;
v___x_3157_ = l_Lake_instDataKindUnit;
v___f_3158_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__0, &l_Lake_Package_barrelFacetConfig___closed__0_once, _init_l_Lake_Package_barrelFacetConfig___closed__0);
v___x_3159_ = l_Lake_Package_keyword;
v___x_3160_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
lean_ctor_set(v___x_3160_, 1, v___f_3158_);
lean_ctor_set(v___x_3160_, 2, v___x_3157_);
lean_ctor_set(v___x_3160_, 3, v___f_3155_);
lean_ctor_set_uint8(v___x_3160_, sizeof(void*)*4, v___x_3156_);
lean_ctor_set_uint8(v___x_3160_, sizeof(void*)*4 + 1, v___x_3156_);
return v___x_3160_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig(void){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__1, &l_Lake_Package_barrelFacetConfig___closed__1_once, _init_l_Lake_Package_barrelFacetConfig___closed__1);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object* v_pkg_3162_, lean_object* v_dir_3163_, lean_object* v_buildArchive_3164_, lean_object* v___x_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
uint8_t v_r_3174_; lean_object* v___y_3175_; lean_object* v_a_3179_; lean_object* v___x_3196_; 
lean_inc_ref(v_pkg_3162_);
v___x_3196_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_pkg_3162_, v___y_3171_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v_a_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
v_a_3198_ = lean_ctor_get(v___x_3196_, 1);
lean_inc(v_a_3198_);
lean_dec_ref_known(v___x_3196_, 2);
v___x_3199_ = l_Lake_defaultLakeDir;
v___x_3200_ = l_Lake_joinRelative(v_dir_3163_, v___x_3199_);
v___x_3201_ = l_Lake_joinRelative(v___x_3200_, v_buildArchive_3164_);
v___x_3202_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_3162_, v_a_3197_, v___x_3201_, v___x_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v_a_3198_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; uint8_t v___x_3204_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 1);
lean_inc(v_a_3203_);
lean_dec_ref_known(v___x_3202_, 2);
v___x_3204_ = 1;
v_r_3174_ = v___x_3204_;
v___y_3175_ = v_a_3203_;
goto v___jp_3173_;
}
else
{
lean_object* v_a_3205_; 
v_a_3205_ = lean_ctor_get(v___x_3202_, 1);
lean_inc(v_a_3205_);
lean_dec_ref_known(v___x_3202_, 2);
v_a_3179_ = v_a_3205_;
goto v___jp_3178_;
}
}
else
{
lean_object* v_a_3206_; 
lean_dec_ref(v_buildArchive_3164_);
lean_dec_ref(v_dir_3163_);
lean_dec_ref(v_pkg_3162_);
v_a_3206_ = lean_ctor_get(v___x_3196_, 1);
lean_inc(v_a_3206_);
lean_dec_ref_known(v___x_3196_, 2);
v_a_3179_ = v_a_3206_;
goto v___jp_3178_;
}
v___jp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = lean_box(v_r_3174_);
v___x_3177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
lean_ctor_set(v___x_3177_, 1, v___y_3175_);
return v___x_3177_;
}
v___jp_3178_:
{
lean_object* v_log_3180_; uint8_t v_action_3181_; uint8_t v_wantsRebuild_3182_; uint8_t v_canceled_3183_; lean_object* v_trace_3184_; lean_object* v_buildTime_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3195_; 
v_log_3180_ = lean_ctor_get(v_a_3179_, 0);
v_action_3181_ = lean_ctor_get_uint8(v_a_3179_, sizeof(void*)*3);
v_wantsRebuild_3182_ = lean_ctor_get_uint8(v_a_3179_, sizeof(void*)*3 + 1);
v_canceled_3183_ = lean_ctor_get_uint8(v_a_3179_, sizeof(void*)*3 + 2);
v_trace_3184_ = lean_ctor_get(v_a_3179_, 1);
v_buildTime_3185_ = lean_ctor_get(v_a_3179_, 2);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_a_3179_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3187_ = v_a_3179_;
v_isShared_3188_ = v_isSharedCheck_3195_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_buildTime_3185_);
lean_inc(v_trace_3184_);
lean_inc(v_log_3180_);
lean_dec(v_a_3179_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3195_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
uint8_t v___x_3189_; uint8_t v___x_3190_; lean_object* v___x_3192_; 
v___x_3189_ = 4;
v___x_3190_ = l_Lake_JobAction_merge(v_action_3181_, v___x_3189_);
if (v_isShared_3188_ == 0)
{
v___x_3192_ = v___x_3187_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_log_3180_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_trace_3184_);
lean_ctor_set(v_reuseFailAlloc_3194_, 2, v_buildTime_3185_);
lean_ctor_set_uint8(v_reuseFailAlloc_3194_, sizeof(void*)*3 + 1, v_wantsRebuild_3182_);
lean_ctor_set_uint8(v_reuseFailAlloc_3194_, sizeof(void*)*3 + 2, v_canceled_3183_);
v___x_3192_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
uint8_t v___x_3193_; 
lean_ctor_set_uint8(v___x_3192_, sizeof(void*)*3, v___x_3190_);
v___x_3193_ = 0;
v_r_3174_ = v___x_3193_;
v___y_3175_ = v___x_3192_;
goto v___jp_3173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object* v_pkg_3207_, lean_object* v_dir_3208_, lean_object* v_buildArchive_3209_, lean_object* v___x_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(v_pkg_3207_, v_dir_3208_, v_buildArchive_3209_, v___x_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_);
lean_dec_ref(v___y_3215_);
lean_dec(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec_ref(v___x_3210_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object* v___x_3219_, lean_object* v___x_3220_, lean_object* v___x_3221_, lean_object* v___x_3222_, lean_object* v_pkg_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v_baseName_3231_; lean_object* v_dir_3232_; lean_object* v_buildArchive_3233_; lean_object* v___f_3234_; uint8_t v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___f_3243_; lean_object* v___x_3244_; 
v_baseName_3231_ = lean_ctor_get(v_pkg_3223_, 1);
lean_inc(v_baseName_3231_);
v_dir_3232_ = lean_ctor_get(v_pkg_3223_, 4);
lean_inc_ref(v_dir_3232_);
v_buildArchive_3233_ = lean_ctor_get(v_pkg_3223_, 21);
lean_inc_ref(v_buildArchive_3233_);
v___f_3234_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3234_, 0, v_pkg_3223_);
lean_closure_set(v___f_3234_, 1, v_dir_3232_);
lean_closure_set(v___f_3234_, 2, v_buildArchive_3233_);
lean_closure_set(v___f_3234_, 3, v___x_3219_);
v___x_3235_ = 1;
v___x_3236_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3231_, v___x_3235_);
v___x_3237_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3238_ = lean_string_append(v___x_3236_, v___x_3237_);
v___x_3239_ = l_Lake_Name_eraseHead(v___x_3220_);
v___x_3240_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3239_, v___x_3235_);
v___x_3241_ = lean_string_append(v___x_3238_, v___x_3240_);
lean_dec_ref(v___x_3240_);
v___x_3242_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_3221_);
v___f_3243_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_3243_, 0, v___x_3221_);
lean_closure_set(v___f_3243_, 1, v___f_3234_);
lean_closure_set(v___f_3243_, 2, v___x_3222_);
lean_closure_set(v___f_3243_, 3, v___x_3242_);
v___x_3244_ = l_Lake_ensureJob___redArg(v___x_3221_, v___f_3243_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3269_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
v_a_3246_ = lean_ctor_get(v___x_3244_, 1);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3248_ = v___x_3244_;
v_isShared_3249_ = v_isSharedCheck_3269_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_inc(v_a_3245_);
lean_dec(v___x_3244_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3269_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v_task_3250_; lean_object* v_kind_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3267_; 
v_task_3250_ = lean_ctor_get(v_a_3245_, 0);
v_kind_3251_ = lean_ctor_get(v_a_3245_, 1);
v_isSharedCheck_3267_ = !lean_is_exclusive(v_a_3245_);
if (v_isSharedCheck_3267_ == 0)
{
lean_object* v_unused_3268_; 
v_unused_3268_ = lean_ctor_get(v_a_3245_, 2);
lean_dec(v_unused_3268_);
v___x_3253_ = v_a_3245_;
v_isShared_3254_ = v_isSharedCheck_3267_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_kind_3251_);
lean_inc(v_task_3250_);
lean_dec(v_a_3245_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3267_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v_registeredJobs_3255_; lean_object* v_job_3257_; 
v_registeredJobs_3255_ = lean_ctor_get(v___y_3228_, 4);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 2, v___x_3241_);
v_job_3257_ = v___x_3253_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_task_3250_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_kind_3251_);
lean_ctor_set(v_reuseFailAlloc_3266_, 2, v___x_3241_);
v_job_3257_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3264_; 
lean_ctor_set_uint8(v_job_3257_, sizeof(void*)*3, v___x_3235_);
v___x_3258_ = lean_st_ref_take(v_registeredJobs_3255_);
lean_inc_ref(v_job_3257_);
v___x_3259_ = l_Lake_Job_toOpaque___redArg(v_job_3257_);
v___x_3260_ = lean_array_push(v___x_3258_, v___x_3259_);
v___x_3261_ = lean_st_ref_put(v_registeredJobs_3255_, v___x_3260_);
v___x_3262_ = l_Lake_Job_renew___redArg(v_job_3257_);
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 0, v___x_3262_);
v___x_3264_ = v___x_3248_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3262_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_a_3246_);
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
}
else
{
lean_dec_ref(v___x_3241_);
return v___x_3244_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_3270_, lean_object* v___x_3271_, lean_object* v___x_3272_, lean_object* v___x_3273_, lean_object* v_pkg_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(v___x_3270_, v___x_3271_, v___x_3272_, v___x_3273_, v_pkg_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec(v___y_3276_);
return v_res_3282_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___f_3289_; 
v___x_3285_ = lean_unsigned_to_nat(0u);
v___x_3286_ = l_Lake_instDataKindBool;
v___x_3287_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3288_ = ((lean_object*)(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0));
v___f_3289_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed), 12, 4);
lean_closure_set(v___f_3289_, 0, v___x_3288_);
lean_closure_set(v___f_3289_, 1, v___x_3287_);
lean_closure_set(v___f_3289_, 2, v___x_3286_);
lean_closure_set(v___f_3289_, 3, v___x_3285_);
return v___f_3289_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3290_; uint8_t v___x_3291_; lean_object* v___x_3292_; lean_object* v___f_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___f_3290_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_3291_ = 1;
v___x_3292_ = l_Lake_instDataKindBool;
v___f_3293_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__1, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1);
v___x_3294_ = l_Lake_Package_keyword;
v___x_3295_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
lean_ctor_set(v___x_3295_, 1, v___f_3293_);
lean_ctor_set(v___x_3295_, 2, v___x_3292_);
lean_ctor_set(v___x_3295_, 3, v___f_3290_);
lean_ctor_set_uint8(v___x_3295_, sizeof(void*)*4, v___x_3291_);
lean_ctor_set_uint8(v___x_3295_, sizeof(void*)*4 + 1, v___x_3291_);
return v___x_3295_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__2, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* v_baseName_3298_, lean_object* v___x_3299_, uint8_t v_success_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v_a_3309_; lean_object* v_a_3310_; 
if (v_success_3300_ == 0)
{
lean_object* v_toBuildConfig_3331_; uint8_t v_verbosity_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; uint8_t v___x_3335_; 
v_toBuildConfig_3331_ = lean_ctor_get(v___y_3305_, 0);
v_verbosity_3332_ = lean_ctor_get_uint8(v_toBuildConfig_3331_, sizeof(void*)*5 + 4);
v___x_3333_ = l_Lake_Verbosity_ctorIdx(v_verbosity_3332_);
v___x_3334_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_3335_ = lean_nat_dec_eq(v___x_3333_, v___x_3334_);
lean_dec(v___x_3333_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; 
lean_dec(v___x_3299_);
lean_dec(v_baseName_3298_);
v___x_3336_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_3309_ = v___x_3336_;
v_a_3310_ = v___y_3306_;
goto v___jp_3308_;
}
else
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3337_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3338_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3298_, v___x_3335_);
v___x_3339_ = lean_string_append(v___x_3337_, v___x_3338_);
lean_dec_ref(v___x_3338_);
v___x_3340_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3341_ = lean_string_append(v___x_3339_, v___x_3340_);
v___x_3342_ = l_Lake_Name_eraseHead(v___x_3299_);
v___x_3343_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3342_, v___x_3335_);
v___x_3344_ = lean_string_append(v___x_3341_, v___x_3343_);
lean_dec_ref(v___x_3343_);
v___x_3345_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_3346_ = lean_string_append(v___x_3344_, v___x_3345_);
v_a_3309_ = v___x_3346_;
v_a_3310_ = v___y_3306_;
goto v___jp_3308_;
}
}
else
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_dec(v___x_3299_);
lean_dec(v_baseName_3298_);
v___x_3347_ = lean_box(0);
v___x_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
lean_ctor_set(v___x_3348_, 1, v___y_3306_);
return v___x_3348_;
}
v___jp_3308_:
{
lean_object* v_log_3311_; uint8_t v_action_3312_; uint8_t v_wantsRebuild_3313_; uint8_t v_canceled_3314_; lean_object* v_trace_3315_; lean_object* v_buildTime_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3330_; 
v_log_3311_ = lean_ctor_get(v_a_3310_, 0);
v_action_3312_ = lean_ctor_get_uint8(v_a_3310_, sizeof(void*)*3);
v_wantsRebuild_3313_ = lean_ctor_get_uint8(v_a_3310_, sizeof(void*)*3 + 1);
v_canceled_3314_ = lean_ctor_get_uint8(v_a_3310_, sizeof(void*)*3 + 2);
v_trace_3315_ = lean_ctor_get(v_a_3310_, 1);
v_buildTime_3316_ = lean_ctor_get(v_a_3310_, 2);
v_isSharedCheck_3330_ = !lean_is_exclusive(v_a_3310_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3318_ = v_a_3310_;
v_isShared_3319_ = v_isSharedCheck_3330_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_buildTime_3316_);
lean_inc(v_trace_3315_);
lean_inc(v_log_3311_);
lean_dec(v_a_3310_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3330_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; uint8_t v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3327_; 
v___x_3320_ = ((lean_object*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0));
v___x_3321_ = lean_string_append(v___x_3320_, v_a_3309_);
lean_dec_ref(v_a_3309_);
v___x_3322_ = 3;
v___x_3323_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3323_, 0, v___x_3321_);
lean_ctor_set_uint8(v___x_3323_, sizeof(void*)*1, v___x_3322_);
v___x_3324_ = lean_array_get_size(v_log_3311_);
v___x_3325_ = lean_array_push(v_log_3311_, v___x_3323_);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v___x_3325_);
v___x_3327_ = v___x_3318_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3325_);
lean_ctor_set(v_reuseFailAlloc_3329_, 1, v_trace_3315_);
lean_ctor_set(v_reuseFailAlloc_3329_, 2, v_buildTime_3316_);
lean_ctor_set_uint8(v_reuseFailAlloc_3329_, sizeof(void*)*3, v_action_3312_);
lean_ctor_set_uint8(v_reuseFailAlloc_3329_, sizeof(void*)*3 + 1, v_wantsRebuild_3313_);
lean_ctor_set_uint8(v_reuseFailAlloc_3329_, sizeof(void*)*3 + 2, v_canceled_3314_);
v___x_3327_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
lean_object* v___x_3328_; 
v___x_3328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3324_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
return v___x_3328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object* v_baseName_3349_, lean_object* v___x_3350_, lean_object* v_success_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
uint8_t v_success_boxed_3359_; lean_object* v_res_3360_; 
v_success_boxed_3359_ = lean_unbox(v_success_3351_);
v_res_3360_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(v_baseName_3349_, v___x_3350_, v_success_boxed_3359_, v___y_3352_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec(v___y_3354_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* v___x_3361_, lean_object* v___x_3362_, lean_object* v___x_3363_, lean_object* v_pkg_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v_baseName_3372_; lean_object* v_keyName_3373_; lean_object* v___f_3374_; uint8_t v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___f_3385_; uint8_t v___x_3386_; lean_object* v___x_3387_; 
v_baseName_3372_ = lean_ctor_get(v_pkg_3364_, 1);
v_keyName_3373_ = lean_ctor_get(v_pkg_3364_, 2);
lean_inc(v___x_3361_);
lean_inc_n(v_baseName_3372_, 2);
v___f_3374_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3374_, 0, v_baseName_3372_);
lean_closure_set(v___f_3374_, 1, v___x_3361_);
v___x_3375_ = 1;
v___x_3376_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3372_, v___x_3375_);
v___x_3377_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3378_ = lean_string_append(v___x_3376_, v___x_3377_);
v___x_3379_ = l_Lake_Name_eraseHead(v___x_3362_);
v___x_3380_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3379_, v___x_3375_);
v___x_3381_ = lean_string_append(v___x_3378_, v___x_3380_);
lean_dec_ref(v___x_3380_);
lean_inc(v_keyName_3373_);
v___x_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3382_, 0, v_keyName_3373_);
v___x_3383_ = l_Lake_Package_keyword;
v___x_3384_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3382_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
lean_ctor_set(v___x_3384_, 2, v_pkg_3364_);
lean_ctor_set(v___x_3384_, 3, v___x_3361_);
lean_inc(v___x_3363_);
v___f_3385_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3385_, 0, v___x_3384_);
lean_closure_set(v___f_3385_, 1, v___x_3363_);
lean_closure_set(v___f_3385_, 2, v___f_3374_);
v___x_3386_ = 0;
v___x_3387_ = l_Lake_ensureJob___redArg(v___x_3363_, v___f_3385_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3412_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
v_a_3389_ = lean_ctor_get(v___x_3387_, 1);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3391_ = v___x_3387_;
v_isShared_3392_ = v_isSharedCheck_3412_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_inc(v_a_3388_);
lean_dec(v___x_3387_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3412_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v_task_3393_; lean_object* v_kind_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3410_; 
v_task_3393_ = lean_ctor_get(v_a_3388_, 0);
v_kind_3394_ = lean_ctor_get(v_a_3388_, 1);
v_isSharedCheck_3410_ = !lean_is_exclusive(v_a_3388_);
if (v_isSharedCheck_3410_ == 0)
{
lean_object* v_unused_3411_; 
v_unused_3411_ = lean_ctor_get(v_a_3388_, 2);
lean_dec(v_unused_3411_);
v___x_3396_ = v_a_3388_;
v_isShared_3397_ = v_isSharedCheck_3410_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_kind_3394_);
lean_inc(v_task_3393_);
lean_dec(v_a_3388_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3410_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v_registeredJobs_3398_; lean_object* v_job_3400_; 
v_registeredJobs_3398_ = lean_ctor_get(v___y_3369_, 4);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 2, v___x_3381_);
v_job_3400_ = v___x_3396_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_task_3393_);
lean_ctor_set(v_reuseFailAlloc_3409_, 1, v_kind_3394_);
lean_ctor_set(v_reuseFailAlloc_3409_, 2, v___x_3381_);
v_job_3400_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3407_; 
lean_ctor_set_uint8(v_job_3400_, sizeof(void*)*3, v___x_3386_);
v___x_3401_ = lean_st_ref_take(v_registeredJobs_3398_);
lean_inc_ref(v_job_3400_);
v___x_3402_ = l_Lake_Job_toOpaque___redArg(v_job_3400_);
v___x_3403_ = lean_array_push(v___x_3401_, v___x_3402_);
v___x_3404_ = lean_st_ref_put(v_registeredJobs_3398_, v___x_3403_);
v___x_3405_ = l_Lake_Job_renew___redArg(v_job_3400_);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v___x_3405_);
v___x_3407_ = v___x_3391_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v_a_3389_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3381_);
return v___x_3387_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_3413_, lean_object* v___x_3414_, lean_object* v___x_3415_, lean_object* v_pkg_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(v___x_3413_, v___x_3414_, v___x_3415_, v_pkg_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec(v___y_3418_);
return v_res_3424_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___f_3428_; 
v___x_3425_ = l_Lake_instDataKindUnit;
v___x_3426_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3427_ = l_Lake_Package_optGitHubReleaseFacet;
v___f_3428_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3428_, 0, v___x_3427_);
lean_closure_set(v___f_3428_, 1, v___x_3426_);
lean_closure_set(v___f_3428_, 2, v___x_3425_);
return v___f_3428_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3429_; uint8_t v___x_3430_; lean_object* v___x_3431_; lean_object* v___f_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___f_3429_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3430_ = 1;
v___x_3431_ = l_Lake_instDataKindUnit;
v___f_3432_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__0, &l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0);
v___x_3433_ = l_Lake_Package_keyword;
v___x_3434_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
lean_ctor_set(v___x_3434_, 1, v___f_3432_);
lean_ctor_set(v___x_3434_, 2, v___x_3431_);
lean_ctor_set(v___x_3434_, 3, v___f_3429_);
lean_ctor_set_uint8(v___x_3434_, sizeof(void*)*4, v___x_3430_);
lean_ctor_set_uint8(v___x_3434_, sizeof(void*)*4 + 1, v___x_3430_);
return v___x_3434_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_3435_; 
v___x_3435_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__1, &l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* v_build_3436_, uint8_t v_x_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_log_3445_; uint8_t v_action_3446_; uint8_t v_wantsRebuild_3447_; uint8_t v_canceled_3448_; lean_object* v_buildTime_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3458_; 
v_log_3445_ = lean_ctor_get(v___y_3443_, 0);
v_action_3446_ = lean_ctor_get_uint8(v___y_3443_, sizeof(void*)*3);
v_wantsRebuild_3447_ = lean_ctor_get_uint8(v___y_3443_, sizeof(void*)*3 + 1);
v_canceled_3448_ = lean_ctor_get_uint8(v___y_3443_, sizeof(void*)*3 + 2);
v_buildTime_3449_ = lean_ctor_get(v___y_3443_, 2);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___y_3443_);
if (v_isSharedCheck_3458_ == 0)
{
lean_object* v_unused_3459_; 
v_unused_3459_ = lean_ctor_get(v___y_3443_, 1);
lean_dec(v_unused_3459_);
v___x_3451_ = v___y_3443_;
v_isShared_3452_ = v_isSharedCheck_3458_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_buildTime_3449_);
lean_inc(v_log_3445_);
lean_dec(v___y_3443_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3458_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; lean_object* v___x_3455_; 
v___x_3453_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 1, v___x_3453_);
v___x_3455_ = v___x_3451_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_log_3445_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3457_, 2, v_buildTime_3449_);
lean_ctor_set_uint8(v_reuseFailAlloc_3457_, sizeof(void*)*3, v_action_3446_);
lean_ctor_set_uint8(v_reuseFailAlloc_3457_, sizeof(void*)*3 + 1, v_wantsRebuild_3447_);
lean_ctor_set_uint8(v_reuseFailAlloc_3457_, sizeof(void*)*3 + 2, v_canceled_3448_);
v___x_3455_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3456_; 
lean_inc_ref(v___y_3442_);
lean_inc(v___y_3441_);
lean_inc(v___y_3440_);
lean_inc(v___y_3439_);
v___x_3456_ = lean_apply_7(v_build_3436_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___x_3455_, lean_box(0));
return v___x_3456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* v_build_3460_, lean_object* v_x_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
uint8_t v_x_1627__boxed_3469_; lean_object* v_res_3470_; 
v_x_1627__boxed_3469_ = lean_unbox(v_x_3461_);
v_res_3470_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(v_build_3460_, v_x_1627__boxed_3469_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec(v___y_3463_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* v_self_3471_, lean_object* v_build_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v_wsIdx_3480_; lean_object* v___x_3481_; uint8_t v___x_3482_; 
v_wsIdx_3480_ = lean_ctor_get(v_self_3471_, 0);
v___x_3481_ = lean_unsigned_to_nat(0u);
v___x_3482_ = lean_nat_dec_eq(v_wsIdx_3480_, v___x_3481_);
if (v___x_3482_ == 0)
{
lean_object* v___f_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___f_3483_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3483_, 0, v_build_3472_);
v___x_3484_ = lean_box(0);
lean_inc_ref(v_a_3473_);
v___x_3485_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3471_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3496_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
v_a_3487_ = lean_ctor_get(v___x_3485_, 1);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3489_ = v___x_3485_;
v_isShared_3490_ = v_isSharedCheck_3496_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_inc(v_a_3486_);
lean_dec(v___x_3485_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3496_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3494_; 
v___x_3491_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3492_ = l_Lake_Job_bindM___redArg(v___x_3484_, v_a_3486_, v___f_3483_, v___x_3481_, v___x_3482_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v___x_3491_);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3492_);
v___x_3494_ = v___x_3489_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3492_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_a_3487_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
else
{
lean_object* v_a_3497_; lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec_ref(v___f_3483_);
lean_dec_ref(v_a_3473_);
v_a_3497_ = lean_ctor_get(v___x_3485_, 0);
v_a_3498_ = lean_ctor_get(v___x_3485_, 1);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3485_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_inc(v_a_3497_);
lean_dec(v___x_3485_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3497_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
else
{
uint8_t v___x_3506_; uint8_t v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
lean_dec_ref(v_self_3471_);
v___x_3506_ = 0;
v___x_3507_ = 0;
v___x_3508_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3509_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3509_, 0, v_a_3478_);
lean_ctor_set(v___x_3509_, 1, v___x_3508_);
lean_ctor_set(v___x_3509_, 2, v___x_3481_);
lean_ctor_set_uint8(v___x_3509_, sizeof(void*)*3, v___x_3506_);
lean_ctor_set_uint8(v___x_3509_, sizeof(void*)*3 + 1, v___x_3507_);
lean_ctor_set_uint8(v___x_3509_, sizeof(void*)*3 + 2, v___x_3507_);
lean_inc_ref(v_a_3477_);
lean_inc(v_a_3476_);
lean_inc(v_a_3475_);
lean_inc(v_a_3474_);
v___x_3510_ = lean_apply_7(v_build_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v___x_3509_, lean_box(0));
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3520_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 1);
v_a_3512_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3514_ = v___x_3510_;
v_isShared_3515_ = v_isSharedCheck_3520_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3511_);
lean_inc(v_a_3512_);
lean_dec(v___x_3510_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3520_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v_log_3516_; lean_object* v___x_3518_; 
v_log_3516_ = lean_ctor_get(v_a_3511_, 0);
lean_inc_ref(v_log_3516_);
lean_dec(v_a_3511_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 1, v_log_3516_);
v___x_3518_ = v___x_3514_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3512_);
lean_ctor_set(v_reuseFailAlloc_3519_, 1, v_log_3516_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
else
{
lean_object* v_a_3521_; lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3530_; 
v_a_3521_ = lean_ctor_get(v___x_3510_, 1);
v_a_3522_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3524_ = v___x_3510_;
v_isShared_3525_ = v_isSharedCheck_3530_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3521_);
lean_inc(v_a_3522_);
lean_dec(v___x_3510_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3530_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v_log_3526_; lean_object* v___x_3528_; 
v_log_3526_ = lean_ctor_get(v_a_3521_, 0);
lean_inc_ref(v_log_3526_);
lean_dec(v_a_3521_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 1, v_log_3526_);
v___x_3528_ = v___x_3524_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3522_);
lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_log_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___boxed(lean_object* v_self_3531_, lean_object* v_build_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3531_, v_build_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_);
lean_dec_ref(v_a_3537_);
lean_dec(v_a_3536_);
lean_dec(v_a_3535_);
lean_dec(v_a_3534_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* v_00_u03b1_3541_, lean_object* v_self_3542_, lean_object* v_build_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_){
_start:
{
lean_object* v___x_3551_; 
v___x_3551_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3542_, v_build_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___boxed(lean_object* v_00_u03b1_3552_, lean_object* v_self_3553_, lean_object* v_build_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lake_Package_afterBuildCacheAsync(v_00_u03b1_3552_, v_self_3553_, v_build_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
lean_dec_ref(v_a_3559_);
lean_dec(v_a_3558_);
lean_dec(v_a_3557_);
lean_dec(v_a_3556_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* v_build_3563_, uint8_t v_x_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v_log_3572_; uint8_t v_action_3573_; uint8_t v_wantsRebuild_3574_; uint8_t v_canceled_3575_; lean_object* v_buildTime_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3585_; 
v_log_3572_ = lean_ctor_get(v___y_3570_, 0);
v_action_3573_ = lean_ctor_get_uint8(v___y_3570_, sizeof(void*)*3);
v_wantsRebuild_3574_ = lean_ctor_get_uint8(v___y_3570_, sizeof(void*)*3 + 1);
v_canceled_3575_ = lean_ctor_get_uint8(v___y_3570_, sizeof(void*)*3 + 2);
v_buildTime_3576_ = lean_ctor_get(v___y_3570_, 2);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___y_3570_);
if (v_isSharedCheck_3585_ == 0)
{
lean_object* v_unused_3586_; 
v_unused_3586_ = lean_ctor_get(v___y_3570_, 1);
lean_dec(v_unused_3586_);
v___x_3578_ = v___y_3570_;
v_isShared_3579_ = v_isSharedCheck_3585_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_buildTime_3576_);
lean_inc(v_log_3572_);
lean_dec(v___y_3570_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3585_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3580_; lean_object* v___x_3582_; 
v___x_3580_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 1, v___x_3580_);
v___x_3582_ = v___x_3578_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_log_3572_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v___x_3580_);
lean_ctor_set(v_reuseFailAlloc_3584_, 2, v_buildTime_3576_);
lean_ctor_set_uint8(v_reuseFailAlloc_3584_, sizeof(void*)*3, v_action_3573_);
lean_ctor_set_uint8(v_reuseFailAlloc_3584_, sizeof(void*)*3 + 1, v_wantsRebuild_3574_);
lean_ctor_set_uint8(v_reuseFailAlloc_3584_, sizeof(void*)*3 + 2, v_canceled_3575_);
v___x_3582_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3583_; 
lean_inc_ref(v___y_3569_);
lean_inc(v___y_3568_);
lean_inc(v___y_3567_);
lean_inc(v___y_3566_);
v___x_3583_ = lean_apply_7(v_build_3563_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___x_3582_, lean_box(0));
return v___x_3583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* v_build_3587_, lean_object* v_x_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
uint8_t v_x_1657__boxed_3596_; lean_object* v_res_3597_; 
v_x_1657__boxed_3596_ = lean_unbox(v_x_3588_);
v_res_3597_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(v_build_3587_, v_x_1657__boxed_3596_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec(v___y_3590_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* v_self_3598_, lean_object* v_build_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v_wsIdx_3607_; lean_object* v___x_3608_; uint8_t v___x_3609_; lean_object* v___x_3610_; 
v_wsIdx_3607_ = lean_ctor_get(v_self_3598_, 0);
v___x_3608_ = lean_unsigned_to_nat(0u);
v___x_3609_ = lean_nat_dec_eq(v_wsIdx_3607_, v___x_3608_);
v___x_3610_ = lean_box(0);
if (v___x_3609_ == 0)
{
lean_object* v___f_3611_; lean_object* v___x_3612_; 
v___f_3611_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3611_, 0, v_build_3599_);
lean_inc_ref(v_a_3600_);
v___x_3612_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3598_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v_a_3605_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3623_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
v_a_3614_ = lean_ctor_get(v___x_3612_, 1);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3616_ = v___x_3612_;
v_isShared_3617_ = v_isSharedCheck_3623_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_inc(v_a_3613_);
lean_dec(v___x_3612_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3623_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3621_; 
v___x_3618_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3619_ = l_Lake_Job_mapM___redArg(v___x_3610_, v_a_3613_, v___f_3611_, v___x_3608_, v___x_3609_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_, v___x_3618_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v___x_3619_);
v___x_3621_ = v___x_3616_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3619_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v_a_3614_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec_ref(v___f_3611_);
lean_dec_ref(v_a_3600_);
v_a_3624_ = lean_ctor_get(v___x_3612_, 0);
v_a_3625_ = lean_ctor_get(v___x_3612_, 1);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3612_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_inc(v_a_3624_);
lean_dec(v___x_3612_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3624_);
lean_ctor_set(v_reuseFailAlloc_3631_, 1, v_a_3625_);
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
else
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
lean_dec_ref(v_self_3598_);
v___x_3633_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_3634_ = l_Lake_Job_async___redArg(v___x_3610_, v_build_3599_, v___x_3608_, v___x_3633_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
v___x_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
lean_ctor_set(v___x_3635_, 1, v_a_3605_);
return v___x_3635_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___boxed(lean_object* v_self_3636_, lean_object* v_build_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3636_, v_build_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
lean_dec_ref(v_a_3642_);
lean_dec(v_a_3641_);
lean_dec(v_a_3640_);
lean_dec(v_a_3639_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* v_00_u03b1_3646_, lean_object* v_self_3647_, lean_object* v_build_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3647_, v_build_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___boxed(lean_object* v_00_u03b1_3657_, lean_object* v_self_3658_, lean_object* v_build_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lake_Package_afterBuildCacheSync(v_00_u03b1_3657_, v_self_3658_, v_build_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
lean_dec_ref(v_a_3664_);
lean_dec(v_a_3663_);
lean_dec(v_a_3662_);
lean_dec(v_a_3661_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(lean_object* v_k_3668_, lean_object* v_v_3669_, lean_object* v_t_3670_){
_start:
{
if (lean_obj_tag(v_t_3670_) == 0)
{
lean_object* v_size_3671_; lean_object* v_k_3672_; lean_object* v_v_3673_; lean_object* v_l_3674_; lean_object* v_r_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3955_; 
v_size_3671_ = lean_ctor_get(v_t_3670_, 0);
v_k_3672_ = lean_ctor_get(v_t_3670_, 1);
v_v_3673_ = lean_ctor_get(v_t_3670_, 2);
v_l_3674_ = lean_ctor_get(v_t_3670_, 3);
v_r_3675_ = lean_ctor_get(v_t_3670_, 4);
v_isSharedCheck_3955_ = !lean_is_exclusive(v_t_3670_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3677_ = v_t_3670_;
v_isShared_3678_ = v_isSharedCheck_3955_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_r_3675_);
lean_inc(v_l_3674_);
lean_inc(v_v_3673_);
lean_inc(v_k_3672_);
lean_inc(v_size_3671_);
lean_dec(v_t_3670_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3955_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
uint8_t v___x_3679_; 
v___x_3679_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3668_, v_k_3672_);
switch(v___x_3679_)
{
case 0:
{
lean_object* v_impl_3680_; lean_object* v___x_3681_; 
lean_dec(v_size_3671_);
v_impl_3680_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3668_, v_v_3669_, v_l_3674_);
v___x_3681_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3675_) == 0)
{
lean_object* v_size_3682_; lean_object* v_size_3683_; lean_object* v_k_3684_; lean_object* v_v_3685_; lean_object* v_l_3686_; lean_object* v_r_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; uint8_t v___x_3690_; 
v_size_3682_ = lean_ctor_get(v_r_3675_, 0);
v_size_3683_ = lean_ctor_get(v_impl_3680_, 0);
lean_inc(v_size_3683_);
v_k_3684_ = lean_ctor_get(v_impl_3680_, 1);
lean_inc(v_k_3684_);
v_v_3685_ = lean_ctor_get(v_impl_3680_, 2);
lean_inc(v_v_3685_);
v_l_3686_ = lean_ctor_get(v_impl_3680_, 3);
lean_inc(v_l_3686_);
v_r_3687_ = lean_ctor_get(v_impl_3680_, 4);
lean_inc(v_r_3687_);
v___x_3688_ = lean_unsigned_to_nat(3u);
v___x_3689_ = lean_nat_mul(v___x_3688_, v_size_3682_);
v___x_3690_ = lean_nat_dec_lt(v___x_3689_, v_size_3683_);
lean_dec(v___x_3689_);
if (v___x_3690_ == 0)
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
lean_dec(v_r_3687_);
lean_dec(v_l_3686_);
lean_dec(v_v_3685_);
lean_dec(v_k_3684_);
v___x_3691_ = lean_nat_add(v___x_3681_, v_size_3683_);
lean_dec(v_size_3683_);
v___x_3692_ = lean_nat_add(v___x_3691_, v_size_3682_);
lean_dec(v___x_3691_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 3, v_impl_3680_);
lean_ctor_set(v___x_3677_, 0, v___x_3692_);
v___x_3694_ = v___x_3677_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v_k_3672_);
lean_ctor_set(v_reuseFailAlloc_3695_, 2, v_v_3673_);
lean_ctor_set(v_reuseFailAlloc_3695_, 3, v_impl_3680_);
lean_ctor_set(v_reuseFailAlloc_3695_, 4, v_r_3675_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
else
{
lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3761_; 
v_isSharedCheck_3761_ = !lean_is_exclusive(v_impl_3680_);
if (v_isSharedCheck_3761_ == 0)
{
lean_object* v_unused_3762_; lean_object* v_unused_3763_; lean_object* v_unused_3764_; lean_object* v_unused_3765_; lean_object* v_unused_3766_; 
v_unused_3762_ = lean_ctor_get(v_impl_3680_, 4);
lean_dec(v_unused_3762_);
v_unused_3763_ = lean_ctor_get(v_impl_3680_, 3);
lean_dec(v_unused_3763_);
v_unused_3764_ = lean_ctor_get(v_impl_3680_, 2);
lean_dec(v_unused_3764_);
v_unused_3765_ = lean_ctor_get(v_impl_3680_, 1);
lean_dec(v_unused_3765_);
v_unused_3766_ = lean_ctor_get(v_impl_3680_, 0);
lean_dec(v_unused_3766_);
v___x_3697_ = v_impl_3680_;
v_isShared_3698_ = v_isSharedCheck_3761_;
goto v_resetjp_3696_;
}
else
{
lean_dec(v_impl_3680_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3761_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v_size_3699_; lean_object* v_size_3700_; lean_object* v_k_3701_; lean_object* v_v_3702_; lean_object* v_l_3703_; lean_object* v_r_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; uint8_t v___x_3707_; 
v_size_3699_ = lean_ctor_get(v_l_3686_, 0);
v_size_3700_ = lean_ctor_get(v_r_3687_, 0);
v_k_3701_ = lean_ctor_get(v_r_3687_, 1);
v_v_3702_ = lean_ctor_get(v_r_3687_, 2);
v_l_3703_ = lean_ctor_get(v_r_3687_, 3);
v_r_3704_ = lean_ctor_get(v_r_3687_, 4);
v___x_3705_ = lean_unsigned_to_nat(2u);
v___x_3706_ = lean_nat_mul(v___x_3705_, v_size_3699_);
v___x_3707_ = lean_nat_dec_lt(v_size_3700_, v___x_3706_);
lean_dec(v___x_3706_);
if (v___x_3707_ == 0)
{
lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3736_; 
lean_inc(v_r_3704_);
lean_inc(v_l_3703_);
lean_inc(v_v_3702_);
lean_inc(v_k_3701_);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_r_3687_);
if (v_isSharedCheck_3736_ == 0)
{
lean_object* v_unused_3737_; lean_object* v_unused_3738_; lean_object* v_unused_3739_; lean_object* v_unused_3740_; lean_object* v_unused_3741_; 
v_unused_3737_ = lean_ctor_get(v_r_3687_, 4);
lean_dec(v_unused_3737_);
v_unused_3738_ = lean_ctor_get(v_r_3687_, 3);
lean_dec(v_unused_3738_);
v_unused_3739_ = lean_ctor_get(v_r_3687_, 2);
lean_dec(v_unused_3739_);
v_unused_3740_ = lean_ctor_get(v_r_3687_, 1);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_r_3687_, 0);
lean_dec(v_unused_3741_);
v___x_3709_ = v_r_3687_;
v_isShared_3710_ = v_isSharedCheck_3736_;
goto v_resetjp_3708_;
}
else
{
lean_dec(v_r_3687_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3736_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___x_3724_; lean_object* v___y_3726_; 
v___x_3711_ = lean_nat_add(v___x_3681_, v_size_3683_);
lean_dec(v_size_3683_);
v___x_3712_ = lean_nat_add(v___x_3711_, v_size_3682_);
lean_dec(v___x_3711_);
v___x_3724_ = lean_nat_add(v___x_3681_, v_size_3699_);
if (lean_obj_tag(v_l_3703_) == 0)
{
lean_object* v_size_3734_; 
v_size_3734_ = lean_ctor_get(v_l_3703_, 0);
lean_inc(v_size_3734_);
v___y_3726_ = v_size_3734_;
goto v___jp_3725_;
}
else
{
lean_object* v___x_3735_; 
v___x_3735_ = lean_unsigned_to_nat(0u);
v___y_3726_ = v___x_3735_;
goto v___jp_3725_;
}
v___jp_3713_:
{
lean_object* v___x_3717_; lean_object* v___x_3719_; 
v___x_3717_ = lean_nat_add(v___y_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec(v___y_3715_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 4, v_r_3675_);
lean_ctor_set(v___x_3709_, 3, v_r_3704_);
lean_ctor_set(v___x_3709_, 2, v_v_3673_);
lean_ctor_set(v___x_3709_, 1, v_k_3672_);
lean_ctor_set(v___x_3709_, 0, v___x_3717_);
v___x_3719_ = v___x_3709_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3717_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_k_3672_);
lean_ctor_set(v_reuseFailAlloc_3723_, 2, v_v_3673_);
lean_ctor_set(v_reuseFailAlloc_3723_, 3, v_r_3704_);
lean_ctor_set(v_reuseFailAlloc_3723_, 4, v_r_3675_);
v___x_3719_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3721_; 
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 4, v___x_3719_);
lean_ctor_set(v___x_3697_, 3, v___y_3714_);
lean_ctor_set(v___x_3697_, 2, v_v_3702_);
lean_ctor_set(v___x_3697_, 1, v_k_3701_);
lean_ctor_set(v___x_3697_, 0, v___x_3712_);
v___x_3721_ = v___x_3697_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3722_, 1, v_k_3701_);
lean_ctor_set(v_reuseFailAlloc_3722_, 2, v_v_3702_);
lean_ctor_set(v_reuseFailAlloc_3722_, 3, v___y_3714_);
lean_ctor_set(v_reuseFailAlloc_3722_, 4, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
v___jp_3725_:
{
lean_object* v___x_3727_; lean_object* v___x_3729_; 
v___x_3727_ = lean_nat_add(v___x_3724_, v___y_3726_);
lean_dec(v___y_3726_);
lean_dec(v___x_3724_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 4, v_l_3703_);
lean_ctor_set(v___x_3677_, 3, v_l_3686_);
lean_ctor_set(v___x_3677_, 2, v_v_3685_);
lean_ctor_set(v___x_3677_, 1, v_k_3684_);
lean_ctor_set(v___x_3677_, 0, v___x_3727_);
v___x_3729_ = v___x_3677_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3727_);
lean_ctor_set(v_reuseFailAlloc_3733_, 1, v_k_3684_);
lean_ctor_set(v_reuseFailAlloc_3733_, 2, v_v_3685_);
lean_ctor_set(v_reuseFailAlloc_3733_, 3, v_l_3686_);
lean_ctor_set(v_reuseFailAlloc_3733_, 4, v_l_3703_);
v___x_3729_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3730_; 
v___x_3730_ = lean_nat_add(v___x_3681_, v_size_3682_);
if (lean_obj_tag(v_r_3704_) == 0)
{
lean_object* v_size_3731_; 
v_size_3731_ = lean_ctor_get(v_r_3704_, 0);
lean_inc(v_size_3731_);
v___y_3714_ = v___x_3729_;
v___y_3715_ = v___x_3730_;
v___y_3716_ = v_size_3731_;
goto v___jp_3713_;
}
else
{
lean_object* v___x_3732_; 
v___x_3732_ = lean_unsigned_to_nat(0u);
v___y_3714_ = v___x_3729_;
v___y_3715_ = v___x_3730_;
v___y_3716_ = v___x_3732_;
goto v___jp_3713_;
}
}
}
}
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
lean_del_object(v___x_3677_);
v___x_3742_ = lean_nat_add(v___x_3681_, v_size_3683_);
lean_dec(v_size_3683_);
v___x_3743_ = lean_nat_add(v___x_3742_, v_size_3682_);
lean_dec(v___x_3742_);
v___x_3744_ = lean_nat_add(v___x_3681_, v_size_3682_);
v___x_3745_ = lean_nat_add(v___x_3744_, v_size_3700_);
lean_dec(v___x_3744_);
lean_inc_ref(v_r_3675_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 4, v_r_3675_);
lean_ctor_set(v___x_3697_, 3, v_r_3687_);
lean_ctor_set(v___x_3697_, 2, v_v_3673_);
lean_ctor_set(v___x_3697_, 1, v_k_3672_);
lean_ctor_set(v___x_3697_, 0, v___x_3745_);
v___x_3747_ = v___x_3697_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3745_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v_k_3672_);
lean_ctor_set(v_reuseFailAlloc_3760_, 2, v_v_3673_);
lean_ctor_set(v_reuseFailAlloc_3760_, 3, v_r_3687_);
lean_ctor_set(v_reuseFailAlloc_3760_, 4, v_r_3675_);
v___x_3747_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
v_isSharedCheck_3754_ = !lean_is_exclusive(v_r_3675_);
if (v_isSharedCheck_3754_ == 0)
{
lean_object* v_unused_3755_; lean_object* v_unused_3756_; lean_object* v_unused_3757_; lean_object* v_unused_3758_; lean_object* v_unused_3759_; 
v_unused_3755_ = lean_ctor_get(v_r_3675_, 4);
lean_dec(v_unused_3755_);
v_unused_3756_ = lean_ctor_get(v_r_3675_, 3);
lean_dec(v_unused_3756_);
v_unused_3757_ = lean_ctor_get(v_r_3675_, 2);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_r_3675_, 1);
lean_dec(v_unused_3758_);
v_unused_3759_ = lean_ctor_get(v_r_3675_, 0);
lean_dec(v_unused_3759_);
v___x_3749_ = v_r_3675_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_dec(v_r_3675_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 4, v___x_3747_);
lean_ctor_set(v___x_3749_, 3, v_l_3686_);
lean_ctor_set(v___x_3749_, 2, v_v_3685_);
lean_ctor_set(v___x_3749_, 1, v_k_3684_);
lean_ctor_set(v___x_3749_, 0, v___x_3743_);
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3743_);
lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_k_3684_);
lean_ctor_set(v_reuseFailAlloc_3753_, 2, v_v_3685_);
lean_ctor_set(v_reuseFailAlloc_3753_, 3, v_l_3686_);
lean_ctor_set(v_reuseFailAlloc_3753_, 4, v___x_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3767_; 
v_l_3767_ = lean_ctor_get(v_impl_3680_, 3);
lean_inc(v_l_3767_);
if (lean_obj_tag(v_l_3767_) == 0)
{
lean_object* v_r_3768_; lean_object* v_k_3769_; lean_object* v_v_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3781_; 
v_r_3768_ = lean_ctor_get(v_impl_3680_, 4);
v_k_3769_ = lean_ctor_get(v_impl_3680_, 1);
v_v_3770_ = lean_ctor_get(v_impl_3680_, 2);
v_isSharedCheck_3781_ = !lean_is_exclusive(v_impl_3680_);
if (v_isSharedCheck_3781_ == 0)
{
lean_object* v_unused_3782_; lean_object* v_unused_3783_; 
v_unused_3782_ = lean_ctor_get(v_impl_3680_, 3);
lean_dec(v_unused_3782_);
v_unused_3783_ = lean_ctor_get(v_impl_3680_, 0);
lean_dec(v_unused_3783_);
v___x_3772_ = v_impl_3680_;
v_isShared_3773_ = v_isSharedCheck_3781_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_r_3768_);
lean_inc(v_v_3770_);
lean_inc(v_k_3769_);
lean_dec(v_impl_3680_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3781_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
v___x_3774_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3768_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 3, v_r_3768_);
lean_ctor_set(v___x_3772_, 2, v_v_3673_);
lean_ctor_set(v___x_3772_, 1, v_k_3672_);
lean_ctor_set(v___x_3772_, 0, v___x_3681_);
v___x_3776_ = v___x_3772_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_k_3672_);
lean_ctor_set(v_reuseFailAlloc_3780_, 2, v_v_3673_);
lean_ctor_set(v_reuseFailAlloc_3780_, 3, v_r_3768_);
lean_ctor_set(v_reuseFailAlloc_3780_, 4, v_r_3768_);
v___x_3776_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
lean_object* v___x_3778_; 
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 4, v___x_3776_);
lean_ctor_set(v___x_3677_, 3, v_l_3767_);
lean_ctor_set(v___x_3677_, 2, v_v_3770_);
lean_ctor_set(v___x_3677_, 1, v_k_3769_);
lean_ctor_set(v___x_3677_, 0, v___x_3774_);
v___x_3778_ = v___x_3677_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3774_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_k_3769_);
lean_ctor_set(v_reuseFailAlloc_3779_, 2, v_v_3770_);
lean_ctor_set(v_reuseFailAlloc_3779_, 3, v_l_3767_);
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
}
else
{
lean_object* v_r_3784_; 
v_r_3784_ = lean_ctor_get(v_impl_3680_, 4);
lean_inc(v_r_3784_);
if (lean_obj_tag(v_r_3784_) == 0)
{
lean_object* v_k_3785_; lean_object* v_v_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3809_; 
v_k_3785_ = lean_ctor_get(v_impl_3680_, 1);
v_v_3786_ = lean_ctor_get(v_impl_3680_, 2);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_impl_3680_);
if (v_isSharedCheck_3809_ == 0)
{
lean_object* v_unused_3810_; lean_object* v_unused_3811_; lean_object* v_unused_3812_; 
v_unused_3810_ = lean_ctor_get(v_impl_3680_, 4);
lean_dec(v_unused_3810_);
v_unused_3811_ = lean_ctor_get(v_impl_3680_, 3);
lean_dec(v_unused_3811_);
v_unused_3812_ = lean_ctor_get(v_impl_3680_, 0);
lean_dec(v_unused_3812_);
v___x_3788_ = v_impl_3680_;
v_isShared_3789_ = v_isSharedCheck_3809_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_v_3786_);
lean_inc(v_k_3785_);
lean_dec(v_impl_3680_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3809_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v_k_3790_; lean_object* v_v_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3805_; 
v_k_3790_ = lean_ctor_get(v_r_3784_, 1);
v_v_3791_ = lean_ctor_get(v_r_3784_, 2);
v_isSharedCheck_3805_ = !lean_is_exclusive(v_r_3784_);
if (v_isSharedCheck_3805_ == 0)
{
lean_object* v_unused_3806_; lean_object* v_unused_3807_; lean_object* v_unused_3808_; 
v_unused_3806_ = lean_ctor_get(v_r_3784_, 4);
lean_dec(v_unused_3806_);
v_unused_3807_ = lean_ctor_get(v_r_3784_, 3);
lean_dec(v_unused_3807_);
v_unused_3808_ = lean_ctor_get(v_r_3784_, 0);
lean_dec(v_unused_3808_);
v___x_3793_ = v_r_3784_;
v_isShared_3794_ = v_isSharedCheck_3805_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_v_3791_);
lean_inc(v_k_3790_);
lean_dec(v_r_3784_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3805_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3795_; lean_object* v___x_3797_; 
v___x_3795_ = lean_unsigned_to_nat(3u);
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 4, v_l_3767_);
lean_ctor_set(v___x_3793_, 3, v_l_3767_);
lean_ctor_set(v___x_3793_, 2, v_v_3786_);
lean_ctor_set(v___x_3793_, 1, v_k_3785_);
lean_ctor_set(v___x_3793_, 0, v___x_3681_);
v___x_3797_ = v___x_3793_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3804_, 1, v_k_3785_);
lean_ctor_set(v_reuseFailAlloc_3804_, 2, v_v_3786_);
lean_ctor_set(v_reuseFailAlloc_3804_, 3, v_l_3767_);
lean_ctor_set(v_reuseFailAlloc_3804_, 4, v_l_3767_);
v___x_3797_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
lean_object* v___x_3799_; 
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 4, v_l_3767_);
lean_ctor_set(v___x_3788_, 2, v_v_3673_);
lean_ctor_set(v___x_3788_, 1, v_k_3672_);
lean_ctor_set(v___x_3788_, 0, v___x_3681_);
v___x_3799_ = v___x_3788_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3681_);
lean_ctor_set(v_reuseFailAlloc_3803_, 1, v_k_3672_);
lean_ctor_set(v_reuseFailAlloc_3803_, 2, v_v_3673_);
lean_ctor_set(v_reuseFailAlloc_3803_, 3, v_l_3767_);
lean_ctor_set(v_reuseFailAlloc_3803_, 4, v_l_3767_);
v___x_3799_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
lean_object* v___x_3801_; 
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 4, v___x_3799_);
lean_ctor_set(v___x_3677_, 3, v___x_3797_);
lean_ctor_set(v___x_3677_, 2, v_v_3791_);
lean_ctor_set(v___x_3677_, 1, v_k_3790_);
lean_ctor_set(v___x_3677_, 0, v___x_3795_);
v___x_3801_ = v___x_3677_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3795_);
lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_k_3790_);
lean_ctor_set(v_reuseFailAlloc_3802_, 2, v_v_3791_);
lean_ctor_set(v_reuseFailAlloc_3802_, 3, v___x_3797_);
lean_ctor_set(v_reuseFailAlloc_3802_, 4, v___x_3799_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
}
}
else
{
lean_object* v___x_3813_; lean_object* v___x_3815_; 
v___x_3813_ = lean_unsigned_to_nat(2u);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 4, v_r_3784_);
lean_ctor_set(v___x_3677_, 3, v_impl_3680_);
lean_ctor_set(v___x_3677_, 0, v___x_3813_);
v___x_3815_ = v___x_3677_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_k_3672_);
lean_ctor_set(v_reuseFailAlloc_3816_, 2, v_v_3673_);
lean_ctor_set(v_reuseFailAlloc_3816_, 3, v_impl_3680_);
lean_ctor_set(v_reuseFailAlloc_3816_, 4, v_r_3784_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3818_; 
lean_dec(v_v_3673_);
lean_dec(v_k_3672_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 2, v_v_3669_);
lean_ctor_set(v___x_3677_, 1, v_k_3668_);
v___x_3818_ = v___x_3677_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_size_3671_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v_k_3668_);
lean_ctor_set(v_reuseFailAlloc_3819_, 2, v_v_3669_);
lean_ctor_set(v_reuseFailAlloc_3819_, 3, v_l_3674_);
lean_ctor_set(v_reuseFailAlloc_3819_, 4, v_r_3675_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
default: 
{
lean_object* v_impl_3820_; lean_object* v___x_3821_; 
lean_dec(v_size_3671_);
v_impl_3820_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3668_, v_v_3669_, v_r_3675_);
v___x_3821_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3674_) == 0)
{
lean_object* v_size_3822_; lean_object* v_size_3823_; lean_object* v_k_3824_; lean_object* v_v_3825_; lean_object* v_l_3826_; lean_object* v_r_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; 
v_size_3822_ = lean_ctor_get(v_l_3674_, 0);
v_size_3823_ = lean_ctor_get(v_impl_3820_, 0);
lean_inc(v_size_3823_);
v_k_3824_ = lean_ctor_get(v_impl_3820_, 1);
lean_inc(v_k_3824_);
v_v_3825_ = lean_ctor_get(v_impl_3820_, 2);
lean_inc(v_v_3825_);
v_l_3826_ = lean_ctor_get(v_impl_3820_, 3);
lean_inc(v_l_3826_);
v_r_3827_ = lean_ctor_get(v_impl_3820_, 4);
lean_inc(v_r_3827_);
v___x_3828_ = lean_unsigned_to_nat(3u);
v___x_3829_ = lean_nat_mul(v___x_3828_, v_size_3822_);
v___x_3830_ = lean_nat_dec_lt(v___x_3829_, v_size_3823_);
lean_dec(v___x_3829_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3834_; 
lean_dec(v_r_3827_);
lean_dec(v_l_3826_);
lean_dec(v_v_3825_);
lean_dec(v_k_3824_);
v___x_3831_ = lean_nat_add(v___x_3821_, v_size_3822_);
v___x_3832_ = lean_nat_add(v___x_3831_, v_size_3823_);
lean_dec(v_size_3823_);
lean_dec(v___x_3831_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 4, v_impl_3820_);
lean_ctor_set(v___x_3677_, 0, v___x_3832_);
v___x_3834_ = v___x_3677_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3832_);
lean_ctor_set(v_reuseFailAlloc_3835_, 1, v_k_3672_);
lean_ctor_set(v_reuseFailAlloc_3835_, 2, v_v_3673_);
lean_ctor_set(v_reuseFailAlloc_3835_, 3, v_l_3674_);
lean_ctor_set(v_reuseFailAlloc_3835_, 4, v_impl_3820_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
else
{
lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3899_; 
v_isSharedCheck_3899_ = !lean_is_exclusive(v_impl_3820_);
if (v_isSharedCheck_3899_ == 0)
{
lean_object* v_unused_3900_; lean_object* v_unused_3901_; lean_object* v_unused_3902_; lean_object* v_unused_3903_; lean_object* v_unused_3904_; 
v_unused_3900_ = lean_ctor_get(v_impl_3820_, 4);
lean_dec(v_unused_3900_);
v_unused_3901_ = lean_ctor_get(v_impl_3820_, 3);
lean_dec(v_unused_3901_);
v_unused_3902_ = lean_ctor_get(v_impl_3820_, 2);
lean_dec(v_unused_3902_);
v_unused_3903_ = lean_ctor_get(v_impl_3820_, 1);
lean_dec(v_unused_3903_);
v_unused_3904_ = lean_ctor_get(v_impl_3820_, 0);
lean_dec(v_unused_3904_);
v___x_3837_ = v_impl_3820_;
v_isShared_3838_ = v_isSharedCheck_3899_;
goto v_resetjp_3836_;
}
else
{
lean_dec(v_impl_3820_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3899_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v_size_3839_; lean_object* v_k_3840_; lean_object* v_v_3841_; lean_object* v_l_3842_; lean_object* v_r_3843_; lean_object* v_size_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; uint8_t v___x_3847_; 
v_size_3839_ = lean_ctor_get(v_l_3826_, 0);
v_k_3840_ = lean_ctor_get(v_l_3826_, 1);
v_v_3841_ = lean_ctor_get(v_l_3826_, 2);
v_l_3842_ = lean_ctor_get(v_l_3826_, 3);
v_r_3843_ = lean_ctor_get(v_l_3826_, 4);
v_size_3844_ = lean_ctor_get(v_r_3827_, 0);
v___x_3845_ = lean_unsigned_to_nat(2u);
v___x_3846_ = lean_nat_mul(v___x_3845_, v_size_3844_);
v___x_3847_ = lean_nat_dec_lt(v_size_3839_, v___x_3846_);
lean_dec(v___x_3846_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3875_; 
lean_inc(v_r_3843_);
lean_inc(v_l_3842_);
lean_inc(v_v_3841_);
lean_inc(v_k_3840_);
v_isSharedCheck_3875_ = !lean_is_exclusive(v_l_3826_);
if (v_isSharedCheck_3875_ == 0)
{
lean_object* v_unused_3876_; lean_object* v_unused_3877_; lean_object* v_unused_3878_; lean_object* v_unused_3879_; lean_object* v_unused_3880_; 
v_unused_3876_ = lean_ctor_get(v_l_3826_, 4);
lean_dec(v_unused_3876_);
v_unused_3877_ = lean_ctor_get(v_l_3826_, 3);
lean_dec(v_unused_3877_);
v_unused_3878_ = lean_ctor_get(v_l_3826_, 2);
lean_dec(v_unused_3878_);
v_unused_3879_ = lean_ctor_get(v_l_3826_, 1);
lean_dec(v_unused_3879_);
v_unused_3880_ = lean_ctor_get(v_l_3826_, 0);
lean_dec(v_unused_3880_);
v___x_3849_ = v_l_3826_;
v_isShared_3850_ = v_isSharedCheck_3875_;
goto v_resetjp_3848_;
}
else
{
lean_dec(v_l_3826_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3875_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3865_; 
v___x_3851_ = lean_nat_add(v___x_3821_, v_size_3822_);
v___x_3852_ = lean_nat_add(v___x_3851_, v_size_3823_);
lean_dec(v_size_3823_);
if (lean_obj_tag(v_l_3842_) == 0)
{
lean_object* v_size_3873_; 
v_size_3873_ = lean_ctor_get(v_l_3842_, 0);
lean_inc(v_size_3873_);
v___y_3865_ = v_size_3873_;
goto v___jp_3864_;
}
else
{
lean_object* v___x_3874_; 
v___x_3874_ = lean_unsigned_to_nat(0u);
v___y_3865_ = v___x_3874_;
goto v___jp_3864_;
}
v___jp_3853_:
{
lean_object* v___x_3857_; lean_object* v___x_3859_; 
v___x_3857_ = lean_nat_add(v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec(v___y_3855_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 4, v_r_3827_);
lean_ctor_set(v___x_3849_, 3, v_r_3843_);
lean_ctor_set(v___x_3849_, 2, v_v_3825_);
lean_ctor_set(v___x_3849_, 1, v_k_3824_);
lean_ctor_set(v___x_3849_, 0, v___x_3857_);
v___x_3859_ = v___x_3849_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v___x_3857_);
lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_k_3824_);
lean_ctor_set(v_reuseFailAlloc_3863_, 2, v_v_3825_);
lean_ctor_set(v_reuseFailAlloc_3863_, 3, v_r_3843_);
lean_ctor_set(v_reuseFailAlloc_3863_, 4, v_r_3827_);
v___x_3859_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
lean_object* v___x_3861_; 
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 4, v___x_3859_);
lean_ctor_set(v___x_3837_, 3, v___y_3854_);
lean_ctor_set(v___x_3837_, 2, v_v_3841_);
lean_ctor_set(v___x_3837_, 1, v_k_3840_);
lean_ctor_set(v___x_3837_, 0, v___x_3852_);
v___x_3861_ = v___x_3837_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_k_3840_);
lean_ctor_set(v_reuseFailAlloc_3862_, 2, v_v_3841_);
lean_ctor_set(v_reuseFailAlloc_3862_, 3, v___y_3854_);
lean_ctor_set(v_reuseFailAlloc_3862_, 4, v___x_3859_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
v___jp_3864_:
{
lean_object* v___x_3866_; lean_object* v___x_3868_; 
v___x_3866_ = lean_nat_add(v___x_3851_, v___y_3865_);
lean_dec(v___y_3865_);
lean_dec(v___x_3851_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 4, v_l_3842_);
lean_ctor_set(v___x_3677_, 0, v___x_3866_);
v___x_3868_ = v___x_3677_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v_k_3672_);
lean_ctor_set(v_reuseFailAlloc_3872_, 2, v_v_3673_);
lean_ctor_set(v_reuseFailAlloc_3872_, 3, v_l_3674_);
lean_ctor_set(v_reuseFailAlloc_3872_, 4, v_l_3842_);
v___x_3868_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
lean_object* v___x_3869_; 
v___x_3869_ = lean_nat_add(v___x_3821_, v_size_3844_);
if (lean_obj_tag(v_r_3843_) == 0)
{
lean_object* v_size_3870_; 
v_size_3870_ = lean_ctor_get(v_r_3843_, 0);
lean_inc(v_size_3870_);
v___y_3854_ = v___x_3868_;
v___y_3855_ = v___x_3869_;
v___y_3856_ = v_size_3870_;
goto v___jp_3853_;
}
else
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_unsigned_to_nat(0u);
v___y_3854_ = v___x_3868_;
v___y_3855_ = v___x_3869_;
v___y_3856_ = v___x_3871_;
goto v___jp_3853_;
}
}
}
}
}
else
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3885_; 
lean_del_object(v___x_3677_);
v___x_3881_ = lean_nat_add(v___x_3821_, v_size_3822_);
v___x_3882_ = lean_nat_add(v___x_3881_, v_size_3823_);
lean_dec(v_size_3823_);
v___x_3883_ = lean_nat_add(v___x_3881_, v_size_3839_);
lean_dec(v___x_3881_);
lean_inc_ref(v_l_3674_);
if (v_isShared_3838_ == 0)
{
lean_ctor_set(v___x_3837_, 4, v_l_3826_);
lean_ctor_set(v___x_3837_, 3, v_l_3674_);
lean_ctor_set(v___x_3837_, 2, v_v_3673_);
lean_ctor_set(v___x_3837_, 1, v_k_3672_);
lean_ctor_set(v___x_3837_, 0, v___x_3883_);
v___x_3885_ = v___x_3837_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v___x_3883_);
lean_ctor_set(v_reuseFailAlloc_3898_, 1, v_k_3672_);
lean_ctor_set(v_reuseFailAlloc_3898_, 2, v_v_3673_);
lean_ctor_set(v_reuseFailAlloc_3898_, 3, v_l_3674_);
lean_ctor_set(v_reuseFailAlloc_3898_, 4, v_l_3826_);
v___x_3885_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
v_isSharedCheck_3892_ = !lean_is_exclusive(v_l_3674_);
if (v_isSharedCheck_3892_ == 0)
{
lean_object* v_unused_3893_; lean_object* v_unused_3894_; lean_object* v_unused_3895_; lean_object* v_unused_3896_; lean_object* v_unused_3897_; 
v_unused_3893_ = lean_ctor_get(v_l_3674_, 4);
lean_dec(v_unused_3893_);
v_unused_3894_ = lean_ctor_get(v_l_3674_, 3);
lean_dec(v_unused_3894_);
v_unused_3895_ = lean_ctor_get(v_l_3674_, 2);
lean_dec(v_unused_3895_);
v_unused_3896_ = lean_ctor_get(v_l_3674_, 1);
lean_dec(v_unused_3896_);
v_unused_3897_ = lean_ctor_get(v_l_3674_, 0);
lean_dec(v_unused_3897_);
v___x_3887_ = v_l_3674_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_dec(v_l_3674_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 4, v_r_3827_);
lean_ctor_set(v___x_3887_, 3, v___x_3885_);
lean_ctor_set(v___x_3887_, 2, v_v_3825_);
lean_ctor_set(v___x_3887_, 1, v_k_3824_);
lean_ctor_set(v___x_3887_, 0, v___x_3882_);
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3882_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_k_3824_);
lean_ctor_set(v_reuseFailAlloc_3891_, 2, v_v_3825_);
lean_ctor_set(v_reuseFailAlloc_3891_, 3, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3891_, 4, v_r_3827_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3905_; 
v_l_3905_ = lean_ctor_get(v_impl_3820_, 3);
lean_inc(v_l_3905_);
if (lean_obj_tag(v_l_3905_) == 0)
{
lean_object* v_r_3906_; lean_object* v_k_3907_; lean_object* v_v_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3931_; 
v_r_3906_ = lean_ctor_get(v_impl_3820_, 4);
v_k_3907_ = lean_ctor_get(v_impl_3820_, 1);
v_v_3908_ = lean_ctor_get(v_impl_3820_, 2);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_impl_3820_);
if (v_isSharedCheck_3931_ == 0)
{
lean_object* v_unused_3932_; lean_object* v_unused_3933_; 
v_unused_3932_ = lean_ctor_get(v_impl_3820_, 3);
lean_dec(v_unused_3932_);
v_unused_3933_ = lean_ctor_get(v_impl_3820_, 0);
lean_dec(v_unused_3933_);
v___x_3910_ = v_impl_3820_;
v_isShared_3911_ = v_isSharedCheck_3931_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_r_3906_);
lean_inc(v_v_3908_);
lean_inc(v_k_3907_);
lean_dec(v_impl_3820_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3931_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v_k_3912_; lean_object* v_v_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3927_; 
v_k_3912_ = lean_ctor_get(v_l_3905_, 1);
v_v_3913_ = lean_ctor_get(v_l_3905_, 2);
v_isSharedCheck_3927_ = !lean_is_exclusive(v_l_3905_);
if (v_isSharedCheck_3927_ == 0)
{
lean_object* v_unused_3928_; lean_object* v_unused_3929_; lean_object* v_unused_3930_; 
v_unused_3928_ = lean_ctor_get(v_l_3905_, 4);
lean_dec(v_unused_3928_);
v_unused_3929_ = lean_ctor_get(v_l_3905_, 3);
lean_dec(v_unused_3929_);
v_unused_3930_ = lean_ctor_get(v_l_3905_, 0);
lean_dec(v_unused_3930_);
v___x_3915_ = v_l_3905_;
v_isShared_3916_ = v_isSharedCheck_3927_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_v_3913_);
lean_inc(v_k_3912_);
lean_dec(v_l_3905_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3927_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3917_; lean_object* v___x_3919_; 
v___x_3917_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3906_, 2);
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 4, v_r_3906_);
lean_ctor_set(v___x_3915_, 3, v_r_3906_);
lean_ctor_set(v___x_3915_, 2, v_v_3673_);
lean_ctor_set(v___x_3915_, 1, v_k_3672_);
lean_ctor_set(v___x_3915_, 0, v___x_3821_);
v___x_3919_ = v___x_3915_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3926_, 1, v_k_3672_);
lean_ctor_set(v_reuseFailAlloc_3926_, 2, v_v_3673_);
lean_ctor_set(v_reuseFailAlloc_3926_, 3, v_r_3906_);
lean_ctor_set(v_reuseFailAlloc_3926_, 4, v_r_3906_);
v___x_3919_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3921_; 
lean_inc(v_r_3906_);
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 3, v_r_3906_);
lean_ctor_set(v___x_3910_, 0, v___x_3821_);
v___x_3921_ = v___x_3910_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v_k_3907_);
lean_ctor_set(v_reuseFailAlloc_3925_, 2, v_v_3908_);
lean_ctor_set(v_reuseFailAlloc_3925_, 3, v_r_3906_);
lean_ctor_set(v_reuseFailAlloc_3925_, 4, v_r_3906_);
v___x_3921_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3923_; 
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 4, v___x_3921_);
lean_ctor_set(v___x_3677_, 3, v___x_3919_);
lean_ctor_set(v___x_3677_, 2, v_v_3913_);
lean_ctor_set(v___x_3677_, 1, v_k_3912_);
lean_ctor_set(v___x_3677_, 0, v___x_3917_);
v___x_3923_ = v___x_3677_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3917_);
lean_ctor_set(v_reuseFailAlloc_3924_, 1, v_k_3912_);
lean_ctor_set(v_reuseFailAlloc_3924_, 2, v_v_3913_);
lean_ctor_set(v_reuseFailAlloc_3924_, 3, v___x_3919_);
lean_ctor_set(v_reuseFailAlloc_3924_, 4, v___x_3921_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
}
}
else
{
lean_object* v_r_3934_; 
v_r_3934_ = lean_ctor_get(v_impl_3820_, 4);
lean_inc(v_r_3934_);
if (lean_obj_tag(v_r_3934_) == 0)
{
lean_object* v_k_3935_; lean_object* v_v_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3947_; 
v_k_3935_ = lean_ctor_get(v_impl_3820_, 1);
v_v_3936_ = lean_ctor_get(v_impl_3820_, 2);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_impl_3820_);
if (v_isSharedCheck_3947_ == 0)
{
lean_object* v_unused_3948_; lean_object* v_unused_3949_; lean_object* v_unused_3950_; 
v_unused_3948_ = lean_ctor_get(v_impl_3820_, 4);
lean_dec(v_unused_3948_);
v_unused_3949_ = lean_ctor_get(v_impl_3820_, 3);
lean_dec(v_unused_3949_);
v_unused_3950_ = lean_ctor_get(v_impl_3820_, 0);
lean_dec(v_unused_3950_);
v___x_3938_ = v_impl_3820_;
v_isShared_3939_ = v_isSharedCheck_3947_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_v_3936_);
lean_inc(v_k_3935_);
lean_dec(v_impl_3820_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3947_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3940_; lean_object* v___x_3942_; 
v___x_3940_ = lean_unsigned_to_nat(3u);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 4, v_l_3905_);
lean_ctor_set(v___x_3938_, 2, v_v_3673_);
lean_ctor_set(v___x_3938_, 1, v_k_3672_);
lean_ctor_set(v___x_3938_, 0, v___x_3821_);
v___x_3942_ = v___x_3938_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3821_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_k_3672_);
lean_ctor_set(v_reuseFailAlloc_3946_, 2, v_v_3673_);
lean_ctor_set(v_reuseFailAlloc_3946_, 3, v_l_3905_);
lean_ctor_set(v_reuseFailAlloc_3946_, 4, v_l_3905_);
v___x_3942_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
lean_object* v___x_3944_; 
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 4, v_r_3934_);
lean_ctor_set(v___x_3677_, 3, v___x_3942_);
lean_ctor_set(v___x_3677_, 2, v_v_3936_);
lean_ctor_set(v___x_3677_, 1, v_k_3935_);
lean_ctor_set(v___x_3677_, 0, v___x_3940_);
v___x_3944_ = v___x_3677_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3940_);
lean_ctor_set(v_reuseFailAlloc_3945_, 1, v_k_3935_);
lean_ctor_set(v_reuseFailAlloc_3945_, 2, v_v_3936_);
lean_ctor_set(v_reuseFailAlloc_3945_, 3, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_3945_, 4, v_r_3934_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
else
{
lean_object* v___x_3951_; lean_object* v___x_3953_; 
v___x_3951_ = lean_unsigned_to_nat(2u);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 4, v_impl_3820_);
lean_ctor_set(v___x_3677_, 3, v_r_3934_);
lean_ctor_set(v___x_3677_, 0, v___x_3951_);
v___x_3953_ = v___x_3677_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3954_, 0, v___x_3951_);
lean_ctor_set(v_reuseFailAlloc_3954_, 1, v_k_3672_);
lean_ctor_set(v_reuseFailAlloc_3954_, 2, v_v_3673_);
lean_ctor_set(v_reuseFailAlloc_3954_, 3, v_r_3934_);
lean_ctor_set(v_reuseFailAlloc_3954_, 4, v_impl_3820_);
v___x_3953_ = v_reuseFailAlloc_3954_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
return v___x_3953_;
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
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = lean_unsigned_to_nat(1u);
v___x_3957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3957_, 0, v___x_3956_);
lean_ctor_set(v___x_3957_, 1, v_k_3668_);
lean_ctor_set(v___x_3957_, 2, v_v_3669_);
lean_ctor_set(v___x_3957_, 3, v_t_3670_);
lean_ctor_set(v___x_3957_, 4, v_t_3670_);
return v___x_3957_;
}
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3958_ = lean_box(1);
v___x_3959_ = l_Lake_Package_depsFacetConfig;
v___x_3960_ = l_Lake_Package_depsFacet;
v___x_3961_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3960_, v___x_3959_, v___x_3958_);
return v___x_3961_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3962_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__0, &l_Lake_Package_initFacetConfigs___closed__0_once, _init_l_Lake_Package_initFacetConfigs___closed__0);
v___x_3963_ = l_Lake_Package_transDepsFacetConfig;
v___x_3964_ = l_Lake_Package_transDepsFacet;
v___x_3965_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3964_, v___x_3963_, v___x_3962_);
return v___x_3965_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3966_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__1, &l_Lake_Package_initFacetConfigs___closed__1_once, _init_l_Lake_Package_initFacetConfigs___closed__1);
v___x_3967_ = l_Lake_Package_defaultModulesFacetConfig;
v___x_3968_ = l_Lake_Package_defaultModulesFacet;
v___x_3969_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3968_, v___x_3967_, v___x_3966_);
return v___x_3969_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3970_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__2, &l_Lake_Package_initFacetConfigs___closed__2_once, _init_l_Lake_Package_initFacetConfigs___closed__2);
v___x_3971_ = l_Lake_Package_extraDepFacetConfig;
v___x_3972_ = l_Lake_Package_extraDepFacet;
v___x_3973_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3972_, v___x_3971_, v___x_3970_);
return v___x_3973_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3974_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__3, &l_Lake_Package_initFacetConfigs___closed__3_once, _init_l_Lake_Package_initFacetConfigs___closed__3);
v___x_3975_ = l_Lake_Package_optBuildCacheFacetConfig;
v___x_3976_ = l_Lake_Package_optBuildCacheFacet;
v___x_3977_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3976_, v___x_3975_, v___x_3974_);
return v___x_3977_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3978_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__4, &l_Lake_Package_initFacetConfigs___closed__4_once, _init_l_Lake_Package_initFacetConfigs___closed__4);
v___x_3979_ = l_Lake_Package_buildCacheFacetConfig;
v___x_3980_ = l_Lake_Package_buildCacheFacet;
v___x_3981_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3980_, v___x_3979_, v___x_3978_);
return v___x_3981_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3982_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__5, &l_Lake_Package_initFacetConfigs___closed__5_once, _init_l_Lake_Package_initFacetConfigs___closed__5);
v___x_3983_ = l_Lake_Package_optBarrelFacetConfig;
v___x_3984_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3985_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3984_, v___x_3983_, v___x_3982_);
return v___x_3985_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3986_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__6, &l_Lake_Package_initFacetConfigs___closed__6_once, _init_l_Lake_Package_initFacetConfigs___closed__6);
v___x_3987_ = l_Lake_Package_barrelFacetConfig;
v___x_3988_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3989_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3988_, v___x_3987_, v___x_3986_);
return v___x_3989_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3990_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__7, &l_Lake_Package_initFacetConfigs___closed__7_once, _init_l_Lake_Package_initFacetConfigs___closed__7);
v___x_3991_ = l_Lake_Package_optGitHubReleaseFacetConfig;
v___x_3992_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3993_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3992_, v___x_3991_, v___x_3990_);
return v___x_3993_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__9(void){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3994_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__8, &l_Lake_Package_initFacetConfigs___closed__8_once, _init_l_Lake_Package_initFacetConfigs___closed__8);
v___x_3995_ = l_Lake_Package_gitHubReleaseFacetConfig;
v___x_3996_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3997_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3996_, v___x_3995_, v___x_3994_);
return v___x_3997_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs(void){
_start:
{
lean_object* v___x_3998_; 
v___x_3998_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__9, &l_Lake_Package_initFacetConfigs___closed__9_once, _init_l_Lake_Package_initFacetConfigs___closed__9);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3999_, lean_object* v_k_4000_, lean_object* v_v_4001_, lean_object* v_t_4002_, lean_object* v_hl_4003_){
_start:
{
lean_object* v___x_4004_; 
v___x_4004_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_4000_, v_v_4001_, v_t_4002_);
return v___x_4004_;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs(void){
_start:
{
lean_object* v___x_4005_; 
v___x_4005_ = l_Lake_Package_initFacetConfigs;
return v___x_4005_;
}
}
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Infos(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Url(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Common(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Targets(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* runtime_initialize_Lake_Reservoir(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Url(builtin);
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
res = runtime_initialize_Lake_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Package_depsFacetConfig = _init_l_Lake_Package_depsFacetConfig();
lean_mark_persistent(l_Lake_Package_depsFacetConfig);
l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2 = _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2();
lean_mark_persistent(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2);
l_Lake_Package_defaultModulesFacetConfig = _init_l_Lake_Package_defaultModulesFacetConfig();
lean_mark_persistent(l_Lake_Package_defaultModulesFacetConfig);
l_Lake_Package_transDepsFacetConfig = _init_l_Lake_Package_transDepsFacetConfig();
lean_mark_persistent(l_Lake_Package_transDepsFacetConfig);
l_Lake_Package_optBuildCacheFacetConfig = _init_l_Lake_Package_optBuildCacheFacetConfig();
lean_mark_persistent(l_Lake_Package_optBuildCacheFacetConfig);
l_Lake_Package_extraDepFacetConfig = _init_l_Lake_Package_extraDepFacetConfig();
lean_mark_persistent(l_Lake_Package_extraDepFacetConfig);
l_Lake_Package_buildCacheFacetConfig = _init_l_Lake_Package_buildCacheFacetConfig();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig);
l_Lake_Package_optBarrelFacetConfig = _init_l_Lake_Package_optBarrelFacetConfig();
lean_mark_persistent(l_Lake_Package_optBarrelFacetConfig);
l_Lake_Package_barrelFacetConfig = _init_l_Lake_Package_barrelFacetConfig();
lean_mark_persistent(l_Lake_Package_barrelFacetConfig);
l_Lake_Package_optGitHubReleaseFacetConfig = _init_l_Lake_Package_optGitHubReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_optGitHubReleaseFacetConfig);
l_Lake_Package_gitHubReleaseFacetConfig = _init_l_Lake_Package_gitHubReleaseFacetConfig();
lean_mark_persistent(l_Lake_Package_gitHubReleaseFacetConfig);
l_Lake_Package_initFacetConfigs = _init_l_Lake_Package_initFacetConfigs();
lean_mark_persistent(l_Lake_Package_initFacetConfigs);
l_Lake_initPackageFacetConfigs = _init_l_Lake_initPackageFacetConfigs();
lean_mark_persistent(l_Lake_initPackageFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Package(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin);
lean_object* initialize_Lake_Build_Infos(uint8_t builtin);
lean_object* initialize_Lake_Util_Git(uint8_t builtin);
lean_object* initialize_Lake_Util_Url(uint8_t builtin);
lean_object* initialize_Lake_Build_Common(uint8_t builtin);
lean_object* initialize_Lake_Build_Targets(uint8_t builtin);
lean_object* initialize_Lake_Build_Job_Register(uint8_t builtin);
lean_object* initialize_Lake_Reservoir(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Package(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Infos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Url(builtin);
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
res = initialize_Lake_Reservoir(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Package(builtin);
}
#ifdef __cplusplus
}
#endif
