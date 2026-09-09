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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_task_pure(lean_object*);
extern lean_object* l_Lake_Package_optBuildCacheFacet;
extern lean_object* l_Lake_Package_keyword;
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_Verbosity_ctorIdx(uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lake_Package_optReservoirBarrelFacet;
lean_object* l_Lake_Name_eraseHead(lean_object*);
extern lean_object* l_Lake_Package_optGitHubReleaseFacet;
extern lean_object* l_Lake_instDataKindUnit;
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
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lake_readTraceFile(lean_object*, lean_object*);
extern uint64_t l_Lake_Hash_nil;
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* lean_io_metadata(lean_object*);
uint8_t l_IO_FS_instOrdSystemTime_ord(lean_object*, lean_object*);
lean_object* l_Lake_OutputStatus_ctorIdx(uint8_t);
lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0_value;
static const lean_array_object l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
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
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_12_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_8_);
lean_ctor_set(v___x_12_, 2, v___x_7_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*3, v___x_10_);
lean_ctor_set_uint8(v___x_12_, sizeof(void*)*3 + 1, v___x_9_);
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
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_nbuckets_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_221_ = lean_array_get_size(v_data_220_);
v___x_222_ = lean_unsigned_to_nat(2u);
v_nbuckets_223_ = lean_nat_mul(v___x_221_, v___x_222_);
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_box(0);
v___x_226_ = lean_mk_array(v_nbuckets_223_, v___x_225_);
v___x_227_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v___x_224_, v_data_220_, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(lean_object* v_m_228_, lean_object* v_a_229_, lean_object* v_b_230_){
_start:
{
lean_object* v_size_231_; lean_object* v_buckets_232_; lean_object* v_keyName_233_; lean_object* v___x_234_; uint64_t v___y_236_; 
v_size_231_ = lean_ctor_get(v_m_228_, 0);
v_buckets_232_ = lean_ctor_get(v_m_228_, 1);
v_keyName_233_ = lean_ctor_get(v_a_229_, 2);
v___x_234_ = lean_array_get_size(v_buckets_232_);
if (lean_obj_tag(v_keyName_233_) == 0)
{
uint64_t v___x_273_; 
v___x_273_ = 1723ULL;
v___y_236_ = v___x_273_;
goto v___jp_235_;
}
else
{
uint64_t v_hash_274_; 
v_hash_274_ = lean_ctor_get_uint64(v_keyName_233_, sizeof(void*)*2);
v___y_236_ = v_hash_274_;
goto v___jp_235_;
}
v___jp_235_:
{
uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v_fold_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; lean_object* v_bkt_248_; uint8_t v___x_249_; 
v___x_237_ = 32ULL;
v___x_238_ = lean_uint64_shift_right(v___y_236_, v___x_237_);
v_fold_239_ = lean_uint64_xor(v___y_236_, v___x_238_);
v___x_240_ = 16ULL;
v___x_241_ = lean_uint64_shift_right(v_fold_239_, v___x_240_);
v___x_242_ = lean_uint64_xor(v_fold_239_, v___x_241_);
v___x_243_ = lean_uint64_to_usize(v___x_242_);
v___x_244_ = lean_usize_of_nat(v___x_234_);
v___x_245_ = ((size_t)1ULL);
v___x_246_ = lean_usize_sub(v___x_244_, v___x_245_);
v___x_247_ = lean_usize_land(v___x_243_, v___x_246_);
v_bkt_248_ = lean_array_uget_borrowed(v_buckets_232_, v___x_247_);
v___x_249_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_229_, v_bkt_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_270_; 
lean_inc_ref(v_buckets_232_);
lean_inc(v_size_231_);
v_isSharedCheck_270_ = !lean_is_exclusive(v_m_228_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; lean_object* v_unused_272_; 
v_unused_271_ = lean_ctor_get(v_m_228_, 1);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_m_228_, 0);
lean_dec(v_unused_272_);
v___x_251_ = v_m_228_;
v_isShared_252_ = v_isSharedCheck_270_;
goto v_resetjp_250_;
}
else
{
lean_dec(v_m_228_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_270_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v_size_x27_254_; lean_object* v___x_255_; lean_object* v_buckets_x27_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_253_ = lean_unsigned_to_nat(1u);
v_size_x27_254_ = lean_nat_add(v_size_231_, v___x_253_);
lean_dec(v_size_231_);
lean_inc(v_bkt_248_);
v___x_255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_255_, 0, v_a_229_);
lean_ctor_set(v___x_255_, 1, v_b_230_);
lean_ctor_set(v___x_255_, 2, v_bkt_248_);
v_buckets_x27_256_ = lean_array_uset(v_buckets_232_, v___x_247_, v___x_255_);
v___x_257_ = lean_unsigned_to_nat(4u);
v___x_258_ = lean_nat_mul(v_size_x27_254_, v___x_257_);
v___x_259_ = lean_unsigned_to_nat(3u);
v___x_260_ = lean_nat_div(v___x_258_, v___x_259_);
lean_dec(v___x_258_);
v___x_261_ = lean_array_get_size(v_buckets_x27_256_);
v___x_262_ = lean_nat_dec_le(v___x_260_, v___x_261_);
lean_dec(v___x_260_);
if (v___x_262_ == 0)
{
lean_object* v_val_263_; lean_object* v___x_265_; 
v_val_263_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_buckets_x27_256_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_val_263_);
lean_ctor_set(v___x_251_, 0, v_size_x27_254_);
v___x_265_ = v___x_251_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_size_x27_254_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_val_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
else
{
lean_object* v___x_268_; 
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_buckets_x27_256_);
lean_ctor_set(v___x_251_, 0, v_size_x27_254_);
v___x_268_ = v___x_251_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_size_x27_254_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_buckets_x27_256_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_dec(v_b_230_);
lean_dec_ref(v_a_229_);
return v_m_228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(lean_object* v_self_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_toHashSet_277_; lean_object* v_toArray_278_; uint8_t v___x_279_; 
v_toHashSet_277_ = lean_ctor_get(v_self_275_, 0);
v_toArray_278_ = lean_ctor_get(v_self_275_, 1);
v___x_279_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_toHashSet_277_, v_a_276_);
if (v___x_279_ == 0)
{
lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_289_; 
lean_inc_ref(v_toArray_278_);
lean_inc_ref(v_toHashSet_277_);
v_isSharedCheck_289_ = !lean_is_exclusive(v_self_275_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; lean_object* v_unused_291_; 
v_unused_290_ = lean_ctor_get(v_self_275_, 1);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_self_275_, 0);
lean_dec(v_unused_291_);
v___x_281_ = v_self_275_;
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
else
{
lean_dec(v_self_275_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_283_ = lean_box(0);
lean_inc_ref(v_a_276_);
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_toHashSet_277_, v_a_276_, v___x_283_);
v___x_285_ = lean_array_push(v_toArray_278_, v_a_276_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v___x_285_);
lean_ctor_set(v___x_281_, 0, v___x_284_);
v___x_287_ = v___x_281_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v___x_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
else
{
lean_dec_ref(v_a_276_);
return v_self_275_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(lean_object* v_as_292_, size_t v_i_293_, size_t v_stop_294_, lean_object* v_b_295_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = lean_usize_dec_eq(v_i_293_, v_stop_294_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; size_t v___x_299_; size_t v___x_300_; 
v___x_297_ = lean_array_uget_borrowed(v_as_292_, v_i_293_);
lean_inc(v___x_297_);
v___x_298_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v_b_295_, v___x_297_);
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_add(v_i_293_, v___x_299_);
v_i_293_ = v___x_300_;
v_b_295_ = v___x_298_;
goto _start;
}
else
{
return v_b_295_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1___boxed(lean_object* v_as_302_, lean_object* v_i_303_, lean_object* v_stop_304_, lean_object* v_b_305_){
_start:
{
size_t v_i_boxed_306_; size_t v_stop_boxed_307_; lean_object* v_res_308_; 
v_i_boxed_306_ = lean_unbox_usize(v_i_303_);
lean_dec(v_i_303_);
v_stop_boxed_307_ = lean_unbox_usize(v_stop_304_);
lean_dec(v_stop_304_);
v_res_308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_as_302_, v_i_boxed_306_, v_stop_boxed_307_, v_b_305_);
lean_dec_ref(v_as_302_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(lean_object* v_as_309_, size_t v_i_310_, size_t v_stop_311_, lean_object* v_b_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
uint8_t v___x_320_; 
v___x_320_ = lean_usize_dec_eq(v_i_310_, v_stop_311_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v_keyName_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_321_ = lean_array_uget_borrowed(v_as_309_, v_i_310_);
v_keyName_322_ = lean_ctor_get(v___x_321_, 2);
v___x_323_ = l_Lake_Package_transDepsFacet;
lean_inc(v_keyName_322_);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v_keyName_322_);
v___x_325_ = l_Lake_Package_keyword;
lean_inc(v___x_321_);
v___x_326_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
lean_ctor_set(v___x_326_, 2, v___x_321_);
lean_ctor_set(v___x_326_, 3, v___x_323_);
lean_inc_ref(v___y_313_);
lean_inc_ref(v___y_317_);
lean_inc(v___y_316_);
lean_inc(v___y_315_);
lean_inc(v___y_314_);
v___x_327_ = lean_apply_7(v___y_313_, v___x_326_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, lean_box(0));
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v_a_329_; lean_object* v___x_330_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
v_a_329_ = lean_ctor_get(v___x_327_, 1);
lean_inc(v_a_329_);
lean_dec_ref_known(v___x_327_, 2);
v___x_330_ = l_Lake_Job_await___redArg(v_a_328_, v_a_329_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v_a_332_; lean_object* v___y_334_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
v_a_332_ = lean_ctor_get(v___x_330_, 1);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_330_, 2);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_array_get_size(v_a_331_);
v___x_341_ = lean_nat_dec_lt(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
lean_dec(v_a_331_);
v___y_334_ = v_b_312_;
goto v___jp_333_;
}
else
{
uint8_t v___x_342_; 
v___x_342_ = lean_nat_dec_le(v___x_340_, v___x_340_);
if (v___x_342_ == 0)
{
if (v___x_341_ == 0)
{
lean_dec(v_a_331_);
v___y_334_ = v_b_312_;
goto v___jp_333_;
}
else
{
size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v___x_343_ = ((size_t)0ULL);
v___x_344_ = lean_usize_of_nat(v___x_340_);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_331_, v___x_343_, v___x_344_, v_b_312_);
lean_dec(v_a_331_);
v___y_334_ = v___x_345_;
goto v___jp_333_;
}
}
else
{
size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; 
v___x_346_ = ((size_t)0ULL);
v___x_347_ = lean_usize_of_nat(v___x_340_);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_331_, v___x_346_, v___x_347_, v_b_312_);
lean_dec(v_a_331_);
v___y_334_ = v___x_348_;
goto v___jp_333_;
}
}
v___jp_333_:
{
lean_object* v___x_335_; size_t v___x_336_; size_t v___x_337_; 
lean_inc(v___x_321_);
v___x_335_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v___y_334_, v___x_321_);
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_add(v_i_310_, v___x_336_);
v_i_310_ = v___x_337_;
v_b_312_ = v___x_335_;
v___y_318_ = v_a_332_;
goto _start;
}
}
else
{
lean_object* v_a_349_; lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec_ref(v___y_313_);
lean_dec_ref(v_b_312_);
v_a_349_ = lean_ctor_get(v___x_330_, 0);
v_a_350_ = lean_ctor_get(v___x_330_, 1);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_330_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_inc(v_a_349_);
lean_dec(v___x_330_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_349_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref(v___y_313_);
lean_dec_ref(v_b_312_);
v_a_358_ = lean_ctor_get(v___x_327_, 0);
v_a_359_ = lean_ctor_get(v___x_327_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_327_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_inc(v_a_358_);
lean_dec(v___x_327_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_358_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
else
{
lean_object* v___x_367_; 
lean_dec_ref(v___y_313_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v_b_312_);
lean_ctor_set(v___x_367_, 1, v___y_318_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3___boxed(lean_object* v_as_368_, lean_object* v_i_369_, lean_object* v_stop_370_, lean_object* v_b_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
size_t v_i_boxed_379_; size_t v_stop_boxed_380_; lean_object* v_res_381_; 
v_i_boxed_379_ = lean_unbox_usize(v_i_369_);
lean_dec(v_i_369_);
v_stop_boxed_380_ = lean_unbox_usize(v_stop_370_);
lean_dec(v_stop_370_);
v_res_381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_as_368_, v_i_boxed_379_, v_stop_boxed_380_, v_b_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v_as_368_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(lean_object* v___x_382_, lean_object* v___x_383_, lean_object* v___x_384_, lean_object* v___x_385_, lean_object* v_depPkgs_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_a_395_; lean_object* v_a_396_; lean_object* v___y_416_; uint8_t v___x_428_; 
v___x_428_ = lean_nat_dec_lt(v___x_382_, v___x_384_);
if (v___x_428_ == 0)
{
lean_dec_ref(v___y_387_);
v_a_395_ = v___x_385_;
v_a_396_ = v___y_392_;
goto v___jp_394_;
}
else
{
uint8_t v___x_429_; 
v___x_429_ = lean_nat_dec_le(v___x_384_, v___x_384_);
if (v___x_429_ == 0)
{
if (v___x_428_ == 0)
{
lean_dec_ref(v___y_387_);
v_a_395_ = v___x_385_;
v_a_396_ = v___y_392_;
goto v___jp_394_;
}
else
{
size_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; 
v___x_430_ = ((size_t)0ULL);
v___x_431_ = lean_usize_of_nat(v___x_384_);
v___x_432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_386_, v___x_430_, v___x_431_, v___x_385_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
v___y_416_ = v___x_432_;
goto v___jp_415_;
}
}
else
{
size_t v___x_433_; size_t v___x_434_; lean_object* v___x_435_; 
v___x_433_ = ((size_t)0ULL);
v___x_434_ = lean_usize_of_nat(v___x_384_);
v___x_435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_386_, v___x_433_, v___x_434_, v___x_385_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
v___y_416_ = v___x_435_;
goto v___jp_415_;
}
}
v___jp_394_:
{
lean_object* v_toArray_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_413_; 
v_toArray_397_ = lean_ctor_get(v_a_395_, 1);
v_isSharedCheck_413_ = !lean_is_exclusive(v_a_395_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v_a_395_, 0);
lean_dec(v_unused_414_);
v___x_399_ = v_a_395_;
v_isShared_400_ = v_isSharedCheck_413_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_toArray_397_);
lean_dec(v_a_395_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_413_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; uint8_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_401_ = lean_mk_empty_array_with_capacity(v___x_382_);
v___x_402_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_403_ = 0;
v___x_404_ = 0;
v___x_405_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_406_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_406_, 0, v___x_401_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
lean_ctor_set(v___x_406_, 2, v___x_382_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*3, v___x_403_);
lean_ctor_set_uint8(v___x_406_, sizeof(void*)*3 + 1, v___x_404_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v___x_406_);
lean_ctor_set(v___x_399_, 0, v_toArray_397_);
v___x_408_ = v___x_399_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_toArray_397_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___x_406_);
v___x_408_ = v_reuseFailAlloc_412_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = lean_task_pure(v___x_408_);
v___x_410_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v___x_383_);
lean_ctor_set(v___x_410_, 2, v___x_402_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*3, v___x_404_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
lean_ctor_set(v___x_411_, 1, v_a_396_);
return v___x_411_;
}
}
}
v___jp_415_:
{
if (lean_obj_tag(v___y_416_) == 0)
{
lean_object* v_a_417_; lean_object* v_a_418_; 
v_a_417_ = lean_ctor_get(v___y_416_, 0);
lean_inc(v_a_417_);
v_a_418_ = lean_ctor_get(v___y_416_, 1);
lean_inc(v_a_418_);
lean_dec_ref_known(v___y_416_, 2);
v_a_395_ = v_a_417_;
v_a_396_ = v_a_418_;
goto v___jp_394_;
}
else
{
lean_object* v_a_419_; lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec(v___x_383_);
lean_dec(v___x_382_);
v_a_419_ = lean_ctor_get(v___y_416_, 0);
v_a_420_ = lean_ctor_get(v___y_416_, 1);
v_isSharedCheck_427_ = !lean_is_exclusive(v___y_416_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___y_416_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_inc(v_a_419_);
lean_dec(v___y_416_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_419_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed(lean_object* v___x_436_, lean_object* v___x_437_, lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v_depPkgs_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(v___x_436_, v___x_437_, v___x_438_, v___x_439_, v_depPkgs_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v_depPkgs_440_);
lean_dec(v___x_438_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(lean_object* v_self_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_depPkgs_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___f_462_; lean_object* v___x_463_; 
v_depPkgs_457_ = lean_ctor_get(v_self_449_, 14);
lean_inc_ref(v_depPkgs_457_);
lean_dec_ref(v_self_449_);
v___x_458_ = lean_box(0);
v___x_459_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2;
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_array_get_size(v_depPkgs_457_);
v___f_462_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed), 12, 5);
lean_closure_set(v___f_462_, 0, v___x_460_);
lean_closure_set(v___f_462_, 1, v___x_458_);
lean_closure_set(v___f_462_, 2, v___x_461_);
lean_closure_set(v___f_462_, 3, v___x_459_);
lean_closure_set(v___f_462_, 4, v_depPkgs_457_);
v___x_463_ = l_Lake_ensureJob___redArg(v___x_458_, v___f_462_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___boxed(lean_object* v_self_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(v_self_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec(v_a_467_);
lean_dec(v_a_466_);
return v_res_472_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object* v_00_u03b2_473_, lean_object* v_m_474_, lean_object* v_a_475_){
_start:
{
uint8_t v___x_476_; 
v___x_476_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_474_, v_a_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_477_, lean_object* v_m_478_, lean_object* v_a_479_){
_start:
{
uint8_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(v_00_u03b2_477_, v_m_478_, v_a_479_);
lean_dec_ref(v_a_479_);
lean_dec_ref(v_m_478_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1(lean_object* v_00_u03b2_482_, lean_object* v_m_483_, lean_object* v_a_484_, lean_object* v_b_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_m_483_, v_a_484_, v_b_485_);
return v___x_486_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_487_, lean_object* v_a_488_, lean_object* v_x_489_){
_start:
{
uint8_t v___x_490_; 
v___x_490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_488_, v_x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_491_, lean_object* v_a_492_, lean_object* v_x_493_){
_start:
{
uint8_t v_res_494_; lean_object* v_r_495_; 
v_res_494_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(v_00_u03b2_491_, v_a_492_, v_x_493_);
lean_dec(v_x_493_);
lean_dec_ref(v_a_492_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_496_, lean_object* v_data_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_data_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_499_, lean_object* v_i_500_, lean_object* v_source_501_, lean_object* v_target_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v_i_500_, v_source_501_, v_target_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_504_, lean_object* v_x_505_, lean_object* v_x_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(v_x_505_, v_x_506_);
return v___x_507_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(lean_object* v_a_508_, lean_object* v_x_509_){
_start:
{
if (lean_obj_tag(v_x_509_) == 0)
{
uint8_t v___x_510_; 
v___x_510_ = 0;
return v___x_510_;
}
else
{
lean_object* v_key_511_; lean_object* v_tail_512_; lean_object* v_name_513_; lean_object* v_name_514_; uint8_t v___x_515_; 
v_key_511_ = lean_ctor_get(v_x_509_, 0);
v_tail_512_ = lean_ctor_get(v_x_509_, 2);
v_name_513_ = lean_ctor_get(v_key_511_, 1);
v_name_514_ = lean_ctor_get(v_a_508_, 1);
v___x_515_ = lean_name_eq(v_name_513_, v_name_514_);
if (v___x_515_ == 0)
{
v_x_509_ = v_tail_512_;
goto _start;
}
else
{
return v___x_515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg___boxed(lean_object* v_a_517_, lean_object* v_x_518_){
_start:
{
uint8_t v_res_519_; lean_object* v_r_520_; 
v_res_519_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_517_, v_x_518_);
lean_dec(v_x_518_);
lean_dec_ref(v_a_517_);
v_r_520_ = lean_box(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(lean_object* v_m_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_buckets_523_; lean_object* v_name_524_; lean_object* v___x_525_; uint64_t v___y_527_; 
v_buckets_523_ = lean_ctor_get(v_m_521_, 1);
v_name_524_ = lean_ctor_get(v_a_522_, 1);
v___x_525_ = lean_array_get_size(v_buckets_523_);
if (lean_obj_tag(v_name_524_) == 0)
{
uint64_t v___x_541_; 
v___x_541_ = 1723ULL;
v___y_527_ = v___x_541_;
goto v___jp_526_;
}
else
{
uint64_t v_hash_542_; 
v_hash_542_ = lean_ctor_get_uint64(v_name_524_, sizeof(void*)*2);
v___y_527_ = v_hash_542_;
goto v___jp_526_;
}
v___jp_526_:
{
uint64_t v___x_528_; uint64_t v___x_529_; uint64_t v_fold_530_; uint64_t v___x_531_; uint64_t v___x_532_; uint64_t v___x_533_; size_t v___x_534_; size_t v___x_535_; size_t v___x_536_; size_t v___x_537_; size_t v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_528_ = 32ULL;
v___x_529_ = lean_uint64_shift_right(v___y_527_, v___x_528_);
v_fold_530_ = lean_uint64_xor(v___y_527_, v___x_529_);
v___x_531_ = 16ULL;
v___x_532_ = lean_uint64_shift_right(v_fold_530_, v___x_531_);
v___x_533_ = lean_uint64_xor(v_fold_530_, v___x_532_);
v___x_534_ = lean_uint64_to_usize(v___x_533_);
v___x_535_ = lean_usize_of_nat(v___x_525_);
v___x_536_ = ((size_t)1ULL);
v___x_537_ = lean_usize_sub(v___x_535_, v___x_536_);
v___x_538_ = lean_usize_land(v___x_534_, v___x_537_);
v___x_539_ = lean_array_uget_borrowed(v_buckets_523_, v___x_538_);
v___x_540_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_522_, v___x_539_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg___boxed(lean_object* v_m_543_, lean_object* v_a_544_){
_start:
{
uint8_t v_res_545_; lean_object* v_r_546_; 
v_res_545_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(v_m_543_, v_a_544_);
lean_dec_ref(v_a_544_);
lean_dec_ref(v_m_543_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
if (lean_obj_tag(v_x_548_) == 0)
{
return v_x_547_;
}
else
{
lean_object* v_key_549_; lean_object* v_value_550_; lean_object* v_tail_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_578_; 
v_key_549_ = lean_ctor_get(v_x_548_, 0);
v_value_550_ = lean_ctor_get(v_x_548_, 1);
v_tail_551_ = lean_ctor_get(v_x_548_, 2);
v_isSharedCheck_578_ = !lean_is_exclusive(v_x_548_);
if (v_isSharedCheck_578_ == 0)
{
v___x_553_ = v_x_548_;
v_isShared_554_ = v_isSharedCheck_578_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_tail_551_);
lean_inc(v_value_550_);
lean_inc(v_key_549_);
lean_dec(v_x_548_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_578_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_name_555_; lean_object* v___x_556_; uint64_t v___y_558_; 
v_name_555_ = lean_ctor_get(v_key_549_, 1);
v___x_556_ = lean_array_get_size(v_x_547_);
if (lean_obj_tag(v_name_555_) == 0)
{
uint64_t v___x_576_; 
v___x_576_ = 1723ULL;
v___y_558_ = v___x_576_;
goto v___jp_557_;
}
else
{
uint64_t v_hash_577_; 
v_hash_577_ = lean_ctor_get_uint64(v_name_555_, sizeof(void*)*2);
v___y_558_ = v_hash_577_;
goto v___jp_557_;
}
v___jp_557_:
{
uint64_t v___x_559_; uint64_t v___x_560_; uint64_t v_fold_561_; uint64_t v___x_562_; uint64_t v___x_563_; uint64_t v___x_564_; size_t v___x_565_; size_t v___x_566_; size_t v___x_567_; size_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_559_ = 32ULL;
v___x_560_ = lean_uint64_shift_right(v___y_558_, v___x_559_);
v_fold_561_ = lean_uint64_xor(v___y_558_, v___x_560_);
v___x_562_ = 16ULL;
v___x_563_ = lean_uint64_shift_right(v_fold_561_, v___x_562_);
v___x_564_ = lean_uint64_xor(v_fold_561_, v___x_563_);
v___x_565_ = lean_uint64_to_usize(v___x_564_);
v___x_566_ = lean_usize_of_nat(v___x_556_);
v___x_567_ = ((size_t)1ULL);
v___x_568_ = lean_usize_sub(v___x_566_, v___x_567_);
v___x_569_ = lean_usize_land(v___x_565_, v___x_568_);
v___x_570_ = lean_array_uget_borrowed(v_x_547_, v___x_569_);
lean_inc(v___x_570_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 2, v___x_570_);
v___x_572_ = v___x_553_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_key_549_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_value_550_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v___x_570_);
v___x_572_ = v_reuseFailAlloc_575_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_573_; 
v___x_573_ = lean_array_uset(v_x_547_, v___x_569_, v___x_572_);
v_x_547_ = v___x_573_;
v_x_548_ = v_tail_551_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3___redArg(lean_object* v_i_579_, lean_object* v_source_580_, lean_object* v_target_581_){
_start:
{
lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_582_ = lean_array_get_size(v_source_580_);
v___x_583_ = lean_nat_dec_lt(v_i_579_, v___x_582_);
if (v___x_583_ == 0)
{
lean_dec_ref(v_source_580_);
lean_dec(v_i_579_);
return v_target_581_;
}
else
{
lean_object* v_es_584_; lean_object* v___x_585_; lean_object* v_source_586_; lean_object* v_target_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_es_584_ = lean_array_fget(v_source_580_, v_i_579_);
v___x_585_ = lean_box(0);
v_source_586_ = lean_array_fset(v_source_580_, v_i_579_, v___x_585_);
v_target_587_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6___redArg(v_target_581_, v_es_584_);
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_nat_add(v_i_579_, v___x_588_);
lean_dec(v_i_579_);
v_i_579_ = v___x_589_;
v_source_580_ = v_source_586_;
v_target_581_ = v_target_587_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2___redArg(lean_object* v_data_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_nbuckets_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_592_ = lean_array_get_size(v_data_591_);
v___x_593_ = lean_unsigned_to_nat(2u);
v_nbuckets_594_ = lean_nat_mul(v___x_592_, v___x_593_);
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_box(0);
v___x_597_ = lean_mk_array(v_nbuckets_594_, v___x_596_);
v___x_598_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3___redArg(v___x_595_, v_data_591_, v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1___redArg(lean_object* v_m_599_, lean_object* v_a_600_, lean_object* v_b_601_){
_start:
{
lean_object* v_size_602_; lean_object* v_buckets_603_; lean_object* v_name_604_; lean_object* v___x_605_; uint64_t v___y_607_; 
v_size_602_ = lean_ctor_get(v_m_599_, 0);
v_buckets_603_ = lean_ctor_get(v_m_599_, 1);
v_name_604_ = lean_ctor_get(v_a_600_, 1);
v___x_605_ = lean_array_get_size(v_buckets_603_);
if (lean_obj_tag(v_name_604_) == 0)
{
uint64_t v___x_644_; 
v___x_644_ = 1723ULL;
v___y_607_ = v___x_644_;
goto v___jp_606_;
}
else
{
uint64_t v_hash_645_; 
v_hash_645_ = lean_ctor_get_uint64(v_name_604_, sizeof(void*)*2);
v___y_607_ = v_hash_645_;
goto v___jp_606_;
}
v___jp_606_:
{
uint64_t v___x_608_; uint64_t v___x_609_; uint64_t v_fold_610_; uint64_t v___x_611_; uint64_t v___x_612_; uint64_t v___x_613_; size_t v___x_614_; size_t v___x_615_; size_t v___x_616_; size_t v___x_617_; size_t v___x_618_; lean_object* v_bkt_619_; uint8_t v___x_620_; 
v___x_608_ = 32ULL;
v___x_609_ = lean_uint64_shift_right(v___y_607_, v___x_608_);
v_fold_610_ = lean_uint64_xor(v___y_607_, v___x_609_);
v___x_611_ = 16ULL;
v___x_612_ = lean_uint64_shift_right(v_fold_610_, v___x_611_);
v___x_613_ = lean_uint64_xor(v_fold_610_, v___x_612_);
v___x_614_ = lean_uint64_to_usize(v___x_613_);
v___x_615_ = lean_usize_of_nat(v___x_605_);
v___x_616_ = ((size_t)1ULL);
v___x_617_ = lean_usize_sub(v___x_615_, v___x_616_);
v___x_618_ = lean_usize_land(v___x_614_, v___x_617_);
v_bkt_619_ = lean_array_uget_borrowed(v_buckets_603_, v___x_618_);
v___x_620_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_600_, v_bkt_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_641_; 
lean_inc_ref(v_buckets_603_);
lean_inc(v_size_602_);
v_isSharedCheck_641_ = !lean_is_exclusive(v_m_599_);
if (v_isSharedCheck_641_ == 0)
{
lean_object* v_unused_642_; lean_object* v_unused_643_; 
v_unused_642_ = lean_ctor_get(v_m_599_, 1);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v_m_599_, 0);
lean_dec(v_unused_643_);
v___x_622_ = v_m_599_;
v_isShared_623_ = v_isSharedCheck_641_;
goto v_resetjp_621_;
}
else
{
lean_dec(v_m_599_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_641_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v_size_x27_625_; lean_object* v___x_626_; lean_object* v_buckets_x27_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_624_ = lean_unsigned_to_nat(1u);
v_size_x27_625_ = lean_nat_add(v_size_602_, v___x_624_);
lean_dec(v_size_602_);
lean_inc(v_bkt_619_);
v___x_626_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_626_, 0, v_a_600_);
lean_ctor_set(v___x_626_, 1, v_b_601_);
lean_ctor_set(v___x_626_, 2, v_bkt_619_);
v_buckets_x27_627_ = lean_array_uset(v_buckets_603_, v___x_618_, v___x_626_);
v___x_628_ = lean_unsigned_to_nat(4u);
v___x_629_ = lean_nat_mul(v_size_x27_625_, v___x_628_);
v___x_630_ = lean_unsigned_to_nat(3u);
v___x_631_ = lean_nat_div(v___x_629_, v___x_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_array_get_size(v_buckets_x27_627_);
v___x_633_ = lean_nat_dec_le(v___x_631_, v___x_632_);
lean_dec(v___x_631_);
if (v___x_633_ == 0)
{
lean_object* v_val_634_; lean_object* v___x_636_; 
v_val_634_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2___redArg(v_buckets_x27_627_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v_val_634_);
lean_ctor_set(v___x_622_, 0, v_size_x27_625_);
v___x_636_ = v___x_622_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_size_x27_625_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_val_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v___x_639_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v_buckets_x27_627_);
lean_ctor_set(v___x_622_, 0, v_size_x27_625_);
v___x_639_ = v___x_622_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_size_x27_625_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_buckets_x27_627_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
else
{
lean_dec(v_b_601_);
lean_dec_ref(v_a_600_);
return v_m_599_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(lean_object* v_as_646_, size_t v_sz_647_, size_t v_i_648_, lean_object* v_b_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_a_653_; lean_object* v_a_654_; uint8_t v___x_658_; 
v___x_658_ = lean_usize_dec_lt(v_i_648_, v_sz_647_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v_b_649_);
lean_ctor_set(v___x_659_, 1, v___y_650_);
return v___x_659_;
}
else
{
lean_object* v_fst_660_; lean_object* v_snd_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_676_; 
v_fst_660_ = lean_ctor_get(v_b_649_, 0);
v_snd_661_ = lean_ctor_get(v_b_649_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_b_649_);
if (v_isSharedCheck_676_ == 0)
{
v___x_663_ = v_b_649_;
v_isShared_664_ = v_isSharedCheck_676_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_snd_661_);
lean_inc(v_fst_660_);
lean_dec(v_b_649_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_676_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_a_665_; uint8_t v___x_666_; 
v_a_665_ = lean_array_uget_borrowed(v_as_646_, v_i_648_);
v___x_666_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(v_snd_661_, v_a_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_667_ = lean_box(0);
lean_inc_n(v_a_665_, 2);
v___x_668_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1___redArg(v_snd_661_, v_a_665_, v___x_667_);
v___x_669_ = lean_array_push(v_fst_660_, v_a_665_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___x_668_);
lean_ctor_set(v___x_663_, 0, v___x_669_);
v___x_671_ = v___x_663_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___x_668_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
v_a_653_ = v___x_671_;
v_a_654_ = v___y_650_;
goto v___jp_652_;
}
}
else
{
lean_object* v___x_674_; 
if (v_isShared_664_ == 0)
{
v___x_674_ = v___x_663_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_fst_660_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_snd_661_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
v_a_653_ = v___x_674_;
v_a_654_ = v___y_650_;
goto v___jp_652_;
}
}
}
}
v___jp_652_:
{
size_t v___x_655_; size_t v___x_656_; 
v___x_655_ = ((size_t)1ULL);
v___x_656_ = lean_usize_add(v_i_648_, v___x_655_);
v_i_648_ = v___x_656_;
v_b_649_ = v_a_653_;
v___y_650_ = v_a_654_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg___boxed(lean_object* v_as_677_, lean_object* v_sz_678_, lean_object* v_i_679_, lean_object* v_b_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
size_t v_sz_boxed_683_; size_t v_i_boxed_684_; lean_object* v_res_685_; 
v_sz_boxed_683_ = lean_unbox_usize(v_sz_678_);
lean_dec(v_sz_678_);
v_i_boxed_684_ = lean_unbox_usize(v_i_679_);
lean_dec(v_i_679_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(v_as_677_, v_sz_boxed_683_, v_i_boxed_684_, v_b_680_, v___y_681_);
lean_dec_ref(v_as_677_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3(lean_object* v_self_691_, lean_object* v_as_692_, size_t v_sz_693_, size_t v_i_694_, lean_object* v_b_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_a_704_; lean_object* v_a_705_; uint8_t v___x_707_; 
v___x_707_ = lean_usize_dec_lt(v_i_694_, v_sz_693_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; 
lean_dec_ref(v___y_696_);
lean_dec_ref(v_self_691_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v_b_695_);
lean_ctor_set(v___x_708_, 1, v___y_701_);
return v___x_708_;
}
else
{
lean_object* v_fst_709_; lean_object* v_snd_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_810_; 
v_fst_709_ = lean_ctor_get(v_b_695_, 0);
v_snd_710_ = lean_ctor_get(v_b_695_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v_b_695_);
if (v_isSharedCheck_810_ == 0)
{
v___x_712_ = v_b_695_;
v_isShared_713_ = v_isSharedCheck_810_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_snd_710_);
lean_inc(v_fst_709_);
lean_dec(v_b_695_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_810_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_targetMods_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v_mods_744_; lean_object* v_a_745_; lean_object* v___x_781_; 
v_mods_744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__0));
v_a_745_ = lean_array_uget_borrowed(v_as_692_, v_i_694_);
v___x_781_ = l_Lake_Package_findTargetDecl_x3f(v_a_745_, v_self_691_);
if (lean_obj_tag(v___x_781_) == 0)
{
goto v___jp_746_;
}
else
{
lean_object* v_val_782_; lean_object* v_name_783_; lean_object* v_kind_784_; lean_object* v_config_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_808_; 
v_val_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_val_782_);
lean_dec_ref_known(v___x_781_, 1);
v_name_783_ = lean_ctor_get(v_val_782_, 1);
v_kind_784_ = lean_ctor_get(v_val_782_, 2);
v_config_785_ = lean_ctor_get(v_val_782_, 3);
v_isSharedCheck_808_ = !lean_is_exclusive(v_val_782_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v_val_782_, 0);
lean_dec(v_unused_809_);
v___x_787_ = v_val_782_;
v_isShared_788_ = v_isSharedCheck_808_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_config_785_);
lean_inc(v_kind_784_);
lean_inc(v_name_783_);
lean_dec(v_val_782_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_808_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__2));
v___x_790_ = lean_name_eq(v_kind_784_, v___x_789_);
lean_dec(v_kind_784_);
if (v___x_790_ == 0)
{
lean_del_object(v___x_787_);
lean_dec(v_config_785_);
lean_dec(v_name_783_);
goto v___jp_746_;
}
else
{
lean_object* v_keyName_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v_keyName_791_ = lean_ctor_get(v_self_691_, 2);
lean_inc(v_name_783_);
lean_inc_ref(v_self_691_);
v___x_792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_792_, 0, v_self_691_);
lean_ctor_set(v___x_792_, 1, v_name_783_);
lean_ctor_set(v___x_792_, 2, v_config_785_);
v___x_793_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_791_);
v___x_794_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_794_, 0, v_keyName_791_);
lean_ctor_set(v___x_794_, 1, v_name_783_);
if (v_isShared_788_ == 0)
{
lean_ctor_set_tag(v___x_787_, 1);
lean_ctor_set(v___x_787_, 3, v___x_793_);
lean_ctor_set(v___x_787_, 2, v___x_792_);
lean_ctor_set(v___x_787_, 1, v___x_789_);
lean_ctor_set(v___x_787_, 0, v___x_794_);
v___x_796_ = v___x_787_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v___x_793_);
v___x_796_ = v_reuseFailAlloc_807_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; 
lean_inc_ref(v___y_696_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc(v___y_698_);
lean_inc(v___y_697_);
v___x_797_ = lean_apply_7(v___y_696_, v___x_796_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, lean_box(0));
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v_a_799_; lean_object* v___x_800_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
v_a_799_ = lean_ctor_get(v___x_797_, 1);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_797_, 2);
v___x_800_ = l_Lake_Job_await___redArg(v_a_798_, v_a_799_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v_a_802_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
v_a_802_ = lean_ctor_get(v___x_800_, 1);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_800_, 2);
lean_inc_ref(v___y_696_);
v_targetMods_715_ = v_a_801_;
v___y_716_ = v___y_696_;
v___y_717_ = v___y_697_;
v___y_718_ = v___y_698_;
v___y_719_ = v___y_699_;
v___y_720_ = v___y_700_;
v___y_721_ = v_a_802_;
goto v___jp_714_;
}
else
{
lean_object* v_a_803_; lean_object* v_a_804_; 
lean_del_object(v___x_712_);
lean_dec(v_snd_710_);
lean_dec(v_fst_709_);
lean_dec_ref(v___y_696_);
lean_dec_ref(v_self_691_);
v_a_803_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_803_);
v_a_804_ = lean_ctor_get(v___x_800_, 1);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_800_, 2);
v_a_704_ = v_a_803_;
v_a_705_ = v_a_804_;
goto v___jp_703_;
}
}
else
{
lean_object* v_a_805_; lean_object* v_a_806_; 
lean_del_object(v___x_712_);
lean_dec(v_snd_710_);
lean_dec(v_fst_709_);
lean_dec_ref(v___y_696_);
lean_dec_ref(v_self_691_);
v_a_805_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_805_);
v_a_806_ = lean_ctor_get(v___x_797_, 1);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_797_, 2);
v_a_704_ = v_a_805_;
v_a_705_ = v_a_806_;
goto v___jp_703_;
}
}
}
}
}
v___jp_714_:
{
lean_object* v___x_723_; 
lean_dec_ref(v___y_716_);
if (v_isShared_713_ == 0)
{
v___x_723_ = v___x_712_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_fst_709_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_snd_710_);
v___x_723_ = v_reuseFailAlloc_743_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
size_t v_sz_724_; size_t v___x_725_; lean_object* v___x_726_; 
v_sz_724_ = lean_array_size(v_targetMods_715_);
v___x_725_ = ((size_t)0ULL);
v___x_726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(v_targetMods_715_, v_sz_724_, v___x_725_, v___x_723_, v___y_721_);
lean_dec_ref(v_targetMods_715_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v_a_728_; lean_object* v_fst_729_; lean_object* v_snd_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_740_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
v_a_728_ = lean_ctor_get(v___x_726_, 1);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_726_, 2);
v_fst_729_ = lean_ctor_get(v_a_727_, 0);
v_snd_730_ = lean_ctor_get(v_a_727_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_a_727_);
if (v_isSharedCheck_740_ == 0)
{
v___x_732_ = v_a_727_;
v_isShared_733_ = v_isSharedCheck_740_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_snd_730_);
lean_inc(v_fst_729_);
lean_dec(v_a_727_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_740_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_fst_729_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_snd_730_);
v___x_735_ = v_reuseFailAlloc_739_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
size_t v___x_736_; size_t v___x_737_; 
v___x_736_ = ((size_t)1ULL);
v___x_737_ = lean_usize_add(v_i_694_, v___x_736_);
v_i_694_ = v___x_737_;
v_b_695_ = v___x_735_;
v___y_701_ = v_a_728_;
goto _start;
}
}
}
else
{
lean_object* v_a_741_; lean_object* v_a_742_; 
lean_dec_ref(v___y_696_);
lean_dec_ref(v_self_691_);
v_a_741_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_741_);
v_a_742_ = lean_ctor_get(v___x_726_, 1);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_726_, 2);
v_a_704_ = v_a_741_;
v_a_705_ = v_a_742_;
goto v___jp_703_;
}
}
}
v___jp_746_:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lake_Package_findTargetDecl_x3f(v_a_745_, v_self_691_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_inc_ref(v___y_696_);
v_targetMods_715_ = v_mods_744_;
v___y_716_ = v___y_696_;
v___y_717_ = v___y_697_;
v___y_718_ = v___y_698_;
v___y_719_ = v___y_699_;
v___y_720_ = v___y_700_;
v___y_721_ = v___y_701_;
goto v___jp_714_;
}
else
{
lean_object* v_val_748_; lean_object* v_name_749_; lean_object* v_kind_750_; lean_object* v_config_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_779_; 
v_val_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_val_748_);
lean_dec_ref_known(v___x_747_, 1);
v_name_749_ = lean_ctor_get(v_val_748_, 1);
v_kind_750_ = lean_ctor_get(v_val_748_, 2);
v_config_751_ = lean_ctor_get(v_val_748_, 3);
v_isSharedCheck_779_ = !lean_is_exclusive(v_val_748_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v_val_748_, 0);
lean_dec(v_unused_780_);
v___x_753_ = v_val_748_;
v_isShared_754_ = v_isSharedCheck_779_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_config_751_);
lean_inc(v_kind_750_);
lean_inc(v_name_749_);
lean_dec(v_val_748_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_779_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = l_Lake_LeanExe_keyword;
v___x_756_ = lean_name_eq(v_kind_750_, v___x_755_);
lean_dec(v_kind_750_);
if (v___x_756_ == 0)
{
lean_del_object(v___x_753_);
lean_dec(v_config_751_);
lean_dec(v_name_749_);
lean_inc_ref(v___y_696_);
v_targetMods_715_ = v_mods_744_;
v___y_716_ = v___y_696_;
v___y_717_ = v___y_697_;
v___y_718_ = v___y_698_;
v___y_719_ = v___y_699_;
v___y_720_ = v___y_700_;
v___y_721_ = v___y_701_;
goto v___jp_714_;
}
else
{
lean_object* v_root_757_; lean_object* v_keyName_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v_root_757_ = lean_ctor_get(v_config_751_, 2);
lean_inc_n(v_root_757_, 2);
v_keyName_758_ = lean_ctor_get(v_self_691_, 2);
v___x_759_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_751_);
lean_dec(v_config_751_);
lean_inc_ref(v_self_691_);
v___x_760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_760_, 0, v_self_691_);
lean_ctor_set(v___x_760_, 1, v_name_749_);
lean_ctor_set(v___x_760_, 2, v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v_root_757_);
v___x_762_ = l_Lake_Module_transImportsFacet;
lean_inc(v_keyName_758_);
v___x_763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_763_, 0, v_keyName_758_);
lean_ctor_set(v___x_763_, 1, v_root_757_);
v___x_764_ = l_Lake_Module_keyword;
lean_inc_ref(v___x_761_);
if (v_isShared_754_ == 0)
{
lean_ctor_set_tag(v___x_753_, 1);
lean_ctor_set(v___x_753_, 3, v___x_762_);
lean_ctor_set(v___x_753_, 2, v___x_761_);
lean_ctor_set(v___x_753_, 1, v___x_764_);
lean_ctor_set(v___x_753_, 0, v___x_763_);
v___x_766_ = v___x_753_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v___x_762_);
v___x_766_ = v_reuseFailAlloc_778_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; 
lean_inc_ref(v___y_696_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc(v___y_698_);
lean_inc(v___y_697_);
v___x_767_ = lean_apply_7(v___y_696_, v___x_766_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, lean_box(0));
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v_a_769_; lean_object* v___x_770_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
v_a_769_ = lean_ctor_get(v___x_767_, 1);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_767_, 2);
v___x_770_ = l_Lake_Job_await___redArg(v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v_a_772_; lean_object* v___x_773_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
v_a_772_ = lean_ctor_get(v___x_770_, 1);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_770_, 2);
v___x_773_ = lean_array_push(v_a_771_, v___x_761_);
lean_inc_ref(v___y_696_);
v_targetMods_715_ = v___x_773_;
v___y_716_ = v___y_696_;
v___y_717_ = v___y_697_;
v___y_718_ = v___y_698_;
v___y_719_ = v___y_699_;
v___y_720_ = v___y_700_;
v___y_721_ = v_a_772_;
goto v___jp_714_;
}
else
{
lean_object* v_a_774_; lean_object* v_a_775_; 
lean_dec_ref_known(v___x_761_, 2);
lean_del_object(v___x_712_);
lean_dec(v_snd_710_);
lean_dec(v_fst_709_);
lean_dec_ref(v___y_696_);
lean_dec_ref(v_self_691_);
v_a_774_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_774_);
v_a_775_ = lean_ctor_get(v___x_770_, 1);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_770_, 2);
v_a_704_ = v_a_774_;
v_a_705_ = v_a_775_;
goto v___jp_703_;
}
}
else
{
lean_object* v_a_776_; lean_object* v_a_777_; 
lean_dec_ref_known(v___x_761_, 2);
lean_del_object(v___x_712_);
lean_dec(v_snd_710_);
lean_dec(v_fst_709_);
lean_dec_ref(v___y_696_);
lean_dec_ref(v_self_691_);
v_a_776_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_776_);
v_a_777_ = lean_ctor_get(v___x_767_, 1);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_767_, 2);
v_a_704_ = v_a_776_;
v_a_705_ = v_a_777_;
goto v___jp_703_;
}
}
}
}
}
}
}
}
v___jp_703_:
{
lean_object* v___x_706_; 
v___x_706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_706_, 0, v_a_704_);
lean_ctor_set(v___x_706_, 1, v_a_705_);
return v___x_706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___boxed(lean_object* v_self_811_, lean_object* v_as_812_, lean_object* v_sz_813_, lean_object* v_i_814_, lean_object* v_b_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
size_t v_sz_boxed_823_; size_t v_i_boxed_824_; lean_object* v_res_825_; 
v_sz_boxed_823_ = lean_unbox_usize(v_sz_813_);
lean_dec(v_sz_813_);
v_i_boxed_824_ = lean_unbox_usize(v_i_814_);
lean_dec(v_i_814_);
v_res_825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3(v_self_811_, v_as_812_, v_sz_boxed_823_, v_i_boxed_824_, v_b_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v_as_812_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0(lean_object* v_self_826_, lean_object* v_defaultTargets_827_, size_t v_sz_828_, size_t v___x_829_, lean_object* v___x_830_, lean_object* v___x_831_, lean_object* v___x_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3(v_self_826_, v_defaultTargets_827_, v_sz_828_, v___x_829_, v___x_830_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_866_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_a_842_ = lean_ctor_get(v___x_840_, 1);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_866_ == 0)
{
v___x_844_ = v___x_840_;
v_isShared_845_ = v_isSharedCheck_866_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_866_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_fst_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_864_; 
v_fst_846_ = lean_ctor_get(v_a_841_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v_a_841_);
if (v_isSharedCheck_864_ == 0)
{
lean_object* v_unused_865_; 
v_unused_865_ = lean_ctor_get(v_a_841_, 1);
lean_dec(v_unused_865_);
v___x_848_ = v_a_841_;
v_isShared_849_ = v_isSharedCheck_864_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_fst_846_);
lean_dec(v_a_841_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_864_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; uint8_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_850_ = lean_mk_empty_array_with_capacity(v___x_831_);
v___x_851_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_852_ = 0;
v___x_853_ = 0;
v___x_854_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_855_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_855_, 0, v___x_850_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
lean_ctor_set(v___x_855_, 2, v___x_831_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*3, v___x_852_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*3 + 1, v___x_853_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v___x_855_);
lean_ctor_set(v___x_844_, 0, v_fst_846_);
v___x_857_ = v___x_844_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_fst_846_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_855_);
v___x_857_ = v_reuseFailAlloc_863_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_858_ = lean_task_pure(v___x_857_);
v___x_859_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v___x_832_);
lean_ctor_set(v___x_859_, 2, v___x_851_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*3, v___x_853_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v_a_842_);
lean_ctor_set(v___x_848_, 0, v___x_859_);
v___x_861_ = v___x_848_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_a_842_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
else
{
lean_object* v_a_867_; lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v___x_832_);
lean_dec(v___x_831_);
v_a_867_ = lean_ctor_get(v___x_840_, 0);
v_a_868_ = lean_ctor_get(v___x_840_, 1);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_840_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_inc(v_a_867_);
lean_dec(v___x_840_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_867_);
lean_ctor_set(v_reuseFailAlloc_874_, 1, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0___boxed(lean_object* v_self_876_, lean_object* v_defaultTargets_877_, lean_object* v_sz_878_, lean_object* v___x_879_, lean_object* v___x_880_, lean_object* v___x_881_, lean_object* v___x_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
size_t v_sz_boxed_890_; size_t v___x_15361__boxed_891_; lean_object* v_res_892_; 
v_sz_boxed_890_ = lean_unbox_usize(v_sz_878_);
lean_dec(v_sz_878_);
v___x_15361__boxed_891_ = lean_unbox_usize(v___x_879_);
lean_dec(v___x_879_);
v_res_892_ = l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0(v_self_876_, v_defaultTargets_877_, v_sz_boxed_890_, v___x_15361__boxed_891_, v___x_880_, v___x_881_, v___x_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v_defaultTargets_877_);
return v_res_892_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_box(0);
v___x_894_ = lean_unsigned_to_nat(16u);
v___x_895_ = lean_mk_array(v___x_894_, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v_seen_898_; 
v___x_896_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0);
v___x_897_ = lean_unsigned_to_nat(0u);
v_seen_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_seen_898_, 0, v___x_897_);
lean_ctor_set(v_seen_898_, 1, v___x_896_);
return v_seen_898_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2(void){
_start:
{
lean_object* v_seen_899_; lean_object* v_mods_900_; lean_object* v___x_901_; 
v_seen_899_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1, &l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1);
v_mods_900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__0));
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v_mods_900_);
lean_ctor_set(v___x_901_, 1, v_seen_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules(lean_object* v_self_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_defaultTargets_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; size_t v_sz_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___f_919_; lean_object* v___x_920_; 
v_defaultTargets_912_ = lean_ctor_get(v_self_904_, 17);
lean_inc_ref(v_defaultTargets_912_);
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_box(0);
v___x_915_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2);
v_sz_916_ = lean_array_size(v_defaultTargets_912_);
v___x_917_ = lean_box_usize(v_sz_916_);
v___x_918_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___boxed__const__1));
v___f_919_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0___boxed), 14, 7);
lean_closure_set(v___f_919_, 0, v_self_904_);
lean_closure_set(v___f_919_, 1, v_defaultTargets_912_);
lean_closure_set(v___f_919_, 2, v___x_917_);
lean_closure_set(v___f_919_, 3, v___x_918_);
lean_closure_set(v___f_919_, 4, v___x_915_);
lean_closure_set(v___f_919_, 5, v___x_913_);
lean_closure_set(v___f_919_, 6, v___x_914_);
v___x_920_ = l_Lake_ensureJob___redArg(v___x_914_, v___f_919_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___boxed(lean_object* v_self_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules(v_self_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec(v_a_924_);
lean_dec(v_a_923_);
return v_res_929_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0(lean_object* v_00_u03b2_930_, lean_object* v_m_931_, lean_object* v_a_932_){
_start:
{
uint8_t v___x_933_; 
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(v_m_931_, v_a_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___boxed(lean_object* v_00_u03b2_934_, lean_object* v_m_935_, lean_object* v_a_936_){
_start:
{
uint8_t v_res_937_; lean_object* v_r_938_; 
v_res_937_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0(v_00_u03b2_934_, v_m_935_, v_a_936_);
lean_dec_ref(v_a_936_);
lean_dec_ref(v_m_935_);
v_r_938_ = lean_box(v_res_937_);
return v_r_938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1(lean_object* v_00_u03b2_939_, lean_object* v_m_940_, lean_object* v_a_941_, lean_object* v_b_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1___redArg(v_m_940_, v_a_941_, v_b_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2(lean_object* v_as_944_, size_t v_sz_945_, size_t v_i_946_, lean_object* v_b_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(v_as_944_, v_sz_945_, v_i_946_, v_b_947_, v___y_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___boxed(lean_object* v_as_956_, lean_object* v_sz_957_, lean_object* v_i_958_, lean_object* v_b_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
size_t v_sz_boxed_967_; size_t v_i_boxed_968_; lean_object* v_res_969_; 
v_sz_boxed_967_ = lean_unbox_usize(v_sz_957_);
lean_dec(v_sz_957_);
v_i_boxed_968_ = lean_unbox_usize(v_i_958_);
lean_dec(v_i_958_);
v_res_969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2(v_as_956_, v_sz_boxed_967_, v_i_boxed_968_, v_b_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec_ref(v_as_956_);
return v_res_969_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0(lean_object* v_00_u03b2_970_, lean_object* v_a_971_, lean_object* v_x_972_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_971_, v_x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___boxed(lean_object* v_00_u03b2_974_, lean_object* v_a_975_, lean_object* v_x_976_){
_start:
{
uint8_t v_res_977_; lean_object* v_r_978_; 
v_res_977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0(v_00_u03b2_974_, v_a_975_, v_x_976_);
lean_dec(v_x_976_);
lean_dec_ref(v_a_975_);
v_r_978_ = lean_box(v_res_977_);
return v_r_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2(lean_object* v_00_u03b2_979_, lean_object* v_data_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2___redArg(v_data_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_982_, lean_object* v_i_983_, lean_object* v_source_984_, lean_object* v_target_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3___redArg(v_i_983_, v_source_984_, v_target_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_987_, lean_object* v_x_988_, lean_object* v_x_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6___redArg(v_x_988_, v_x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0(lean_object* v_as_991_, size_t v_i_992_, size_t v_stop_993_, lean_object* v_b_994_){
_start:
{
uint8_t v___x_995_; 
v___x_995_ = lean_usize_dec_eq(v_i_992_, v_stop_993_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v_name_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; size_t v___x_1003_; size_t v___x_1004_; 
v___x_996_ = lean_array_uget_borrowed(v_as_991_, v_i_992_);
v_name_997_ = lean_ctor_get(v___x_996_, 1);
v___x_998_ = 1;
lean_inc(v_name_997_);
v___x_999_ = l_Lean_Name_toString(v_name_997_, v___x_998_);
v___x_1000_ = lean_string_append(v_b_994_, v___x_999_);
lean_dec_ref(v___x_999_);
v___x_1001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0));
v___x_1002_ = lean_string_append(v___x_1000_, v___x_1001_);
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_add(v_i_992_, v___x_1003_);
v_i_992_ = v___x_1004_;
v_b_994_ = v___x_1002_;
goto _start;
}
else
{
return v_b_994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_1006_, lean_object* v_i_1007_, lean_object* v_stop_1008_, lean_object* v_b_1009_){
_start:
{
size_t v_i_boxed_1010_; size_t v_stop_boxed_1011_; lean_object* v_res_1012_; 
v_i_boxed_1010_ = lean_unbox_usize(v_i_1007_);
lean_dec(v_i_1007_);
v_stop_boxed_1011_ = lean_unbox_usize(v_stop_1008_);
lean_dec(v_stop_1008_);
v_res_1012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0(v_as_1006_, v_i_boxed_1010_, v_stop_boxed_1011_, v_b_1009_);
lean_dec_ref(v_as_1006_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2(size_t v_sz_1013_, size_t v_i_1014_, lean_object* v_bs_1015_){
_start:
{
uint8_t v___x_1016_; 
v___x_1016_ = lean_usize_dec_lt(v_i_1014_, v_sz_1013_);
if (v___x_1016_ == 0)
{
return v_bs_1015_;
}
else
{
lean_object* v_v_1017_; lean_object* v_name_1018_; lean_object* v___x_1019_; lean_object* v_bs_x27_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; lean_object* v___x_1025_; 
v_v_1017_ = lean_array_uget_borrowed(v_bs_1015_, v_i_1014_);
v_name_1018_ = lean_ctor_get(v_v_1017_, 1);
lean_inc(v_name_1018_);
v___x_1019_ = lean_unsigned_to_nat(0u);
v_bs_x27_1020_ = lean_array_uset(v_bs_1015_, v_i_1014_, v___x_1019_);
v___x_1021_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1018_, v___x_1016_);
v___x_1022_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
v___x_1023_ = ((size_t)1ULL);
v___x_1024_ = lean_usize_add(v_i_1014_, v___x_1023_);
v___x_1025_ = lean_array_uset(v_bs_x27_1020_, v_i_1014_, v___x_1022_);
v_i_1014_ = v___x_1024_;
v_bs_1015_ = v___x_1025_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_1027_, lean_object* v_i_1028_, lean_object* v_bs_1029_){
_start:
{
size_t v_sz_boxed_1030_; size_t v_i_boxed_1031_; lean_object* v_res_1032_; 
v_sz_boxed_1030_ = lean_unbox_usize(v_sz_1027_);
lean_dec(v_sz_1027_);
v_i_boxed_1031_ = lean_unbox_usize(v_i_1028_);
lean_dec(v_i_1028_);
v_res_1032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_1030_, v_i_boxed_1031_, v_bs_1029_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1(lean_object* v_a_1033_){
_start:
{
size_t v_sz_1034_; size_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_sz_1034_ = lean_array_size(v_a_1033_);
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2(v_sz_1034_, v___x_1035_, v_a_1033_);
v___x_1037_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0(uint8_t v_fmt_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___y_1041_; 
if (v_fmt_1038_ == 0)
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1048_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1049_ = lean_unsigned_to_nat(0u);
v___x_1050_ = lean_array_get_size(v_a_1039_);
v___x_1051_ = lean_nat_dec_lt(v___x_1049_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_dec_ref(v_a_1039_);
v___y_1041_ = v___x_1048_;
goto v___jp_1040_;
}
else
{
size_t v___x_1052_; size_t v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = ((size_t)0ULL);
v___x_1053_ = lean_usize_of_nat(v___x_1050_);
v___x_1054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0(v_a_1039_, v___x_1052_, v___x_1053_, v___x_1048_);
lean_dec_ref(v_a_1039_);
v___y_1041_ = v___x_1054_;
goto v___jp_1040_;
}
}
else
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = l_Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1(v_a_1039_);
v___x_1056_ = l_Lean_Json_compress(v___x_1055_);
return v___x_1056_;
}
v___jp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1042_ = lean_unsigned_to_nat(1u);
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = lean_string_utf8_byte_size(v___y_1041_);
lean_inc_ref(v___y_1041_);
v___x_1045_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1045_, 0, v___y_1041_);
lean_ctor_set(v___x_1045_, 1, v___x_1043_);
lean_ctor_set(v___x_1045_, 2, v___x_1044_);
v___x_1046_ = l_String_Slice_Pos_prevn(v___x_1045_, v___x_1044_, v___x_1042_);
lean_dec_ref_known(v___x_1045_, 3);
v___x_1047_ = lean_string_utf8_extract_fast(v___y_1041_, v___x_1043_, v___x_1046_);
lean_dec(v___x_1046_);
lean_dec_ref(v___y_1041_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0___boxed(lean_object* v_fmt_1057_, lean_object* v_a_1058_){
_start:
{
uint8_t v_fmt_boxed_1059_; lean_object* v_res_1060_; 
v_fmt_boxed_1059_ = lean_unbox(v_fmt_1057_);
v_res_1060_ = l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0(v_fmt_boxed_1059_, v_a_1058_);
return v_res_1060_;
}
}
static lean_object* _init_l_Lake_Package_defaultModulesFacetConfig___closed__2(void){
_start:
{
uint8_t v___x_1063_; lean_object* v___f_1064_; uint8_t v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1063_ = 1;
v___f_1064_ = ((lean_object*)(l_Lake_Package_defaultModulesFacetConfig___closed__0));
v___x_1065_ = 0;
v___x_1066_ = lean_box(0);
v___x_1067_ = ((lean_object*)(l_Lake_Package_defaultModulesFacetConfig___closed__1));
v___x_1068_ = l_Lake_Package_keyword;
v___x_1069_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1067_);
lean_ctor_set(v___x_1069_, 2, v___x_1066_);
lean_ctor_set(v___x_1069_, 3, v___f_1064_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*4, v___x_1065_);
lean_ctor_set_uint8(v___x_1069_, sizeof(void*)*4 + 1, v___x_1063_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lake_Package_defaultModulesFacetConfig(void){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_obj_once(&l_Lake_Package_defaultModulesFacetConfig___closed__2, &l_Lake_Package_defaultModulesFacetConfig___closed__2_once, _init_l_Lake_Package_defaultModulesFacetConfig___closed__2);
return v___x_1070_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_1072_; lean_object* v___f_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1072_ = 1;
v___f_1073_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__0));
v___x_1074_ = 0;
v___x_1075_ = lean_box(0);
v___x_1076_ = ((lean_object*)(l_Lake_Package_transDepsFacetConfig___closed__0));
v___x_1077_ = l_Lake_Package_keyword;
v___x_1078_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1076_);
lean_ctor_set(v___x_1078_, 2, v___x_1075_);
lean_ctor_set(v___x_1078_, 3, v___f_1073_);
lean_ctor_set_uint8(v___x_1078_, sizeof(void*)*4, v___x_1074_);
lean_ctor_set_uint8(v___x_1078_, sizeof(void*)*4 + 1, v___x_1072_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig(void){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_obj_once(&l_Lake_Package_transDepsFacetConfig___closed__1, &l_Lake_Package_transDepsFacetConfig___closed__1_once, _init_l_Lake_Package_transDepsFacetConfig___closed__1);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object* v_self_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_config_1088_; uint8_t v_preferReleaseBuild_1089_; 
v_config_1088_ = lean_ctor_get(v_self_1080_, 6);
v_preferReleaseBuild_1089_ = lean_ctor_get_uint8(v_config_1088_, sizeof(void*)*28 + 2);
if (v_preferReleaseBuild_1089_ == 0)
{
lean_object* v_keyName_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_keyName_1090_ = lean_ctor_get(v_self_1080_, 2);
v___x_1091_ = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(v_keyName_1090_);
v___x_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_keyName_1090_);
v___x_1093_ = l_Lake_Package_keyword;
v___x_1094_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
lean_ctor_set(v___x_1094_, 2, v_self_1080_);
lean_ctor_set(v___x_1094_, 3, v___x_1091_);
lean_inc_ref(v_a_1085_);
lean_inc(v_a_1084_);
lean_inc(v_a_1083_);
lean_inc(v_a_1082_);
v___x_1095_ = lean_apply_7(v_a_1081_, v___x_1094_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, lean_box(0));
return v___x_1095_;
}
else
{
lean_object* v_keyName_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_keyName_1096_ = lean_ctor_get(v_self_1080_, 2);
v___x_1097_ = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(v_keyName_1096_);
v___x_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1098_, 0, v_keyName_1096_);
v___x_1099_ = l_Lake_Package_keyword;
v___x_1100_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
lean_ctor_set(v___x_1100_, 2, v_self_1080_);
lean_ctor_set(v___x_1100_, 3, v___x_1097_);
lean_inc_ref(v_a_1085_);
lean_inc(v_a_1084_);
lean_inc(v_a_1083_);
lean_inc(v_a_1082_);
v___x_1101_ = lean_apply_7(v_a_1081_, v___x_1100_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, lean_box(0));
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___boxed(lean_object* v_self_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(v_self_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec(v_a_1104_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t v_fmt_1113_, uint8_t v_a_1114_){
_start:
{
if (v_fmt_1113_ == 0)
{
if (v_a_1114_ == 0)
{
lean_object* v___x_1115_; 
v___x_1115_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0));
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; 
v___x_1116_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1));
return v___x_1116_;
}
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1117_, 0, v_a_1114_);
v___x_1118_ = l_Lean_Json_compress(v___x_1117_);
return v___x_1118_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object* v_fmt_1119_, lean_object* v_a_1120_){
_start:
{
uint8_t v_fmt_boxed_1121_; uint8_t v_a_boxed_1122_; lean_object* v_res_1123_; 
v_fmt_boxed_1121_ = lean_unbox(v_fmt_1119_);
v_a_boxed_1122_ = lean_unbox(v_a_1120_);
v_res_1123_ = l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(v_fmt_boxed_1121_, v_a_boxed_1122_);
return v_res_1123_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1126_; uint8_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___f_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___f_1126_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_1127_ = 1;
v___x_1128_ = l_Lake_instDataKindBool;
v___f_1129_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__0));
v___x_1130_ = l_Lake_Package_keyword;
v___x_1131_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v___f_1129_);
lean_ctor_set(v___x_1131_, 2, v___x_1128_);
lean_ctor_set(v___x_1131_, 3, v___f_1126_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*4, v___x_1127_);
lean_ctor_set_uint8(v___x_1131_, sizeof(void*)*4 + 1, v___x_1127_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig(void){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_obj_once(&l_Lake_Package_optBuildCacheFacetConfig___closed__2, &l_Lake_Package_optBuildCacheFacetConfig___closed__2_once, _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(lean_object* v_self_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v___y_1144_; uint8_t v___y_1145_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1168_; uint8_t v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v_toContext_1175_; lean_object* v_lakeEnv_1176_; uint8_t v_noCache_1177_; lean_object* v_toolchain_1178_; uint8_t v_a_1180_; lean_object* v_a_1181_; 
v_toContext_1175_ = lean_ctor_get(v_a_1140_, 1);
v_lakeEnv_1176_ = lean_ctor_get(v_toContext_1175_, 0);
v_noCache_1177_ = lean_ctor_get_uint8(v_lakeEnv_1176_, sizeof(void*)*20);
v_toolchain_1178_ = lean_ctor_get(v_lakeEnv_1176_, 19);
if (v_noCache_1177_ == 0)
{
uint8_t v___x_1196_; 
v___x_1196_ = 1;
v_a_1180_ = v___x_1196_;
v_a_1181_ = v_a_1141_;
goto v___jp_1179_;
}
else
{
uint8_t v___x_1197_; 
v___x_1197_ = 0;
v_a_1180_ = v___x_1197_;
v_a_1181_ = v_a_1141_;
goto v___jp_1179_;
}
v___jp_1143_:
{
uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1146_ = 1;
v___x_1147_ = lean_box(0);
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1150_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1151_ = 0;
v___x_1152_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_1153_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1153_, 0, v___x_1149_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
lean_ctor_set(v___x_1153_, 2, v___x_1148_);
lean_ctor_set_uint8(v___x_1153_, sizeof(void*)*3, v___x_1151_);
lean_ctor_set_uint8(v___x_1153_, sizeof(void*)*3 + 1, v___y_1145_);
v___x_1154_ = lean_box(v___x_1146_);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
lean_ctor_set(v___x_1155_, 1, v___x_1153_);
v___x_1156_ = lean_task_pure(v___x_1155_);
v___x_1157_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set(v___x_1157_, 1, v___x_1147_);
lean_ctor_set(v___x_1157_, 2, v___x_1150_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*3, v___y_1145_);
v___x_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v___y_1144_);
return v___x_1158_;
}
v___jp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1162_ = l_Lake_Package_optBuildCacheFacet;
v___x_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___y_1161_);
v___x_1164_ = l_Lake_Package_keyword;
v___x_1165_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1163_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
lean_ctor_set(v___x_1165_, 2, v_self_1135_);
lean_ctor_set(v___x_1165_, 3, v___x_1162_);
lean_inc_ref(v_a_1140_);
lean_inc(v_a_1139_);
lean_inc(v_a_1138_);
lean_inc(v_a_1137_);
v___x_1166_ = lean_apply_7(v_a_1136_, v___x_1165_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v___y_1160_, lean_box(0));
return v___x_1166_;
}
v___jp_1167_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v___x_1172_ = lean_string_utf8_byte_size(v___y_1170_);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_nat_dec_eq(v___x_1172_, v___x_1173_);
if (v___x_1174_ == 0)
{
v___y_1160_ = v___y_1168_;
v___y_1161_ = v___y_1171_;
goto v___jp_1159_;
}
else
{
lean_dec(v___y_1171_);
lean_dec_ref(v_a_1136_);
lean_dec_ref(v_self_1135_);
v___y_1144_ = v___y_1168_;
v___y_1145_ = v___y_1169_;
goto v___jp_1143_;
}
}
v___jp_1179_:
{
lean_object* v_config_1182_; lean_object* v_keyName_1183_; lean_object* v_dir_1184_; lean_object* v_scope_1185_; lean_object* v_buildDir_1186_; uint8_t v_preferReleaseBuild_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; 
v_config_1182_ = lean_ctor_get(v_self_1135_, 6);
v_keyName_1183_ = lean_ctor_get(v_self_1135_, 2);
v_dir_1184_ = lean_ctor_get(v_self_1135_, 4);
v_scope_1185_ = lean_ctor_get(v_self_1135_, 10);
v_buildDir_1186_ = lean_ctor_get(v_config_1182_, 5);
v_preferReleaseBuild_1187_ = lean_ctor_get_uint8(v_config_1182_, sizeof(void*)*28 + 2);
lean_inc_ref(v_buildDir_1186_);
v___x_1188_ = l_System_FilePath_normalize(v_buildDir_1186_);
lean_inc_ref(v_dir_1184_);
v___x_1189_ = l_Lake_joinRelative(v_dir_1184_, v___x_1188_);
v___x_1190_ = l_System_FilePath_pathExists(v___x_1189_);
lean_dec_ref(v___x_1189_);
if (v_a_1180_ == 0)
{
lean_dec_ref(v_a_1136_);
lean_dec_ref(v_self_1135_);
v___y_1144_ = v_a_1181_;
v___y_1145_ = v_a_1180_;
goto v___jp_1143_;
}
else
{
if (v___x_1190_ == 0)
{
if (v_preferReleaseBuild_1187_ == 0)
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0));
v___x_1192_ = lean_string_dec_eq(v_scope_1185_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1));
v___x_1194_ = lean_string_dec_eq(v_scope_1185_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_dec_ref(v_a_1136_);
lean_dec_ref(v_self_1135_);
v___y_1144_ = v_a_1181_;
v___y_1145_ = v___x_1194_;
goto v___jp_1143_;
}
else
{
lean_inc(v_keyName_1183_);
v___y_1168_ = v_a_1181_;
v___y_1169_ = v_preferReleaseBuild_1187_;
v___y_1170_ = v_toolchain_1178_;
v___y_1171_ = v_keyName_1183_;
goto v___jp_1167_;
}
}
else
{
lean_inc(v_keyName_1183_);
v___y_1168_ = v_a_1181_;
v___y_1169_ = v_preferReleaseBuild_1187_;
v___y_1170_ = v_toolchain_1178_;
v___y_1171_ = v_keyName_1183_;
goto v___jp_1167_;
}
}
else
{
lean_inc(v_keyName_1183_);
v___y_1160_ = v_a_1181_;
v___y_1161_ = v_keyName_1183_;
goto v___jp_1159_;
}
}
else
{
uint8_t v___x_1195_; 
lean_dec_ref(v_a_1136_);
lean_dec_ref(v_self_1135_);
v___x_1195_ = 0;
v___y_1144_ = v_a_1181_;
v___y_1145_ = v___x_1195_;
goto v___jp_1143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___boxed(lean_object* v_self_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec(v_a_1200_);
return v_res_1206_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0(void){
_start:
{
uint8_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = 2;
v___x_1208_ = l_Lake_Verbosity_ctorIdx(v___x_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object* v_self_1213_, lean_object* v_facet_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v_toBuildConfig_1218_; uint8_t v_verbosity_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v_toBuildConfig_1218_ = lean_ctor_get(v_a_1215_, 0);
v_verbosity_1219_ = lean_ctor_get_uint8(v_toBuildConfig_1218_, sizeof(void*)*4 + 4);
v___x_1220_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1219_);
v___x_1221_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_1222_ = lean_nat_dec_eq(v___x_1220_, v___x_1221_);
lean_dec(v___x_1220_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec(v_facet_1214_);
lean_dec_ref(v_self_1213_);
v___x_1223_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v_a_1216_);
return v___x_1224_;
}
else
{
lean_object* v_baseName_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v_baseName_1225_ = lean_ctor_get(v_self_1213_, 1);
lean_inc(v_baseName_1225_);
lean_dec_ref(v_self_1213_);
v___x_1226_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1227_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1225_, v___x_1222_);
v___x_1228_ = lean_string_append(v___x_1226_, v___x_1227_);
lean_dec_ref(v___x_1227_);
v___x_1229_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1230_ = lean_string_append(v___x_1228_, v___x_1229_);
v___x_1231_ = l_Lake_Name_eraseHead(v_facet_1214_);
v___x_1232_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1231_, v___x_1222_);
v___x_1233_ = lean_string_append(v___x_1230_, v___x_1232_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_1235_ = lean_string_append(v___x_1233_, v___x_1234_);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v_a_1216_);
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* v_self_1237_, lean_object* v_facet_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(v_self_1237_, v_facet_1238_, v_a_1239_, v_a_1240_);
lean_dec_ref(v_a_1239_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* v_self_1243_, lean_object* v_facet_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_toBuildConfig_1252_; uint8_t v_verbosity_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_toBuildConfig_1252_ = lean_ctor_get(v_a_1249_, 0);
v_verbosity_1253_ = lean_ctor_get_uint8(v_toBuildConfig_1252_, sizeof(void*)*4 + 4);
v___x_1254_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1253_);
v___x_1255_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_1256_ = lean_nat_dec_eq(v___x_1254_, v___x_1255_);
lean_dec(v___x_1254_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_dec(v_facet_1244_);
lean_dec_ref(v_self_1243_);
v___x_1257_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v_a_1250_);
return v___x_1258_;
}
else
{
lean_object* v_baseName_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_baseName_1259_ = lean_ctor_get(v_self_1243_, 1);
lean_inc(v_baseName_1259_);
lean_dec_ref(v_self_1243_);
v___x_1260_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1261_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1259_, v___x_1256_);
v___x_1262_ = lean_string_append(v___x_1260_, v___x_1261_);
lean_dec_ref(v___x_1261_);
v___x_1263_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1264_ = lean_string_append(v___x_1262_, v___x_1263_);
v___x_1265_ = l_Lake_Name_eraseHead(v_facet_1244_);
v___x_1266_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1265_, v___x_1256_);
v___x_1267_ = lean_string_append(v___x_1264_, v___x_1266_);
lean_dec_ref(v___x_1266_);
v___x_1268_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_1269_ = lean_string_append(v___x_1267_, v___x_1268_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v_a_1250_);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* v_self_1271_, lean_object* v_facet_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(v_self_1271_, v_facet_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
return v_res_1280_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_1284_ = l_Lake_Name_eraseHead(v___x_1283_);
return v___x_1284_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_1286_ = l_Lake_Name_eraseHead(v___x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(lean_object* v_self_1287_, uint8_t v_success_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_a_1297_; lean_object* v_a_1298_; lean_object* v_a_1319_; lean_object* v_a_1320_; 
if (v_success_1288_ == 0)
{
lean_object* v_config_1340_; uint8_t v_preferReleaseBuild_1341_; 
v_config_1340_ = lean_ctor_get(v_self_1287_, 6);
v_preferReleaseBuild_1341_ = lean_ctor_get_uint8(v_config_1340_, sizeof(void*)*28 + 2);
if (v_preferReleaseBuild_1341_ == 0)
{
lean_object* v_toBuildConfig_1342_; lean_object* v_baseName_1343_; uint8_t v_verbosity_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v_toBuildConfig_1342_ = lean_ctor_get(v___y_1293_, 0);
v_baseName_1343_ = lean_ctor_get(v_self_1287_, 1);
lean_inc(v_baseName_1343_);
lean_dec_ref(v_self_1287_);
v_verbosity_1344_ = lean_ctor_get_uint8(v_toBuildConfig_1342_, sizeof(void*)*4 + 4);
v___x_1345_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1344_);
v___x_1346_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_1347_ = lean_nat_dec_eq(v___x_1345_, v___x_1346_);
lean_dec(v___x_1345_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
lean_dec(v_baseName_1343_);
v___x_1348_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_1297_ = v___x_1348_;
v_a_1298_ = v___y_1294_;
goto v___jp_1296_;
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1349_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1350_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1343_, v___x_1347_);
v___x_1351_ = lean_string_append(v___x_1349_, v___x_1350_);
lean_dec_ref(v___x_1350_);
v___x_1352_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1353_ = lean_string_append(v___x_1351_, v___x_1352_);
v___x_1354_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2);
v___x_1355_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1354_, v___x_1347_);
v___x_1356_ = lean_string_append(v___x_1353_, v___x_1355_);
lean_dec_ref(v___x_1355_);
v___x_1357_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_1358_ = lean_string_append(v___x_1356_, v___x_1357_);
v_a_1297_ = v___x_1358_;
v_a_1298_ = v___y_1294_;
goto v___jp_1296_;
}
}
else
{
lean_object* v_toBuildConfig_1359_; lean_object* v_baseName_1360_; uint8_t v_verbosity_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v_toBuildConfig_1359_ = lean_ctor_get(v___y_1293_, 0);
v_baseName_1360_ = lean_ctor_get(v_self_1287_, 1);
lean_inc(v_baseName_1360_);
lean_dec_ref(v_self_1287_);
v_verbosity_1361_ = lean_ctor_get_uint8(v_toBuildConfig_1359_, sizeof(void*)*4 + 4);
v___x_1362_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1361_);
v___x_1363_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_1364_ = lean_nat_dec_eq(v___x_1362_, v___x_1363_);
lean_dec(v___x_1362_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; 
lean_dec(v_baseName_1360_);
v___x_1365_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_1319_ = v___x_1365_;
v_a_1320_ = v___y_1294_;
goto v___jp_1318_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1366_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1367_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1360_, v___x_1364_);
v___x_1368_ = lean_string_append(v___x_1366_, v___x_1367_);
lean_dec_ref(v___x_1367_);
v___x_1369_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1370_ = lean_string_append(v___x_1368_, v___x_1369_);
v___x_1371_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
v___x_1372_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1371_, v___x_1364_);
v___x_1373_ = lean_string_append(v___x_1370_, v___x_1372_);
lean_dec_ref(v___x_1372_);
v___x_1374_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_1375_ = lean_string_append(v___x_1373_, v___x_1374_);
v_a_1319_ = v___x_1375_;
v_a_1320_ = v___y_1294_;
goto v___jp_1318_;
}
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec_ref(v_self_1287_);
v___x_1376_ = lean_box(0);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
lean_ctor_set(v___x_1377_, 1, v___y_1294_);
return v___x_1377_;
}
v___jp_1296_:
{
lean_object* v_log_1299_; uint8_t v_action_1300_; uint8_t v_wantsRebuild_1301_; lean_object* v_trace_1302_; lean_object* v_buildTime_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1317_; 
v_log_1299_ = lean_ctor_get(v_a_1298_, 0);
v_action_1300_ = lean_ctor_get_uint8(v_a_1298_, sizeof(void*)*3);
v_wantsRebuild_1301_ = lean_ctor_get_uint8(v_a_1298_, sizeof(void*)*3 + 1);
v_trace_1302_ = lean_ctor_get(v_a_1298_, 1);
v_buildTime_1303_ = lean_ctor_get(v_a_1298_, 2);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_a_1298_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1305_ = v_a_1298_;
v_isShared_1306_ = v_isSharedCheck_1317_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_buildTime_1303_);
lean_inc(v_trace_1302_);
lean_inc(v_log_1299_);
lean_dec(v_a_1298_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1317_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1307_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0));
v___x_1308_ = lean_string_append(v___x_1307_, v_a_1297_);
lean_dec_ref(v_a_1297_);
v___x_1309_ = 0;
v___x_1310_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1310_, 0, v___x_1308_);
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*1, v___x_1309_);
v___x_1311_ = lean_box(0);
v___x_1312_ = lean_array_push(v_log_1299_, v___x_1310_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 0, v___x_1312_);
v___x_1314_ = v___x_1305_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_trace_1302_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_buildTime_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1316_, sizeof(void*)*3, v_action_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1316_, sizeof(void*)*3 + 1, v_wantsRebuild_1301_);
v___x_1314_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1311_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
return v___x_1315_;
}
}
}
v___jp_1318_:
{
lean_object* v_log_1321_; uint8_t v_action_1322_; uint8_t v_wantsRebuild_1323_; lean_object* v_trace_1324_; lean_object* v_buildTime_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1339_; 
v_log_1321_ = lean_ctor_get(v_a_1320_, 0);
v_action_1322_ = lean_ctor_get_uint8(v_a_1320_, sizeof(void*)*3);
v_wantsRebuild_1323_ = lean_ctor_get_uint8(v_a_1320_, sizeof(void*)*3 + 1);
v_trace_1324_ = lean_ctor_get(v_a_1320_, 1);
v_buildTime_1325_ = lean_ctor_get(v_a_1320_, 2);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_a_1320_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1327_ = v_a_1320_;
v_isShared_1328_ = v_isSharedCheck_1339_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_buildTime_1325_);
lean_inc(v_trace_1324_);
lean_inc(v_log_1321_);
lean_dec(v_a_1320_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1339_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1329_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1));
v___x_1330_ = lean_string_append(v___x_1329_, v_a_1319_);
lean_dec_ref(v_a_1319_);
v___x_1331_ = 2;
v___x_1332_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set_uint8(v___x_1332_, sizeof(void*)*1, v___x_1331_);
v___x_1333_ = lean_box(0);
v___x_1334_ = lean_array_push(v_log_1321_, v___x_1332_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1334_);
v___x_1336_ = v___x_1327_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_trace_1324_);
lean_ctor_set(v_reuseFailAlloc_1338_, 2, v_buildTime_1325_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, sizeof(void*)*3, v_action_1322_);
lean_ctor_set_uint8(v_reuseFailAlloc_1338_, sizeof(void*)*3 + 1, v_wantsRebuild_1323_);
v___x_1336_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1333_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
return v___x_1337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* v_self_1378_, lean_object* v_success_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
uint8_t v_success_boxed_1387_; lean_object* v_res_1388_; 
v_success_boxed_1387_ = lean_unbox(v_success_1379_);
v_res_1388_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(v_self_1378_, v_success_boxed_1387_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* v_self_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v___x_1397_; 
lean_inc_ref(v_a_1390_);
lean_inc_ref(v_self_1389_);
v___x_1397_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1412_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_a_1399_ = lean_ctor_get(v___x_1397_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1401_ = v___x_1397_;
v_isShared_1402_ = v_isSharedCheck_1412_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1412_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___f_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___f_1403_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(v___f_1403_, 0, v_self_1389_);
v___x_1404_ = l_Lake_instDataKindUnit;
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = 0;
v___x_1407_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_1408_ = l_Lake_Job_mapM___redArg(v___x_1404_, v_a_1398_, v___f_1403_, v___x_1405_, v___x_1406_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v___x_1407_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1408_);
v___x_1410_ = v___x_1401_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_a_1399_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec_ref(v_a_1390_);
lean_dec_ref(v_self_1389_);
v_a_1413_ = lean_ctor_get(v___x_1397_, 0);
v_a_1414_ = lean_ctor_get(v___x_1397_, 1);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1397_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_inc(v_a_1413_);
lean_dec(v___x_1397_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1413_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(lean_object* v_self_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec(v_a_1425_);
lean_dec(v_a_1424_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* v_self_1431_, lean_object* v_as_1432_, size_t v_sz_1433_, size_t v_i_1434_, lean_object* v_b_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
uint8_t v___x_1443_; 
v___x_1443_ = lean_usize_dec_lt(v_i_1434_, v_sz_1433_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; 
lean_dec_ref(v___y_1436_);
lean_dec_ref(v_self_1431_);
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v_b_1435_);
lean_ctor_set(v___x_1444_, 1, v___y_1441_);
return v___x_1444_;
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1446_; 
v_a_1445_ = lean_array_uget_borrowed(v_as_1432_, v_i_1434_);
lean_inc_ref(v___y_1436_);
lean_inc(v_a_1445_);
lean_inc_ref(v_self_1431_);
v___x_1446_ = l_Lake_Package_fetchTargetJob(v_self_1431_, v_a_1445_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v_a_1447_; lean_object* v_a_1448_; lean_object* v___x_1449_; size_t v___x_1450_; size_t v___x_1451_; 
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_a_1447_);
v_a_1448_ = lean_ctor_get(v___x_1446_, 1);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1446_, 2);
v___x_1449_ = l_Lake_Job_mix___redArg(v_b_1435_, v_a_1447_);
v___x_1450_ = ((size_t)1ULL);
v___x_1451_ = lean_usize_add(v_i_1434_, v___x_1450_);
v_i_1434_ = v___x_1451_;
v_b_1435_ = v___x_1449_;
v___y_1441_ = v_a_1448_;
goto _start;
}
else
{
lean_object* v_a_1453_; lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec_ref(v___y_1436_);
lean_dec_ref(v_b_1435_);
lean_dec_ref(v_self_1431_);
v_a_1453_ = lean_ctor_get(v___x_1446_, 0);
v_a_1454_ = lean_ctor_get(v___x_1446_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1446_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_inc(v_a_1453_);
lean_dec(v___x_1446_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1453_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* v_self_1462_, lean_object* v_as_1463_, lean_object* v_sz_1464_, lean_object* v_i_1465_, lean_object* v_b_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
size_t v_sz_boxed_1474_; size_t v_i_boxed_1475_; lean_object* v_res_1476_; 
v_sz_boxed_1474_ = lean_unbox_usize(v_sz_1464_);
lean_dec(v_sz_1464_);
v_i_boxed_1475_ = lean_unbox_usize(v_i_1465_);
lean_dec(v_i_1465_);
v_res_1476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1462_, v_as_1463_, v_sz_boxed_1474_, v_i_boxed_1475_, v_b_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v_as_1463_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object* v_config_1477_, lean_object* v_self_1478_, lean_object* v_____r_1479_, lean_object* v_job_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_extraDepTargets_1488_; size_t v_sz_1489_; size_t v___x_1490_; lean_object* v___x_1491_; 
v_extraDepTargets_1488_ = lean_ctor_get(v_config_1477_, 2);
v_sz_1489_ = lean_array_size(v_extraDepTargets_1488_);
v___x_1490_ = ((size_t)0ULL);
v___x_1491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1478_, v_extraDepTargets_1488_, v_sz_1489_, v___x_1490_, v_job_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object* v_config_1492_, lean_object* v_self_1493_, lean_object* v_____r_1494_, lean_object* v_job_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(v_config_1492_, v_self_1493_, v_____r_1494_, v_job_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v_config_1492_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(uint8_t v___x_1504_, lean_object* v_self_1505_, lean_object* v_job_1506_, lean_object* v___f_1507_, lean_object* v___x_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
if (v___x_1504_ == 0)
{
lean_object* v___x_1516_; 
lean_inc_ref(v___y_1509_);
v___x_1516_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1505_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v_a_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
v_a_1518_ = lean_ctor_get(v___x_1516_, 1);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1516_, 2);
v___x_1519_ = l_Lake_Job_add___redArg(v_job_1506_, v_a_1517_);
lean_inc_ref(v___y_1513_);
lean_inc(v___y_1512_);
lean_inc(v___y_1511_);
lean_inc(v___y_1510_);
v___x_1520_ = lean_apply_9(v___f_1507_, v___x_1508_, v___x_1519_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v_a_1518_, lean_box(0));
return v___x_1520_;
}
else
{
lean_dec_ref(v___y_1509_);
lean_dec_ref(v___f_1507_);
lean_dec_ref(v_job_1506_);
return v___x_1516_;
}
}
else
{
lean_object* v___x_1521_; 
lean_dec_ref(v_self_1505_);
lean_inc_ref(v___y_1513_);
lean_inc(v___y_1512_);
lean_inc(v___y_1511_);
lean_inc(v___y_1510_);
v___x_1521_ = lean_apply_9(v___f_1507_, v___x_1508_, v_job_1506_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, lean_box(0));
return v___x_1521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* v___x_1522_, lean_object* v_self_1523_, lean_object* v_job_1524_, lean_object* v___f_1525_, lean_object* v___x_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
uint8_t v___x_4121__boxed_1534_; lean_object* v_res_1535_; 
v___x_4121__boxed_1534_ = lean_unbox(v___x_1522_);
v_res_1535_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(v___x_4121__boxed_1534_, v_self_1523_, v_job_1524_, v___f_1525_, v___x_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec(v___y_1528_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object* v_self_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_wsIdx_1546_; lean_object* v_baseName_1547_; lean_object* v_config_1548_; lean_object* v___f_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v_job_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___y_1571_; lean_object* v___x_1572_; 
v_wsIdx_1546_ = lean_ctor_get(v_self_1538_, 0);
v_baseName_1547_ = lean_ctor_get(v_self_1538_, 1);
v_config_1548_ = lean_ctor_get(v_self_1538_, 6);
lean_inc_ref(v_self_1538_);
lean_inc_ref(v_config_1548_);
v___f_1549_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1549_, 0, v_config_1548_);
lean_closure_set(v___f_1549_, 1, v_self_1538_);
v___x_1550_ = l_Lake_instDataKindUnit;
v___x_1551_ = 1;
lean_inc(v_baseName_1547_);
v___x_1552_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1547_, v___x_1551_);
v___x_1553_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0));
v___x_1554_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1));
v___x_1555_ = lean_string_append(v___x_1554_, v___x_1552_);
v___x_1556_ = lean_string_append(v___x_1555_, v___x_1553_);
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_box(0);
v___x_1559_ = lean_unsigned_to_nat(0u);
v___x_1560_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1561_ = 0;
v___x_1562_ = 0;
v___x_1563_ = l_Lake_BuildTrace_nil(v___x_1556_);
v___x_1564_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1564_, 0, v___x_1560_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
lean_ctor_set(v___x_1564_, 2, v___x_1559_);
lean_ctor_set_uint8(v___x_1564_, sizeof(void*)*3, v___x_1561_);
lean_ctor_set_uint8(v___x_1564_, sizeof(void*)*3 + 1, v___x_1562_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1557_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = lean_task_pure(v___x_1565_);
v___x_1567_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_job_1568_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_1568_, 0, v___x_1566_);
lean_ctor_set(v_job_1568_, 1, v___x_1558_);
lean_ctor_set(v_job_1568_, 2, v___x_1567_);
lean_ctor_set_uint8(v_job_1568_, sizeof(void*)*3, v___x_1562_);
v___x_1569_ = lean_nat_dec_eq(v_wsIdx_1546_, v___x_1559_);
v___x_1570_ = lean_box(v___x_1569_);
v___y_1571_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 12, 5);
lean_closure_set(v___y_1571_, 0, v___x_1570_);
lean_closure_set(v___y_1571_, 1, v_self_1538_);
lean_closure_set(v___y_1571_, 2, v_job_1568_);
lean_closure_set(v___y_1571_, 3, v___f_1549_);
lean_closure_set(v___y_1571_, 4, v___x_1557_);
v___x_1572_ = l_Lake_ensureJob___redArg(v___x_1550_, v___y_1571_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1598_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_a_1574_ = lean_ctor_get(v___x_1572_, 1);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1576_ = v___x_1572_;
v_isShared_1577_ = v_isSharedCheck_1598_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1598_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_task_1578_; lean_object* v_kind_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1596_; 
v_task_1578_ = lean_ctor_get(v_a_1573_, 0);
v_kind_1579_ = lean_ctor_get(v_a_1573_, 1);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_a_1573_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; 
v_unused_1597_ = lean_ctor_get(v_a_1573_, 2);
lean_dec(v_unused_1597_);
v___x_1581_ = v_a_1573_;
v_isShared_1582_ = v_isSharedCheck_1596_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_kind_1579_);
lean_inc(v_task_1578_);
lean_dec(v_a_1573_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1596_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v_registeredJobs_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v_job_1587_; 
v_registeredJobs_1583_ = lean_ctor_get(v_a_1543_, 4);
v___x_1584_ = lean_st_ref_take(v_registeredJobs_1583_);
v___x_1585_ = lean_string_append(v___x_1552_, v___x_1553_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 2, v___x_1585_);
v_job_1587_ = v___x_1581_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_task_1578_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_kind_1579_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v___x_1585_);
v_job_1587_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
lean_ctor_set_uint8(v_job_1587_, sizeof(void*)*3, v___x_1562_);
lean_inc_ref(v_job_1587_);
v___x_1588_ = l_Lake_Job_toOpaque___redArg(v_job_1587_);
v___x_1589_ = lean_array_push(v___x_1584_, v___x_1588_);
v___x_1590_ = lean_st_ref_put(v_registeredJobs_1583_, v___x_1589_);
v___x_1591_ = l_Lake_Job_renew___redArg(v_job_1587_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1591_);
v___x_1593_ = v___x_1576_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_a_1574_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1552_);
return v___x_1572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(lean_object* v_self_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(v_self_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec(v_a_1601_);
return v_res_1607_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = lean_box(0);
v___x_1609_ = l_Lean_Json_compress(v___x_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t v_fmt_1610_){
_start:
{
if (v_fmt_1610_ == 0)
{
lean_object* v___x_1611_; 
v___x_1611_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_1613_){
_start:
{
uint8_t v_fmt_boxed_1614_; lean_object* v_res_1615_; 
v_fmt_boxed_1614_ = lean_unbox(v_fmt_1613_);
v_res_1615_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_boxed_1614_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(uint8_t v_fmt_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_1616_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object* v_fmt_1619_, lean_object* v_a_1620_){
_start:
{
uint8_t v_fmt_boxed_1621_; lean_object* v_res_1622_; 
v_fmt_boxed_1621_ = lean_unbox(v_fmt_1619_);
v_res_1622_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(v_fmt_boxed_1621_, v_a_1620_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v___y_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
uint8_t v___y_67__boxed_1628_; lean_object* v_res_1629_; 
v___y_67__boxed_1628_ = lean_unbox(v___y_1626_);
v_res_1629_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_67__boxed_1628_, v___y_1627_);
return v_res_1629_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___f_1632_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_1633_ = 1;
v___x_1634_ = l_Lake_instDataKindUnit;
v___x_1635_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__1));
v___x_1636_ = l_Lake_Package_keyword;
v___x_1637_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1637_, 0, v___x_1636_);
lean_ctor_set(v___x_1637_, 1, v___x_1635_);
lean_ctor_set(v___x_1637_, 2, v___x_1634_);
lean_ctor_set(v___x_1637_, 3, v___f_1632_);
lean_ctor_set_uint8(v___x_1637_, sizeof(void*)*4, v___x_1633_);
lean_ctor_set_uint8(v___x_1637_, sizeof(void*)*4 + 1, v___x_1633_);
return v___x_1637_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_obj_once(&l_Lake_Package_extraDepFacetConfig___closed__2, &l_Lake_Package_extraDepFacetConfig___closed__2_once, _init_l_Lake_Package_extraDepFacetConfig___closed__2);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object* v_self_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_origName_1658_; lean_object* v_dir_1659_; lean_object* v_scope_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v_origName_1658_ = lean_ctor_get(v_self_1654_, 3);
lean_inc(v_origName_1658_);
v_dir_1659_ = lean_ctor_get(v_self_1654_, 4);
lean_inc_ref(v_dir_1659_);
v_scope_1660_ = lean_ctor_get(v_self_1654_, 10);
lean_inc_ref(v_scope_1660_);
lean_dec_ref(v_self_1654_);
v___x_1661_ = lean_string_utf8_byte_size(v_scope_1660_);
v___x_1662_ = lean_unsigned_to_nat(0u);
v___x_1663_ = lean_nat_dec_eq(v___x_1661_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
v___x_1665_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1664_, v_dir_1659_);
if (lean_obj_tag(v___x_1665_) == 1)
{
lean_object* v_toContext_1666_; lean_object* v_lakeEnv_1667_; lean_object* v_log_1668_; uint8_t v_action_1669_; uint8_t v_wantsRebuild_1670_; lean_object* v_trace_1671_; lean_object* v_buildTime_1672_; lean_object* v_val_1673_; lean_object* v_toolchain_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v_toContext_1666_ = lean_ctor_get(v_a_1655_, 1);
v_lakeEnv_1667_ = lean_ctor_get(v_toContext_1666_, 0);
v_log_1668_ = lean_ctor_get(v_a_1656_, 0);
v_action_1669_ = lean_ctor_get_uint8(v_a_1656_, sizeof(void*)*3);
v_wantsRebuild_1670_ = lean_ctor_get_uint8(v_a_1656_, sizeof(void*)*3 + 1);
v_trace_1671_ = lean_ctor_get(v_a_1656_, 1);
v_buildTime_1672_ = lean_ctor_get(v_a_1656_, 2);
v_val_1673_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_val_1673_);
lean_dec_ref_known(v___x_1665_, 1);
v_toolchain_1674_ = lean_ctor_get(v_lakeEnv_1667_, 19);
v___x_1675_ = lean_string_utf8_byte_size(v_toolchain_1674_);
v___x_1676_ = lean_nat_dec_eq(v___x_1675_, v___x_1662_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1677_ = l_Lean_Name_toString(v_origName_1658_, v___x_1663_);
lean_inc_ref(v_lakeEnv_1667_);
v___x_1678_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_1667_, v_scope_1660_, v___x_1677_);
v___x_1679_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1));
v___x_1680_ = lean_string_append(v___x_1678_, v___x_1679_);
v___x_1681_ = lean_string_append(v___x_1680_, v_val_1673_);
lean_dec(v_val_1673_);
v___x_1682_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2));
v___x_1683_ = lean_string_append(v___x_1681_, v___x_1682_);
v___x_1684_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc_ref(v_toolchain_1674_);
v___x_1685_ = l_Lake_uriEncode(v_toolchain_1674_, v___x_1684_);
v___x_1686_ = lean_string_append(v___x_1683_, v___x_1685_);
lean_dec_ref(v___x_1685_);
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v_a_1656_);
return v___x_1687_;
}
else
{
lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1698_; 
lean_inc(v_buildTime_1672_);
lean_inc_ref(v_trace_1671_);
lean_inc_ref(v_log_1668_);
lean_dec(v_val_1673_);
lean_dec_ref(v_scope_1660_);
lean_dec(v_origName_1658_);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_a_1656_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; lean_object* v_unused_1700_; lean_object* v_unused_1701_; 
v_unused_1699_ = lean_ctor_get(v_a_1656_, 2);
lean_dec(v_unused_1699_);
v_unused_1700_ = lean_ctor_get(v_a_1656_, 1);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v_a_1656_, 0);
lean_dec(v_unused_1701_);
v___x_1689_ = v_a_1656_;
v_isShared_1690_ = v_isSharedCheck_1698_;
goto v_resetjp_1688_;
}
else
{
lean_dec(v_a_1656_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1698_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1695_; 
v___x_1691_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4));
v___x_1692_ = lean_array_get_size(v_log_1668_);
v___x_1693_ = lean_array_push(v_log_1668_, v___x_1691_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1693_);
v___x_1695_ = v___x_1689_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_trace_1671_);
lean_ctor_set(v_reuseFailAlloc_1697_, 2, v_buildTime_1672_);
lean_ctor_set_uint8(v_reuseFailAlloc_1697_, sizeof(void*)*3, v_action_1669_);
lean_ctor_set_uint8(v_reuseFailAlloc_1697_, sizeof(void*)*3 + 1, v_wantsRebuild_1670_);
v___x_1695_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1692_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
return v___x_1696_;
}
}
}
}
else
{
lean_object* v_log_1702_; uint8_t v_action_1703_; uint8_t v_wantsRebuild_1704_; lean_object* v_trace_1705_; lean_object* v_buildTime_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1717_; 
lean_dec(v___x_1665_);
lean_dec_ref(v_scope_1660_);
lean_dec(v_origName_1658_);
v_log_1702_ = lean_ctor_get(v_a_1656_, 0);
v_action_1703_ = lean_ctor_get_uint8(v_a_1656_, sizeof(void*)*3);
v_wantsRebuild_1704_ = lean_ctor_get_uint8(v_a_1656_, sizeof(void*)*3 + 1);
v_trace_1705_ = lean_ctor_get(v_a_1656_, 1);
v_buildTime_1706_ = lean_ctor_get(v_a_1656_, 2);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_a_1656_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1708_ = v_a_1656_;
v_isShared_1709_ = v_isSharedCheck_1717_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_buildTime_1706_);
lean_inc(v_trace_1705_);
lean_inc(v_log_1702_);
lean_dec(v_a_1656_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1717_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1710_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6));
v___x_1711_ = lean_array_get_size(v_log_1702_);
v___x_1712_ = lean_array_push(v_log_1702_, v___x_1710_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 0, v___x_1712_);
v___x_1714_ = v___x_1708_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_trace_1705_);
lean_ctor_set(v_reuseFailAlloc_1716_, 2, v_buildTime_1706_);
lean_ctor_set_uint8(v_reuseFailAlloc_1716_, sizeof(void*)*3, v_action_1703_);
lean_ctor_set_uint8(v_reuseFailAlloc_1716_, sizeof(void*)*3 + 1, v_wantsRebuild_1704_);
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
lean_object* v_log_1718_; uint8_t v_action_1719_; uint8_t v_wantsRebuild_1720_; lean_object* v_trace_1721_; lean_object* v_buildTime_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1733_; 
lean_dec_ref(v_scope_1660_);
lean_dec_ref(v_dir_1659_);
lean_dec(v_origName_1658_);
v_log_1718_ = lean_ctor_get(v_a_1656_, 0);
v_action_1719_ = lean_ctor_get_uint8(v_a_1656_, sizeof(void*)*3);
v_wantsRebuild_1720_ = lean_ctor_get_uint8(v_a_1656_, sizeof(void*)*3 + 1);
v_trace_1721_ = lean_ctor_get(v_a_1656_, 1);
v_buildTime_1722_ = lean_ctor_get(v_a_1656_, 2);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_a_1656_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1724_ = v_a_1656_;
v_isShared_1725_ = v_isSharedCheck_1733_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_buildTime_1722_);
lean_inc(v_trace_1721_);
lean_inc(v_log_1718_);
lean_dec(v_a_1656_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1733_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1726_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8));
v___x_1727_ = lean_array_get_size(v_log_1718_);
v___x_1728_ = lean_array_push(v_log_1718_, v___x_1726_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1728_);
v___x_1730_ = v___x_1724_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_trace_1721_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_buildTime_1722_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*3, v_action_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*3 + 1, v_wantsRebuild_1720_);
v___x_1730_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1727_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
return v___x_1731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___boxed(lean_object* v_self_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1734_, v_a_1735_, v_a_1736_);
lean_dec_ref(v_a_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object* v_self_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1739_, v_a_1744_, v_a_1745_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object* v_self_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(v_self_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec(v_a_1750_);
lean_dec_ref(v_a_1749_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object* v_self_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v_rev_1770_; lean_object* v_log_1771_; uint8_t v_action_1772_; uint8_t v_wantsRebuild_1773_; lean_object* v_trace_1774_; lean_object* v_buildTime_1775_; lean_object* v_dir_1784_; lean_object* v_config_1785_; lean_object* v_remoteUrl_1786_; lean_object* v_buildArchive_1787_; lean_object* v___y_1789_; lean_object* v___y_1790_; uint8_t v___y_1791_; uint8_t v___y_1792_; lean_object* v___y_1793_; lean_object* v_val_1794_; lean_object* v___y_1814_; lean_object* v_releaseRepo_1845_; 
v_dir_1784_ = lean_ctor_get(v_self_1766_, 4);
lean_inc_ref(v_dir_1784_);
v_config_1785_ = lean_ctor_get(v_self_1766_, 6);
lean_inc_ref(v_config_1785_);
v_remoteUrl_1786_ = lean_ctor_get(v_self_1766_, 11);
lean_inc_ref(v_remoteUrl_1786_);
v_buildArchive_1787_ = lean_ctor_get(v_self_1766_, 21);
lean_inc_ref(v_buildArchive_1787_);
lean_dec_ref(v_self_1766_);
v_releaseRepo_1845_ = lean_ctor_get(v_config_1785_, 10);
lean_inc(v_releaseRepo_1845_);
lean_dec_ref(v_config_1785_);
if (lean_obj_tag(v_releaseRepo_1845_) == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v___x_1846_ = lean_string_utf8_byte_size(v_remoteUrl_1786_);
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = lean_nat_dec_eq(v___x_1846_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; 
v___x_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1849_, 0, v_remoteUrl_1786_);
v___y_1814_ = v___x_1849_;
goto v___jp_1813_;
}
else
{
lean_dec_ref(v_remoteUrl_1786_);
v___y_1814_ = v_releaseRepo_1845_;
goto v___jp_1813_;
}
}
else
{
lean_dec_ref(v_remoteUrl_1786_);
v___y_1814_ = v_releaseRepo_1845_;
goto v___jp_1813_;
}
v___jp_1769_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1776_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0));
v___x_1777_ = lean_string_append(v___x_1776_, v_rev_1770_);
lean_dec_ref(v_rev_1770_);
v___x_1778_ = 3;
v___x_1779_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set_uint8(v___x_1779_, sizeof(void*)*1, v___x_1778_);
v___x_1780_ = lean_array_get_size(v_log_1771_);
v___x_1781_ = lean_array_push(v_log_1771_, v___x_1779_);
v___x_1782_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v_trace_1774_);
lean_ctor_set(v___x_1782_, 2, v_buildTime_1775_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*3, v_action_1772_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*3 + 1, v_wantsRebuild_1773_);
v___x_1783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1780_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
return v___x_1783_;
}
v___jp_1788_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
lean_inc_ref(v_dir_1784_);
v___x_1796_ = l_Lake_GitRepo_findTag_x3f(v___x_1795_, v_dir_1784_);
if (lean_obj_tag(v___x_1796_) == 1)
{
lean_object* v_val_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec_ref(v_dir_1784_);
v_val_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_val_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1798_, 0, v___y_1793_);
lean_ctor_set(v___x_1798_, 1, v___y_1790_);
lean_ctor_set(v___x_1798_, 2, v___y_1789_);
lean_ctor_set_uint8(v___x_1798_, sizeof(void*)*3, v___y_1792_);
lean_ctor_set_uint8(v___x_1798_, sizeof(void*)*3 + 1, v___y_1791_);
v___x_1799_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1));
v___x_1800_ = lean_string_append(v_val_1794_, v___x_1799_);
v___x_1801_ = lean_string_append(v___x_1800_, v_val_1797_);
lean_dec(v_val_1797_);
v___x_1802_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2));
v___x_1803_ = lean_string_append(v___x_1801_, v___x_1802_);
v___x_1804_ = lean_string_append(v___x_1803_, v_buildArchive_1787_);
lean_dec_ref(v_buildArchive_1787_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v___x_1798_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; 
lean_dec(v___x_1796_);
lean_dec_ref(v_val_1794_);
lean_dec_ref(v_buildArchive_1787_);
v___x_1806_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1795_, v_dir_1784_);
if (lean_obj_tag(v___x_1806_) == 1)
{
lean_object* v_val_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_val_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_val_1807_);
lean_dec_ref_known(v___x_1806_, 1);
v___x_1808_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3));
v___x_1809_ = lean_string_append(v___x_1808_, v_val_1807_);
lean_dec(v_val_1807_);
v___x_1810_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4));
v___x_1811_ = lean_string_append(v___x_1809_, v___x_1810_);
v_rev_1770_ = v___x_1811_;
v_log_1771_ = v___y_1793_;
v_action_1772_ = v___y_1792_;
v_wantsRebuild_1773_ = v___y_1791_;
v_trace_1774_ = v___y_1790_;
v_buildTime_1775_ = v___y_1789_;
goto v___jp_1769_;
}
else
{
lean_object* v___x_1812_; 
lean_dec(v___x_1806_);
v___x_1812_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_rev_1770_ = v___x_1812_;
v_log_1771_ = v___y_1793_;
v_action_1772_ = v___y_1792_;
v_wantsRebuild_1773_ = v___y_1791_;
v_trace_1774_ = v___y_1790_;
v_buildTime_1775_ = v___y_1789_;
goto v___jp_1769_;
}
}
}
v___jp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_dir_1784_);
v___x_1816_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v___x_1815_, v_dir_1784_);
if (lean_obj_tag(v___y_1814_) == 0)
{
if (lean_obj_tag(v___x_1816_) == 1)
{
lean_object* v_log_1817_; uint8_t v_action_1818_; uint8_t v_wantsRebuild_1819_; lean_object* v_trace_1820_; lean_object* v_buildTime_1821_; lean_object* v_val_1822_; 
v_log_1817_ = lean_ctor_get(v_a_1767_, 0);
lean_inc_ref(v_log_1817_);
v_action_1818_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*3);
v_wantsRebuild_1819_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*3 + 1);
v_trace_1820_ = lean_ctor_get(v_a_1767_, 1);
lean_inc_ref(v_trace_1820_);
v_buildTime_1821_ = lean_ctor_get(v_a_1767_, 2);
lean_inc(v_buildTime_1821_);
lean_dec_ref(v_a_1767_);
v_val_1822_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_val_1822_);
lean_dec_ref_known(v___x_1816_, 1);
v___y_1789_ = v_buildTime_1821_;
v___y_1790_ = v_trace_1820_;
v___y_1791_ = v_wantsRebuild_1819_;
v___y_1792_ = v_action_1818_;
v___y_1793_ = v_log_1817_;
v_val_1794_ = v_val_1822_;
goto v___jp_1788_;
}
else
{
lean_object* v_log_1823_; uint8_t v_action_1824_; uint8_t v_wantsRebuild_1825_; lean_object* v_trace_1826_; lean_object* v_buildTime_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1838_; 
lean_dec(v___x_1816_);
lean_dec_ref(v_buildArchive_1787_);
lean_dec_ref(v_dir_1784_);
v_log_1823_ = lean_ctor_get(v_a_1767_, 0);
v_action_1824_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*3);
v_wantsRebuild_1825_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*3 + 1);
v_trace_1826_ = lean_ctor_get(v_a_1767_, 1);
v_buildTime_1827_ = lean_ctor_get(v_a_1767_, 2);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_a_1767_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1829_ = v_a_1767_;
v_isShared_1830_ = v_isSharedCheck_1838_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_buildTime_1827_);
lean_inc(v_trace_1826_);
lean_inc(v_log_1823_);
lean_dec(v_a_1767_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1838_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1831_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6));
v___x_1832_ = lean_array_get_size(v_log_1823_);
v___x_1833_ = lean_array_push(v_log_1823_, v___x_1831_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1833_);
v___x_1835_ = v___x_1829_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1833_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_trace_1826_);
lean_ctor_set(v_reuseFailAlloc_1837_, 2, v_buildTime_1827_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, sizeof(void*)*3, v_action_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1837_, sizeof(void*)*3 + 1, v_wantsRebuild_1825_);
v___x_1835_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1832_);
lean_ctor_set(v___x_1836_, 1, v___x_1835_);
return v___x_1836_;
}
}
}
}
else
{
lean_object* v_log_1839_; uint8_t v_action_1840_; uint8_t v_wantsRebuild_1841_; lean_object* v_trace_1842_; lean_object* v_buildTime_1843_; lean_object* v_val_1844_; 
lean_dec(v___x_1816_);
v_log_1839_ = lean_ctor_get(v_a_1767_, 0);
lean_inc_ref(v_log_1839_);
v_action_1840_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*3);
v_wantsRebuild_1841_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*3 + 1);
v_trace_1842_ = lean_ctor_get(v_a_1767_, 1);
lean_inc_ref(v_trace_1842_);
v_buildTime_1843_ = lean_ctor_get(v_a_1767_, 2);
lean_inc(v_buildTime_1843_);
lean_dec_ref(v_a_1767_);
v_val_1844_ = lean_ctor_get(v___y_1814_, 0);
lean_inc(v_val_1844_);
lean_dec_ref_known(v___y_1814_, 1);
v___y_1789_ = v_buildTime_1843_;
v___y_1790_ = v_trace_1842_;
v___y_1791_ = v_wantsRebuild_1841_;
v___y_1792_ = v_action_1840_;
v___y_1793_ = v_log_1839_;
v_val_1794_ = v_val_1844_;
goto v___jp_1788_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(lean_object* v_self_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1850_, v_a_1851_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object* v_self_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1854_, v_a_1860_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object* v_self_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(v_self_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(lean_object* v_val_1872_, lean_object* v_a_x3f_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___x_1876_; lean_object* v_log_1877_; uint8_t v_action_1878_; uint8_t v_wantsRebuild_1879_; lean_object* v_trace_1880_; lean_object* v_buildTime_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1892_; 
v___x_1876_ = lean_io_mono_ms_now();
v_log_1877_ = lean_ctor_get(v___y_1874_, 0);
v_action_1878_ = lean_ctor_get_uint8(v___y_1874_, sizeof(void*)*3);
v_wantsRebuild_1879_ = lean_ctor_get_uint8(v___y_1874_, sizeof(void*)*3 + 1);
v_trace_1880_ = lean_ctor_get(v___y_1874_, 1);
v_buildTime_1881_ = lean_ctor_get(v___y_1874_, 2);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___y_1874_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1883_ = v___y_1874_;
v_isShared_1884_ = v_isSharedCheck_1892_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_buildTime_1881_);
lean_inc(v_trace_1880_);
lean_inc(v_log_1877_);
lean_dec(v___y_1874_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1892_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1885_ = lean_nat_sub(v___x_1876_, v_val_1872_);
lean_dec(v___x_1876_);
v___x_1886_ = lean_box(0);
v___x_1887_ = lean_nat_add(v_buildTime_1881_, v___x_1885_);
lean_dec(v___x_1885_);
lean_dec(v_buildTime_1881_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 2, v___x_1887_);
v___x_1889_ = v___x_1883_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_log_1877_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_trace_1880_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v___x_1887_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*3, v_action_1878_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*3 + 1, v_wantsRebuild_1879_);
v___x_1889_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1886_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
return v___x_1890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0___boxed(lean_object* v_val_1893_, lean_object* v_a_x3f_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v_val_1893_, v_a_x3f_1894_, v___y_1895_);
lean_dec(v_a_x3f_1894_);
lean_dec(v_val_1893_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(lean_object* v_url_1903_, lean_object* v_archiveFile_1904_, lean_object* v_headers_1905_, lean_object* v_depTrace_1906_, lean_object* v_traceFile_1907_, uint8_t v_action_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v_a_1913_; lean_object* v_a_1914_; lean_object* v_log_1917_; uint8_t v_action_1918_; uint8_t v_wantsRebuild_1919_; lean_object* v_trace_1920_; lean_object* v_buildTime_1921_; lean_object* v_toBuildConfig_1927_; lean_object* v_log_1928_; uint8_t v_action_1929_; uint8_t v_wantsRebuild_1930_; lean_object* v_trace_1931_; lean_object* v_buildTime_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_2022_; 
v_toBuildConfig_1927_ = lean_ctor_get(v_a_1909_, 0);
v_log_1928_ = lean_ctor_get(v_a_1910_, 0);
v_action_1929_ = lean_ctor_get_uint8(v_a_1910_, sizeof(void*)*3);
v_wantsRebuild_1930_ = lean_ctor_get_uint8(v_a_1910_, sizeof(void*)*3 + 1);
v_trace_1931_ = lean_ctor_get(v_a_1910_, 1);
v_buildTime_1932_ = lean_ctor_get(v_a_1910_, 2);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_a_1910_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_1934_ = v_a_1910_;
v_isShared_1935_ = v_isSharedCheck_2022_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_buildTime_1932_);
lean_inc(v_trace_1931_);
lean_inc(v_log_1928_);
lean_dec(v_a_1910_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_2022_;
goto v_resetjp_1933_;
}
v___jp_1912_:
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1915_, 0, v_a_1913_);
lean_ctor_set(v___x_1915_, 1, v_a_1914_);
return v___x_1915_;
}
v___jp_1916_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1922_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1));
v___x_1923_ = lean_array_get_size(v_log_1917_);
v___x_1924_ = lean_array_push(v_log_1917_, v___x_1922_);
v___x_1925_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
lean_ctor_set(v___x_1925_, 1, v_trace_1920_);
lean_ctor_set(v___x_1925_, 2, v_buildTime_1921_);
lean_ctor_set_uint8(v___x_1925_, sizeof(void*)*3, v_action_1918_);
lean_ctor_set_uint8(v___x_1925_, sizeof(void*)*3 + 1, v_wantsRebuild_1919_);
v___x_1926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1923_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
return v___x_1926_;
}
v_resetjp_1933_:
{
uint8_t v_noBuild_1936_; uint8_t v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_noBuild_1936_ = lean_ctor_get_uint8(v_toBuildConfig_1927_, sizeof(void*)*4 + 2);
v___x_1937_ = l_Lake_JobAction_merge(v_action_1929_, v_action_1908_);
v___x_1938_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2));
lean_inc_ref(v_traceFile_1907_);
v___x_1939_ = l_System_FilePath_addExtension(v_traceFile_1907_, v___x_1938_);
if (v_noBuild_1936_ == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v_a_1943_; lean_object* v_a_1944_; 
v___x_1940_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1928_);
v___x_1941_ = l_Lake_download(v_url_1903_, v_archiveFile_1904_, v_headers_1905_, v_log_1928_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1948_; lean_object* v_a_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v_a_1948_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1948_);
v_a_1949_ = lean_ctor_get(v___x_1941_, 1);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1941_, 2);
v___x_1950_ = lean_array_get_size(v_log_1928_);
lean_dec_ref(v_log_1928_);
v___x_1951_ = lean_array_get_size(v_a_1949_);
v___x_1952_ = l_Array_extract___redArg(v_a_1949_, v___x_1950_, v___x_1951_);
v___x_1953_ = lean_box(0);
v___x_1954_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1906_, v___x_1953_, v___x_1952_);
v___x_1955_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1907_, v___x_1954_);
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
lean_ctor_set(v___x_1934_, 0, v_a_1949_);
v___x_1964_ = v___x_1934_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1949_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_trace_1931_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_buildTime_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*3 + 1, v_wantsRebuild_1930_);
v___x_1964_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1966_; 
lean_ctor_set_uint8(v___x_1964_, sizeof(void*)*3, v___x_1937_);
lean_inc(v_a_1948_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v_a_1948_);
v___x_1966_ = v___x_1961_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1948_);
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
lean_ctor_set(v___x_1972_, 0, v_a_1948_);
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1948_);
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
lean_dec(v_a_1948_);
v_a_1984_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___x_1959_, 1);
v___x_1985_ = lean_io_error_to_string(v_a_1984_);
v___x_1986_ = 3;
v___x_1987_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1987_, 0, v___x_1985_);
lean_ctor_set_uint8(v___x_1987_, sizeof(void*)*1, v___x_1986_);
v___x_1988_ = lean_array_push(v_a_1949_, v___x_1987_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v___x_1988_);
v___x_1990_ = v___x_1934_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_trace_1931_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_buildTime_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_1991_, sizeof(void*)*3 + 1, v_wantsRebuild_1930_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*3, v___x_1937_);
v_a_1943_ = v___x_1951_;
v_a_1944_ = v___x_1990_;
goto v___jp_1942_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
lean_dec(v_a_1948_);
lean_dec_ref(v___x_1939_);
v_a_1994_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1995_ = lean_io_error_to_string(v_a_1994_);
v___x_1996_ = 3;
v___x_1997_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1997_, 0, v___x_1995_);
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*1, v___x_1996_);
v___x_1998_ = lean_array_push(v_a_1949_, v___x_1997_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v___x_1998_);
v___x_2000_ = v___x_1934_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_trace_1931_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v_buildTime_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_2001_, sizeof(void*)*3 + 1, v_wantsRebuild_1930_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*3, v___x_1937_);
v_a_1943_ = v___x_1951_;
v_a_1944_ = v___x_2000_;
goto v___jp_1942_;
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v_a_2003_; lean_object* v___x_2005_; 
lean_dec_ref(v___x_1939_);
lean_dec_ref(v_log_1928_);
lean_dec_ref(v_traceFile_1907_);
v_a_2002_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_2002_);
v_a_2003_ = lean_ctor_get(v___x_1941_, 1);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_1941_, 2);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v_a_2003_);
v___x_2005_ = v___x_1934_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2003_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_trace_1931_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_buildTime_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_2006_, sizeof(void*)*3 + 1, v_wantsRebuild_1930_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*3, v___x_1937_);
v_a_1943_ = v_a_2002_;
v_a_1944_ = v___x_2005_;
goto v___jp_1942_;
}
}
v___jp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v_a_1947_; 
v___x_1945_ = lean_box(0);
v___x_1946_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1940_, v___x_1945_, v_a_1944_);
lean_dec(v___x_1940_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 1);
lean_inc(v_a_1947_);
lean_dec_ref(v___x_1946_);
v_a_1913_ = v_a_1943_;
v_a_1914_ = v_a_1947_;
goto v___jp_1912_;
}
}
else
{
uint8_t v___x_2007_; 
lean_dec_ref(v_archiveFile_1904_);
lean_dec_ref(v_url_1903_);
v___x_2007_ = l_System_FilePath_pathExists(v_traceFile_1907_);
lean_dec_ref(v_traceFile_1907_);
if (v___x_2007_ == 0)
{
lean_dec_ref(v___x_1939_);
lean_del_object(v___x_1934_);
v_log_1917_ = v_log_1928_;
v_action_1918_ = v___x_1937_;
v_wantsRebuild_1919_ = v_noBuild_1936_;
v_trace_1920_ = v_trace_1931_;
v_buildTime_1921_ = v_buildTime_1932_;
goto v___jp_1916_;
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2008_ = lean_box(0);
v___x_2009_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_2010_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1906_, v___x_2008_, v___x_2009_);
v___x_2011_ = l_Lake_BuildMetadata_writeFile(v___x_1939_, v___x_2010_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_dec_ref_known(v___x_2011_, 1);
lean_del_object(v___x_1934_);
v_log_1917_ = v_log_1928_;
v_action_1918_ = v___x_1937_;
v_wantsRebuild_1919_ = v_noBuild_1936_;
v_trace_1920_ = v_trace_1931_;
v_buildTime_1921_ = v_buildTime_1932_;
goto v___jp_1916_;
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
v___x_2016_ = lean_array_get_size(v_log_1928_);
v___x_2017_ = lean_array_push(v_log_1928_, v___x_2015_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v___x_2017_);
v___x_2019_ = v___x_1934_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_trace_1931_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v_buildTime_1932_);
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
v_oldMode_2104_ = lean_ctor_get_uint8(v_toBuildConfig_2103_, sizeof(void*)*4);
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
lean_object* v_data_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2194_; 
v_data_2143_ = lean_ctor_get(v_savedTrace_2135_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_savedTrace_2135_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2145_ = v_savedTrace_2135_;
v_isShared_2146_ = v_isSharedCheck_2194_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_data_2143_);
lean_dec(v_savedTrace_2135_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2194_;
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
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2152_; lean_object* v_a_2153_; lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2192_; 
v___x_2152_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2133_, v_depTrace_2134_, v___x_2151_, v_oldTrace_2136_, v_a_2140_, v_a_2141_);
lean_dec_ref(v___x_2151_);
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_a_2154_ = lean_ctor_get(v___x_2152_, 1);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2156_ = v___x_2152_;
v_isShared_2157_ = v_isSharedCheck_2192_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2192_;
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
lean_object* v_log_2167_; uint8_t v_action_2168_; uint8_t v_wantsRebuild_2169_; lean_object* v_trace_2170_; lean_object* v_buildTime_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2191_; 
v_log_2167_ = lean_ctor_get(v_a_2154_, 0);
v_action_2168_ = lean_ctor_get_uint8(v_a_2154_, sizeof(void*)*3);
v_wantsRebuild_2169_ = lean_ctor_get_uint8(v_a_2154_, sizeof(void*)*3 + 1);
v_trace_2170_ = lean_ctor_get(v_a_2154_, 1);
v_buildTime_2171_ = lean_ctor_get(v_a_2154_, 2);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_a_2154_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2173_ = v_a_2154_;
v_isShared_2174_ = v_isSharedCheck_2191_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_buildTime_2171_);
lean_inc(v_trace_2170_);
lean_inc(v_log_2167_);
lean_dec(v_a_2154_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2191_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
uint8_t v___x_2175_; uint8_t v___x_2176_; lean_object* v___x_2178_; 
v___x_2175_ = 2;
v___x_2176_ = l_Lake_JobAction_merge(v_action_2168_, v___x_2175_);
if (v_isShared_2174_ == 0)
{
v___x_2178_ = v___x_2173_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_log_2167_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_trace_2170_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v_buildTime_2171_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*3 + 1, v_wantsRebuild_2169_);
v___x_2178_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2179_; 
lean_ctor_set_uint8(v___x_2178_, sizeof(void*)*3, v___x_2176_);
v___x_2179_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_2148_, v_a_2132_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v___x_2178_);
lean_dec_ref(v_log_2148_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 1);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 2);
v___y_2159_ = v_a_2180_;
goto v___jp_2158_;
}
else
{
lean_object* v_a_2181_; lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_del_object(v___x_2156_);
lean_dec(v_a_2153_);
v_a_2181_ = lean_ctor_get(v___x_2179_, 0);
v_a_2182_ = lean_ctor_get(v___x_2179_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2179_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_inc(v_a_2181_);
lean_dec(v___x_2179_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2181_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
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
lean_object* v_toBuildConfig_2195_; uint8_t v_oldMode_2196_; 
lean_dec(v_savedTrace_2135_);
v_toBuildConfig_2195_ = lean_ctor_get(v_a_2140_, 0);
v_oldMode_2196_ = lean_ctor_get_uint8(v_toBuildConfig_2195_, sizeof(void*)*4);
if (v_oldMode_2196_ == 0)
{
uint8_t v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = 0;
v___x_2198_ = lean_box(v___x_2197_);
v___x_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
lean_ctor_set(v___x_2199_, 1, v_a_2141_);
return v___x_2199_;
}
else
{
uint8_t v___x_2200_; 
v___x_2200_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2133_, v_oldTrace_2136_);
if (v___x_2200_ == 0)
{
uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = 0;
v___x_2202_ = lean_box(v___x_2201_);
v___x_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
lean_ctor_set(v___x_2203_, 1, v_a_2141_);
return v___x_2203_;
}
else
{
uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = 1;
v___x_2205_ = lean_box(v___x_2204_);
v___x_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v_a_2141_);
return v___x_2206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object* v_a_2207_, lean_object* v_info_2208_, lean_object* v_depTrace_2209_, lean_object* v_savedTrace_2210_, lean_object* v_oldTrace_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_2207_, v_info_2208_, v_depTrace_2209_, v_savedTrace_2210_, v_oldTrace_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
lean_dec_ref(v_a_2215_);
lean_dec(v_a_2214_);
lean_dec(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_oldTrace_2211_);
lean_dec_ref(v_depTrace_2209_);
lean_dec_ref(v_info_2208_);
lean_dec_ref(v_a_2207_);
return v_res_2218_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_unsigned_to_nat(0u);
v___x_2224_ = lean_nat_to_int(v___x_2223_);
return v___x_2224_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4(void){
_start:
{
uint32_t v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = 0;
v___x_2226_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3);
v___x_2227_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set_uint32(v___x_2227_, sizeof(void*)*1, v___x_2225_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(lean_object* v_self_2228_, lean_object* v_url_2229_, lean_object* v_archiveFile_2230_, lean_object* v_headers_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v_a_2240_; lean_object* v_a_2241_; lean_object* v___y_2244_; lean_object* v___y_2245_; uint8_t v___y_2246_; uint8_t v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; uint8_t v_a_2275_; lean_object* v_a_2276_; lean_object* v_log_2295_; uint8_t v_action_2296_; uint8_t v_wantsRebuild_2297_; lean_object* v_trace_2298_; lean_object* v_buildTime_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2339_; 
v_log_2295_ = lean_ctor_get(v_a_2237_, 0);
v_action_2296_ = lean_ctor_get_uint8(v_a_2237_, sizeof(void*)*3);
v_wantsRebuild_2297_ = lean_ctor_get_uint8(v_a_2237_, sizeof(void*)*3 + 1);
v_trace_2298_ = lean_ctor_get(v_a_2237_, 1);
v_buildTime_2299_ = lean_ctor_get(v_a_2237_, 2);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_a_2237_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2301_ = v_a_2237_;
v_isShared_2302_ = v_isSharedCheck_2339_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_buildTime_2299_);
lean_inc(v_trace_2298_);
lean_inc(v_log_2295_);
lean_dec(v_a_2237_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2339_;
goto v_resetjp_2300_;
}
v___jp_2239_:
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2242_, 0, v_a_2240_);
lean_ctor_set(v___x_2242_, 1, v_a_2241_);
return v___x_2242_;
}
v___jp_2243_:
{
uint8_t v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; uint8_t v___x_2253_; 
v___x_2250_ = 1;
v___x_2251_ = l_Lake_untar(v_archiveFile_2230_, v___y_2248_, v___x_2250_, v___y_2245_);
v___x_2252_ = 3;
v___x_2253_ = l_Lake_JobAction_merge(v___y_2247_, v___x_2252_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2254_; lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2263_; 
v_a_2254_ = lean_ctor_get(v___x_2251_, 0);
v_a_2255_ = lean_ctor_get(v___x_2251_, 1);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2257_ = v___x_2251_;
v_isShared_2258_ = v_isSharedCheck_2263_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_inc(v_a_2254_);
lean_dec(v___x_2251_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2263_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2259_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2259_, 0, v_a_2255_);
lean_ctor_set(v___x_2259_, 1, v___y_2249_);
lean_ctor_set(v___x_2259_, 2, v___y_2244_);
lean_ctor_set_uint8(v___x_2259_, sizeof(void*)*3, v___x_2253_);
lean_ctor_set_uint8(v___x_2259_, sizeof(void*)*3 + 1, v___y_2246_);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 1, v___x_2259_);
v___x_2261_ = v___x_2257_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2254_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
else
{
lean_object* v_a_2264_; lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2273_; 
v_a_2264_ = lean_ctor_get(v___x_2251_, 0);
v_a_2265_ = lean_ctor_get(v___x_2251_, 1);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2267_ = v___x_2251_;
v_isShared_2268_ = v_isSharedCheck_2273_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_inc(v_a_2264_);
lean_dec(v___x_2251_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2273_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2269_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2269_, 0, v_a_2265_);
lean_ctor_set(v___x_2269_, 1, v___y_2249_);
lean_ctor_set(v___x_2269_, 2, v___y_2244_);
lean_ctor_set_uint8(v___x_2269_, sizeof(void*)*3, v___x_2253_);
lean_ctor_set_uint8(v___x_2269_, sizeof(void*)*3 + 1, v___y_2246_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 1, v___x_2269_);
v___x_2271_ = v___x_2267_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2264_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
v___jp_2274_:
{
lean_object* v_config_2277_; lean_object* v_dir_2278_; lean_object* v_buildDir_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v_config_2277_ = lean_ctor_get(v_self_2228_, 6);
lean_inc_ref(v_config_2277_);
v_dir_2278_ = lean_ctor_get(v_self_2228_, 4);
lean_inc_ref(v_dir_2278_);
lean_dec_ref(v_self_2228_);
v_buildDir_2279_ = lean_ctor_get(v_config_2277_, 5);
lean_inc_ref(v_buildDir_2279_);
lean_dec_ref(v_config_2277_);
v___x_2280_ = l_System_FilePath_normalize(v_buildDir_2279_);
v___x_2281_ = l_Lake_joinRelative(v_dir_2278_, v___x_2280_);
v___x_2282_ = l_System_FilePath_pathExists(v___x_2281_);
if (v_a_2275_ == 0)
{
lean_object* v_log_2283_; uint8_t v_action_2284_; uint8_t v_wantsRebuild_2285_; lean_object* v_trace_2286_; lean_object* v_buildTime_2287_; 
v_log_2283_ = lean_ctor_get(v_a_2276_, 0);
lean_inc_ref(v_log_2283_);
v_action_2284_ = lean_ctor_get_uint8(v_a_2276_, sizeof(void*)*3);
v_wantsRebuild_2285_ = lean_ctor_get_uint8(v_a_2276_, sizeof(void*)*3 + 1);
v_trace_2286_ = lean_ctor_get(v_a_2276_, 1);
lean_inc_ref(v_trace_2286_);
v_buildTime_2287_ = lean_ctor_get(v_a_2276_, 2);
lean_inc(v_buildTime_2287_);
lean_dec_ref(v_a_2276_);
v___y_2244_ = v_buildTime_2287_;
v___y_2245_ = v_log_2283_;
v___y_2246_ = v_wantsRebuild_2285_;
v___y_2247_ = v_action_2284_;
v___y_2248_ = v___x_2281_;
v___y_2249_ = v_trace_2286_;
goto v___jp_2243_;
}
else
{
if (v___x_2282_ == 0)
{
lean_object* v_log_2288_; uint8_t v_action_2289_; uint8_t v_wantsRebuild_2290_; lean_object* v_trace_2291_; lean_object* v_buildTime_2292_; 
v_log_2288_ = lean_ctor_get(v_a_2276_, 0);
lean_inc_ref(v_log_2288_);
v_action_2289_ = lean_ctor_get_uint8(v_a_2276_, sizeof(void*)*3);
v_wantsRebuild_2290_ = lean_ctor_get_uint8(v_a_2276_, sizeof(void*)*3 + 1);
v_trace_2291_ = lean_ctor_get(v_a_2276_, 1);
lean_inc_ref(v_trace_2291_);
v_buildTime_2292_ = lean_ctor_get(v_a_2276_, 2);
lean_inc(v_buildTime_2292_);
lean_dec_ref(v_a_2276_);
v___y_2244_ = v_buildTime_2292_;
v___y_2245_ = v_log_2288_;
v___y_2246_ = v_wantsRebuild_2290_;
v___y_2247_ = v_action_2289_;
v___y_2248_ = v___x_2281_;
v___y_2249_ = v_trace_2291_;
goto v___jp_2243_;
}
else
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_dec_ref(v___x_2281_);
lean_dec_ref(v_archiveFile_2230_);
v___x_2293_ = lean_box(0);
v___x_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v_a_2276_);
return v___x_2294_;
}
}
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; lean_object* v_traceFile_2304_; lean_object* v___x_2305_; 
v___x_2303_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0));
lean_inc_ref(v_archiveFile_2230_);
v_traceFile_2304_ = l_System_FilePath_addExtension(v_archiveFile_2230_, v___x_2303_);
lean_inc_ref(v_traceFile_2304_);
v___x_2305_ = l_Lake_readTraceFile(v_traceFile_2304_, v_log_2295_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v_a_2307_; lean_object* v___x_2308_; uint64_t v___x_2309_; uint64_t v___x_2310_; uint64_t v_depTrace_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2316_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
v_a_2307_ = lean_ctor_get(v___x_2305_, 1);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2305_, 2);
v___x_2308_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1));
v___x_2309_ = l_Lake_Hash_nil;
v___x_2310_ = lean_string_hash(v_url_2229_);
v_depTrace_2311_ = lean_uint64_mix_hash(v___x_2309_, v___x_2310_);
v___x_2312_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2));
v___x_2313_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
v___x_2314_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2308_);
lean_ctor_set(v___x_2314_, 2, v___x_2313_);
lean_ctor_set_uint64(v___x_2314_, sizeof(void*)*3, v_depTrace_2311_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v_a_2307_);
v___x_2316_ = v___x_2301_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2307_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_trace_2298_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_buildTime_2299_);
lean_ctor_set_uint8(v_reuseFailAlloc_2333_, sizeof(void*)*3, v_action_2296_);
lean_ctor_set_uint8(v_reuseFailAlloc_2333_, sizeof(void*)*3 + 1, v_wantsRebuild_2297_);
v___x_2316_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_2232_, v_archiveFile_2230_, v___x_2314_, v_a_2306_, v___x_2313_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v___x_2316_);
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
lean_dec_ref_known(v___x_2314_, 3);
lean_dec_ref(v_traceFile_2304_);
lean_dec_ref(v_url_2229_);
v___x_2324_ = 1;
v_a_2275_ = v___x_2324_;
v_a_2276_ = v_a_2319_;
goto v___jp_2274_;
}
else
{
uint8_t v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = 4;
lean_inc_ref(v_archiveFile_2230_);
v___x_2326_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2229_, v_archiveFile_2230_, v_headers_2231_, v___x_2314_, v_traceFile_2304_, v___x_2325_, v_a_2236_, v_a_2319_);
lean_dec_ref_known(v___x_2314_, 3);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; uint8_t v___x_2328_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 1);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2326_, 2);
v___x_2328_ = 0;
v_a_2275_ = v___x_2328_;
v_a_2276_ = v_a_2327_;
goto v___jp_2274_;
}
else
{
lean_object* v_a_2329_; lean_object* v_a_2330_; 
lean_dec_ref(v_archiveFile_2230_);
lean_dec_ref(v_self_2228_);
v_a_2329_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2329_);
v_a_2330_ = lean_ctor_get(v___x_2326_, 1);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2326_, 2);
v_a_2240_ = v_a_2329_;
v_a_2241_ = v_a_2330_;
goto v___jp_2239_;
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v_a_2332_; 
lean_dec_ref_known(v___x_2314_, 3);
lean_dec_ref(v_traceFile_2304_);
lean_dec_ref(v_archiveFile_2230_);
lean_dec_ref(v_url_2229_);
lean_dec_ref(v_self_2228_);
v_a_2331_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2331_);
v_a_2332_ = lean_ctor_get(v___x_2317_, 1);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2317_, 2);
v_a_2240_ = v_a_2331_;
v_a_2241_ = v_a_2332_;
goto v___jp_2239_;
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v_a_2335_; lean_object* v___x_2337_; 
lean_dec_ref(v_traceFile_2304_);
lean_dec_ref(v_archiveFile_2230_);
lean_dec_ref(v_url_2229_);
lean_dec_ref(v_self_2228_);
v_a_2334_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2334_);
v_a_2335_ = lean_ctor_get(v___x_2305_, 1);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2305_, 2);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v_a_2335_);
v___x_2337_ = v___x_2301_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2335_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_trace_2298_);
lean_ctor_set(v_reuseFailAlloc_2338_, 2, v_buildTime_2299_);
lean_ctor_set_uint8(v_reuseFailAlloc_2338_, sizeof(void*)*3, v_action_2296_);
lean_ctor_set_uint8(v_reuseFailAlloc_2338_, sizeof(void*)*3 + 1, v_wantsRebuild_2297_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
v_a_2240_ = v_a_2334_;
v_a_2241_ = v___x_2337_;
goto v___jp_2239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object* v_self_2340_, lean_object* v_url_2341_, lean_object* v_archiveFile_2342_, lean_object* v_headers_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_self_2340_, v_url_2341_, v_archiveFile_2342_, v_headers_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec_ref(v_headers_2343_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object* v_a_2352_, lean_object* v_info_2353_, lean_object* v_depTrace_2354_, lean_object* v_depHash_2355_, lean_object* v_oldTrace_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2353_, v_depTrace_2354_, v_depHash_2355_, v_oldTrace_2356_, v_a_2360_, v_a_2361_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object* v_a_2364_, lean_object* v_info_2365_, lean_object* v_depTrace_2366_, lean_object* v_depHash_2367_, lean_object* v_oldTrace_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_2364_, v_info_2365_, v_depTrace_2366_, v_depHash_2367_, v_oldTrace_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec(v_a_2370_);
lean_dec(v_a_2369_);
lean_dec_ref(v_oldTrace_2368_);
lean_dec(v_depHash_2367_);
lean_dec_ref(v_depTrace_2366_);
lean_dec_ref(v_info_2365_);
lean_dec_ref(v_a_2364_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_getUrl_2376_, lean_object* v_pkg_2377_, lean_object* v_archiveFile_2378_, lean_object* v_headers_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
uint8_t v_r_2388_; lean_object* v___y_2389_; lean_object* v_a_2393_; lean_object* v___x_2409_; 
lean_inc_ref(v___y_2384_);
lean_inc(v___y_2383_);
lean_inc(v___y_2382_);
lean_inc(v___y_2381_);
lean_inc_ref(v___y_2380_);
lean_inc_ref(v_pkg_2377_);
v___x_2409_ = lean_apply_8(v_getUrl_2376_, v_pkg_2377_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, lean_box(0));
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v_a_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
v_a_2411_ = lean_ctor_get(v___x_2409_, 1);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2409_, 2);
lean_inc_ref(v_pkg_2377_);
v___x_2412_ = lean_apply_1(v_archiveFile_2378_, v_pkg_2377_);
v___x_2413_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2377_, v_a_2410_, v___x_2412_, v_headers_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v_a_2411_);
lean_dec_ref(v___y_2380_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; uint8_t v___x_2415_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 1);
lean_inc(v_a_2414_);
lean_dec_ref_known(v___x_2413_, 2);
v___x_2415_ = 1;
v_r_2388_ = v___x_2415_;
v___y_2389_ = v_a_2414_;
goto v___jp_2387_;
}
else
{
lean_object* v_a_2416_; 
v_a_2416_ = lean_ctor_get(v___x_2413_, 1);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2413_, 2);
v_a_2393_ = v_a_2416_;
goto v___jp_2392_;
}
}
else
{
lean_object* v_a_2417_; 
lean_dec_ref(v___y_2380_);
lean_dec_ref(v_archiveFile_2378_);
lean_dec_ref(v_pkg_2377_);
v_a_2417_ = lean_ctor_get(v___x_2409_, 1);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2409_, 2);
v_a_2393_ = v_a_2417_;
goto v___jp_2392_;
}
v___jp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_box(v_r_2388_);
v___x_2391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v___y_2389_);
return v___x_2391_;
}
v___jp_2392_:
{
lean_object* v_log_2394_; uint8_t v_action_2395_; uint8_t v_wantsRebuild_2396_; lean_object* v_trace_2397_; lean_object* v_buildTime_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2408_; 
v_log_2394_ = lean_ctor_get(v_a_2393_, 0);
v_action_2395_ = lean_ctor_get_uint8(v_a_2393_, sizeof(void*)*3);
v_wantsRebuild_2396_ = lean_ctor_get_uint8(v_a_2393_, sizeof(void*)*3 + 1);
v_trace_2397_ = lean_ctor_get(v_a_2393_, 1);
v_buildTime_2398_ = lean_ctor_get(v_a_2393_, 2);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_a_2393_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2400_ = v_a_2393_;
v_isShared_2401_ = v_isSharedCheck_2408_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_buildTime_2398_);
lean_inc(v_trace_2397_);
lean_inc(v_log_2394_);
lean_dec(v_a_2393_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2408_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
uint8_t v___x_2402_; uint8_t v___x_2403_; lean_object* v___x_2405_; 
v___x_2402_ = 4;
v___x_2403_ = l_Lake_JobAction_merge(v_action_2395_, v___x_2402_);
if (v_isShared_2401_ == 0)
{
v___x_2405_ = v___x_2400_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_log_2394_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_trace_2397_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v_buildTime_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2407_, sizeof(void*)*3 + 1, v_wantsRebuild_2396_);
v___x_2405_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
uint8_t v___x_2406_; 
lean_ctor_set_uint8(v___x_2405_, sizeof(void*)*3, v___x_2403_);
v___x_2406_ = 0;
v_r_2388_ = v___x_2406_;
v___y_2389_ = v___x_2405_;
goto v___jp_2387_;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* v_getUrl_2430_, lean_object* v_archiveFile_2431_, lean_object* v_headers_2432_, lean_object* v___x_2433_, lean_object* v_facet_2434_, lean_object* v_pkg_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___f_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
lean_inc_ref(v_pkg_2435_);
v___f_2443_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2443_, 0, v_getUrl_2430_);
lean_closure_set(v___f_2443_, 1, v_pkg_2435_);
lean_closure_set(v___f_2443_, 2, v_archiveFile_2431_);
lean_closure_set(v___f_2443_, 3, v_headers_2432_);
v___x_2444_ = lean_unsigned_to_nat(0u);
v___x_2445_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2433_);
v___x_2446_ = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(v___x_2446_, 0, lean_box(0));
lean_closure_set(v___x_2446_, 1, v___x_2433_);
lean_closure_set(v___x_2446_, 2, v___f_2443_);
lean_closure_set(v___x_2446_, 3, v___x_2444_);
lean_closure_set(v___x_2446_, 4, v___x_2445_);
v___x_2447_ = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM___boxed), 9, 2);
lean_closure_set(v___x_2447_, 0, lean_box(0));
lean_closure_set(v___x_2447_, 1, v___x_2446_);
v___x_2448_ = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM___boxed), 9, 2);
lean_closure_set(v___x_2448_, 0, lean_box(0));
lean_closure_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = l_Lake_ensureJob___redArg(v___x_2433_, v___x_2448_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2482_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_a_2451_ = lean_ctor_get(v___x_2449_, 1);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2453_ = v___x_2449_;
v_isShared_2454_ = v_isSharedCheck_2482_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2482_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_task_2455_; lean_object* v_kind_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2480_; 
v_task_2455_ = lean_ctor_get(v_a_2450_, 0);
v_kind_2456_ = lean_ctor_get(v_a_2450_, 1);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_a_2450_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; 
v_unused_2481_ = lean_ctor_get(v_a_2450_, 2);
lean_dec(v_unused_2481_);
v___x_2458_ = v_a_2450_;
v_isShared_2459_ = v_isSharedCheck_2480_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_kind_2456_);
lean_inc(v_task_2455_);
lean_dec(v_a_2450_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2480_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v_registeredJobs_2460_; lean_object* v___x_2461_; lean_object* v_baseName_2462_; uint8_t v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v_job_2471_; 
v_registeredJobs_2460_ = lean_ctor_get(v___y_2440_, 4);
v___x_2461_ = lean_st_ref_take(v_registeredJobs_2460_);
v_baseName_2462_ = lean_ctor_get(v_pkg_2435_, 1);
lean_inc(v_baseName_2462_);
lean_dec_ref(v_pkg_2435_);
v___x_2463_ = 1;
v___x_2464_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2462_, v___x_2463_);
v___x_2465_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2466_ = lean_string_append(v___x_2464_, v___x_2465_);
v___x_2467_ = l_Lake_Name_eraseHead(v_facet_2434_);
v___x_2468_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2467_, v___x_2463_);
v___x_2469_ = lean_string_append(v___x_2466_, v___x_2468_);
lean_dec_ref(v___x_2468_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 2, v___x_2469_);
v_job_2471_ = v___x_2458_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_task_2455_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_kind_2456_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v___x_2469_);
v_job_2471_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
lean_ctor_set_uint8(v_job_2471_, sizeof(void*)*3, v___x_2463_);
lean_inc_ref(v_job_2471_);
v___x_2472_ = l_Lake_Job_toOpaque___redArg(v_job_2471_);
v___x_2473_ = lean_array_push(v___x_2461_, v___x_2472_);
v___x_2474_ = lean_st_ref_put(v_registeredJobs_2460_, v___x_2473_);
v___x_2475_ = l_Lake_Job_renew___redArg(v_job_2471_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2475_);
v___x_2477_ = v___x_2453_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_a_2451_);
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
lean_dec_ref(v_pkg_2435_);
lean_dec(v_facet_2434_);
return v___x_2449_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v_getUrl_2483_, lean_object* v_archiveFile_2484_, lean_object* v_headers_2485_, lean_object* v___x_2486_, lean_object* v_facet_2487_, lean_object* v_pkg_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_2483_, v_archiveFile_2484_, v_headers_2485_, v___x_2486_, v_facet_2487_, v_pkg_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
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
lean_closure_set(v___f_2509_, 3, v___x_2508_);
lean_closure_set(v___f_2509_, 4, v_facet_2504_);
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
lean_closure_set(v___f_2520_, 3, v___x_2519_);
lean_closure_set(v___f_2520_, 4, v_facet_2514_);
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
lean_object* v_toBuildConfig_2560_; uint8_t v_verbosity_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v_toBuildConfig_2560_ = lean_ctor_get(v___y_2534_, 0);
v_verbosity_2561_ = lean_ctor_get_uint8(v_toBuildConfig_2560_, sizeof(void*)*4 + 4);
v___x_2562_ = l_Lake_Verbosity_ctorIdx(v_verbosity_2561_);
v___x_2563_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_2564_ = lean_nat_dec_eq(v___x_2562_, v___x_2563_);
lean_dec(v___x_2562_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; 
lean_dec(v_optFacet_2528_);
lean_dec(v_baseName_2527_);
v___x_2565_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_2538_ = v___x_2565_;
v_a_2539_ = v___y_2535_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2566_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2567_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2527_, v___x_2564_);
v___x_2568_ = lean_string_append(v___x_2566_, v___x_2567_);
lean_dec_ref(v___x_2567_);
v___x_2569_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2570_ = lean_string_append(v___x_2568_, v___x_2569_);
v___x_2571_ = l_Lake_Name_eraseHead(v_optFacet_2528_);
v___x_2572_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2571_, v___x_2564_);
v___x_2573_ = lean_string_append(v___x_2570_, v___x_2572_);
lean_dec_ref(v___x_2572_);
v___x_2574_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_2575_ = lean_string_append(v___x_2573_, v___x_2574_);
v_a_2538_ = v___x_2575_;
v_a_2539_ = v___y_2535_;
goto v___jp_2537_;
}
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec(v_optFacet_2528_);
lean_dec(v_baseName_2527_);
v___x_2576_ = lean_box(0);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v___y_2535_);
return v___x_2577_;
}
v___jp_2537_:
{
lean_object* v_log_2540_; uint8_t v_action_2541_; uint8_t v_wantsRebuild_2542_; lean_object* v_trace_2543_; lean_object* v_buildTime_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2559_; 
v_log_2540_ = lean_ctor_get(v_a_2539_, 0);
v_action_2541_ = lean_ctor_get_uint8(v_a_2539_, sizeof(void*)*3);
v_wantsRebuild_2542_ = lean_ctor_get_uint8(v_a_2539_, sizeof(void*)*3 + 1);
v_trace_2543_ = lean_ctor_get(v_a_2539_, 1);
v_buildTime_2544_ = lean_ctor_get(v_a_2539_, 2);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_a_2539_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2546_ = v_a_2539_;
v_isShared_2547_ = v_isSharedCheck_2559_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_buildTime_2544_);
lean_inc(v_trace_2543_);
lean_inc(v_log_2540_);
lean_dec(v_a_2539_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2559_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2556_; 
v___x_2548_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0));
v___x_2549_ = lean_string_append(v___x_2548_, v_what_2526_);
v___x_2550_ = lean_string_append(v___x_2549_, v_a_2538_);
lean_dec_ref(v_a_2538_);
v___x_2551_ = 3;
v___x_2552_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set_uint8(v___x_2552_, sizeof(void*)*1, v___x_2551_);
v___x_2553_ = lean_array_get_size(v_log_2540_);
v___x_2554_ = lean_array_push(v_log_2540_, v___x_2552_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v___x_2554_);
v___x_2556_ = v___x_2546_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2554_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_trace_2543_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v_buildTime_2544_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*3, v_action_2541_);
lean_ctor_set_uint8(v_reuseFailAlloc_2558_, sizeof(void*)*3 + 1, v_wantsRebuild_2542_);
v___x_2556_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
lean_object* v___x_2557_; 
v___x_2557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2553_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
return v___x_2557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_what_2578_, lean_object* v_baseName_2579_, lean_object* v_optFacet_2580_, lean_object* v_success_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
uint8_t v_success_boxed_2589_; lean_object* v_res_2590_; 
v_success_boxed_2589_ = lean_unbox(v_success_2581_);
v_res_2590_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(v_what_2578_, v_baseName_2579_, v_optFacet_2580_, v_success_boxed_2589_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec_ref(v_what_2578_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object* v___x_2591_, lean_object* v___x_2592_, lean_object* v___f_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___x_2601_; 
lean_inc_ref(v___y_2594_);
lean_inc_ref(v___y_2598_);
lean_inc(v___y_2597_);
lean_inc(v___y_2596_);
lean_inc(v___y_2595_);
v___x_2601_ = lean_apply_7(v___y_2594_, v___x_2591_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, lean_box(0));
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2614_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_a_2603_ = lean_ctor_get(v___x_2601_, 1);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2605_ = v___x_2601_;
v_isShared_2606_ = v_isSharedCheck_2614_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2614_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; uint8_t v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2607_ = lean_unsigned_to_nat(0u);
v___x_2608_ = 0;
v___x_2609_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2610_ = l_Lake_Job_mapM___redArg(v___x_2592_, v_a_2602_, v___f_2593_, v___x_2607_, v___x_2608_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___x_2609_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2610_);
v___x_2612_ = v___x_2605_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_a_2603_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v___y_2594_);
lean_dec_ref(v___f_2593_);
lean_dec(v___x_2592_);
v_a_2615_ = lean_ctor_get(v___x_2601_, 0);
v_a_2616_ = lean_ctor_get(v___x_2601_, 1);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2601_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_inc(v_a_2615_);
lean_dec(v___x_2601_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2615_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v___x_2624_, lean_object* v___x_2625_, lean_object* v___f_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(v___x_2624_, v___x_2625_, v___f_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec(v___y_2628_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object* v_what_2635_, lean_object* v_optFacet_2636_, lean_object* v___x_2637_, lean_object* v_facet_2638_, lean_object* v_pkg_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_baseName_2647_; lean_object* v_keyName_2648_; lean_object* v___f_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___f_2653_; lean_object* v___x_2654_; 
v_baseName_2647_ = lean_ctor_get(v_pkg_2639_, 1);
lean_inc_n(v_baseName_2647_, 2);
v_keyName_2648_ = lean_ctor_get(v_pkg_2639_, 2);
lean_inc(v_optFacet_2636_);
v___f_2649_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2649_, 0, v_what_2635_);
lean_closure_set(v___f_2649_, 1, v_baseName_2647_);
lean_closure_set(v___f_2649_, 2, v_optFacet_2636_);
lean_inc(v_keyName_2648_);
v___x_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2650_, 0, v_keyName_2648_);
v___x_2651_ = l_Lake_Package_keyword;
v___x_2652_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2650_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
lean_ctor_set(v___x_2652_, 2, v_pkg_2639_);
lean_ctor_set(v___x_2652_, 3, v_optFacet_2636_);
lean_inc(v___x_2637_);
v___f_2653_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2653_, 0, v___x_2652_);
lean_closure_set(v___f_2653_, 1, v___x_2637_);
lean_closure_set(v___f_2653_, 2, v___f_2649_);
v___x_2654_ = l_Lake_ensureJob___redArg(v___x_2637_, v___f_2653_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2687_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
v_a_2656_ = lean_ctor_get(v___x_2654_, 1);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2658_ = v___x_2654_;
v_isShared_2659_ = v_isSharedCheck_2687_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_inc(v_a_2655_);
lean_dec(v___x_2654_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2687_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v_task_2660_; lean_object* v_kind_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2685_; 
v_task_2660_ = lean_ctor_get(v_a_2655_, 0);
v_kind_2661_ = lean_ctor_get(v_a_2655_, 1);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_a_2655_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; 
v_unused_2686_ = lean_ctor_get(v_a_2655_, 2);
lean_dec(v_unused_2686_);
v___x_2663_ = v_a_2655_;
v_isShared_2664_ = v_isSharedCheck_2685_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_kind_2661_);
lean_inc(v_task_2660_);
lean_dec(v_a_2655_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2685_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v_registeredJobs_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; lean_object* v_job_2676_; 
v_registeredJobs_2665_ = lean_ctor_get(v___y_2644_, 4);
v___x_2666_ = lean_st_ref_take(v_registeredJobs_2665_);
v___x_2667_ = 1;
v___x_2668_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2647_, v___x_2667_);
v___x_2669_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2670_ = lean_string_append(v___x_2668_, v___x_2669_);
v___x_2671_ = l_Lake_Name_eraseHead(v_facet_2638_);
v___x_2672_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2671_, v___x_2667_);
v___x_2673_ = lean_string_append(v___x_2670_, v___x_2672_);
lean_dec_ref(v___x_2672_);
v___x_2674_ = 0;
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 2, v___x_2673_);
v_job_2676_ = v___x_2663_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_task_2660_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_kind_2661_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v___x_2673_);
v_job_2676_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2682_; 
lean_ctor_set_uint8(v_job_2676_, sizeof(void*)*3, v___x_2674_);
lean_inc_ref(v_job_2676_);
v___x_2677_ = l_Lake_Job_toOpaque___redArg(v_job_2676_);
v___x_2678_ = lean_array_push(v___x_2666_, v___x_2677_);
v___x_2679_ = lean_st_ref_put(v_registeredJobs_2665_, v___x_2678_);
v___x_2680_ = l_Lake_Job_renew___redArg(v_job_2676_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2680_);
v___x_2682_ = v___x_2658_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v_a_2656_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2647_);
lean_dec(v_facet_2638_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object* v_what_2688_, lean_object* v_optFacet_2689_, lean_object* v___x_2690_, lean_object* v_facet_2691_, lean_object* v_pkg_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(v_what_2688_, v_optFacet_2689_, v___x_2690_, v_facet_2691_, v_pkg_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec(v___y_2694_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object* v_facet_2708_, lean_object* v_optFacet_2709_, lean_object* v_what_2710_){
_start:
{
lean_object* v___x_2711_; lean_object* v___f_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2711_ = l_Lake_instDataKindUnit;
v___f_2712_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2712_, 0, v_what_2710_);
lean_closure_set(v___f_2712_, 1, v_optFacet_2709_);
lean_closure_set(v___f_2712_, 2, v___x_2711_);
lean_closure_set(v___f_2712_, 3, v_facet_2708_);
v___x_2713_ = l_Lake_Package_keyword;
v___x_2714_ = 1;
v___x_2715_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2716_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2716_, 0, v___x_2713_);
lean_ctor_set(v___x_2716_, 1, v___f_2712_);
lean_ctor_set(v___x_2716_, 2, v___x_2711_);
lean_ctor_set(v___x_2716_, 3, v___x_2715_);
lean_ctor_set_uint8(v___x_2716_, sizeof(void*)*4, v___x_2714_);
lean_ctor_set_uint8(v___x_2716_, sizeof(void*)*4 + 1, v___x_2714_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* v_facet_2717_, lean_object* v_optFacet_2718_, lean_object* v_what_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_){
_start:
{
lean_object* v___x_2722_; lean_object* v___f_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2722_ = l_Lake_instDataKindUnit;
v___f_2723_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2723_, 0, v_what_2719_);
lean_closure_set(v___f_2723_, 1, v_optFacet_2718_);
lean_closure_set(v___f_2723_, 2, v___x_2722_);
lean_closure_set(v___f_2723_, 3, v_facet_2717_);
v___x_2724_ = l_Lake_Package_keyword;
v___x_2725_ = 1;
v___x_2726_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2727_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2727_, 0, v___x_2724_);
lean_ctor_set(v___x_2727_, 1, v___f_2723_);
lean_ctor_set(v___x_2727_, 2, v___x_2722_);
lean_ctor_set(v___x_2727_, 3, v___x_2726_);
lean_ctor_set_uint8(v___x_2727_, sizeof(void*)*4, v___x_2725_);
lean_ctor_set_uint8(v___x_2727_, sizeof(void*)*4 + 1, v___x_2725_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* v_baseName_2729_, lean_object* v___x_2730_, uint8_t v_success_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_a_2740_; lean_object* v_a_2741_; 
if (v_success_2731_ == 0)
{
lean_object* v_toBuildConfig_2761_; uint8_t v_verbosity_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v_toBuildConfig_2761_ = lean_ctor_get(v___y_2736_, 0);
v_verbosity_2762_ = lean_ctor_get_uint8(v_toBuildConfig_2761_, sizeof(void*)*4 + 4);
v___x_2763_ = l_Lake_Verbosity_ctorIdx(v_verbosity_2762_);
v___x_2764_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_2765_ = lean_nat_dec_eq(v___x_2763_, v___x_2764_);
lean_dec(v___x_2763_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; 
lean_dec(v___x_2730_);
lean_dec(v_baseName_2729_);
v___x_2766_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_2740_ = v___x_2766_;
v_a_2741_ = v___y_2737_;
goto v___jp_2739_;
}
else
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2767_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2768_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2729_, v___x_2765_);
v___x_2769_ = lean_string_append(v___x_2767_, v___x_2768_);
lean_dec_ref(v___x_2768_);
v___x_2770_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2771_ = lean_string_append(v___x_2769_, v___x_2770_);
v___x_2772_ = l_Lake_Name_eraseHead(v___x_2730_);
v___x_2773_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2772_, v___x_2765_);
v___x_2774_ = lean_string_append(v___x_2771_, v___x_2773_);
lean_dec_ref(v___x_2773_);
v___x_2775_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_2776_ = lean_string_append(v___x_2774_, v___x_2775_);
v_a_2740_ = v___x_2776_;
v_a_2741_ = v___y_2737_;
goto v___jp_2739_;
}
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
lean_dec(v___x_2730_);
lean_dec(v_baseName_2729_);
v___x_2777_ = lean_box(0);
v___x_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
lean_ctor_set(v___x_2778_, 1, v___y_2737_);
return v___x_2778_;
}
v___jp_2739_:
{
lean_object* v_log_2742_; uint8_t v_action_2743_; uint8_t v_wantsRebuild_2744_; lean_object* v_trace_2745_; lean_object* v_buildTime_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2760_; 
v_log_2742_ = lean_ctor_get(v_a_2741_, 0);
v_action_2743_ = lean_ctor_get_uint8(v_a_2741_, sizeof(void*)*3);
v_wantsRebuild_2744_ = lean_ctor_get_uint8(v_a_2741_, sizeof(void*)*3 + 1);
v_trace_2745_ = lean_ctor_get(v_a_2741_, 1);
v_buildTime_2746_ = lean_ctor_get(v_a_2741_, 2);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_a_2741_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2748_ = v_a_2741_;
v_isShared_2749_ = v_isSharedCheck_2760_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_buildTime_2746_);
lean_inc(v_trace_2745_);
lean_inc(v_log_2742_);
lean_dec(v_a_2741_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2760_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2750_ = ((lean_object*)(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0));
v___x_2751_ = lean_string_append(v___x_2750_, v_a_2740_);
lean_dec_ref(v_a_2740_);
v___x_2752_ = 3;
v___x_2753_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set_uint8(v___x_2753_, sizeof(void*)*1, v___x_2752_);
v___x_2754_ = lean_array_get_size(v_log_2742_);
v___x_2755_ = lean_array_push(v_log_2742_, v___x_2753_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2755_);
v___x_2757_ = v___x_2748_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_trace_2745_);
lean_ctor_set(v_reuseFailAlloc_2759_, 2, v_buildTime_2746_);
lean_ctor_set_uint8(v_reuseFailAlloc_2759_, sizeof(void*)*3, v_action_2743_);
lean_ctor_set_uint8(v_reuseFailAlloc_2759_, sizeof(void*)*3 + 1, v_wantsRebuild_2744_);
v___x_2757_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2754_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
return v___x_2758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object* v_baseName_2779_, lean_object* v___x_2780_, lean_object* v_success_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
uint8_t v_success_boxed_2789_; lean_object* v_res_2790_; 
v_success_boxed_2789_ = lean_unbox(v_success_2781_);
v_res_2790_ = l_Lake_Package_buildCacheFacetConfig___lam__1(v_baseName_2779_, v___x_2780_, v_success_boxed_2789_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* v___x_2791_, lean_object* v___x_2792_, lean_object* v___x_2793_, lean_object* v_pkg_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_baseName_2802_; lean_object* v_keyName_2803_; lean_object* v___f_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___f_2808_; lean_object* v___x_2809_; 
v_baseName_2802_ = lean_ctor_get(v_pkg_2794_, 1);
lean_inc_n(v_baseName_2802_, 2);
v_keyName_2803_ = lean_ctor_get(v_pkg_2794_, 2);
lean_inc(v___x_2791_);
v___f_2804_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2804_, 0, v_baseName_2802_);
lean_closure_set(v___f_2804_, 1, v___x_2791_);
lean_inc(v_keyName_2803_);
v___x_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2805_, 0, v_keyName_2803_);
v___x_2806_ = l_Lake_Package_keyword;
v___x_2807_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2805_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
lean_ctor_set(v___x_2807_, 2, v_pkg_2794_);
lean_ctor_set(v___x_2807_, 3, v___x_2791_);
lean_inc(v___x_2792_);
v___f_2808_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2808_, 0, v___x_2807_);
lean_closure_set(v___f_2808_, 1, v___x_2792_);
lean_closure_set(v___f_2808_, 2, v___f_2804_);
v___x_2809_ = l_Lake_ensureJob___redArg(v___x_2792_, v___f_2808_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2842_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
v_a_2811_ = lean_ctor_get(v___x_2809_, 1);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2813_ = v___x_2809_;
v_isShared_2814_ = v_isSharedCheck_2842_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_inc(v_a_2810_);
lean_dec(v___x_2809_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2842_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v_task_2815_; lean_object* v_kind_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2840_; 
v_task_2815_ = lean_ctor_get(v_a_2810_, 0);
v_kind_2816_ = lean_ctor_get(v_a_2810_, 1);
v_isSharedCheck_2840_ = !lean_is_exclusive(v_a_2810_);
if (v_isSharedCheck_2840_ == 0)
{
lean_object* v_unused_2841_; 
v_unused_2841_ = lean_ctor_get(v_a_2810_, 2);
lean_dec(v_unused_2841_);
v___x_2818_ = v_a_2810_;
v_isShared_2819_ = v_isSharedCheck_2840_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_kind_2816_);
lean_inc(v_task_2815_);
lean_dec(v_a_2810_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2840_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_registeredJobs_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; uint8_t v___x_2829_; lean_object* v_job_2831_; 
v_registeredJobs_2820_ = lean_ctor_get(v___y_2799_, 4);
v___x_2821_ = lean_st_ref_take(v_registeredJobs_2820_);
v___x_2822_ = 1;
v___x_2823_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2802_, v___x_2822_);
v___x_2824_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2825_ = lean_string_append(v___x_2823_, v___x_2824_);
v___x_2826_ = l_Lake_Name_eraseHead(v___x_2793_);
v___x_2827_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2826_, v___x_2822_);
v___x_2828_ = lean_string_append(v___x_2825_, v___x_2827_);
lean_dec_ref(v___x_2827_);
v___x_2829_ = 0;
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 2, v___x_2828_);
v_job_2831_ = v___x_2818_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_task_2815_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_kind_2816_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v___x_2828_);
v_job_2831_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2837_; 
lean_ctor_set_uint8(v_job_2831_, sizeof(void*)*3, v___x_2829_);
lean_inc_ref(v_job_2831_);
v___x_2832_ = l_Lake_Job_toOpaque___redArg(v_job_2831_);
v___x_2833_ = lean_array_push(v___x_2821_, v___x_2832_);
v___x_2834_ = lean_st_ref_put(v_registeredJobs_2820_, v___x_2833_);
v___x_2835_ = l_Lake_Job_renew___redArg(v_job_2831_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2835_);
v___x_2837_ = v___x_2813_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_a_2811_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2802_);
lean_dec(v___x_2793_);
return v___x_2809_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object* v___x_2843_, lean_object* v___x_2844_, lean_object* v___x_2845_, lean_object* v_pkg_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l_Lake_Package_buildCacheFacetConfig___lam__2(v___x_2843_, v___x_2844_, v___x_2845_, v_pkg_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec(v___y_2848_);
return v_res_2854_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___f_2858_; 
v___x_2855_ = l_Lake_Package_buildCacheFacet;
v___x_2856_ = l_Lake_instDataKindUnit;
v___x_2857_ = l_Lake_Package_optBuildCacheFacet;
v___f_2858_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2858_, 0, v___x_2857_);
lean_closure_set(v___f_2858_, 1, v___x_2856_);
lean_closure_set(v___f_2858_, 2, v___x_2855_);
return v___f_2858_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2859_; uint8_t v___x_2860_; lean_object* v___x_2861_; lean_object* v___f_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___f_2859_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2860_ = 1;
v___x_2861_ = l_Lake_instDataKindUnit;
v___f_2862_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__0, &l_Lake_Package_buildCacheFacetConfig___closed__0_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__0);
v___x_2863_ = l_Lake_Package_keyword;
v___x_2864_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
lean_ctor_set(v___x_2864_, 1, v___f_2862_);
lean_ctor_set(v___x_2864_, 2, v___x_2861_);
lean_ctor_set(v___x_2864_, 3, v___f_2859_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*4, v___x_2860_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*4 + 1, v___x_2860_);
return v___x_2864_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig(void){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__1, &l_Lake_Package_buildCacheFacetConfig___closed__1_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__1);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* v_pkg_2867_, lean_object* v___x_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
uint8_t v_r_2877_; lean_object* v___y_2878_; lean_object* v_a_2882_; lean_object* v___x_2898_; 
lean_inc_ref(v_pkg_2867_);
v___x_2898_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_pkg_2867_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v_a_2900_; lean_object* v_dir_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
v_a_2900_ = lean_ctor_get(v___x_2898_, 1);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2898_, 2);
v_dir_2901_ = lean_ctor_get(v_pkg_2867_, 4);
v___x_2902_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_2901_);
v___x_2903_ = l_Lake_joinRelative(v_dir_2901_, v___x_2902_);
v___x_2904_ = ((lean_object*)(l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0));
v___x_2905_ = l_Lake_joinRelative(v___x_2903_, v___x_2904_);
v___x_2906_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2867_, v_a_2899_, v___x_2905_, v___x_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v_a_2900_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; uint8_t v___x_2908_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 1);
lean_inc(v_a_2907_);
lean_dec_ref_known(v___x_2906_, 2);
v___x_2908_ = 1;
v_r_2877_ = v___x_2908_;
v___y_2878_ = v_a_2907_;
goto v___jp_2876_;
}
else
{
lean_object* v_a_2909_; 
v_a_2909_ = lean_ctor_get(v___x_2906_, 1);
lean_inc(v_a_2909_);
lean_dec_ref_known(v___x_2906_, 2);
v_a_2882_ = v_a_2909_;
goto v___jp_2881_;
}
}
else
{
lean_object* v_a_2910_; 
lean_dec_ref(v_pkg_2867_);
v_a_2910_ = lean_ctor_get(v___x_2898_, 1);
lean_inc(v_a_2910_);
lean_dec_ref_known(v___x_2898_, 2);
v_a_2882_ = v_a_2910_;
goto v___jp_2881_;
}
v___jp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2879_ = lean_box(v_r_2877_);
v___x_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
lean_ctor_set(v___x_2880_, 1, v___y_2878_);
return v___x_2880_;
}
v___jp_2881_:
{
lean_object* v_log_2883_; uint8_t v_action_2884_; uint8_t v_wantsRebuild_2885_; lean_object* v_trace_2886_; lean_object* v_buildTime_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2897_; 
v_log_2883_ = lean_ctor_get(v_a_2882_, 0);
v_action_2884_ = lean_ctor_get_uint8(v_a_2882_, sizeof(void*)*3);
v_wantsRebuild_2885_ = lean_ctor_get_uint8(v_a_2882_, sizeof(void*)*3 + 1);
v_trace_2886_ = lean_ctor_get(v_a_2882_, 1);
v_buildTime_2887_ = lean_ctor_get(v_a_2882_, 2);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_a_2882_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2889_ = v_a_2882_;
v_isShared_2890_ = v_isSharedCheck_2897_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_buildTime_2887_);
lean_inc(v_trace_2886_);
lean_inc(v_log_2883_);
lean_dec(v_a_2882_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2897_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
uint8_t v___x_2891_; uint8_t v___x_2892_; lean_object* v___x_2894_; 
v___x_2891_ = 4;
v___x_2892_ = l_Lake_JobAction_merge(v_action_2884_, v___x_2891_);
if (v_isShared_2890_ == 0)
{
v___x_2894_ = v___x_2889_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_log_2883_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_trace_2886_);
lean_ctor_set(v_reuseFailAlloc_2896_, 2, v_buildTime_2887_);
lean_ctor_set_uint8(v_reuseFailAlloc_2896_, sizeof(void*)*3 + 1, v_wantsRebuild_2885_);
v___x_2894_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
uint8_t v___x_2895_; 
lean_ctor_set_uint8(v___x_2894_, sizeof(void*)*3, v___x_2892_);
v___x_2895_ = 0;
v_r_2877_ = v___x_2895_;
v___y_2878_ = v___x_2894_;
goto v___jp_2876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* v_pkg_2911_, lean_object* v___x_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lake_Package_optBarrelFacetConfig___lam__0(v_pkg_2911_, v___x_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec_ref(v___x_2912_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* v___x_2921_, lean_object* v___f_2922_, lean_object* v___x_2923_, lean_object* v___x_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2932_ = l_Lake_Job_async___redArg(v___x_2921_, v___f_2922_, v___x_2923_, v___x_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
v___x_2933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
lean_ctor_set(v___x_2933_, 1, v___y_2930_);
return v___x_2933_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object* v___x_2934_, lean_object* v___f_2935_, lean_object* v___x_2936_, lean_object* v___x_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lake_Package_optBarrelFacetConfig___lam__1(v___x_2934_, v___f_2935_, v___x_2936_, v___x_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec(v___y_2939_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* v___x_2946_, lean_object* v___x_2947_, lean_object* v___x_2948_, lean_object* v_pkg_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v___f_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___f_2960_; lean_object* v___x_2961_; 
lean_inc_ref(v_pkg_2949_);
v___f_2957_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2957_, 0, v_pkg_2949_);
lean_closure_set(v___f_2957_, 1, v___x_2946_);
v___x_2958_ = lean_unsigned_to_nat(0u);
v___x_2959_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2947_);
v___f_2960_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2960_, 0, v___x_2947_);
lean_closure_set(v___f_2960_, 1, v___f_2957_);
lean_closure_set(v___f_2960_, 2, v___x_2958_);
lean_closure_set(v___f_2960_, 3, v___x_2959_);
v___x_2961_ = l_Lake_ensureJob___redArg(v___x_2947_, v___f_2960_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2994_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
v_a_2963_ = lean_ctor_get(v___x_2961_, 1);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2965_ = v___x_2961_;
v_isShared_2966_ = v_isSharedCheck_2994_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_inc(v_a_2962_);
lean_dec(v___x_2961_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2994_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v_task_2967_; lean_object* v_kind_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2992_; 
v_task_2967_ = lean_ctor_get(v_a_2962_, 0);
v_kind_2968_ = lean_ctor_get(v_a_2962_, 1);
v_isSharedCheck_2992_ = !lean_is_exclusive(v_a_2962_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; 
v_unused_2993_ = lean_ctor_get(v_a_2962_, 2);
lean_dec(v_unused_2993_);
v___x_2970_ = v_a_2962_;
v_isShared_2971_ = v_isSharedCheck_2992_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_kind_2968_);
lean_inc(v_task_2967_);
lean_dec(v_a_2962_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2992_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v_registeredJobs_2972_; lean_object* v___x_2973_; lean_object* v_baseName_2974_; uint8_t v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v_job_2983_; 
v_registeredJobs_2972_ = lean_ctor_get(v___y_2954_, 4);
v___x_2973_ = lean_st_ref_take(v_registeredJobs_2972_);
v_baseName_2974_ = lean_ctor_get(v_pkg_2949_, 1);
lean_inc(v_baseName_2974_);
lean_dec_ref(v_pkg_2949_);
v___x_2975_ = 1;
v___x_2976_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2974_, v___x_2975_);
v___x_2977_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2978_ = lean_string_append(v___x_2976_, v___x_2977_);
v___x_2979_ = l_Lake_Name_eraseHead(v___x_2948_);
v___x_2980_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2979_, v___x_2975_);
v___x_2981_ = lean_string_append(v___x_2978_, v___x_2980_);
lean_dec_ref(v___x_2980_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 2, v___x_2981_);
v_job_2983_ = v___x_2970_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_task_2967_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_kind_2968_);
lean_ctor_set(v_reuseFailAlloc_2991_, 2, v___x_2981_);
v_job_2983_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; 
lean_ctor_set_uint8(v_job_2983_, sizeof(void*)*3, v___x_2975_);
lean_inc_ref(v_job_2983_);
v___x_2984_ = l_Lake_Job_toOpaque___redArg(v_job_2983_);
v___x_2985_ = lean_array_push(v___x_2973_, v___x_2984_);
v___x_2986_ = lean_st_ref_put(v_registeredJobs_2972_, v___x_2985_);
v___x_2987_ = l_Lake_Job_renew___redArg(v_job_2983_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 0, v___x_2987_);
v___x_2989_ = v___x_2965_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_a_2963_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_2949_);
lean_dec(v___x_2948_);
return v___x_2961_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object* v___x_2995_, lean_object* v___x_2996_, lean_object* v___x_2997_, lean_object* v_pkg_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l_Lake_Package_optBarrelFacetConfig___lam__2(v___x_2995_, v___x_2996_, v___x_2997_, v_pkg_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec(v___y_3000_);
return v_res_3006_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___f_3010_; 
v___x_3007_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3008_ = l_Lake_instDataKindBool;
v___x_3009_ = l_Lake_Reservoir_lakeHeaders;
v___f_3010_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3010_, 0, v___x_3009_);
lean_closure_set(v___f_3010_, 1, v___x_3008_);
lean_closure_set(v___f_3010_, 2, v___x_3007_);
return v___f_3010_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3011_; uint8_t v___x_3012_; lean_object* v___x_3013_; lean_object* v___f_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___f_3011_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_3012_ = 1;
v___x_3013_ = l_Lake_instDataKindBool;
v___f_3014_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__0, &l_Lake_Package_optBarrelFacetConfig___closed__0_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__0);
v___x_3015_ = l_Lake_Package_keyword;
v___x_3016_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
lean_ctor_set(v___x_3016_, 1, v___f_3014_);
lean_ctor_set(v___x_3016_, 2, v___x_3013_);
lean_ctor_set(v___x_3016_, 3, v___f_3011_);
lean_ctor_set_uint8(v___x_3016_, sizeof(void*)*4, v___x_3012_);
lean_ctor_set_uint8(v___x_3016_, sizeof(void*)*4 + 1, v___x_3012_);
return v___x_3016_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig(void){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__1, &l_Lake_Package_optBarrelFacetConfig___closed__1_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__1);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* v_baseName_3019_, lean_object* v___x_3020_, uint8_t v_success_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
lean_object* v_a_3030_; lean_object* v_a_3031_; 
if (v_success_3021_ == 0)
{
lean_object* v_toBuildConfig_3051_; uint8_t v_verbosity_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; 
v_toBuildConfig_3051_ = lean_ctor_get(v___y_3026_, 0);
v_verbosity_3052_ = lean_ctor_get_uint8(v_toBuildConfig_3051_, sizeof(void*)*4 + 4);
v___x_3053_ = l_Lake_Verbosity_ctorIdx(v_verbosity_3052_);
v___x_3054_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_3055_ = lean_nat_dec_eq(v___x_3053_, v___x_3054_);
lean_dec(v___x_3053_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
lean_dec(v___x_3020_);
lean_dec(v_baseName_3019_);
v___x_3056_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_3030_ = v___x_3056_;
v_a_3031_ = v___y_3027_;
goto v___jp_3029_;
}
else
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3057_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3058_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3019_, v___x_3055_);
v___x_3059_ = lean_string_append(v___x_3057_, v___x_3058_);
lean_dec_ref(v___x_3058_);
v___x_3060_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3061_ = lean_string_append(v___x_3059_, v___x_3060_);
v___x_3062_ = l_Lake_Name_eraseHead(v___x_3020_);
v___x_3063_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3062_, v___x_3055_);
v___x_3064_ = lean_string_append(v___x_3061_, v___x_3063_);
lean_dec_ref(v___x_3063_);
v___x_3065_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_3066_ = lean_string_append(v___x_3064_, v___x_3065_);
v_a_3030_ = v___x_3066_;
v_a_3031_ = v___y_3027_;
goto v___jp_3029_;
}
}
else
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
lean_dec(v___x_3020_);
lean_dec(v_baseName_3019_);
v___x_3067_ = lean_box(0);
v___x_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
lean_ctor_set(v___x_3068_, 1, v___y_3027_);
return v___x_3068_;
}
v___jp_3029_:
{
lean_object* v_log_3032_; uint8_t v_action_3033_; uint8_t v_wantsRebuild_3034_; lean_object* v_trace_3035_; lean_object* v_buildTime_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3050_; 
v_log_3032_ = lean_ctor_get(v_a_3031_, 0);
v_action_3033_ = lean_ctor_get_uint8(v_a_3031_, sizeof(void*)*3);
v_wantsRebuild_3034_ = lean_ctor_get_uint8(v_a_3031_, sizeof(void*)*3 + 1);
v_trace_3035_ = lean_ctor_get(v_a_3031_, 1);
v_buildTime_3036_ = lean_ctor_get(v_a_3031_, 2);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_a_3031_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3038_ = v_a_3031_;
v_isShared_3039_ = v_isSharedCheck_3050_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_buildTime_3036_);
lean_inc(v_trace_3035_);
lean_inc(v_log_3032_);
lean_dec(v_a_3031_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3050_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3040_ = ((lean_object*)(l_Lake_Package_barrelFacetConfig___lam__1___closed__0));
v___x_3041_ = lean_string_append(v___x_3040_, v_a_3030_);
lean_dec_ref(v_a_3030_);
v___x_3042_ = 3;
v___x_3043_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3043_, 0, v___x_3041_);
lean_ctor_set_uint8(v___x_3043_, sizeof(void*)*1, v___x_3042_);
v___x_3044_ = lean_array_get_size(v_log_3032_);
v___x_3045_ = lean_array_push(v_log_3032_, v___x_3043_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3045_);
v___x_3047_ = v___x_3038_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_trace_3035_);
lean_ctor_set(v_reuseFailAlloc_3049_, 2, v_buildTime_3036_);
lean_ctor_set_uint8(v_reuseFailAlloc_3049_, sizeof(void*)*3, v_action_3033_);
lean_ctor_set_uint8(v_reuseFailAlloc_3049_, sizeof(void*)*3 + 1, v_wantsRebuild_3034_);
v___x_3047_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
lean_object* v___x_3048_; 
v___x_3048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3044_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
return v___x_3048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object* v_baseName_3069_, lean_object* v___x_3070_, lean_object* v_success_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
uint8_t v_success_boxed_3079_; lean_object* v_res_3080_; 
v_success_boxed_3079_ = lean_unbox(v_success_3071_);
v_res_3080_ = l_Lake_Package_barrelFacetConfig___lam__1(v_baseName_3069_, v___x_3070_, v_success_boxed_3079_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* v___x_3081_, lean_object* v___x_3082_, lean_object* v___x_3083_, lean_object* v_pkg_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_baseName_3092_; lean_object* v_keyName_3093_; lean_object* v___f_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___f_3098_; lean_object* v___x_3099_; 
v_baseName_3092_ = lean_ctor_get(v_pkg_3084_, 1);
lean_inc_n(v_baseName_3092_, 2);
v_keyName_3093_ = lean_ctor_get(v_pkg_3084_, 2);
lean_inc(v___x_3081_);
v___f_3094_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3094_, 0, v_baseName_3092_);
lean_closure_set(v___f_3094_, 1, v___x_3081_);
lean_inc(v_keyName_3093_);
v___x_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3095_, 0, v_keyName_3093_);
v___x_3096_ = l_Lake_Package_keyword;
v___x_3097_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3095_);
lean_ctor_set(v___x_3097_, 1, v___x_3096_);
lean_ctor_set(v___x_3097_, 2, v_pkg_3084_);
lean_ctor_set(v___x_3097_, 3, v___x_3081_);
lean_inc(v___x_3082_);
v___f_3098_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3098_, 0, v___x_3097_);
lean_closure_set(v___f_3098_, 1, v___x_3082_);
lean_closure_set(v___f_3098_, 2, v___f_3094_);
v___x_3099_ = l_Lake_ensureJob___redArg(v___x_3082_, v___f_3098_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3132_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
v_a_3101_ = lean_ctor_get(v___x_3099_, 1);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3103_ = v___x_3099_;
v_isShared_3104_ = v_isSharedCheck_3132_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_inc(v_a_3100_);
lean_dec(v___x_3099_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3132_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v_task_3105_; lean_object* v_kind_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3130_; 
v_task_3105_ = lean_ctor_get(v_a_3100_, 0);
v_kind_3106_ = lean_ctor_get(v_a_3100_, 1);
v_isSharedCheck_3130_ = !lean_is_exclusive(v_a_3100_);
if (v_isSharedCheck_3130_ == 0)
{
lean_object* v_unused_3131_; 
v_unused_3131_ = lean_ctor_get(v_a_3100_, 2);
lean_dec(v_unused_3131_);
v___x_3108_ = v_a_3100_;
v_isShared_3109_ = v_isSharedCheck_3130_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_kind_3106_);
lean_inc(v_task_3105_);
lean_dec(v_a_3100_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3130_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v_registeredJobs_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; lean_object* v_job_3121_; 
v_registeredJobs_3110_ = lean_ctor_get(v___y_3089_, 4);
v___x_3111_ = lean_st_ref_take(v_registeredJobs_3110_);
v___x_3112_ = 1;
v___x_3113_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3092_, v___x_3112_);
v___x_3114_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3115_ = lean_string_append(v___x_3113_, v___x_3114_);
v___x_3116_ = l_Lake_Name_eraseHead(v___x_3083_);
v___x_3117_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3116_, v___x_3112_);
v___x_3118_ = lean_string_append(v___x_3115_, v___x_3117_);
lean_dec_ref(v___x_3117_);
v___x_3119_ = 0;
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 2, v___x_3118_);
v_job_3121_ = v___x_3108_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_task_3105_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v_kind_3106_);
lean_ctor_set(v_reuseFailAlloc_3129_, 2, v___x_3118_);
v_job_3121_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3127_; 
lean_ctor_set_uint8(v_job_3121_, sizeof(void*)*3, v___x_3119_);
lean_inc_ref(v_job_3121_);
v___x_3122_ = l_Lake_Job_toOpaque___redArg(v_job_3121_);
v___x_3123_ = lean_array_push(v___x_3111_, v___x_3122_);
v___x_3124_ = lean_st_ref_put(v_registeredJobs_3110_, v___x_3123_);
v___x_3125_ = l_Lake_Job_renew___redArg(v_job_3121_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3125_);
v___x_3127_ = v___x_3103_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3125_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_a_3101_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
}
else
{
lean_dec(v_baseName_3092_);
lean_dec(v___x_3083_);
return v___x_3099_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object* v___x_3133_, lean_object* v___x_3134_, lean_object* v___x_3135_, lean_object* v_pkg_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_Lake_Package_barrelFacetConfig___lam__2(v___x_3133_, v___x_3134_, v___x_3135_, v_pkg_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec(v___y_3138_);
return v_res_3144_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___f_3148_; 
v___x_3145_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3146_ = l_Lake_instDataKindUnit;
v___x_3147_ = l_Lake_Package_optReservoirBarrelFacet;
v___f_3148_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3148_, 0, v___x_3147_);
lean_closure_set(v___f_3148_, 1, v___x_3146_);
lean_closure_set(v___f_3148_, 2, v___x_3145_);
return v___f_3148_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3149_; uint8_t v___x_3150_; lean_object* v___x_3151_; lean_object* v___f_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___f_3149_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3150_ = 1;
v___x_3151_ = l_Lake_instDataKindUnit;
v___f_3152_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__0, &l_Lake_Package_barrelFacetConfig___closed__0_once, _init_l_Lake_Package_barrelFacetConfig___closed__0);
v___x_3153_ = l_Lake_Package_keyword;
v___x_3154_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
lean_ctor_set(v___x_3154_, 1, v___f_3152_);
lean_ctor_set(v___x_3154_, 2, v___x_3151_);
lean_ctor_set(v___x_3154_, 3, v___f_3149_);
lean_ctor_set_uint8(v___x_3154_, sizeof(void*)*4, v___x_3150_);
lean_ctor_set_uint8(v___x_3154_, sizeof(void*)*4 + 1, v___x_3150_);
return v___x_3154_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig(void){
_start:
{
lean_object* v___x_3155_; 
v___x_3155_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__1, &l_Lake_Package_barrelFacetConfig___closed__1_once, _init_l_Lake_Package_barrelFacetConfig___closed__1);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object* v_pkg_3156_, lean_object* v___x_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
uint8_t v_r_3166_; lean_object* v___y_3167_; lean_object* v_a_3171_; lean_object* v___x_3187_; 
lean_inc_ref(v_pkg_3156_);
v___x_3187_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_pkg_3156_, v___y_3163_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v_a_3189_; lean_object* v_dir_3190_; lean_object* v_buildArchive_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
v_a_3189_ = lean_ctor_get(v___x_3187_, 1);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3187_, 2);
v_dir_3190_ = lean_ctor_get(v_pkg_3156_, 4);
v_buildArchive_3191_ = lean_ctor_get(v_pkg_3156_, 21);
v___x_3192_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_3190_);
v___x_3193_ = l_Lake_joinRelative(v_dir_3190_, v___x_3192_);
lean_inc_ref(v_buildArchive_3191_);
v___x_3194_ = l_Lake_joinRelative(v___x_3193_, v_buildArchive_3191_);
v___x_3195_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_3156_, v_a_3188_, v___x_3194_, v___x_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v_a_3189_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; uint8_t v___x_3197_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 1);
lean_inc(v_a_3196_);
lean_dec_ref_known(v___x_3195_, 2);
v___x_3197_ = 1;
v_r_3166_ = v___x_3197_;
v___y_3167_ = v_a_3196_;
goto v___jp_3165_;
}
else
{
lean_object* v_a_3198_; 
v_a_3198_ = lean_ctor_get(v___x_3195_, 1);
lean_inc(v_a_3198_);
lean_dec_ref_known(v___x_3195_, 2);
v_a_3171_ = v_a_3198_;
goto v___jp_3170_;
}
}
else
{
lean_object* v_a_3199_; 
lean_dec_ref(v_pkg_3156_);
v_a_3199_ = lean_ctor_get(v___x_3187_, 1);
lean_inc(v_a_3199_);
lean_dec_ref_known(v___x_3187_, 2);
v_a_3171_ = v_a_3199_;
goto v___jp_3170_;
}
v___jp_3165_:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = lean_box(v_r_3166_);
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
lean_ctor_set(v___x_3169_, 1, v___y_3167_);
return v___x_3169_;
}
v___jp_3170_:
{
lean_object* v_log_3172_; uint8_t v_action_3173_; uint8_t v_wantsRebuild_3174_; lean_object* v_trace_3175_; lean_object* v_buildTime_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3186_; 
v_log_3172_ = lean_ctor_get(v_a_3171_, 0);
v_action_3173_ = lean_ctor_get_uint8(v_a_3171_, sizeof(void*)*3);
v_wantsRebuild_3174_ = lean_ctor_get_uint8(v_a_3171_, sizeof(void*)*3 + 1);
v_trace_3175_ = lean_ctor_get(v_a_3171_, 1);
v_buildTime_3176_ = lean_ctor_get(v_a_3171_, 2);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_a_3171_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3178_ = v_a_3171_;
v_isShared_3179_ = v_isSharedCheck_3186_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_buildTime_3176_);
lean_inc(v_trace_3175_);
lean_inc(v_log_3172_);
lean_dec(v_a_3171_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3186_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
uint8_t v___x_3180_; uint8_t v___x_3181_; lean_object* v___x_3183_; 
v___x_3180_ = 4;
v___x_3181_ = l_Lake_JobAction_merge(v_action_3173_, v___x_3180_);
if (v_isShared_3179_ == 0)
{
v___x_3183_ = v___x_3178_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_log_3172_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v_trace_3175_);
lean_ctor_set(v_reuseFailAlloc_3185_, 2, v_buildTime_3176_);
lean_ctor_set_uint8(v_reuseFailAlloc_3185_, sizeof(void*)*3 + 1, v_wantsRebuild_3174_);
v___x_3183_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
uint8_t v___x_3184_; 
lean_ctor_set_uint8(v___x_3183_, sizeof(void*)*3, v___x_3181_);
v___x_3184_ = 0;
v_r_3166_ = v___x_3184_;
v___y_3167_ = v___x_3183_;
goto v___jp_3165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object* v_pkg_3200_, lean_object* v___x_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(v_pkg_3200_, v___x_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec_ref(v___x_3201_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object* v___x_3210_, lean_object* v___x_3211_, lean_object* v___x_3212_, lean_object* v___x_3213_, lean_object* v_pkg_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v___f_3222_; lean_object* v___x_3223_; lean_object* v___f_3224_; lean_object* v___x_3225_; 
lean_inc_ref(v_pkg_3214_);
v___f_3222_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3222_, 0, v_pkg_3214_);
lean_closure_set(v___f_3222_, 1, v___x_3210_);
v___x_3223_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_3211_);
v___f_3224_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_3224_, 0, v___x_3211_);
lean_closure_set(v___f_3224_, 1, v___f_3222_);
lean_closure_set(v___f_3224_, 2, v___x_3212_);
lean_closure_set(v___f_3224_, 3, v___x_3223_);
v___x_3225_ = l_Lake_ensureJob___redArg(v___x_3211_, v___f_3224_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3258_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_a_3227_ = lean_ctor_get(v___x_3225_, 1);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3229_ = v___x_3225_;
v_isShared_3230_ = v_isSharedCheck_3258_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3258_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v_task_3231_; lean_object* v_kind_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3256_; 
v_task_3231_ = lean_ctor_get(v_a_3226_, 0);
v_kind_3232_ = lean_ctor_get(v_a_3226_, 1);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_a_3226_);
if (v_isSharedCheck_3256_ == 0)
{
lean_object* v_unused_3257_; 
v_unused_3257_ = lean_ctor_get(v_a_3226_, 2);
lean_dec(v_unused_3257_);
v___x_3234_ = v_a_3226_;
v_isShared_3235_ = v_isSharedCheck_3256_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_kind_3232_);
lean_inc(v_task_3231_);
lean_dec(v_a_3226_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3256_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v_registeredJobs_3236_; lean_object* v___x_3237_; lean_object* v_baseName_3238_; uint8_t v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v_job_3247_; 
v_registeredJobs_3236_ = lean_ctor_get(v___y_3219_, 4);
v___x_3237_ = lean_st_ref_take(v_registeredJobs_3236_);
v_baseName_3238_ = lean_ctor_get(v_pkg_3214_, 1);
lean_inc(v_baseName_3238_);
lean_dec_ref(v_pkg_3214_);
v___x_3239_ = 1;
v___x_3240_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3238_, v___x_3239_);
v___x_3241_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3242_ = lean_string_append(v___x_3240_, v___x_3241_);
v___x_3243_ = l_Lake_Name_eraseHead(v___x_3213_);
v___x_3244_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3243_, v___x_3239_);
v___x_3245_ = lean_string_append(v___x_3242_, v___x_3244_);
lean_dec_ref(v___x_3244_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 2, v___x_3245_);
v_job_3247_ = v___x_3234_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_task_3231_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v_kind_3232_);
lean_ctor_set(v_reuseFailAlloc_3255_, 2, v___x_3245_);
v_job_3247_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3253_; 
lean_ctor_set_uint8(v_job_3247_, sizeof(void*)*3, v___x_3239_);
lean_inc_ref(v_job_3247_);
v___x_3248_ = l_Lake_Job_toOpaque___redArg(v_job_3247_);
v___x_3249_ = lean_array_push(v___x_3237_, v___x_3248_);
v___x_3250_ = lean_st_ref_put(v_registeredJobs_3236_, v___x_3249_);
v___x_3251_ = l_Lake_Job_renew___redArg(v_job_3247_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 0, v___x_3251_);
v___x_3253_ = v___x_3229_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v_a_3227_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_3214_);
lean_dec(v___x_3213_);
return v___x_3225_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_3259_, lean_object* v___x_3260_, lean_object* v___x_3261_, lean_object* v___x_3262_, lean_object* v_pkg_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(v___x_3259_, v___x_3260_, v___x_3261_, v___x_3262_, v_pkg_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec(v___y_3265_);
return v_res_3271_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___f_3278_; 
v___x_3274_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3275_ = lean_unsigned_to_nat(0u);
v___x_3276_ = l_Lake_instDataKindBool;
v___x_3277_ = ((lean_object*)(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0));
v___f_3278_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed), 12, 4);
lean_closure_set(v___f_3278_, 0, v___x_3277_);
lean_closure_set(v___f_3278_, 1, v___x_3276_);
lean_closure_set(v___f_3278_, 2, v___x_3275_);
lean_closure_set(v___f_3278_, 3, v___x_3274_);
return v___f_3278_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3279_; uint8_t v___x_3280_; lean_object* v___x_3281_; lean_object* v___f_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___f_3279_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_3280_ = 1;
v___x_3281_ = l_Lake_instDataKindBool;
v___f_3282_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__1, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1);
v___x_3283_ = l_Lake_Package_keyword;
v___x_3284_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
lean_ctor_set(v___x_3284_, 1, v___f_3282_);
lean_ctor_set(v___x_3284_, 2, v___x_3281_);
lean_ctor_set(v___x_3284_, 3, v___f_3279_);
lean_ctor_set_uint8(v___x_3284_, sizeof(void*)*4, v___x_3280_);
lean_ctor_set_uint8(v___x_3284_, sizeof(void*)*4 + 1, v___x_3280_);
return v___x_3284_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__2, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* v_baseName_3287_, lean_object* v___x_3288_, uint8_t v_success_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_a_3298_; lean_object* v_a_3299_; 
if (v_success_3289_ == 0)
{
lean_object* v_toBuildConfig_3319_; uint8_t v_verbosity_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; uint8_t v___x_3323_; 
v_toBuildConfig_3319_ = lean_ctor_get(v___y_3294_, 0);
v_verbosity_3320_ = lean_ctor_get_uint8(v_toBuildConfig_3319_, sizeof(void*)*4 + 4);
v___x_3321_ = l_Lake_Verbosity_ctorIdx(v_verbosity_3320_);
v___x_3322_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_3323_ = lean_nat_dec_eq(v___x_3321_, v___x_3322_);
lean_dec(v___x_3321_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; 
lean_dec(v___x_3288_);
lean_dec(v_baseName_3287_);
v___x_3324_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_3298_ = v___x_3324_;
v_a_3299_ = v___y_3295_;
goto v___jp_3297_;
}
else
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3325_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3326_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3287_, v___x_3323_);
v___x_3327_ = lean_string_append(v___x_3325_, v___x_3326_);
lean_dec_ref(v___x_3326_);
v___x_3328_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3329_ = lean_string_append(v___x_3327_, v___x_3328_);
v___x_3330_ = l_Lake_Name_eraseHead(v___x_3288_);
v___x_3331_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3330_, v___x_3323_);
v___x_3332_ = lean_string_append(v___x_3329_, v___x_3331_);
lean_dec_ref(v___x_3331_);
v___x_3333_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_3334_ = lean_string_append(v___x_3332_, v___x_3333_);
v_a_3298_ = v___x_3334_;
v_a_3299_ = v___y_3295_;
goto v___jp_3297_;
}
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
lean_dec(v___x_3288_);
lean_dec(v_baseName_3287_);
v___x_3335_ = lean_box(0);
v___x_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
lean_ctor_set(v___x_3336_, 1, v___y_3295_);
return v___x_3336_;
}
v___jp_3297_:
{
lean_object* v_log_3300_; uint8_t v_action_3301_; uint8_t v_wantsRebuild_3302_; lean_object* v_trace_3303_; lean_object* v_buildTime_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3318_; 
v_log_3300_ = lean_ctor_get(v_a_3299_, 0);
v_action_3301_ = lean_ctor_get_uint8(v_a_3299_, sizeof(void*)*3);
v_wantsRebuild_3302_ = lean_ctor_get_uint8(v_a_3299_, sizeof(void*)*3 + 1);
v_trace_3303_ = lean_ctor_get(v_a_3299_, 1);
v_buildTime_3304_ = lean_ctor_get(v_a_3299_, 2);
v_isSharedCheck_3318_ = !lean_is_exclusive(v_a_3299_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3306_ = v_a_3299_;
v_isShared_3307_ = v_isSharedCheck_3318_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_buildTime_3304_);
lean_inc(v_trace_3303_);
lean_inc(v_log_3300_);
lean_dec(v_a_3299_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3318_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3315_; 
v___x_3308_ = ((lean_object*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0));
v___x_3309_ = lean_string_append(v___x_3308_, v_a_3298_);
lean_dec_ref(v_a_3298_);
v___x_3310_ = 3;
v___x_3311_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set_uint8(v___x_3311_, sizeof(void*)*1, v___x_3310_);
v___x_3312_ = lean_array_get_size(v_log_3300_);
v___x_3313_ = lean_array_push(v_log_3300_, v___x_3311_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 0, v___x_3313_);
v___x_3315_ = v___x_3306_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3317_, 1, v_trace_3303_);
lean_ctor_set(v_reuseFailAlloc_3317_, 2, v_buildTime_3304_);
lean_ctor_set_uint8(v_reuseFailAlloc_3317_, sizeof(void*)*3, v_action_3301_);
lean_ctor_set_uint8(v_reuseFailAlloc_3317_, sizeof(void*)*3 + 1, v_wantsRebuild_3302_);
v___x_3315_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
lean_object* v___x_3316_; 
v___x_3316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3312_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
return v___x_3316_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object* v_baseName_3337_, lean_object* v___x_3338_, lean_object* v_success_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
uint8_t v_success_boxed_3347_; lean_object* v_res_3348_; 
v_success_boxed_3347_ = lean_unbox(v_success_3339_);
v_res_3348_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(v_baseName_3337_, v___x_3338_, v_success_boxed_3347_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec_ref(v___y_3344_);
lean_dec(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
return v_res_3348_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* v___x_3349_, lean_object* v___x_3350_, lean_object* v___x_3351_, lean_object* v_pkg_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v_baseName_3360_; lean_object* v_keyName_3361_; lean_object* v___f_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___f_3366_; lean_object* v___x_3367_; 
v_baseName_3360_ = lean_ctor_get(v_pkg_3352_, 1);
lean_inc_n(v_baseName_3360_, 2);
v_keyName_3361_ = lean_ctor_get(v_pkg_3352_, 2);
lean_inc(v___x_3349_);
v___f_3362_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3362_, 0, v_baseName_3360_);
lean_closure_set(v___f_3362_, 1, v___x_3349_);
lean_inc(v_keyName_3361_);
v___x_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3363_, 0, v_keyName_3361_);
v___x_3364_ = l_Lake_Package_keyword;
v___x_3365_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3363_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
lean_ctor_set(v___x_3365_, 2, v_pkg_3352_);
lean_ctor_set(v___x_3365_, 3, v___x_3349_);
lean_inc(v___x_3350_);
v___f_3366_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3366_, 0, v___x_3365_);
lean_closure_set(v___f_3366_, 1, v___x_3350_);
lean_closure_set(v___f_3366_, 2, v___f_3362_);
v___x_3367_ = l_Lake_ensureJob___redArg(v___x_3350_, v___f_3366_, v___y_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3400_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
v_a_3369_ = lean_ctor_get(v___x_3367_, 1);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3371_ = v___x_3367_;
v_isShared_3372_ = v_isSharedCheck_3400_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_inc(v_a_3368_);
lean_dec(v___x_3367_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3400_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v_task_3373_; lean_object* v_kind_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3398_; 
v_task_3373_ = lean_ctor_get(v_a_3368_, 0);
v_kind_3374_ = lean_ctor_get(v_a_3368_, 1);
v_isSharedCheck_3398_ = !lean_is_exclusive(v_a_3368_);
if (v_isSharedCheck_3398_ == 0)
{
lean_object* v_unused_3399_; 
v_unused_3399_ = lean_ctor_get(v_a_3368_, 2);
lean_dec(v_unused_3399_);
v___x_3376_ = v_a_3368_;
v_isShared_3377_ = v_isSharedCheck_3398_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_kind_3374_);
lean_inc(v_task_3373_);
lean_dec(v_a_3368_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3398_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v_registeredJobs_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; uint8_t v___x_3387_; lean_object* v_job_3389_; 
v_registeredJobs_3378_ = lean_ctor_get(v___y_3357_, 4);
v___x_3379_ = lean_st_ref_take(v_registeredJobs_3378_);
v___x_3380_ = 1;
v___x_3381_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3360_, v___x_3380_);
v___x_3382_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3383_ = lean_string_append(v___x_3381_, v___x_3382_);
v___x_3384_ = l_Lake_Name_eraseHead(v___x_3351_);
v___x_3385_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3384_, v___x_3380_);
v___x_3386_ = lean_string_append(v___x_3383_, v___x_3385_);
lean_dec_ref(v___x_3385_);
v___x_3387_ = 0;
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 2, v___x_3386_);
v_job_3389_ = v___x_3376_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_task_3373_);
lean_ctor_set(v_reuseFailAlloc_3397_, 1, v_kind_3374_);
lean_ctor_set(v_reuseFailAlloc_3397_, 2, v___x_3386_);
v_job_3389_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3395_; 
lean_ctor_set_uint8(v_job_3389_, sizeof(void*)*3, v___x_3387_);
lean_inc_ref(v_job_3389_);
v___x_3390_ = l_Lake_Job_toOpaque___redArg(v_job_3389_);
v___x_3391_ = lean_array_push(v___x_3379_, v___x_3390_);
v___x_3392_ = lean_st_ref_put(v_registeredJobs_3378_, v___x_3391_);
v___x_3393_ = l_Lake_Job_renew___redArg(v_job_3389_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3393_);
v___x_3395_ = v___x_3371_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3393_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_a_3369_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
}
else
{
lean_dec(v_baseName_3360_);
lean_dec(v___x_3351_);
return v___x_3367_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_3401_, lean_object* v___x_3402_, lean_object* v___x_3403_, lean_object* v_pkg_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(v___x_3401_, v___x_3402_, v___x_3403_, v_pkg_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec(v___y_3406_);
return v_res_3412_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___f_3416_; 
v___x_3413_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3414_ = l_Lake_instDataKindUnit;
v___x_3415_ = l_Lake_Package_optGitHubReleaseFacet;
v___f_3416_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3416_, 0, v___x_3415_);
lean_closure_set(v___f_3416_, 1, v___x_3414_);
lean_closure_set(v___f_3416_, 2, v___x_3413_);
return v___f_3416_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3417_; uint8_t v___x_3418_; lean_object* v___x_3419_; lean_object* v___f_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___f_3417_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3418_ = 1;
v___x_3419_ = l_Lake_instDataKindUnit;
v___f_3420_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__0, &l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0);
v___x_3421_ = l_Lake_Package_keyword;
v___x_3422_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
lean_ctor_set(v___x_3422_, 1, v___f_3420_);
lean_ctor_set(v___x_3422_, 2, v___x_3419_);
lean_ctor_set(v___x_3422_, 3, v___f_3417_);
lean_ctor_set_uint8(v___x_3422_, sizeof(void*)*4, v___x_3418_);
lean_ctor_set_uint8(v___x_3422_, sizeof(void*)*4 + 1, v___x_3418_);
return v___x_3422_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__1, &l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* v_build_3424_, uint8_t v_x_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v_log_3433_; uint8_t v_action_3434_; uint8_t v_wantsRebuild_3435_; lean_object* v_buildTime_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3445_; 
v_log_3433_ = lean_ctor_get(v___y_3431_, 0);
v_action_3434_ = lean_ctor_get_uint8(v___y_3431_, sizeof(void*)*3);
v_wantsRebuild_3435_ = lean_ctor_get_uint8(v___y_3431_, sizeof(void*)*3 + 1);
v_buildTime_3436_ = lean_ctor_get(v___y_3431_, 2);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___y_3431_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; 
v_unused_3446_ = lean_ctor_get(v___y_3431_, 1);
lean_dec(v_unused_3446_);
v___x_3438_ = v___y_3431_;
v_isShared_3439_ = v_isSharedCheck_3445_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_buildTime_3436_);
lean_inc(v_log_3433_);
lean_dec(v___y_3431_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3445_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3440_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 1, v___x_3440_);
v___x_3442_ = v___x_3438_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_log_3433_);
lean_ctor_set(v_reuseFailAlloc_3444_, 1, v___x_3440_);
lean_ctor_set(v_reuseFailAlloc_3444_, 2, v_buildTime_3436_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, sizeof(void*)*3, v_action_3434_);
lean_ctor_set_uint8(v_reuseFailAlloc_3444_, sizeof(void*)*3 + 1, v_wantsRebuild_3435_);
v___x_3442_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3443_; 
lean_inc_ref(v___y_3430_);
lean_inc(v___y_3429_);
lean_inc(v___y_3428_);
lean_inc(v___y_3427_);
v___x_3443_ = lean_apply_7(v_build_3424_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___x_3442_, lean_box(0));
return v___x_3443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* v_build_3447_, lean_object* v_x_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
uint8_t v_x_1602__boxed_3456_; lean_object* v_res_3457_; 
v_x_1602__boxed_3456_ = lean_unbox(v_x_3448_);
v_res_3457_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(v_build_3447_, v_x_1602__boxed_3456_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec(v___y_3450_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* v_self_3458_, lean_object* v_build_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v_wsIdx_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; 
v_wsIdx_3467_ = lean_ctor_get(v_self_3458_, 0);
v___x_3468_ = lean_unsigned_to_nat(0u);
v___x_3469_ = lean_nat_dec_eq(v_wsIdx_3467_, v___x_3468_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; 
lean_inc_ref(v_a_3460_);
v___x_3470_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3458_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3483_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
v_a_3472_ = lean_ctor_get(v___x_3470_, 1);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3474_ = v___x_3470_;
v_isShared_3475_ = v_isSharedCheck_3483_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_inc(v_a_3471_);
lean_dec(v___x_3470_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3483_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___f_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3481_; 
v___f_3476_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3476_, 0, v_build_3459_);
v___x_3477_ = lean_box(0);
v___x_3478_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3479_ = l_Lake_Job_bindM___redArg(v___x_3477_, v_a_3471_, v___f_3476_, v___x_3468_, v___x_3469_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v___x_3478_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v___x_3479_);
v___x_3481_ = v___x_3474_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_a_3472_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
else
{
lean_object* v_a_3484_; lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v_a_3460_);
lean_dec_ref(v_build_3459_);
v_a_3484_ = lean_ctor_get(v___x_3470_, 0);
v_a_3485_ = lean_ctor_get(v___x_3470_, 1);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3470_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_inc(v_a_3484_);
lean_dec(v___x_3470_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3484_);
lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
else
{
uint8_t v___x_3493_; uint8_t v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
lean_dec_ref(v_self_3458_);
v___x_3493_ = 0;
v___x_3494_ = 0;
v___x_3495_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3496_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3496_, 0, v_a_3465_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
lean_ctor_set(v___x_3496_, 2, v___x_3468_);
lean_ctor_set_uint8(v___x_3496_, sizeof(void*)*3, v___x_3493_);
lean_ctor_set_uint8(v___x_3496_, sizeof(void*)*3 + 1, v___x_3494_);
lean_inc_ref(v_a_3464_);
lean_inc(v_a_3463_);
lean_inc(v_a_3462_);
lean_inc(v_a_3461_);
v___x_3497_ = lean_apply_7(v_build_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v___x_3496_, lean_box(0));
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3507_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 1);
v_a_3499_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3501_ = v___x_3497_;
v_isShared_3502_ = v_isSharedCheck_3507_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3498_);
lean_inc(v_a_3499_);
lean_dec(v___x_3497_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3507_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v_log_3503_; lean_object* v___x_3505_; 
v_log_3503_ = lean_ctor_get(v_a_3498_, 0);
lean_inc_ref(v_log_3503_);
lean_dec(v_a_3498_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 1, v_log_3503_);
v___x_3505_ = v___x_3501_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3499_);
lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_log_3503_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
else
{
lean_object* v_a_3508_; lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3517_; 
v_a_3508_ = lean_ctor_get(v___x_3497_, 1);
v_a_3509_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3511_ = v___x_3497_;
v_isShared_3512_ = v_isSharedCheck_3517_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3508_);
lean_inc(v_a_3509_);
lean_dec(v___x_3497_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3517_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v_log_3513_; lean_object* v___x_3515_; 
v_log_3513_ = lean_ctor_get(v_a_3508_, 0);
lean_inc_ref(v_log_3513_);
lean_dec(v_a_3508_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 1, v_log_3513_);
v___x_3515_ = v___x_3511_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3509_);
lean_ctor_set(v_reuseFailAlloc_3516_, 1, v_log_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___boxed(lean_object* v_self_3518_, lean_object* v_build_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v_res_3527_; 
v_res_3527_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3518_, v_build_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_);
lean_dec_ref(v_a_3524_);
lean_dec(v_a_3523_);
lean_dec(v_a_3522_);
lean_dec(v_a_3521_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* v_00_u03b1_3528_, lean_object* v_self_3529_, lean_object* v_build_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_){
_start:
{
lean_object* v___x_3538_; 
v___x_3538_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3529_, v_build_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___boxed(lean_object* v_00_u03b1_3539_, lean_object* v_self_3540_, lean_object* v_build_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_Lake_Package_afterBuildCacheAsync(v_00_u03b1_3539_, v_self_3540_, v_build_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_);
lean_dec_ref(v_a_3546_);
lean_dec(v_a_3545_);
lean_dec(v_a_3544_);
lean_dec(v_a_3543_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* v_build_3550_, uint8_t v_x_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v_log_3559_; uint8_t v_action_3560_; uint8_t v_wantsRebuild_3561_; lean_object* v_buildTime_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3571_; 
v_log_3559_ = lean_ctor_get(v___y_3557_, 0);
v_action_3560_ = lean_ctor_get_uint8(v___y_3557_, sizeof(void*)*3);
v_wantsRebuild_3561_ = lean_ctor_get_uint8(v___y_3557_, sizeof(void*)*3 + 1);
v_buildTime_3562_ = lean_ctor_get(v___y_3557_, 2);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___y_3557_);
if (v_isSharedCheck_3571_ == 0)
{
lean_object* v_unused_3572_; 
v_unused_3572_ = lean_ctor_get(v___y_3557_, 1);
lean_dec(v_unused_3572_);
v___x_3564_ = v___y_3557_;
v_isShared_3565_ = v_isSharedCheck_3571_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_buildTime_3562_);
lean_inc(v_log_3559_);
lean_dec(v___y_3557_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3571_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3566_; lean_object* v___x_3568_; 
v___x_3566_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_3565_ == 0)
{
lean_ctor_set(v___x_3564_, 1, v___x_3566_);
v___x_3568_ = v___x_3564_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_log_3559_);
lean_ctor_set(v_reuseFailAlloc_3570_, 1, v___x_3566_);
lean_ctor_set(v_reuseFailAlloc_3570_, 2, v_buildTime_3562_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*3, v_action_3560_);
lean_ctor_set_uint8(v_reuseFailAlloc_3570_, sizeof(void*)*3 + 1, v_wantsRebuild_3561_);
v___x_3568_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
lean_object* v___x_3569_; 
lean_inc_ref(v___y_3556_);
lean_inc(v___y_3555_);
lean_inc(v___y_3554_);
lean_inc(v___y_3553_);
v___x_3569_ = lean_apply_7(v_build_3550_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___x_3568_, lean_box(0));
return v___x_3569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* v_build_3573_, lean_object* v_x_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
uint8_t v_x_1631__boxed_3582_; lean_object* v_res_3583_; 
v_x_1631__boxed_3582_ = lean_unbox(v_x_3574_);
v_res_3583_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(v_build_3573_, v_x_1631__boxed_3582_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_);
lean_dec_ref(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec(v___y_3577_);
lean_dec(v___y_3576_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* v_self_3584_, lean_object* v_build_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_){
_start:
{
lean_object* v_wsIdx_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; lean_object* v___x_3596_; 
v_wsIdx_3593_ = lean_ctor_get(v_self_3584_, 0);
v___x_3594_ = lean_unsigned_to_nat(0u);
v___x_3595_ = lean_nat_dec_eq(v_wsIdx_3593_, v___x_3594_);
v___x_3596_ = lean_box(0);
if (v___x_3595_ == 0)
{
lean_object* v___x_3597_; 
lean_inc_ref(v_a_3586_);
v___x_3597_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3584_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3609_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_a_3599_ = lean_ctor_get(v___x_3597_, 1);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3601_ = v___x_3597_;
v_isShared_3602_ = v_isSharedCheck_3609_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3609_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___f_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3607_; 
v___f_3603_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3603_, 0, v_build_3585_);
v___x_3604_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3605_ = l_Lake_Job_mapM___redArg(v___x_3596_, v_a_3598_, v___f_3603_, v___x_3594_, v___x_3595_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v___x_3604_);
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 0, v___x_3605_);
v___x_3607_ = v___x_3601_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3605_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_a_3599_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec_ref(v_a_3586_);
lean_dec_ref(v_build_3585_);
v_a_3610_ = lean_ctor_get(v___x_3597_, 0);
v_a_3611_ = lean_ctor_get(v___x_3597_, 1);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3597_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_inc(v_a_3610_);
lean_dec(v___x_3597_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3610_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_a_3611_);
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
else
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
lean_dec_ref(v_self_3584_);
v___x_3619_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_3620_ = l_Lake_Job_async___redArg(v___x_3596_, v_build_3585_, v___x_3594_, v___x_3619_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_);
v___x_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
lean_ctor_set(v___x_3621_, 1, v_a_3591_);
return v___x_3621_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___boxed(lean_object* v_self_3622_, lean_object* v_build_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_){
_start:
{
lean_object* v_res_3631_; 
v_res_3631_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3622_, v_build_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_);
lean_dec_ref(v_a_3628_);
lean_dec(v_a_3627_);
lean_dec(v_a_3626_);
lean_dec(v_a_3625_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* v_00_u03b1_3632_, lean_object* v_self_3633_, lean_object* v_build_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3633_, v_build_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___boxed(lean_object* v_00_u03b1_3643_, lean_object* v_self_3644_, lean_object* v_build_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l_Lake_Package_afterBuildCacheSync(v_00_u03b1_3643_, v_self_3644_, v_build_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_);
lean_dec_ref(v_a_3650_);
lean_dec(v_a_3649_);
lean_dec(v_a_3648_);
lean_dec(v_a_3647_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(lean_object* v_k_3654_, lean_object* v_v_3655_, lean_object* v_t_3656_){
_start:
{
if (lean_obj_tag(v_t_3656_) == 0)
{
lean_object* v_size_3657_; lean_object* v_k_3658_; lean_object* v_v_3659_; lean_object* v_l_3660_; lean_object* v_r_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3941_; 
v_size_3657_ = lean_ctor_get(v_t_3656_, 0);
v_k_3658_ = lean_ctor_get(v_t_3656_, 1);
v_v_3659_ = lean_ctor_get(v_t_3656_, 2);
v_l_3660_ = lean_ctor_get(v_t_3656_, 3);
v_r_3661_ = lean_ctor_get(v_t_3656_, 4);
v_isSharedCheck_3941_ = !lean_is_exclusive(v_t_3656_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3663_ = v_t_3656_;
v_isShared_3664_ = v_isSharedCheck_3941_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_r_3661_);
lean_inc(v_l_3660_);
lean_inc(v_v_3659_);
lean_inc(v_k_3658_);
lean_inc(v_size_3657_);
lean_dec(v_t_3656_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3941_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
uint8_t v___x_3665_; 
v___x_3665_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3654_, v_k_3658_);
switch(v___x_3665_)
{
case 0:
{
lean_object* v_impl_3666_; lean_object* v___x_3667_; 
lean_dec(v_size_3657_);
v_impl_3666_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3654_, v_v_3655_, v_l_3660_);
v___x_3667_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3661_) == 0)
{
lean_object* v_size_3668_; lean_object* v_size_3669_; lean_object* v_k_3670_; lean_object* v_v_3671_; lean_object* v_l_3672_; lean_object* v_r_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
v_size_3668_ = lean_ctor_get(v_r_3661_, 0);
v_size_3669_ = lean_ctor_get(v_impl_3666_, 0);
lean_inc(v_size_3669_);
v_k_3670_ = lean_ctor_get(v_impl_3666_, 1);
lean_inc(v_k_3670_);
v_v_3671_ = lean_ctor_get(v_impl_3666_, 2);
lean_inc(v_v_3671_);
v_l_3672_ = lean_ctor_get(v_impl_3666_, 3);
lean_inc(v_l_3672_);
v_r_3673_ = lean_ctor_get(v_impl_3666_, 4);
lean_inc(v_r_3673_);
v___x_3674_ = lean_unsigned_to_nat(3u);
v___x_3675_ = lean_nat_mul(v___x_3674_, v_size_3668_);
v___x_3676_ = lean_nat_dec_lt(v___x_3675_, v_size_3669_);
lean_dec(v___x_3675_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3680_; 
lean_dec(v_r_3673_);
lean_dec(v_l_3672_);
lean_dec(v_v_3671_);
lean_dec(v_k_3670_);
v___x_3677_ = lean_nat_add(v___x_3667_, v_size_3669_);
lean_dec(v_size_3669_);
v___x_3678_ = lean_nat_add(v___x_3677_, v_size_3668_);
lean_dec(v___x_3677_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 3, v_impl_3666_);
lean_ctor_set(v___x_3663_, 0, v___x_3678_);
v___x_3680_ = v___x_3663_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
lean_ctor_set(v_reuseFailAlloc_3681_, 1, v_k_3658_);
lean_ctor_set(v_reuseFailAlloc_3681_, 2, v_v_3659_);
lean_ctor_set(v_reuseFailAlloc_3681_, 3, v_impl_3666_);
lean_ctor_set(v_reuseFailAlloc_3681_, 4, v_r_3661_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
else
{
lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3747_; 
v_isSharedCheck_3747_ = !lean_is_exclusive(v_impl_3666_);
if (v_isSharedCheck_3747_ == 0)
{
lean_object* v_unused_3748_; lean_object* v_unused_3749_; lean_object* v_unused_3750_; lean_object* v_unused_3751_; lean_object* v_unused_3752_; 
v_unused_3748_ = lean_ctor_get(v_impl_3666_, 4);
lean_dec(v_unused_3748_);
v_unused_3749_ = lean_ctor_get(v_impl_3666_, 3);
lean_dec(v_unused_3749_);
v_unused_3750_ = lean_ctor_get(v_impl_3666_, 2);
lean_dec(v_unused_3750_);
v_unused_3751_ = lean_ctor_get(v_impl_3666_, 1);
lean_dec(v_unused_3751_);
v_unused_3752_ = lean_ctor_get(v_impl_3666_, 0);
lean_dec(v_unused_3752_);
v___x_3683_ = v_impl_3666_;
v_isShared_3684_ = v_isSharedCheck_3747_;
goto v_resetjp_3682_;
}
else
{
lean_dec(v_impl_3666_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3747_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v_size_3685_; lean_object* v_size_3686_; lean_object* v_k_3687_; lean_object* v_v_3688_; lean_object* v_l_3689_; lean_object* v_r_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; 
v_size_3685_ = lean_ctor_get(v_l_3672_, 0);
v_size_3686_ = lean_ctor_get(v_r_3673_, 0);
v_k_3687_ = lean_ctor_get(v_r_3673_, 1);
v_v_3688_ = lean_ctor_get(v_r_3673_, 2);
v_l_3689_ = lean_ctor_get(v_r_3673_, 3);
v_r_3690_ = lean_ctor_get(v_r_3673_, 4);
v___x_3691_ = lean_unsigned_to_nat(2u);
v___x_3692_ = lean_nat_mul(v___x_3691_, v_size_3685_);
v___x_3693_ = lean_nat_dec_lt(v_size_3686_, v___x_3692_);
lean_dec(v___x_3692_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3722_; 
lean_inc(v_r_3690_);
lean_inc(v_l_3689_);
lean_inc(v_v_3688_);
lean_inc(v_k_3687_);
v_isSharedCheck_3722_ = !lean_is_exclusive(v_r_3673_);
if (v_isSharedCheck_3722_ == 0)
{
lean_object* v_unused_3723_; lean_object* v_unused_3724_; lean_object* v_unused_3725_; lean_object* v_unused_3726_; lean_object* v_unused_3727_; 
v_unused_3723_ = lean_ctor_get(v_r_3673_, 4);
lean_dec(v_unused_3723_);
v_unused_3724_ = lean_ctor_get(v_r_3673_, 3);
lean_dec(v_unused_3724_);
v_unused_3725_ = lean_ctor_get(v_r_3673_, 2);
lean_dec(v_unused_3725_);
v_unused_3726_ = lean_ctor_get(v_r_3673_, 1);
lean_dec(v_unused_3726_);
v_unused_3727_ = lean_ctor_get(v_r_3673_, 0);
lean_dec(v_unused_3727_);
v___x_3695_ = v_r_3673_;
v_isShared_3696_ = v_isSharedCheck_3722_;
goto v_resetjp_3694_;
}
else
{
lean_dec(v_r_3673_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3722_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___x_3710_; lean_object* v___y_3712_; 
v___x_3697_ = lean_nat_add(v___x_3667_, v_size_3669_);
lean_dec(v_size_3669_);
v___x_3698_ = lean_nat_add(v___x_3697_, v_size_3668_);
lean_dec(v___x_3697_);
v___x_3710_ = lean_nat_add(v___x_3667_, v_size_3685_);
if (lean_obj_tag(v_l_3689_) == 0)
{
lean_object* v_size_3720_; 
v_size_3720_ = lean_ctor_get(v_l_3689_, 0);
lean_inc(v_size_3720_);
v___y_3712_ = v_size_3720_;
goto v___jp_3711_;
}
else
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_unsigned_to_nat(0u);
v___y_3712_ = v___x_3721_;
goto v___jp_3711_;
}
v___jp_3699_:
{
lean_object* v___x_3703_; lean_object* v___x_3705_; 
v___x_3703_ = lean_nat_add(v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec(v___y_3701_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 4, v_r_3661_);
lean_ctor_set(v___x_3695_, 3, v_r_3690_);
lean_ctor_set(v___x_3695_, 2, v_v_3659_);
lean_ctor_set(v___x_3695_, 1, v_k_3658_);
lean_ctor_set(v___x_3695_, 0, v___x_3703_);
v___x_3705_ = v___x_3695_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3703_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_k_3658_);
lean_ctor_set(v_reuseFailAlloc_3709_, 2, v_v_3659_);
lean_ctor_set(v_reuseFailAlloc_3709_, 3, v_r_3690_);
lean_ctor_set(v_reuseFailAlloc_3709_, 4, v_r_3661_);
v___x_3705_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3707_; 
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 4, v___x_3705_);
lean_ctor_set(v___x_3683_, 3, v___y_3700_);
lean_ctor_set(v___x_3683_, 2, v_v_3688_);
lean_ctor_set(v___x_3683_, 1, v_k_3687_);
lean_ctor_set(v___x_3683_, 0, v___x_3698_);
v___x_3707_ = v___x_3683_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v_k_3687_);
lean_ctor_set(v_reuseFailAlloc_3708_, 2, v_v_3688_);
lean_ctor_set(v_reuseFailAlloc_3708_, 3, v___y_3700_);
lean_ctor_set(v_reuseFailAlloc_3708_, 4, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
v___jp_3711_:
{
lean_object* v___x_3713_; lean_object* v___x_3715_; 
v___x_3713_ = lean_nat_add(v___x_3710_, v___y_3712_);
lean_dec(v___y_3712_);
lean_dec(v___x_3710_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v_l_3689_);
lean_ctor_set(v___x_3663_, 3, v_l_3672_);
lean_ctor_set(v___x_3663_, 2, v_v_3671_);
lean_ctor_set(v___x_3663_, 1, v_k_3670_);
lean_ctor_set(v___x_3663_, 0, v___x_3713_);
v___x_3715_ = v___x_3663_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3713_);
lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_k_3670_);
lean_ctor_set(v_reuseFailAlloc_3719_, 2, v_v_3671_);
lean_ctor_set(v_reuseFailAlloc_3719_, 3, v_l_3672_);
lean_ctor_set(v_reuseFailAlloc_3719_, 4, v_l_3689_);
v___x_3715_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3716_; 
v___x_3716_ = lean_nat_add(v___x_3667_, v_size_3668_);
if (lean_obj_tag(v_r_3690_) == 0)
{
lean_object* v_size_3717_; 
v_size_3717_ = lean_ctor_get(v_r_3690_, 0);
lean_inc(v_size_3717_);
v___y_3700_ = v___x_3715_;
v___y_3701_ = v___x_3716_;
v___y_3702_ = v_size_3717_;
goto v___jp_3699_;
}
else
{
lean_object* v___x_3718_; 
v___x_3718_ = lean_unsigned_to_nat(0u);
v___y_3700_ = v___x_3715_;
v___y_3701_ = v___x_3716_;
v___y_3702_ = v___x_3718_;
goto v___jp_3699_;
}
}
}
}
}
else
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3733_; 
lean_del_object(v___x_3663_);
v___x_3728_ = lean_nat_add(v___x_3667_, v_size_3669_);
lean_dec(v_size_3669_);
v___x_3729_ = lean_nat_add(v___x_3728_, v_size_3668_);
lean_dec(v___x_3728_);
v___x_3730_ = lean_nat_add(v___x_3667_, v_size_3668_);
v___x_3731_ = lean_nat_add(v___x_3730_, v_size_3686_);
lean_dec(v___x_3730_);
lean_inc_ref(v_r_3661_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 4, v_r_3661_);
lean_ctor_set(v___x_3683_, 3, v_r_3673_);
lean_ctor_set(v___x_3683_, 2, v_v_3659_);
lean_ctor_set(v___x_3683_, 1, v_k_3658_);
lean_ctor_set(v___x_3683_, 0, v___x_3731_);
v___x_3733_ = v___x_3683_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3731_);
lean_ctor_set(v_reuseFailAlloc_3746_, 1, v_k_3658_);
lean_ctor_set(v_reuseFailAlloc_3746_, 2, v_v_3659_);
lean_ctor_set(v_reuseFailAlloc_3746_, 3, v_r_3673_);
lean_ctor_set(v_reuseFailAlloc_3746_, 4, v_r_3661_);
v___x_3733_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
v_isSharedCheck_3740_ = !lean_is_exclusive(v_r_3661_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; lean_object* v_unused_3742_; lean_object* v_unused_3743_; lean_object* v_unused_3744_; lean_object* v_unused_3745_; 
v_unused_3741_ = lean_ctor_get(v_r_3661_, 4);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_r_3661_, 3);
lean_dec(v_unused_3742_);
v_unused_3743_ = lean_ctor_get(v_r_3661_, 2);
lean_dec(v_unused_3743_);
v_unused_3744_ = lean_ctor_get(v_r_3661_, 1);
lean_dec(v_unused_3744_);
v_unused_3745_ = lean_ctor_get(v_r_3661_, 0);
lean_dec(v_unused_3745_);
v___x_3735_ = v_r_3661_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_dec(v_r_3661_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 4, v___x_3733_);
lean_ctor_set(v___x_3735_, 3, v_l_3672_);
lean_ctor_set(v___x_3735_, 2, v_v_3671_);
lean_ctor_set(v___x_3735_, 1, v_k_3670_);
lean_ctor_set(v___x_3735_, 0, v___x_3729_);
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3729_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v_k_3670_);
lean_ctor_set(v_reuseFailAlloc_3739_, 2, v_v_3671_);
lean_ctor_set(v_reuseFailAlloc_3739_, 3, v_l_3672_);
lean_ctor_set(v_reuseFailAlloc_3739_, 4, v___x_3733_);
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
}
else
{
lean_object* v_l_3753_; 
v_l_3753_ = lean_ctor_get(v_impl_3666_, 3);
lean_inc(v_l_3753_);
if (lean_obj_tag(v_l_3753_) == 0)
{
lean_object* v_r_3754_; lean_object* v_k_3755_; lean_object* v_v_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3767_; 
v_r_3754_ = lean_ctor_get(v_impl_3666_, 4);
v_k_3755_ = lean_ctor_get(v_impl_3666_, 1);
v_v_3756_ = lean_ctor_get(v_impl_3666_, 2);
v_isSharedCheck_3767_ = !lean_is_exclusive(v_impl_3666_);
if (v_isSharedCheck_3767_ == 0)
{
lean_object* v_unused_3768_; lean_object* v_unused_3769_; 
v_unused_3768_ = lean_ctor_get(v_impl_3666_, 3);
lean_dec(v_unused_3768_);
v_unused_3769_ = lean_ctor_get(v_impl_3666_, 0);
lean_dec(v_unused_3769_);
v___x_3758_ = v_impl_3666_;
v_isShared_3759_ = v_isSharedCheck_3767_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_r_3754_);
lean_inc(v_v_3756_);
lean_inc(v_k_3755_);
lean_dec(v_impl_3666_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3767_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3760_; lean_object* v___x_3762_; 
v___x_3760_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3754_);
if (v_isShared_3759_ == 0)
{
lean_ctor_set(v___x_3758_, 3, v_r_3754_);
lean_ctor_set(v___x_3758_, 2, v_v_3659_);
lean_ctor_set(v___x_3758_, 1, v_k_3658_);
lean_ctor_set(v___x_3758_, 0, v___x_3667_);
v___x_3762_ = v___x_3758_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3766_, 1, v_k_3658_);
lean_ctor_set(v_reuseFailAlloc_3766_, 2, v_v_3659_);
lean_ctor_set(v_reuseFailAlloc_3766_, 3, v_r_3754_);
lean_ctor_set(v_reuseFailAlloc_3766_, 4, v_r_3754_);
v___x_3762_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
lean_object* v___x_3764_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v___x_3762_);
lean_ctor_set(v___x_3663_, 3, v_l_3753_);
lean_ctor_set(v___x_3663_, 2, v_v_3756_);
lean_ctor_set(v___x_3663_, 1, v_k_3755_);
lean_ctor_set(v___x_3663_, 0, v___x_3760_);
v___x_3764_ = v___x_3663_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3760_);
lean_ctor_set(v_reuseFailAlloc_3765_, 1, v_k_3755_);
lean_ctor_set(v_reuseFailAlloc_3765_, 2, v_v_3756_);
lean_ctor_set(v_reuseFailAlloc_3765_, 3, v_l_3753_);
lean_ctor_set(v_reuseFailAlloc_3765_, 4, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
else
{
lean_object* v_r_3770_; 
v_r_3770_ = lean_ctor_get(v_impl_3666_, 4);
lean_inc(v_r_3770_);
if (lean_obj_tag(v_r_3770_) == 0)
{
lean_object* v_k_3771_; lean_object* v_v_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3795_; 
v_k_3771_ = lean_ctor_get(v_impl_3666_, 1);
v_v_3772_ = lean_ctor_get(v_impl_3666_, 2);
v_isSharedCheck_3795_ = !lean_is_exclusive(v_impl_3666_);
if (v_isSharedCheck_3795_ == 0)
{
lean_object* v_unused_3796_; lean_object* v_unused_3797_; lean_object* v_unused_3798_; 
v_unused_3796_ = lean_ctor_get(v_impl_3666_, 4);
lean_dec(v_unused_3796_);
v_unused_3797_ = lean_ctor_get(v_impl_3666_, 3);
lean_dec(v_unused_3797_);
v_unused_3798_ = lean_ctor_get(v_impl_3666_, 0);
lean_dec(v_unused_3798_);
v___x_3774_ = v_impl_3666_;
v_isShared_3775_ = v_isSharedCheck_3795_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_v_3772_);
lean_inc(v_k_3771_);
lean_dec(v_impl_3666_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3795_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v_k_3776_; lean_object* v_v_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3791_; 
v_k_3776_ = lean_ctor_get(v_r_3770_, 1);
v_v_3777_ = lean_ctor_get(v_r_3770_, 2);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_r_3770_);
if (v_isSharedCheck_3791_ == 0)
{
lean_object* v_unused_3792_; lean_object* v_unused_3793_; lean_object* v_unused_3794_; 
v_unused_3792_ = lean_ctor_get(v_r_3770_, 4);
lean_dec(v_unused_3792_);
v_unused_3793_ = lean_ctor_get(v_r_3770_, 3);
lean_dec(v_unused_3793_);
v_unused_3794_ = lean_ctor_get(v_r_3770_, 0);
lean_dec(v_unused_3794_);
v___x_3779_ = v_r_3770_;
v_isShared_3780_ = v_isSharedCheck_3791_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_v_3777_);
lean_inc(v_k_3776_);
lean_dec(v_r_3770_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3791_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3781_; lean_object* v___x_3783_; 
v___x_3781_ = lean_unsigned_to_nat(3u);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 4, v_l_3753_);
lean_ctor_set(v___x_3779_, 3, v_l_3753_);
lean_ctor_set(v___x_3779_, 2, v_v_3772_);
lean_ctor_set(v___x_3779_, 1, v_k_3771_);
lean_ctor_set(v___x_3779_, 0, v___x_3667_);
v___x_3783_ = v___x_3779_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3790_, 1, v_k_3771_);
lean_ctor_set(v_reuseFailAlloc_3790_, 2, v_v_3772_);
lean_ctor_set(v_reuseFailAlloc_3790_, 3, v_l_3753_);
lean_ctor_set(v_reuseFailAlloc_3790_, 4, v_l_3753_);
v___x_3783_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
lean_object* v___x_3785_; 
if (v_isShared_3775_ == 0)
{
lean_ctor_set(v___x_3774_, 4, v_l_3753_);
lean_ctor_set(v___x_3774_, 2, v_v_3659_);
lean_ctor_set(v___x_3774_, 1, v_k_3658_);
lean_ctor_set(v___x_3774_, 0, v___x_3667_);
v___x_3785_ = v___x_3774_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3667_);
lean_ctor_set(v_reuseFailAlloc_3789_, 1, v_k_3658_);
lean_ctor_set(v_reuseFailAlloc_3789_, 2, v_v_3659_);
lean_ctor_set(v_reuseFailAlloc_3789_, 3, v_l_3753_);
lean_ctor_set(v_reuseFailAlloc_3789_, 4, v_l_3753_);
v___x_3785_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
lean_object* v___x_3787_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v___x_3785_);
lean_ctor_set(v___x_3663_, 3, v___x_3783_);
lean_ctor_set(v___x_3663_, 2, v_v_3777_);
lean_ctor_set(v___x_3663_, 1, v_k_3776_);
lean_ctor_set(v___x_3663_, 0, v___x_3781_);
v___x_3787_ = v___x_3663_;
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
lean_object* v___x_3799_; lean_object* v___x_3801_; 
v___x_3799_ = lean_unsigned_to_nat(2u);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v_r_3770_);
lean_ctor_set(v___x_3663_, 3, v_impl_3666_);
lean_ctor_set(v___x_3663_, 0, v___x_3799_);
v___x_3801_ = v___x_3663_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3799_);
lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_k_3658_);
lean_ctor_set(v_reuseFailAlloc_3802_, 2, v_v_3659_);
lean_ctor_set(v_reuseFailAlloc_3802_, 3, v_impl_3666_);
lean_ctor_set(v_reuseFailAlloc_3802_, 4, v_r_3770_);
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
case 1:
{
lean_object* v___x_3804_; 
lean_dec(v_v_3659_);
lean_dec(v_k_3658_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 2, v_v_3655_);
lean_ctor_set(v___x_3663_, 1, v_k_3654_);
v___x_3804_ = v___x_3663_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_size_3657_);
lean_ctor_set(v_reuseFailAlloc_3805_, 1, v_k_3654_);
lean_ctor_set(v_reuseFailAlloc_3805_, 2, v_v_3655_);
lean_ctor_set(v_reuseFailAlloc_3805_, 3, v_l_3660_);
lean_ctor_set(v_reuseFailAlloc_3805_, 4, v_r_3661_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
default: 
{
lean_object* v_impl_3806_; lean_object* v___x_3807_; 
lean_dec(v_size_3657_);
v_impl_3806_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3654_, v_v_3655_, v_r_3661_);
v___x_3807_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3660_) == 0)
{
lean_object* v_size_3808_; lean_object* v_size_3809_; lean_object* v_k_3810_; lean_object* v_v_3811_; lean_object* v_l_3812_; lean_object* v_r_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v_size_3808_ = lean_ctor_get(v_l_3660_, 0);
v_size_3809_ = lean_ctor_get(v_impl_3806_, 0);
lean_inc(v_size_3809_);
v_k_3810_ = lean_ctor_get(v_impl_3806_, 1);
lean_inc(v_k_3810_);
v_v_3811_ = lean_ctor_get(v_impl_3806_, 2);
lean_inc(v_v_3811_);
v_l_3812_ = lean_ctor_get(v_impl_3806_, 3);
lean_inc(v_l_3812_);
v_r_3813_ = lean_ctor_get(v_impl_3806_, 4);
lean_inc(v_r_3813_);
v___x_3814_ = lean_unsigned_to_nat(3u);
v___x_3815_ = lean_nat_mul(v___x_3814_, v_size_3808_);
v___x_3816_ = lean_nat_dec_lt(v___x_3815_, v_size_3809_);
lean_dec(v___x_3815_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3820_; 
lean_dec(v_r_3813_);
lean_dec(v_l_3812_);
lean_dec(v_v_3811_);
lean_dec(v_k_3810_);
v___x_3817_ = lean_nat_add(v___x_3807_, v_size_3808_);
v___x_3818_ = lean_nat_add(v___x_3817_, v_size_3809_);
lean_dec(v_size_3809_);
lean_dec(v___x_3817_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v_impl_3806_);
lean_ctor_set(v___x_3663_, 0, v___x_3818_);
v___x_3820_ = v___x_3663_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3818_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_k_3658_);
lean_ctor_set(v_reuseFailAlloc_3821_, 2, v_v_3659_);
lean_ctor_set(v_reuseFailAlloc_3821_, 3, v_l_3660_);
lean_ctor_set(v_reuseFailAlloc_3821_, 4, v_impl_3806_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
else
{
lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3885_; 
v_isSharedCheck_3885_ = !lean_is_exclusive(v_impl_3806_);
if (v_isSharedCheck_3885_ == 0)
{
lean_object* v_unused_3886_; lean_object* v_unused_3887_; lean_object* v_unused_3888_; lean_object* v_unused_3889_; lean_object* v_unused_3890_; 
v_unused_3886_ = lean_ctor_get(v_impl_3806_, 4);
lean_dec(v_unused_3886_);
v_unused_3887_ = lean_ctor_get(v_impl_3806_, 3);
lean_dec(v_unused_3887_);
v_unused_3888_ = lean_ctor_get(v_impl_3806_, 2);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_impl_3806_, 1);
lean_dec(v_unused_3889_);
v_unused_3890_ = lean_ctor_get(v_impl_3806_, 0);
lean_dec(v_unused_3890_);
v___x_3823_ = v_impl_3806_;
v_isShared_3824_ = v_isSharedCheck_3885_;
goto v_resetjp_3822_;
}
else
{
lean_dec(v_impl_3806_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3885_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v_size_3825_; lean_object* v_k_3826_; lean_object* v_v_3827_; lean_object* v_l_3828_; lean_object* v_r_3829_; lean_object* v_size_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v_size_3825_ = lean_ctor_get(v_l_3812_, 0);
v_k_3826_ = lean_ctor_get(v_l_3812_, 1);
v_v_3827_ = lean_ctor_get(v_l_3812_, 2);
v_l_3828_ = lean_ctor_get(v_l_3812_, 3);
v_r_3829_ = lean_ctor_get(v_l_3812_, 4);
v_size_3830_ = lean_ctor_get(v_r_3813_, 0);
v___x_3831_ = lean_unsigned_to_nat(2u);
v___x_3832_ = lean_nat_mul(v___x_3831_, v_size_3830_);
v___x_3833_ = lean_nat_dec_lt(v_size_3825_, v___x_3832_);
lean_dec(v___x_3832_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3861_; 
lean_inc(v_r_3829_);
lean_inc(v_l_3828_);
lean_inc(v_v_3827_);
lean_inc(v_k_3826_);
v_isSharedCheck_3861_ = !lean_is_exclusive(v_l_3812_);
if (v_isSharedCheck_3861_ == 0)
{
lean_object* v_unused_3862_; lean_object* v_unused_3863_; lean_object* v_unused_3864_; lean_object* v_unused_3865_; lean_object* v_unused_3866_; 
v_unused_3862_ = lean_ctor_get(v_l_3812_, 4);
lean_dec(v_unused_3862_);
v_unused_3863_ = lean_ctor_get(v_l_3812_, 3);
lean_dec(v_unused_3863_);
v_unused_3864_ = lean_ctor_get(v_l_3812_, 2);
lean_dec(v_unused_3864_);
v_unused_3865_ = lean_ctor_get(v_l_3812_, 1);
lean_dec(v_unused_3865_);
v_unused_3866_ = lean_ctor_get(v_l_3812_, 0);
lean_dec(v_unused_3866_);
v___x_3835_ = v_l_3812_;
v_isShared_3836_ = v_isSharedCheck_3861_;
goto v_resetjp_3834_;
}
else
{
lean_dec(v_l_3812_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3861_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3851_; 
v___x_3837_ = lean_nat_add(v___x_3807_, v_size_3808_);
v___x_3838_ = lean_nat_add(v___x_3837_, v_size_3809_);
lean_dec(v_size_3809_);
if (lean_obj_tag(v_l_3828_) == 0)
{
lean_object* v_size_3859_; 
v_size_3859_ = lean_ctor_get(v_l_3828_, 0);
lean_inc(v_size_3859_);
v___y_3851_ = v_size_3859_;
goto v___jp_3850_;
}
else
{
lean_object* v___x_3860_; 
v___x_3860_ = lean_unsigned_to_nat(0u);
v___y_3851_ = v___x_3860_;
goto v___jp_3850_;
}
v___jp_3839_:
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3843_ = lean_nat_add(v___y_3841_, v___y_3842_);
lean_dec(v___y_3842_);
lean_dec(v___y_3841_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 4, v_r_3813_);
lean_ctor_set(v___x_3835_, 3, v_r_3829_);
lean_ctor_set(v___x_3835_, 2, v_v_3811_);
lean_ctor_set(v___x_3835_, 1, v_k_3810_);
lean_ctor_set(v___x_3835_, 0, v___x_3843_);
v___x_3845_ = v___x_3835_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3849_, 1, v_k_3810_);
lean_ctor_set(v_reuseFailAlloc_3849_, 2, v_v_3811_);
lean_ctor_set(v_reuseFailAlloc_3849_, 3, v_r_3829_);
lean_ctor_set(v_reuseFailAlloc_3849_, 4, v_r_3813_);
v___x_3845_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3847_; 
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 4, v___x_3845_);
lean_ctor_set(v___x_3823_, 3, v___y_3840_);
lean_ctor_set(v___x_3823_, 2, v_v_3827_);
lean_ctor_set(v___x_3823_, 1, v_k_3826_);
lean_ctor_set(v___x_3823_, 0, v___x_3838_);
v___x_3847_ = v___x_3823_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3838_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_k_3826_);
lean_ctor_set(v_reuseFailAlloc_3848_, 2, v_v_3827_);
lean_ctor_set(v_reuseFailAlloc_3848_, 3, v___y_3840_);
lean_ctor_set(v_reuseFailAlloc_3848_, 4, v___x_3845_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
v___jp_3850_:
{
lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3852_ = lean_nat_add(v___x_3837_, v___y_3851_);
lean_dec(v___y_3851_);
lean_dec(v___x_3837_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v_l_3828_);
lean_ctor_set(v___x_3663_, 0, v___x_3852_);
v___x_3854_ = v___x_3663_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3858_, 1, v_k_3658_);
lean_ctor_set(v_reuseFailAlloc_3858_, 2, v_v_3659_);
lean_ctor_set(v_reuseFailAlloc_3858_, 3, v_l_3660_);
lean_ctor_set(v_reuseFailAlloc_3858_, 4, v_l_3828_);
v___x_3854_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
lean_object* v___x_3855_; 
v___x_3855_ = lean_nat_add(v___x_3807_, v_size_3830_);
if (lean_obj_tag(v_r_3829_) == 0)
{
lean_object* v_size_3856_; 
v_size_3856_ = lean_ctor_get(v_r_3829_, 0);
lean_inc(v_size_3856_);
v___y_3840_ = v___x_3854_;
v___y_3841_ = v___x_3855_;
v___y_3842_ = v_size_3856_;
goto v___jp_3839_;
}
else
{
lean_object* v___x_3857_; 
v___x_3857_ = lean_unsigned_to_nat(0u);
v___y_3840_ = v___x_3854_;
v___y_3841_ = v___x_3855_;
v___y_3842_ = v___x_3857_;
goto v___jp_3839_;
}
}
}
}
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3871_; 
lean_del_object(v___x_3663_);
v___x_3867_ = lean_nat_add(v___x_3807_, v_size_3808_);
v___x_3868_ = lean_nat_add(v___x_3867_, v_size_3809_);
lean_dec(v_size_3809_);
v___x_3869_ = lean_nat_add(v___x_3867_, v_size_3825_);
lean_dec(v___x_3867_);
lean_inc_ref(v_l_3660_);
if (v_isShared_3824_ == 0)
{
lean_ctor_set(v___x_3823_, 4, v_l_3812_);
lean_ctor_set(v___x_3823_, 3, v_l_3660_);
lean_ctor_set(v___x_3823_, 2, v_v_3659_);
lean_ctor_set(v___x_3823_, 1, v_k_3658_);
lean_ctor_set(v___x_3823_, 0, v___x_3869_);
v___x_3871_ = v___x_3823_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v___x_3869_);
lean_ctor_set(v_reuseFailAlloc_3884_, 1, v_k_3658_);
lean_ctor_set(v_reuseFailAlloc_3884_, 2, v_v_3659_);
lean_ctor_set(v_reuseFailAlloc_3884_, 3, v_l_3660_);
lean_ctor_set(v_reuseFailAlloc_3884_, 4, v_l_3812_);
v___x_3871_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3878_; 
v_isSharedCheck_3878_ = !lean_is_exclusive(v_l_3660_);
if (v_isSharedCheck_3878_ == 0)
{
lean_object* v_unused_3879_; lean_object* v_unused_3880_; lean_object* v_unused_3881_; lean_object* v_unused_3882_; lean_object* v_unused_3883_; 
v_unused_3879_ = lean_ctor_get(v_l_3660_, 4);
lean_dec(v_unused_3879_);
v_unused_3880_ = lean_ctor_get(v_l_3660_, 3);
lean_dec(v_unused_3880_);
v_unused_3881_ = lean_ctor_get(v_l_3660_, 2);
lean_dec(v_unused_3881_);
v_unused_3882_ = lean_ctor_get(v_l_3660_, 1);
lean_dec(v_unused_3882_);
v_unused_3883_ = lean_ctor_get(v_l_3660_, 0);
lean_dec(v_unused_3883_);
v___x_3873_ = v_l_3660_;
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
else
{
lean_dec(v_l_3660_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3876_; 
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 4, v_r_3813_);
lean_ctor_set(v___x_3873_, 3, v___x_3871_);
lean_ctor_set(v___x_3873_, 2, v_v_3811_);
lean_ctor_set(v___x_3873_, 1, v_k_3810_);
lean_ctor_set(v___x_3873_, 0, v___x_3868_);
v___x_3876_ = v___x_3873_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3868_);
lean_ctor_set(v_reuseFailAlloc_3877_, 1, v_k_3810_);
lean_ctor_set(v_reuseFailAlloc_3877_, 2, v_v_3811_);
lean_ctor_set(v_reuseFailAlloc_3877_, 3, v___x_3871_);
lean_ctor_set(v_reuseFailAlloc_3877_, 4, v_r_3813_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3891_; 
v_l_3891_ = lean_ctor_get(v_impl_3806_, 3);
lean_inc(v_l_3891_);
if (lean_obj_tag(v_l_3891_) == 0)
{
lean_object* v_r_3892_; lean_object* v_k_3893_; lean_object* v_v_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3917_; 
v_r_3892_ = lean_ctor_get(v_impl_3806_, 4);
v_k_3893_ = lean_ctor_get(v_impl_3806_, 1);
v_v_3894_ = lean_ctor_get(v_impl_3806_, 2);
v_isSharedCheck_3917_ = !lean_is_exclusive(v_impl_3806_);
if (v_isSharedCheck_3917_ == 0)
{
lean_object* v_unused_3918_; lean_object* v_unused_3919_; 
v_unused_3918_ = lean_ctor_get(v_impl_3806_, 3);
lean_dec(v_unused_3918_);
v_unused_3919_ = lean_ctor_get(v_impl_3806_, 0);
lean_dec(v_unused_3919_);
v___x_3896_ = v_impl_3806_;
v_isShared_3897_ = v_isSharedCheck_3917_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_r_3892_);
lean_inc(v_v_3894_);
lean_inc(v_k_3893_);
lean_dec(v_impl_3806_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3917_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v_k_3898_; lean_object* v_v_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3913_; 
v_k_3898_ = lean_ctor_get(v_l_3891_, 1);
v_v_3899_ = lean_ctor_get(v_l_3891_, 2);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_l_3891_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; lean_object* v_unused_3915_; lean_object* v_unused_3916_; 
v_unused_3914_ = lean_ctor_get(v_l_3891_, 4);
lean_dec(v_unused_3914_);
v_unused_3915_ = lean_ctor_get(v_l_3891_, 3);
lean_dec(v_unused_3915_);
v_unused_3916_ = lean_ctor_get(v_l_3891_, 0);
lean_dec(v_unused_3916_);
v___x_3901_ = v_l_3891_;
v_isShared_3902_ = v_isSharedCheck_3913_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_v_3899_);
lean_inc(v_k_3898_);
lean_dec(v_l_3891_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3913_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3903_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3892_, 2);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 4, v_r_3892_);
lean_ctor_set(v___x_3901_, 3, v_r_3892_);
lean_ctor_set(v___x_3901_, 2, v_v_3659_);
lean_ctor_set(v___x_3901_, 1, v_k_3658_);
lean_ctor_set(v___x_3901_, 0, v___x_3807_);
v___x_3905_ = v___x_3901_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3807_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v_k_3658_);
lean_ctor_set(v_reuseFailAlloc_3912_, 2, v_v_3659_);
lean_ctor_set(v_reuseFailAlloc_3912_, 3, v_r_3892_);
lean_ctor_set(v_reuseFailAlloc_3912_, 4, v_r_3892_);
v___x_3905_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3907_; 
lean_inc(v_r_3892_);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 3, v_r_3892_);
lean_ctor_set(v___x_3896_, 0, v___x_3807_);
v___x_3907_ = v___x_3896_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3807_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_k_3893_);
lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_v_3894_);
lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_r_3892_);
lean_ctor_set(v_reuseFailAlloc_3911_, 4, v_r_3892_);
v___x_3907_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3909_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v___x_3907_);
lean_ctor_set(v___x_3663_, 3, v___x_3905_);
lean_ctor_set(v___x_3663_, 2, v_v_3899_);
lean_ctor_set(v___x_3663_, 1, v_k_3898_);
lean_ctor_set(v___x_3663_, 0, v___x_3903_);
v___x_3909_ = v___x_3663_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3910_, 1, v_k_3898_);
lean_ctor_set(v_reuseFailAlloc_3910_, 2, v_v_3899_);
lean_ctor_set(v_reuseFailAlloc_3910_, 3, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_3910_, 4, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
}
}
else
{
lean_object* v_r_3920_; 
v_r_3920_ = lean_ctor_get(v_impl_3806_, 4);
lean_inc(v_r_3920_);
if (lean_obj_tag(v_r_3920_) == 0)
{
lean_object* v_k_3921_; lean_object* v_v_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3933_; 
v_k_3921_ = lean_ctor_get(v_impl_3806_, 1);
v_v_3922_ = lean_ctor_get(v_impl_3806_, 2);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_impl_3806_);
if (v_isSharedCheck_3933_ == 0)
{
lean_object* v_unused_3934_; lean_object* v_unused_3935_; lean_object* v_unused_3936_; 
v_unused_3934_ = lean_ctor_get(v_impl_3806_, 4);
lean_dec(v_unused_3934_);
v_unused_3935_ = lean_ctor_get(v_impl_3806_, 3);
lean_dec(v_unused_3935_);
v_unused_3936_ = lean_ctor_get(v_impl_3806_, 0);
lean_dec(v_unused_3936_);
v___x_3924_ = v_impl_3806_;
v_isShared_3925_ = v_isSharedCheck_3933_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_v_3922_);
lean_inc(v_k_3921_);
lean_dec(v_impl_3806_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3933_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3926_ = lean_unsigned_to_nat(3u);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 4, v_l_3891_);
lean_ctor_set(v___x_3924_, 2, v_v_3659_);
lean_ctor_set(v___x_3924_, 1, v_k_3658_);
lean_ctor_set(v___x_3924_, 0, v___x_3807_);
v___x_3928_ = v___x_3924_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3807_);
lean_ctor_set(v_reuseFailAlloc_3932_, 1, v_k_3658_);
lean_ctor_set(v_reuseFailAlloc_3932_, 2, v_v_3659_);
lean_ctor_set(v_reuseFailAlloc_3932_, 3, v_l_3891_);
lean_ctor_set(v_reuseFailAlloc_3932_, 4, v_l_3891_);
v___x_3928_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3930_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v_r_3920_);
lean_ctor_set(v___x_3663_, 3, v___x_3928_);
lean_ctor_set(v___x_3663_, 2, v_v_3922_);
lean_ctor_set(v___x_3663_, 1, v_k_3921_);
lean_ctor_set(v___x_3663_, 0, v___x_3926_);
v___x_3930_ = v___x_3663_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3931_, 1, v_k_3921_);
lean_ctor_set(v_reuseFailAlloc_3931_, 2, v_v_3922_);
lean_ctor_set(v_reuseFailAlloc_3931_, 3, v___x_3928_);
lean_ctor_set(v_reuseFailAlloc_3931_, 4, v_r_3920_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
else
{
lean_object* v___x_3937_; lean_object* v___x_3939_; 
v___x_3937_ = lean_unsigned_to_nat(2u);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v_impl_3806_);
lean_ctor_set(v___x_3663_, 3, v_r_3920_);
lean_ctor_set(v___x_3663_, 0, v___x_3937_);
v___x_3939_ = v___x_3663_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3937_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_k_3658_);
lean_ctor_set(v_reuseFailAlloc_3940_, 2, v_v_3659_);
lean_ctor_set(v_reuseFailAlloc_3940_, 3, v_r_3920_);
lean_ctor_set(v_reuseFailAlloc_3940_, 4, v_impl_3806_);
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
}
}
}
}
else
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3942_ = lean_unsigned_to_nat(1u);
v___x_3943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
lean_ctor_set(v___x_3943_, 1, v_k_3654_);
lean_ctor_set(v___x_3943_, 2, v_v_3655_);
lean_ctor_set(v___x_3943_, 3, v_t_3656_);
lean_ctor_set(v___x_3943_, 4, v_t_3656_);
return v___x_3943_;
}
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3944_ = lean_box(1);
v___x_3945_ = l_Lake_Package_depsFacetConfig;
v___x_3946_ = l_Lake_Package_depsFacet;
v___x_3947_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3946_, v___x_3945_, v___x_3944_);
return v___x_3947_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3948_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__0, &l_Lake_Package_initFacetConfigs___closed__0_once, _init_l_Lake_Package_initFacetConfigs___closed__0);
v___x_3949_ = l_Lake_Package_transDepsFacetConfig;
v___x_3950_ = l_Lake_Package_transDepsFacet;
v___x_3951_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3950_, v___x_3949_, v___x_3948_);
return v___x_3951_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3952_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__1, &l_Lake_Package_initFacetConfigs___closed__1_once, _init_l_Lake_Package_initFacetConfigs___closed__1);
v___x_3953_ = l_Lake_Package_defaultModulesFacetConfig;
v___x_3954_ = l_Lake_Package_defaultModulesFacet;
v___x_3955_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3954_, v___x_3953_, v___x_3952_);
return v___x_3955_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3956_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__2, &l_Lake_Package_initFacetConfigs___closed__2_once, _init_l_Lake_Package_initFacetConfigs___closed__2);
v___x_3957_ = l_Lake_Package_extraDepFacetConfig;
v___x_3958_ = l_Lake_Package_extraDepFacet;
v___x_3959_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3958_, v___x_3957_, v___x_3956_);
return v___x_3959_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3960_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__3, &l_Lake_Package_initFacetConfigs___closed__3_once, _init_l_Lake_Package_initFacetConfigs___closed__3);
v___x_3961_ = l_Lake_Package_optBuildCacheFacetConfig;
v___x_3962_ = l_Lake_Package_optBuildCacheFacet;
v___x_3963_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3962_, v___x_3961_, v___x_3960_);
return v___x_3963_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3964_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__4, &l_Lake_Package_initFacetConfigs___closed__4_once, _init_l_Lake_Package_initFacetConfigs___closed__4);
v___x_3965_ = l_Lake_Package_buildCacheFacetConfig;
v___x_3966_ = l_Lake_Package_buildCacheFacet;
v___x_3967_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3966_, v___x_3965_, v___x_3964_);
return v___x_3967_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3968_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__5, &l_Lake_Package_initFacetConfigs___closed__5_once, _init_l_Lake_Package_initFacetConfigs___closed__5);
v___x_3969_ = l_Lake_Package_optBarrelFacetConfig;
v___x_3970_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3971_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3970_, v___x_3969_, v___x_3968_);
return v___x_3971_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3972_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__6, &l_Lake_Package_initFacetConfigs___closed__6_once, _init_l_Lake_Package_initFacetConfigs___closed__6);
v___x_3973_ = l_Lake_Package_barrelFacetConfig;
v___x_3974_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3975_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3974_, v___x_3973_, v___x_3972_);
return v___x_3975_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3976_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__7, &l_Lake_Package_initFacetConfigs___closed__7_once, _init_l_Lake_Package_initFacetConfigs___closed__7);
v___x_3977_ = l_Lake_Package_optGitHubReleaseFacetConfig;
v___x_3978_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3979_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3978_, v___x_3977_, v___x_3976_);
return v___x_3979_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__9(void){
_start:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3980_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__8, &l_Lake_Package_initFacetConfigs___closed__8_once, _init_l_Lake_Package_initFacetConfigs___closed__8);
v___x_3981_ = l_Lake_Package_gitHubReleaseFacetConfig;
v___x_3982_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3983_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3982_, v___x_3981_, v___x_3980_);
return v___x_3983_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs(void){
_start:
{
lean_object* v___x_3984_; 
v___x_3984_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__9, &l_Lake_Package_initFacetConfigs___closed__9_once, _init_l_Lake_Package_initFacetConfigs___closed__9);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3985_, lean_object* v_k_3986_, lean_object* v_v_3987_, lean_object* v_t_3988_, lean_object* v_hl_3989_){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3986_, v_v_3987_, v_t_3988_);
return v___x_3990_;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs(void){
_start:
{
lean_object* v___x_3991_; 
v___x_3991_ = l_Lake_Package_initFacetConfigs;
return v___x_3991_;
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
