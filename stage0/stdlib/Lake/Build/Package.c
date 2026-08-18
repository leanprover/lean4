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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
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
uint8_t l_Lake_instDecidableEqOutputStatus(uint8_t, uint8_t);
lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildMetadata_writeFile(lean_object*, lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lake_Package_transDepsFacet;
lean_object* l_Lake_Job_await___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lake_Package_depsFacet;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
extern lean_object* l_Lake_Package_gitHubReleaseFacet;
lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instQueryJsonUnit___lam__0(lean_object*);
lean_object* l_instToStringBool___lam__0___boxed(lean_object*);
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
static lean_once_cell_t l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2;
static const lean_array_object l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3 = (const lean_object*)&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3_value;
static lean_once_cell_t l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " (run with '-v' for details)"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " (see '"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "' for details)"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3_value;
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
uint8_t v___x_103_; 
v___x_103_ = lean_nat_dec_le(v___x_101_, v___x_101_);
if (v___x_103_ == 0)
{
if (v___x_102_ == 0)
{
lean_dec_ref(v_a_90_);
v___y_92_ = v___x_99_;
goto v___jp_91_;
}
else
{
size_t v___x_104_; size_t v___x_105_; lean_object* v___x_106_; 
v___x_104_ = ((size_t)0ULL);
v___x_105_ = lean_usize_of_nat(v___x_101_);
v___x_106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(v_a_90_, v___x_104_, v___x_105_, v___x_99_);
lean_dec_ref(v_a_90_);
v___y_92_ = v___x_106_;
goto v___jp_91_;
}
}
else
{
size_t v___x_107_; size_t v___x_108_; lean_object* v___x_109_; 
v___x_107_ = ((size_t)0ULL);
v___x_108_ = lean_usize_of_nat(v___x_101_);
v___x_109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(v_a_90_, v___x_107_, v___x_108_, v___x_99_);
lean_dec_ref(v_a_90_);
v___y_92_ = v___x_109_;
goto v___jp_91_;
}
}
}
else
{
size_t v_sz_110_; size_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_sz_110_ = lean_array_size(v_a_90_);
v___x_111_ = ((size_t)0ULL);
v___x_112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(v_sz_110_, v___x_111_, v_a_90_);
v___x_113_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
v___x_114_ = l_Lean_Json_compress(v___x_113_);
return v___x_114_;
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
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0___boxed(lean_object* v_fmt_115_, lean_object* v_a_116_){
_start:
{
uint8_t v_fmt_boxed_117_; lean_object* v_res_118_; 
v_fmt_boxed_117_ = lean_unbox(v_fmt_115_);
v_res_118_ = l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0(v_fmt_boxed_117_, v_a_116_);
return v_res_118_;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__2(void){
_start:
{
uint8_t v___x_121_; lean_object* v___f_122_; uint8_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_121_ = 1;
v___f_122_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__0));
v___x_123_ = 0;
v___x_124_ = lean_box(0);
v___x_125_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__1));
v___x_126_ = l_Lake_Package_keyword;
v___x_127_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_125_);
lean_ctor_set(v___x_127_, 2, v___x_124_);
lean_ctor_set(v___x_127_, 3, v___f_122_);
lean_ctor_set_uint8(v___x_127_, sizeof(void*)*4, v___x_123_);
lean_ctor_set_uint8(v___x_127_, sizeof(void*)*4 + 1, v___x_121_);
return v___x_127_;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig(void){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Lake_Package_depsFacetConfig___closed__2, &l_Lake_Package_depsFacetConfig___closed__2_once, _init_l_Lake_Package_depsFacetConfig___closed__2);
return v___x_128_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0(void){
_start:
{
lean_object* v_cellCount_129_; lean_object* v___x_130_; 
v_cellCount_129_ = lean_unsigned_to_nat(16u);
v___x_130_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1(void){
_start:
{
lean_object* v_cellCount_131_; lean_object* v___x_132_; 
v_cellCount_131_ = lean_unsigned_to_nat(16u);
v___x_132_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_131_);
return v___x_132_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_133_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1);
v___x_134_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v___x_134_);
lean_ctor_set(v___x_136_, 2, v___x_133_);
return v___x_136_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__4(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3));
v___x_140_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2);
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2(void){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__4, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__4_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__4);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(lean_object* v_m_143_, lean_object* v_query_144_, lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
lean_object* v_zero_148_; uint8_t v_isZero_149_; 
v_zero_148_ = lean_unsigned_to_nat(0u);
v_isZero_149_ = lean_nat_dec_eq(v_x_146_, v_zero_148_);
if (v_isZero_149_ == 1)
{
lean_dec(v_x_147_);
lean_dec(v_x_146_);
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v___x_150_; 
v___x_150_ = lean_box(2);
return v___x_150_;
}
else
{
lean_object* v_val_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
v_val_151_ = lean_ctor_get(v_x_145_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_145_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v_x_145_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_val_151_);
lean_dec(v_x_145_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_val_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
else
{
lean_object* v_keyArray_159_; lean_object* v_valueArray_160_; lean_object* v___x_161_; uint8_t v_isSome_162_; 
v_keyArray_159_ = lean_ctor_get(v_m_143_, 1);
v_valueArray_160_ = lean_ctor_get(v_m_143_, 2);
v___x_161_ = lean_array_fget_borrowed(v_keyArray_159_, v_x_147_);
v_isSome_162_ = lean_noption_is_some(v___x_161_);
if (v_isSome_162_ == 0)
{
lean_dec(v_x_146_);
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v___x_163_; 
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v_x_147_);
return v___x_163_;
}
else
{
lean_object* v_val_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec(v_x_147_);
v_val_164_ = lean_ctor_get(v_x_145_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v_x_145_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v_x_145_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_val_164_);
lean_dec(v_x_145_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_val_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
else
{
lean_object* v_one_172_; lean_object* v_n_173_; lean_object* v___y_175_; 
v_one_172_ = lean_unsigned_to_nat(1u);
v_n_173_ = lean_nat_sub(v_x_146_, v_one_172_);
lean_dec(v_x_146_);
if (v_isSome_162_ == 0)
{
goto v___jp_181_;
}
else
{
lean_object* v___x_183_; uint8_t v_isSome_184_; 
v___x_183_ = lean_array_fget_borrowed(v_valueArray_160_, v_x_147_);
v_isSome_184_ = lean_noption_is_some(v___x_183_);
if (v_isSome_184_ == 0)
{
goto v___jp_181_;
}
else
{
lean_object* v_val_185_; lean_object* v_wsIdx_186_; lean_object* v_wsIdx_187_; uint8_t v___x_188_; 
lean_inc(v___x_161_);
v_val_185_ = lean_noption_get(v___x_161_);
v_wsIdx_186_ = lean_ctor_get(v_val_185_, 0);
lean_inc(v_wsIdx_186_);
v_wsIdx_187_ = lean_ctor_get(v_query_144_, 0);
v___x_188_ = lean_nat_dec_eq(v_wsIdx_186_, v_wsIdx_187_);
lean_dec(v_wsIdx_186_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
lean_dec(v_val_185_);
v___x_189_ = lean_array_get_size(v_keyArray_159_);
v___x_190_ = lean_nat_add(v_x_147_, v_one_172_);
lean_dec(v_x_147_);
v___x_191_ = lean_nat_dec_lt(v___x_190_, v___x_189_);
if (v___x_191_ == 0)
{
lean_dec(v___x_190_);
v_x_146_ = v_n_173_;
v_x_147_ = v_zero_148_;
goto _start;
}
else
{
v_x_146_ = v_n_173_;
v_x_147_ = v___x_190_;
goto _start;
}
}
else
{
lean_object* v_val_194_; lean_object* v___x_195_; 
lean_dec(v_n_173_);
lean_dec(v_x_145_);
lean_inc(v___x_183_);
v_val_194_ = lean_noption_get(v___x_183_);
v___x_195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_195_, 0, v_x_147_);
lean_ctor_set(v___x_195_, 1, v_val_185_);
lean_ctor_set(v___x_195_, 2, v_val_194_);
return v___x_195_;
}
}
}
v___jp_174_:
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_176_ = lean_array_get_size(v_keyArray_159_);
v___x_177_ = lean_nat_add(v_x_147_, v_one_172_);
lean_dec(v_x_147_);
v___x_178_ = lean_nat_dec_lt(v___x_177_, v___x_176_);
if (v___x_178_ == 0)
{
lean_dec(v___x_177_);
v_x_145_ = v___y_175_;
v_x_146_ = v_n_173_;
v_x_147_ = v_zero_148_;
goto _start;
}
else
{
v_x_145_ = v___y_175_;
v_x_146_ = v_n_173_;
v_x_147_ = v___x_177_;
goto _start;
}
}
v___jp_181_:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v___x_182_; 
lean_inc(v_x_147_);
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v_x_147_);
v___y_175_ = v___x_182_;
goto v___jp_174_;
}
else
{
v___y_175_ = v_x_145_;
goto v___jp_174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_m_196_, lean_object* v_query_197_, lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_x_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_m_196_, v_query_197_, v_x_198_, v_x_199_, v_x_200_);
lean_dec_ref(v_query_197_);
lean_dec_ref(v_m_196_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(lean_object* v_m_202_, lean_object* v_query_203_){
_start:
{
lean_object* v_keyArray_204_; lean_object* v_keyName_205_; lean_object* v___x_206_; uint64_t v___y_208_; 
v_keyArray_204_ = lean_ctor_get(v_m_202_, 1);
v_keyName_205_ = lean_ctor_get(v_query_203_, 2);
v___x_206_ = lean_array_get_size(v_keyArray_204_);
if (lean_obj_tag(v_keyName_205_) == 0)
{
uint64_t v___x_223_; 
v___x_223_ = 1723ULL;
v___y_208_ = v___x_223_;
goto v___jp_207_;
}
else
{
uint64_t v_hash_224_; 
v_hash_224_ = lean_ctor_get_uint64(v_keyName_205_, sizeof(void*)*2);
v___y_208_ = v_hash_224_;
goto v___jp_207_;
}
v___jp_207_:
{
uint64_t v___x_209_; uint64_t v___x_210_; uint64_t v_fold_211_; uint64_t v___x_212_; uint64_t v___x_213_; uint64_t v___x_214_; size_t v___x_215_; size_t v___x_216_; size_t v___x_217_; size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_209_ = 32ULL;
v___x_210_ = lean_uint64_shift_right(v___y_208_, v___x_209_);
v_fold_211_ = lean_uint64_xor(v___y_208_, v___x_210_);
v___x_212_ = 16ULL;
v___x_213_ = lean_uint64_shift_right(v_fold_211_, v___x_212_);
v___x_214_ = lean_uint64_xor(v_fold_211_, v___x_213_);
v___x_215_ = lean_uint64_to_usize(v___x_214_);
v___x_216_ = lean_usize_of_nat(v___x_206_);
v___x_217_ = ((size_t)1ULL);
v___x_218_ = lean_usize_sub(v___x_216_, v___x_217_);
v___x_219_ = lean_usize_land(v___x_215_, v___x_218_);
v___x_220_ = lean_usize_to_nat(v___x_219_);
v___x_221_ = lean_box(0);
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_m_202_, v_query_203_, v___x_221_, v___x_206_, v___x_220_);
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg___boxed(lean_object* v_m_225_, lean_object* v_query_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_m_225_, v_query_226_);
lean_dec_ref(v_query_226_);
lean_dec_ref(v_m_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(lean_object* v_m_228_, lean_object* v_query_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_m_228_, v_query_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_index_231_; lean_object* v_key_232_; lean_object* v_value_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
v_index_231_ = lean_ctor_get(v___x_230_, 0);
v_key_232_ = lean_ctor_get(v___x_230_, 1);
v_value_233_ = lean_ctor_get(v___x_230_, 2);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_230_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_value_233_);
lean_inc(v_key_232_);
lean_inc(v_index_231_);
lean_dec(v___x_230_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_index_231_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_key_232_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_value_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
else
{
lean_object* v___x_241_; 
lean_dec(v___x_230_);
v___x_241_ = lean_box(1);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_242_, lean_object* v_query_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_m_242_, v_query_243_);
lean_dec_ref(v_query_243_);
lean_dec_ref(v_m_242_);
return v_res_244_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(lean_object* v_m_245_, lean_object* v_a_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_m_245_, v_a_246_);
if (lean_obj_tag(v___x_247_) == 0)
{
uint8_t v___x_248_; 
lean_dec_ref_known(v___x_247_, 3);
v___x_248_ = 1;
return v___x_248_;
}
else
{
uint8_t v___x_249_; 
v___x_249_ = 0;
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(lean_object* v_m_250_, lean_object* v_a_251_){
_start:
{
uint8_t v_res_252_; lean_object* v_r_253_; 
v_res_252_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_250_, v_a_251_);
lean_dec_ref(v_a_251_);
lean_dec_ref(v_m_250_);
v_r_253_ = lean_box(v_res_252_);
return v_r_253_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6_spec__9___redArg(lean_object* v_b_254_, lean_object* v_acc_255_, lean_object* v_i_256_){
_start:
{
lean_object* v___y_258_; lean_object* v_keyArray_266_; lean_object* v_valueArray_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v_keyArray_266_ = lean_ctor_get(v_b_254_, 1);
v_valueArray_267_ = lean_ctor_get(v_b_254_, 2);
v___x_268_ = lean_array_get_size(v_keyArray_266_);
v___x_269_ = lean_nat_dec_lt(v_i_256_, v___x_268_);
if (v___x_269_ == 0)
{
lean_dec(v_i_256_);
return v_acc_255_;
}
else
{
lean_object* v___x_270_; uint8_t v_isSome_271_; 
v___x_270_ = lean_array_fget_borrowed(v_keyArray_266_, v_i_256_);
v_isSome_271_ = lean_noption_is_some(v___x_270_);
if (v_isSome_271_ == 0)
{
goto v___jp_262_;
}
else
{
lean_object* v___x_272_; uint8_t v_isSome_273_; 
v___x_272_ = lean_array_fget_borrowed(v_valueArray_267_, v_i_256_);
v_isSome_273_ = lean_noption_is_some(v___x_272_);
if (v_isSome_273_ == 0)
{
goto v___jp_262_;
}
else
{
lean_object* v_val_274_; lean_object* v_val_275_; lean_object* v_i_277_; lean_object* v___x_282_; 
lean_inc(v___x_270_);
v_val_274_ = lean_noption_get(v___x_270_);
lean_inc(v___x_272_);
v_val_275_ = lean_noption_get(v___x_272_);
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_acc_255_, v_val_274_);
switch(lean_obj_tag(v___x_282_))
{
case 0:
{
lean_object* v_index_283_; lean_object* v_size_284_; lean_object* v___x_285_; 
v_index_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_index_283_);
lean_dec_ref_known(v___x_282_, 3);
v_size_284_ = lean_ctor_get(v_acc_255_, 0);
lean_inc(v_size_284_);
v___x_285_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_255_, v_size_284_, v_index_283_, v_val_274_, v_val_275_);
lean_dec(v_index_283_);
v___y_258_ = v___x_285_;
goto v___jp_257_;
}
case 1:
{
lean_object* v_index_286_; 
v_index_286_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_index_286_);
lean_dec_ref_known(v___x_282_, 1);
v_i_277_ = v_index_286_;
goto v___jp_276_;
}
default: 
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_255_, v___x_287_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_index_289_; 
v_index_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_index_289_);
lean_dec_ref_known(v___x_288_, 1);
v_i_277_ = v_index_289_;
goto v___jp_276_;
}
else
{
lean_dec(v_val_275_);
lean_dec(v_val_274_);
v___y_258_ = v_acc_255_;
goto v___jp_257_;
}
}
}
v___jp_276_:
{
lean_object* v_size_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_size_278_ = lean_ctor_get(v_acc_255_, 0);
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_add(v_size_278_, v___x_279_);
v___x_281_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_255_, v___x_280_, v_i_277_, v_val_274_, v_val_275_);
lean_dec(v_i_277_);
v___y_258_ = v___x_281_;
goto v___jp_257_;
}
}
}
}
v___jp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_unsigned_to_nat(1u);
v___x_260_ = lean_nat_add(v_i_256_, v___x_259_);
lean_dec(v_i_256_);
v_acc_255_ = v___y_258_;
v_i_256_ = v___x_260_;
goto _start;
}
v___jp_262_:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = lean_nat_add(v_i_256_, v___x_263_);
lean_dec(v_i_256_);
v_i_256_ = v___x_264_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6_spec__9___redArg___boxed(lean_object* v_b_290_, lean_object* v_acc_291_, lean_object* v_i_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6_spec__9___redArg(v_b_290_, v_acc_291_, v_i_292_);
lean_dec_ref(v_b_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6___redArg(lean_object* v_init_294_, lean_object* v_b_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6_spec__9___redArg(v_b_295_, v_init_294_, v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_init_298_, lean_object* v_b_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6___redArg(v_init_298_, v_b_299_);
lean_dec_ref(v_b_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___redArg(lean_object* v_m_301_){
_start:
{
lean_object* v_keyArray_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_cellCount_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v_target_309_; lean_object* v___x_310_; 
v_keyArray_302_ = lean_ctor_get(v_m_301_, 1);
v___x_303_ = lean_array_get_size(v_keyArray_302_);
v___x_304_ = lean_unsigned_to_nat(2u);
v_cellCount_305_ = lean_nat_mul(v___x_303_, v___x_304_);
v___x_306_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_305_);
v___x_307_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_305_);
v___x_308_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_305_);
v_target_309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_309_, 0, v___x_306_);
lean_ctor_set(v_target_309_, 1, v___x_307_);
lean_ctor_set(v_target_309_, 2, v___x_308_);
v___x_310_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6___redArg(v_target_309_, v_m_301_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___redArg___boxed(lean_object* v_m_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___redArg(v_m_311_);
lean_dec_ref(v_m_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(lean_object* v_self_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_toHashSet_315_; lean_object* v_toArray_316_; lean_object* v___y_318_; uint8_t v___x_321_; 
v_toHashSet_315_ = lean_ctor_get(v_self_313_, 0);
v_toArray_316_ = lean_ctor_get(v_self_313_, 1);
v___x_321_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_toHashSet_315_, v_a_314_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___y_324_; lean_object* v_i_325_; lean_object* v___y_331_; lean_object* v___y_341_; lean_object* v_i_342_; lean_object* v___x_357_; 
lean_inc_ref(v_toArray_316_);
lean_inc_ref(v_toHashSet_315_);
lean_dec_ref(v_self_313_);
v___x_322_ = lean_box(0);
v___x_357_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_toHashSet_315_, v_a_314_);
switch(lean_obj_tag(v___x_357_))
{
case 0:
{
lean_dec_ref_known(v___x_357_, 3);
v___y_318_ = v_toHashSet_315_;
goto v___jp_317_;
}
case 1:
{
lean_object* v_index_358_; lean_object* v_size_359_; lean_object* v_keyArray_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_index_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_index_358_);
lean_dec_ref_known(v___x_357_, 1);
v_size_359_ = lean_ctor_get(v_toHashSet_315_, 0);
v_keyArray_360_ = lean_ctor_get(v_toHashSet_315_, 1);
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = lean_nat_add(v_size_359_, v___x_361_);
v___x_363_ = lean_array_get_size(v_keyArray_360_);
v___x_364_ = lean_nat_dec_lt(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_dec(v___x_362_);
lean_dec(v_index_358_);
goto v___jp_347_;
}
else
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_365_ = lean_unsigned_to_nat(4u);
v___x_366_ = lean_nat_mul(v___x_362_, v___x_365_);
v___x_367_ = lean_unsigned_to_nat(3u);
v___x_368_ = lean_nat_mul(v___x_363_, v___x_367_);
v___x_369_ = lean_nat_dec_le(v___x_366_, v___x_368_);
lean_dec(v___x_368_);
lean_dec(v___x_366_);
if (v___x_369_ == 0)
{
lean_dec(v___x_362_);
lean_dec(v_index_358_);
goto v___jp_347_;
}
else
{
lean_object* v___x_370_; 
lean_inc_ref(v_a_314_);
v___x_370_ = l_Std_DHashMap_Raw_setEntry___redArg(v_toHashSet_315_, v___x_362_, v_index_358_, v_a_314_, v___x_322_);
lean_dec(v_index_358_);
v___y_318_ = v___x_370_;
goto v___jp_317_;
}
}
}
default: 
{
lean_object* v_size_371_; lean_object* v_keyArray_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v_size_371_ = lean_ctor_get(v_toHashSet_315_, 0);
v_keyArray_372_ = lean_ctor_get(v_toHashSet_315_, 1);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_nat_add(v_size_371_, v___x_373_);
v___x_375_ = lean_array_get_size(v_keyArray_372_);
v___x_376_ = lean_nat_dec_lt(v___x_374_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
lean_dec(v___x_374_);
v___x_377_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___redArg(v_toHashSet_315_);
lean_dec_ref(v_toHashSet_315_);
v___y_331_ = v___x_377_;
goto v___jp_330_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_378_ = lean_unsigned_to_nat(4u);
v___x_379_ = lean_nat_mul(v___x_374_, v___x_378_);
lean_dec(v___x_374_);
v___x_380_ = lean_unsigned_to_nat(3u);
v___x_381_ = lean_nat_mul(v___x_375_, v___x_380_);
v___x_382_ = lean_nat_dec_le(v___x_379_, v___x_381_);
lean_dec(v___x_381_);
lean_dec(v___x_379_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
v___x_383_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___redArg(v_toHashSet_315_);
lean_dec_ref(v_toHashSet_315_);
v___y_331_ = v___x_383_;
goto v___jp_330_;
}
else
{
v___y_331_ = v_toHashSet_315_;
goto v___jp_330_;
}
}
}
}
v___jp_323_:
{
lean_object* v_size_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_size_326_ = lean_ctor_get(v___y_324_, 0);
v___x_327_ = lean_unsigned_to_nat(1u);
v___x_328_ = lean_nat_add(v_size_326_, v___x_327_);
lean_inc_ref(v_a_314_);
v___x_329_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_324_, v___x_328_, v_i_325_, v_a_314_, v___x_322_);
lean_dec(v_i_325_);
v___y_318_ = v___x_329_;
goto v___jp_317_;
}
v___jp_330_:
{
lean_object* v___x_332_; 
v___x_332_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v___y_331_, v_a_314_);
switch(lean_obj_tag(v___x_332_))
{
case 0:
{
lean_object* v_index_333_; lean_object* v_size_334_; lean_object* v___x_335_; 
v_index_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_index_333_);
lean_dec_ref_known(v___x_332_, 3);
v_size_334_ = lean_ctor_get(v___y_331_, 0);
lean_inc(v_size_334_);
lean_inc_ref(v_a_314_);
v___x_335_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_331_, v_size_334_, v_index_333_, v_a_314_, v___x_322_);
lean_dec(v_index_333_);
v___y_318_ = v___x_335_;
goto v___jp_317_;
}
case 1:
{
lean_object* v_index_336_; 
v_index_336_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_index_336_);
lean_dec_ref_known(v___x_332_, 1);
v___y_324_ = v___y_331_;
v_i_325_ = v_index_336_;
goto v___jp_323_;
}
default: 
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_331_, v___x_337_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_index_339_; 
v_index_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_index_339_);
lean_dec_ref_known(v___x_338_, 1);
v___y_324_ = v___y_331_;
v_i_325_ = v_index_339_;
goto v___jp_323_;
}
else
{
v___y_318_ = v___y_331_;
goto v___jp_317_;
}
}
}
}
v___jp_340_:
{
lean_object* v_size_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_size_343_ = lean_ctor_get(v___y_341_, 0);
v___x_344_ = lean_unsigned_to_nat(1u);
v___x_345_ = lean_nat_add(v_size_343_, v___x_344_);
lean_inc_ref(v_a_314_);
v___x_346_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_341_, v___x_345_, v_i_342_, v_a_314_, v___x_322_);
lean_dec(v_i_342_);
v___y_318_ = v___x_346_;
goto v___jp_317_;
}
v___jp_347_:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___redArg(v_toHashSet_315_);
lean_dec_ref(v_toHashSet_315_);
v___x_349_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v___x_348_, v_a_314_);
switch(lean_obj_tag(v___x_349_))
{
case 0:
{
lean_object* v_index_350_; lean_object* v_size_351_; lean_object* v___x_352_; 
v_index_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_index_350_);
lean_dec_ref_known(v___x_349_, 3);
v_size_351_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_size_351_);
lean_inc_ref(v_a_314_);
v___x_352_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_348_, v_size_351_, v_index_350_, v_a_314_, v___x_322_);
lean_dec(v_index_350_);
v___y_318_ = v___x_352_;
goto v___jp_317_;
}
case 1:
{
lean_object* v_index_353_; 
v_index_353_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_index_353_);
lean_dec_ref_known(v___x_349_, 1);
v___y_341_ = v___x_348_;
v_i_342_ = v_index_353_;
goto v___jp_340_;
}
default: 
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_348_, v___x_354_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_index_356_; 
v_index_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_index_356_);
lean_dec_ref_known(v___x_355_, 1);
v___y_341_ = v___x_348_;
v_i_342_ = v_index_356_;
goto v___jp_340_;
}
else
{
v___y_318_ = v___x_348_;
goto v___jp_317_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_314_);
return v_self_313_;
}
v___jp_317_:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_array_push(v_toArray_316_, v_a_314_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___y_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(lean_object* v_as_384_, size_t v_i_385_, size_t v_stop_386_, lean_object* v_b_387_){
_start:
{
uint8_t v___x_388_; 
v___x_388_ = lean_usize_dec_eq(v_i_385_, v_stop_386_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; size_t v___x_391_; size_t v___x_392_; 
v___x_389_ = lean_array_uget_borrowed(v_as_384_, v_i_385_);
lean_inc(v___x_389_);
v___x_390_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v_b_387_, v___x_389_);
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_385_, v___x_391_);
v_i_385_ = v___x_392_;
v_b_387_ = v___x_390_;
goto _start;
}
else
{
return v_b_387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1___boxed(lean_object* v_as_394_, lean_object* v_i_395_, lean_object* v_stop_396_, lean_object* v_b_397_){
_start:
{
size_t v_i_boxed_398_; size_t v_stop_boxed_399_; lean_object* v_res_400_; 
v_i_boxed_398_ = lean_unbox_usize(v_i_395_);
lean_dec(v_i_395_);
v_stop_boxed_399_ = lean_unbox_usize(v_stop_396_);
lean_dec(v_stop_396_);
v_res_400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_as_394_, v_i_boxed_398_, v_stop_boxed_399_, v_b_397_);
lean_dec_ref(v_as_394_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(lean_object* v_as_401_, size_t v_i_402_, size_t v_stop_403_, lean_object* v_b_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
uint8_t v___x_412_; 
v___x_412_ = lean_usize_dec_eq(v_i_402_, v_stop_403_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v_keyName_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_413_ = lean_array_uget_borrowed(v_as_401_, v_i_402_);
v_keyName_414_ = lean_ctor_get(v___x_413_, 2);
v___x_415_ = l_Lake_Package_transDepsFacet;
lean_inc(v_keyName_414_);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v_keyName_414_);
v___x_417_ = l_Lake_Package_keyword;
lean_inc(v___x_413_);
v___x_418_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
lean_ctor_set(v___x_418_, 2, v___x_413_);
lean_ctor_set(v___x_418_, 3, v___x_415_);
lean_inc_ref(v___y_405_);
lean_inc_ref(v___y_409_);
lean_inc(v___y_408_);
lean_inc(v___y_407_);
lean_inc(v___y_406_);
v___x_419_ = lean_apply_7(v___y_405_, v___x_418_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, lean_box(0));
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v_a_421_; lean_object* v___x_422_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
v_a_421_ = lean_ctor_get(v___x_419_, 1);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_419_, 2);
v___x_422_ = l_Lake_Job_await___redArg(v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v_a_424_; lean_object* v___y_426_; lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_a_423_);
v_a_424_ = lean_ctor_get(v___x_422_, 1);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_422_, 2);
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = lean_array_get_size(v_a_423_);
v___x_433_ = lean_nat_dec_lt(v___x_431_, v___x_432_);
if (v___x_433_ == 0)
{
lean_dec(v_a_423_);
v___y_426_ = v_b_404_;
goto v___jp_425_;
}
else
{
uint8_t v___x_434_; 
v___x_434_ = lean_nat_dec_le(v___x_432_, v___x_432_);
if (v___x_434_ == 0)
{
if (v___x_433_ == 0)
{
lean_dec(v_a_423_);
v___y_426_ = v_b_404_;
goto v___jp_425_;
}
else
{
size_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; 
v___x_435_ = ((size_t)0ULL);
v___x_436_ = lean_usize_of_nat(v___x_432_);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_423_, v___x_435_, v___x_436_, v_b_404_);
lean_dec(v_a_423_);
v___y_426_ = v___x_437_;
goto v___jp_425_;
}
}
else
{
size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; 
v___x_438_ = ((size_t)0ULL);
v___x_439_ = lean_usize_of_nat(v___x_432_);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_423_, v___x_438_, v___x_439_, v_b_404_);
lean_dec(v_a_423_);
v___y_426_ = v___x_440_;
goto v___jp_425_;
}
}
v___jp_425_:
{
lean_object* v___x_427_; size_t v___x_428_; size_t v___x_429_; 
lean_inc(v___x_413_);
v___x_427_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v___y_426_, v___x_413_);
v___x_428_ = ((size_t)1ULL);
v___x_429_ = lean_usize_add(v_i_402_, v___x_428_);
v_i_402_ = v___x_429_;
v_b_404_ = v___x_427_;
v___y_410_ = v_a_424_;
goto _start;
}
}
else
{
lean_object* v_a_441_; lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
lean_dec_ref(v___y_405_);
lean_dec_ref(v_b_404_);
v_a_441_ = lean_ctor_get(v___x_422_, 0);
v_a_442_ = lean_ctor_get(v___x_422_, 1);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_422_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_inc(v_a_441_);
lean_dec(v___x_422_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_441_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
lean_object* v_a_450_; lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec_ref(v___y_405_);
lean_dec_ref(v_b_404_);
v_a_450_ = lean_ctor_get(v___x_419_, 0);
v_a_451_ = lean_ctor_get(v___x_419_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_419_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_inc(v_a_450_);
lean_dec(v___x_419_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_450_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
else
{
lean_object* v___x_459_; 
lean_dec_ref(v___y_405_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_b_404_);
lean_ctor_set(v___x_459_, 1, v___y_410_);
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3___boxed(lean_object* v_as_460_, lean_object* v_i_461_, lean_object* v_stop_462_, lean_object* v_b_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
size_t v_i_boxed_471_; size_t v_stop_boxed_472_; lean_object* v_res_473_; 
v_i_boxed_471_ = lean_unbox_usize(v_i_461_);
lean_dec(v_i_461_);
v_stop_boxed_472_ = lean_unbox_usize(v_stop_462_);
lean_dec(v_stop_462_);
v_res_473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_as_460_, v_i_boxed_471_, v_stop_boxed_472_, v_b_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v_as_460_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(lean_object* v___x_474_, lean_object* v___x_475_, lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v_depPkgs_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_a_487_; lean_object* v_a_488_; lean_object* v___y_508_; uint8_t v___x_520_; 
v___x_520_ = lean_nat_dec_lt(v___x_474_, v___x_476_);
if (v___x_520_ == 0)
{
lean_dec_ref(v___y_479_);
v_a_487_ = v___x_477_;
v_a_488_ = v___y_484_;
goto v___jp_486_;
}
else
{
uint8_t v___x_521_; 
v___x_521_ = lean_nat_dec_le(v___x_476_, v___x_476_);
if (v___x_521_ == 0)
{
if (v___x_520_ == 0)
{
lean_dec_ref(v___y_479_);
v_a_487_ = v___x_477_;
v_a_488_ = v___y_484_;
goto v___jp_486_;
}
else
{
size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; 
v___x_522_ = ((size_t)0ULL);
v___x_523_ = lean_usize_of_nat(v___x_476_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_478_, v___x_522_, v___x_523_, v___x_477_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
v___y_508_ = v___x_524_;
goto v___jp_507_;
}
}
else
{
size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v___x_525_ = ((size_t)0ULL);
v___x_526_ = lean_usize_of_nat(v___x_476_);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_478_, v___x_525_, v___x_526_, v___x_477_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
v___y_508_ = v___x_527_;
goto v___jp_507_;
}
}
v___jp_486_:
{
lean_object* v_toArray_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_505_; 
v_toArray_489_ = lean_ctor_get(v_a_487_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_a_487_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v_a_487_, 0);
lean_dec(v_unused_506_);
v___x_491_ = v_a_487_;
v_isShared_492_ = v_isSharedCheck_505_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_toArray_489_);
lean_dec(v_a_487_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_505_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_493_ = lean_mk_empty_array_with_capacity(v___x_474_);
v___x_494_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_495_ = 0;
v___x_496_ = 0;
v___x_497_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_498_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_498_, 0, v___x_493_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
lean_ctor_set(v___x_498_, 2, v___x_474_);
lean_ctor_set_uint8(v___x_498_, sizeof(void*)*3, v___x_495_);
lean_ctor_set_uint8(v___x_498_, sizeof(void*)*3 + 1, v___x_496_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v___x_498_);
lean_ctor_set(v___x_491_, 0, v_toArray_489_);
v___x_500_ = v___x_491_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_toArray_489_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_498_);
v___x_500_ = v_reuseFailAlloc_504_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_task_pure(v___x_500_);
v___x_502_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_502_, 0, v___x_501_);
lean_ctor_set(v___x_502_, 1, v___x_475_);
lean_ctor_set(v___x_502_, 2, v___x_494_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*3, v___x_496_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v_a_488_);
return v___x_503_;
}
}
}
v___jp_507_:
{
if (lean_obj_tag(v___y_508_) == 0)
{
lean_object* v_a_509_; lean_object* v_a_510_; 
v_a_509_ = lean_ctor_get(v___y_508_, 0);
lean_inc(v_a_509_);
v_a_510_ = lean_ctor_get(v___y_508_, 1);
lean_inc(v_a_510_);
lean_dec_ref_known(v___y_508_, 2);
v_a_487_ = v_a_509_;
v_a_488_ = v_a_510_;
goto v___jp_486_;
}
else
{
lean_object* v_a_511_; lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec(v___x_475_);
lean_dec(v___x_474_);
v_a_511_ = lean_ctor_get(v___y_508_, 0);
v_a_512_ = lean_ctor_get(v___y_508_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v___y_508_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___y_508_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_inc(v_a_511_);
lean_dec(v___y_508_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_511_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed(lean_object* v___x_528_, lean_object* v___x_529_, lean_object* v___x_530_, lean_object* v___x_531_, lean_object* v_depPkgs_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(v___x_528_, v___x_529_, v___x_530_, v___x_531_, v_depPkgs_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v_depPkgs_532_);
lean_dec(v___x_530_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(lean_object* v_self_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_depPkgs_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___f_554_; lean_object* v___x_555_; 
v_depPkgs_549_ = lean_ctor_get(v_self_541_, 14);
lean_inc_ref(v_depPkgs_549_);
lean_dec_ref(v_self_541_);
v___x_550_ = lean_box(0);
v___x_551_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2;
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_array_get_size(v_depPkgs_549_);
v___f_554_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed), 12, 5);
lean_closure_set(v___f_554_, 0, v___x_552_);
lean_closure_set(v___f_554_, 1, v___x_550_);
lean_closure_set(v___f_554_, 2, v___x_553_);
lean_closure_set(v___f_554_, 3, v___x_551_);
lean_closure_set(v___f_554_, 4, v_depPkgs_549_);
v___x_555_ = l_Lake_ensureJob___redArg(v___x_550_, v___f_554_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___boxed(lean_object* v_self_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(v_self_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec(v_a_559_);
lean_dec(v_a_558_);
return v_res_564_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object* v_00_u03b2_565_, lean_object* v_m_566_, lean_object* v_a_567_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_566_, v_a_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_569_, lean_object* v_m_570_, lean_object* v_a_571_){
_start:
{
uint8_t v_res_572_; lean_object* v_r_573_; 
v_res_572_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(v_00_u03b2_569_, v_m_570_, v_a_571_);
lean_dec_ref(v_a_571_);
lean_dec_ref(v_m_570_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1(lean_object* v_00_u03b2_574_, lean_object* v_m_575_, lean_object* v_query_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_m_575_, v_query_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___boxed(lean_object* v_00_u03b2_578_, lean_object* v_m_579_, lean_object* v_query_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1(v_00_u03b2_578_, v_m_579_, v_query_580_);
lean_dec_ref(v_query_580_);
lean_dec_ref(v_m_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2(lean_object* v_00_u03b2_582_, lean_object* v_m_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___redArg(v_m_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2___boxed(lean_object* v_00_u03b2_585_, lean_object* v_m_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2(v_00_u03b2_585_, v_m_586_);
lean_dec_ref(v_m_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_588_, lean_object* v_m_589_, lean_object* v_query_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_m_589_, v_query_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_592_, lean_object* v_m_593_, lean_object* v_query_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(v_00_u03b2_592_, v_m_593_, v_query_594_);
lean_dec_ref(v_query_594_);
lean_dec_ref(v_m_593_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_596_, lean_object* v_m_597_, lean_object* v_query_598_, lean_object* v_x_599_, lean_object* v_x_600_, lean_object* v_x_601_, lean_object* v_x_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_m_597_, v_query_598_, v_x_599_, v_x_600_, v_x_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_604_, lean_object* v_m_605_, lean_object* v_query_606_, lean_object* v_x_607_, lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4(v_00_u03b2_604_, v_m_605_, v_query_606_, v_x_607_, v_x_608_, v_x_609_, v_x_610_);
lean_dec_ref(v_query_606_);
lean_dec_ref(v_m_605_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_612_, lean_object* v_init_613_, lean_object* v_b_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6___redArg(v_init_613_, v_b_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_616_, lean_object* v_init_617_, lean_object* v_b_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6(v_00_u03b2_616_, v_init_617_, v_b_618_);
lean_dec_ref(v_b_618_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6_spec__9(lean_object* v_00_u03b2_620_, lean_object* v_b_621_, lean_object* v_acc_622_, lean_object* v_i_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6_spec__9___redArg(v_b_621_, v_acc_622_, v_i_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6_spec__9___boxed(lean_object* v_00_u03b2_625_, lean_object* v_b_626_, lean_object* v_acc_627_, lean_object* v_i_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__2_spec__6_spec__9(v_00_u03b2_625_, v_b_626_, v_acc_627_, v_i_628_);
lean_dec_ref(v_b_626_);
return v_res_629_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_631_; lean_object* v___f_632_; uint8_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_631_ = 1;
v___f_632_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__0));
v___x_633_ = 0;
v___x_634_ = lean_box(0);
v___x_635_ = ((lean_object*)(l_Lake_Package_transDepsFacetConfig___closed__0));
v___x_636_ = l_Lake_Package_keyword;
v___x_637_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_635_);
lean_ctor_set(v___x_637_, 2, v___x_634_);
lean_ctor_set(v___x_637_, 3, v___f_632_);
lean_ctor_set_uint8(v___x_637_, sizeof(void*)*4, v___x_633_);
lean_ctor_set_uint8(v___x_637_, sizeof(void*)*4 + 1, v___x_631_);
return v___x_637_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig(void){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = lean_obj_once(&l_Lake_Package_transDepsFacetConfig___closed__1, &l_Lake_Package_transDepsFacetConfig___closed__1_once, _init_l_Lake_Package_transDepsFacetConfig___closed__1);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object* v_self_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_config_647_; uint8_t v_preferReleaseBuild_648_; 
v_config_647_ = lean_ctor_get(v_self_639_, 6);
v_preferReleaseBuild_648_ = lean_ctor_get_uint8(v_config_647_, sizeof(void*)*27 + 2);
if (v_preferReleaseBuild_648_ == 0)
{
lean_object* v_keyName_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_keyName_649_ = lean_ctor_get(v_self_639_, 2);
v___x_650_ = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(v_keyName_649_);
v___x_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_651_, 0, v_keyName_649_);
v___x_652_ = l_Lake_Package_keyword;
v___x_653_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
lean_ctor_set(v___x_653_, 2, v_self_639_);
lean_ctor_set(v___x_653_, 3, v___x_650_);
lean_inc_ref(v_a_644_);
lean_inc(v_a_643_);
lean_inc(v_a_642_);
lean_inc(v_a_641_);
v___x_654_ = lean_apply_7(v_a_640_, v___x_653_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, lean_box(0));
return v___x_654_;
}
else
{
lean_object* v_keyName_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_keyName_655_ = lean_ctor_get(v_self_639_, 2);
v___x_656_ = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(v_keyName_655_);
v___x_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_657_, 0, v_keyName_655_);
v___x_658_ = l_Lake_Package_keyword;
v___x_659_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
lean_ctor_set(v___x_659_, 2, v_self_639_);
lean_ctor_set(v___x_659_, 3, v___x_656_);
lean_inc_ref(v_a_644_);
lean_inc(v_a_643_);
lean_inc(v_a_642_);
lean_inc(v_a_641_);
v___x_660_ = lean_apply_7(v_a_640_, v___x_659_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, lean_box(0));
return v___x_660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___boxed(lean_object* v_self_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(v_self_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec(v_a_664_);
lean_dec(v_a_663_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t v_fmt_672_, uint8_t v_a_673_){
_start:
{
if (v_fmt_672_ == 0)
{
if (v_a_673_ == 0)
{
lean_object* v___x_674_; 
v___x_674_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0));
return v___x_674_;
}
else
{
lean_object* v___x_675_; 
v___x_675_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1));
return v___x_675_;
}
}
else
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_676_, 0, v_a_673_);
v___x_677_ = l_Lean_Json_compress(v___x_676_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object* v_fmt_678_, lean_object* v_a_679_){
_start:
{
uint8_t v_fmt_boxed_680_; uint8_t v_a_boxed_681_; lean_object* v_res_682_; 
v_fmt_boxed_680_ = lean_unbox(v_fmt_678_);
v_a_boxed_681_ = lean_unbox(v_a_679_);
v_res_682_ = l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(v_fmt_boxed_680_, v_a_boxed_681_);
return v_res_682_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_685_; uint8_t v___x_686_; lean_object* v___x_687_; lean_object* v___f_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___f_685_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_686_ = 1;
v___x_687_ = l_Lake_instDataKindBool;
v___f_688_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__0));
v___x_689_ = l_Lake_Package_keyword;
v___x_690_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___f_688_);
lean_ctor_set(v___x_690_, 2, v___x_687_);
lean_ctor_set(v___x_690_, 3, v___f_685_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*4, v___x_686_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*4 + 1, v___x_686_);
return v___x_690_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig(void){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = lean_obj_once(&l_Lake_Package_optBuildCacheFacetConfig___closed__2, &l_Lake_Package_optBuildCacheFacetConfig___closed__2_once, _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(lean_object* v_self_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v___y_703_; uint8_t v___y_704_; lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; uint8_t v___y_730_; uint8_t v___y_731_; lean_object* v_toContext_735_; lean_object* v_lakeEnv_736_; uint8_t v_noCache_737_; lean_object* v_toolchain_738_; uint8_t v_a_740_; lean_object* v_a_741_; 
v_toContext_735_ = lean_ctor_get(v_a_699_, 1);
v_lakeEnv_736_ = lean_ctor_get(v_toContext_735_, 0);
v_noCache_737_ = lean_ctor_get_uint8(v_lakeEnv_736_, sizeof(void*)*20);
v_toolchain_738_ = lean_ctor_get(v_lakeEnv_736_, 19);
if (v_noCache_737_ == 0)
{
uint8_t v___x_756_; 
v___x_756_ = 1;
v_a_740_ = v___x_756_;
v_a_741_ = v_a_700_;
goto v___jp_739_;
}
else
{
uint8_t v___x_757_; 
v___x_757_ = 0;
v_a_740_ = v___x_757_;
v_a_741_ = v_a_700_;
goto v___jp_739_;
}
v___jp_702_:
{
uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_705_ = 1;
v___x_706_ = lean_box(0);
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_709_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_710_ = 0;
v___x_711_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_712_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_712_, 0, v___x_708_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
lean_ctor_set(v___x_712_, 2, v___x_707_);
lean_ctor_set_uint8(v___x_712_, sizeof(void*)*3, v___x_710_);
lean_ctor_set_uint8(v___x_712_, sizeof(void*)*3 + 1, v___y_704_);
v___x_713_ = lean_box(v___x_705_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___x_712_);
v___x_715_ = lean_task_pure(v___x_714_);
v___x_716_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v___x_706_);
lean_ctor_set(v___x_716_, 2, v___x_709_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*3, v___y_704_);
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v___y_703_);
return v___x_717_;
}
v___jp_718_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_721_ = l_Lake_Package_optBuildCacheFacet;
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v___y_720_);
v___x_723_ = l_Lake_Package_keyword;
v___x_724_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_724_, 0, v___x_722_);
lean_ctor_set(v___x_724_, 1, v___x_723_);
lean_ctor_set(v___x_724_, 2, v_self_694_);
lean_ctor_set(v___x_724_, 3, v___x_721_);
lean_inc_ref(v_a_699_);
lean_inc(v_a_698_);
lean_inc(v_a_697_);
lean_inc(v_a_696_);
v___x_725_ = lean_apply_7(v_a_695_, v___x_724_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v___y_719_, lean_box(0));
return v___x_725_;
}
v___jp_726_:
{
if (v___y_731_ == 0)
{
lean_dec(v___y_728_);
lean_dec_ref(v_a_695_);
lean_dec_ref(v_self_694_);
v___y_703_ = v___y_727_;
v___y_704_ = v___y_731_;
goto v___jp_702_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_732_ = lean_string_utf8_byte_size(v___y_729_);
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = lean_nat_dec_eq(v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
v___y_719_ = v___y_727_;
v___y_720_ = v___y_728_;
goto v___jp_718_;
}
else
{
lean_dec(v___y_728_);
lean_dec_ref(v_a_695_);
lean_dec_ref(v_self_694_);
v___y_703_ = v___y_727_;
v___y_704_ = v___y_730_;
goto v___jp_702_;
}
}
}
v___jp_739_:
{
lean_object* v_config_742_; lean_object* v_keyName_743_; lean_object* v_dir_744_; lean_object* v_scope_745_; lean_object* v_buildDir_746_; uint8_t v_preferReleaseBuild_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_config_742_ = lean_ctor_get(v_self_694_, 6);
v_keyName_743_ = lean_ctor_get(v_self_694_, 2);
v_dir_744_ = lean_ctor_get(v_self_694_, 4);
v_scope_745_ = lean_ctor_get(v_self_694_, 10);
v_buildDir_746_ = lean_ctor_get(v_config_742_, 5);
v_preferReleaseBuild_747_ = lean_ctor_get_uint8(v_config_742_, sizeof(void*)*27 + 2);
lean_inc_ref(v_buildDir_746_);
v___x_748_ = l_System_FilePath_normalize(v_buildDir_746_);
lean_inc_ref(v_dir_744_);
v___x_749_ = l_Lake_joinRelative(v_dir_744_, v___x_748_);
v___x_750_ = l_System_FilePath_pathExists(v___x_749_);
lean_dec_ref(v___x_749_);
if (v_a_740_ == 0)
{
lean_dec_ref(v_a_695_);
lean_dec_ref(v_self_694_);
v___y_703_ = v_a_741_;
v___y_704_ = v_a_740_;
goto v___jp_702_;
}
else
{
if (v___x_750_ == 0)
{
if (v_preferReleaseBuild_747_ == 0)
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0));
v___x_752_ = lean_string_dec_eq(v_scope_745_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_753_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1));
v___x_754_ = lean_string_dec_eq(v_scope_745_, v___x_753_);
lean_inc(v_keyName_743_);
v___y_727_ = v_a_741_;
v___y_728_ = v_keyName_743_;
v___y_729_ = v_toolchain_738_;
v___y_730_ = v_preferReleaseBuild_747_;
v___y_731_ = v___x_754_;
goto v___jp_726_;
}
else
{
lean_inc(v_keyName_743_);
v___y_727_ = v_a_741_;
v___y_728_ = v_keyName_743_;
v___y_729_ = v_toolchain_738_;
v___y_730_ = v_preferReleaseBuild_747_;
v___y_731_ = v___x_752_;
goto v___jp_726_;
}
}
else
{
lean_inc(v_keyName_743_);
v___y_719_ = v_a_741_;
v___y_720_ = v_keyName_743_;
goto v___jp_718_;
}
}
else
{
uint8_t v___x_755_; 
lean_dec_ref(v_a_695_);
lean_dec_ref(v_self_694_);
v___x_755_ = 0;
v___y_703_ = v_a_741_;
v___y_704_ = v___x_755_;
goto v___jp_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___boxed(lean_object* v_self_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec(v_a_761_);
lean_dec(v_a_760_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object* v_self_771_, lean_object* v_facet_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_toBuildConfig_776_; uint8_t v_verbosity_777_; uint8_t v___x_778_; uint8_t v___x_779_; 
v_toBuildConfig_776_ = lean_ctor_get(v_a_773_, 0);
v_verbosity_777_ = lean_ctor_get_uint8(v_toBuildConfig_776_, sizeof(void*)*4 + 3);
v___x_778_ = 2;
v___x_779_ = l_Lake_instDecidableEqVerbosity(v_verbosity_777_, v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec(v_facet_772_);
lean_dec_ref(v_self_771_);
v___x_780_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v_a_774_);
return v___x_781_;
}
else
{
lean_object* v_baseName_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v_baseName_782_ = lean_ctor_get(v_self_771_, 1);
lean_inc(v_baseName_782_);
lean_dec_ref(v_self_771_);
v___x_783_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_784_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_782_, v___x_779_);
v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
lean_dec_ref(v___x_784_);
v___x_786_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_787_ = lean_string_append(v___x_785_, v___x_786_);
v___x_788_ = l_Lake_Name_eraseHead(v_facet_772_);
v___x_789_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_788_, v___x_779_);
v___x_790_ = lean_string_append(v___x_787_, v___x_789_);
lean_dec_ref(v___x_789_);
v___x_791_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_792_ = lean_string_append(v___x_790_, v___x_791_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v_a_774_);
return v___x_793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* v_self_794_, lean_object* v_facet_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(v_self_794_, v_facet_795_, v_a_796_, v_a_797_);
lean_dec_ref(v_a_796_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* v_self_800_, lean_object* v_facet_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_toBuildConfig_809_; uint8_t v_verbosity_810_; uint8_t v___x_811_; uint8_t v___x_812_; 
v_toBuildConfig_809_ = lean_ctor_get(v_a_806_, 0);
v_verbosity_810_ = lean_ctor_get_uint8(v_toBuildConfig_809_, sizeof(void*)*4 + 3);
v___x_811_ = 2;
v___x_812_ = l_Lake_instDecidableEqVerbosity(v_verbosity_810_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec(v_facet_801_);
lean_dec_ref(v_self_800_);
v___x_813_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v_a_807_);
return v___x_814_;
}
else
{
lean_object* v_baseName_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_baseName_815_ = lean_ctor_get(v_self_800_, 1);
lean_inc(v_baseName_815_);
lean_dec_ref(v_self_800_);
v___x_816_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_817_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_815_, v___x_812_);
v___x_818_ = lean_string_append(v___x_816_, v___x_817_);
lean_dec_ref(v___x_817_);
v___x_819_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_820_ = lean_string_append(v___x_818_, v___x_819_);
v___x_821_ = l_Lake_Name_eraseHead(v_facet_801_);
v___x_822_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_821_, v___x_812_);
v___x_823_ = lean_string_append(v___x_820_, v___x_822_);
lean_dec_ref(v___x_822_);
v___x_824_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_825_ = lean_string_append(v___x_823_, v___x_824_);
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v_a_807_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* v_self_827_, lean_object* v_facet_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(v_self_827_, v_facet_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
return v_res_836_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_840_ = l_Lake_Name_eraseHead(v___x_839_);
return v___x_840_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_842_ = l_Lake_Name_eraseHead(v___x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(lean_object* v_self_843_, uint8_t v_success_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_a_853_; lean_object* v_a_854_; lean_object* v_a_875_; lean_object* v_a_876_; 
if (v_success_844_ == 0)
{
lean_object* v_config_896_; uint8_t v_preferReleaseBuild_897_; 
v_config_896_ = lean_ctor_get(v_self_843_, 6);
v_preferReleaseBuild_897_ = lean_ctor_get_uint8(v_config_896_, sizeof(void*)*27 + 2);
if (v_preferReleaseBuild_897_ == 0)
{
lean_object* v_toBuildConfig_898_; lean_object* v_baseName_899_; uint8_t v_verbosity_900_; uint8_t v___x_901_; uint8_t v___x_902_; 
v_toBuildConfig_898_ = lean_ctor_get(v___y_849_, 0);
v_baseName_899_ = lean_ctor_get(v_self_843_, 1);
lean_inc(v_baseName_899_);
lean_dec_ref(v_self_843_);
v_verbosity_900_ = lean_ctor_get_uint8(v_toBuildConfig_898_, sizeof(void*)*4 + 3);
v___x_901_ = 2;
v___x_902_ = l_Lake_instDecidableEqVerbosity(v_verbosity_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; 
lean_dec(v_baseName_899_);
v___x_903_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_853_ = v___x_903_;
v_a_854_ = v___y_850_;
goto v___jp_852_;
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_904_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_905_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_899_, v___x_902_);
v___x_906_ = lean_string_append(v___x_904_, v___x_905_);
lean_dec_ref(v___x_905_);
v___x_907_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_908_ = lean_string_append(v___x_906_, v___x_907_);
v___x_909_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2);
v___x_910_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_909_, v___x_902_);
v___x_911_ = lean_string_append(v___x_908_, v___x_910_);
lean_dec_ref(v___x_910_);
v___x_912_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_913_ = lean_string_append(v___x_911_, v___x_912_);
v_a_853_ = v___x_913_;
v_a_854_ = v___y_850_;
goto v___jp_852_;
}
}
else
{
lean_object* v_toBuildConfig_914_; lean_object* v_baseName_915_; uint8_t v_verbosity_916_; uint8_t v___x_917_; uint8_t v___x_918_; 
v_toBuildConfig_914_ = lean_ctor_get(v___y_849_, 0);
v_baseName_915_ = lean_ctor_get(v_self_843_, 1);
lean_inc(v_baseName_915_);
lean_dec_ref(v_self_843_);
v_verbosity_916_ = lean_ctor_get_uint8(v_toBuildConfig_914_, sizeof(void*)*4 + 3);
v___x_917_ = 2;
v___x_918_ = l_Lake_instDecidableEqVerbosity(v_verbosity_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; 
lean_dec(v_baseName_915_);
v___x_919_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_875_ = v___x_919_;
v_a_876_ = v___y_850_;
goto v___jp_874_;
}
else
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_920_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_921_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_915_, v___x_918_);
v___x_922_ = lean_string_append(v___x_920_, v___x_921_);
lean_dec_ref(v___x_921_);
v___x_923_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_924_ = lean_string_append(v___x_922_, v___x_923_);
v___x_925_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
v___x_926_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_925_, v___x_918_);
v___x_927_ = lean_string_append(v___x_924_, v___x_926_);
lean_dec_ref(v___x_926_);
v___x_928_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_929_ = lean_string_append(v___x_927_, v___x_928_);
v_a_875_ = v___x_929_;
v_a_876_ = v___y_850_;
goto v___jp_874_;
}
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec_ref(v_self_843_);
v___x_930_ = lean_box(0);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v___y_850_);
return v___x_931_;
}
v___jp_852_:
{
lean_object* v_log_855_; uint8_t v_action_856_; uint8_t v_wantsRebuild_857_; lean_object* v_trace_858_; lean_object* v_buildTime_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_873_; 
v_log_855_ = lean_ctor_get(v_a_854_, 0);
v_action_856_ = lean_ctor_get_uint8(v_a_854_, sizeof(void*)*3);
v_wantsRebuild_857_ = lean_ctor_get_uint8(v_a_854_, sizeof(void*)*3 + 1);
v_trace_858_ = lean_ctor_get(v_a_854_, 1);
v_buildTime_859_ = lean_ctor_get(v_a_854_, 2);
v_isSharedCheck_873_ = !lean_is_exclusive(v_a_854_);
if (v_isSharedCheck_873_ == 0)
{
v___x_861_ = v_a_854_;
v_isShared_862_ = v_isSharedCheck_873_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_buildTime_859_);
lean_inc(v_trace_858_);
lean_inc(v_log_855_);
lean_dec(v_a_854_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_873_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_863_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0));
v___x_864_ = lean_string_append(v___x_863_, v_a_853_);
lean_dec_ref(v_a_853_);
v___x_865_ = 0;
v___x_866_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set_uint8(v___x_866_, sizeof(void*)*1, v___x_865_);
v___x_867_ = lean_box(0);
v___x_868_ = lean_array_push(v_log_855_, v___x_866_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_868_);
v___x_870_ = v___x_861_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_trace_858_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_buildTime_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_872_, sizeof(void*)*3, v_action_856_);
lean_ctor_set_uint8(v_reuseFailAlloc_872_, sizeof(void*)*3 + 1, v_wantsRebuild_857_);
v___x_870_ = v_reuseFailAlloc_872_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_871_; 
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_867_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
return v___x_871_;
}
}
}
v___jp_874_:
{
lean_object* v_log_877_; uint8_t v_action_878_; uint8_t v_wantsRebuild_879_; lean_object* v_trace_880_; lean_object* v_buildTime_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_895_; 
v_log_877_ = lean_ctor_get(v_a_876_, 0);
v_action_878_ = lean_ctor_get_uint8(v_a_876_, sizeof(void*)*3);
v_wantsRebuild_879_ = lean_ctor_get_uint8(v_a_876_, sizeof(void*)*3 + 1);
v_trace_880_ = lean_ctor_get(v_a_876_, 1);
v_buildTime_881_ = lean_ctor_get(v_a_876_, 2);
v_isSharedCheck_895_ = !lean_is_exclusive(v_a_876_);
if (v_isSharedCheck_895_ == 0)
{
v___x_883_ = v_a_876_;
v_isShared_884_ = v_isSharedCheck_895_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_buildTime_881_);
lean_inc(v_trace_880_);
lean_inc(v_log_877_);
lean_dec(v_a_876_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_895_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_885_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1));
v___x_886_ = lean_string_append(v___x_885_, v_a_875_);
lean_dec_ref(v_a_875_);
v___x_887_ = 2;
v___x_888_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set_uint8(v___x_888_, sizeof(void*)*1, v___x_887_);
v___x_889_ = lean_box(0);
v___x_890_ = lean_array_push(v_log_877_, v___x_888_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_890_);
v___x_892_ = v___x_883_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_trace_880_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_buildTime_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_894_, sizeof(void*)*3, v_action_878_);
lean_ctor_set_uint8(v_reuseFailAlloc_894_, sizeof(void*)*3 + 1, v_wantsRebuild_879_);
v___x_892_ = v_reuseFailAlloc_894_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; 
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_889_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
return v___x_893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* v_self_932_, lean_object* v_success_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
uint8_t v_success_boxed_941_; lean_object* v_res_942_; 
v_success_boxed_941_ = lean_unbox(v_success_933_);
v_res_942_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(v_self_932_, v_success_boxed_941_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* v_self_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v___x_951_; 
lean_inc_ref(v_a_944_);
lean_inc_ref(v_self_943_);
v___x_951_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_966_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
v_a_953_ = lean_ctor_get(v___x_951_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_966_ == 0)
{
v___x_955_ = v___x_951_;
v_isShared_956_ = v_isSharedCheck_966_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_inc(v_a_952_);
lean_dec(v___x_951_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_966_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___f_957_; lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v___f_957_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(v___f_957_, 0, v_self_943_);
v___x_958_ = l_Lake_instDataKindUnit;
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = 0;
v___x_961_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_962_ = l_Lake_Job_mapM___redArg(v___x_958_, v_a_952_, v___f_957_, v___x_959_, v___x_960_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v___x_961_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_962_);
v___x_964_ = v___x_955_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_a_953_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_object* v_a_967_; lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec_ref(v_a_944_);
lean_dec_ref(v_self_943_);
v_a_967_ = lean_ctor_get(v___x_951_, 0);
v_a_968_ = lean_ctor_get(v___x_951_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_951_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_inc(v_a_967_);
lean_dec(v___x_951_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_967_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(lean_object* v_self_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec(v_a_979_);
lean_dec(v_a_978_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* v_self_985_, lean_object* v_as_986_, size_t v_sz_987_, size_t v_i_988_, lean_object* v_b_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
uint8_t v___x_997_; 
v___x_997_ = lean_usize_dec_lt(v_i_988_, v_sz_987_);
if (v___x_997_ == 0)
{
lean_object* v___x_998_; 
lean_dec_ref(v___y_990_);
lean_dec_ref(v_self_985_);
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v_b_989_);
lean_ctor_set(v___x_998_, 1, v___y_995_);
return v___x_998_;
}
else
{
lean_object* v_a_999_; lean_object* v___x_1000_; 
v_a_999_ = lean_array_uget_borrowed(v_as_986_, v_i_988_);
lean_inc_ref(v___y_990_);
lean_inc(v_a_999_);
lean_inc_ref(v_self_985_);
v___x_1000_ = l_Lake_Package_fetchTargetJob(v_self_985_, v_a_999_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v_a_1002_; lean_object* v___x_1003_; size_t v___x_1004_; size_t v___x_1005_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
v_a_1002_ = lean_ctor_get(v___x_1000_, 1);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1000_, 2);
v___x_1003_ = l_Lake_Job_mix___redArg(v_b_989_, v_a_1001_);
v___x_1004_ = ((size_t)1ULL);
v___x_1005_ = lean_usize_add(v_i_988_, v___x_1004_);
v_i_988_ = v___x_1005_;
v_b_989_ = v___x_1003_;
v___y_995_ = v_a_1002_;
goto _start;
}
else
{
lean_object* v_a_1007_; lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v___y_990_);
lean_dec_ref(v_b_989_);
lean_dec_ref(v_self_985_);
v_a_1007_ = lean_ctor_get(v___x_1000_, 0);
v_a_1008_ = lean_ctor_get(v___x_1000_, 1);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_1000_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_inc(v_a_1007_);
lean_dec(v___x_1000_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1007_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* v_self_1016_, lean_object* v_as_1017_, lean_object* v_sz_1018_, lean_object* v_i_1019_, lean_object* v_b_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
size_t v_sz_boxed_1028_; size_t v_i_boxed_1029_; lean_object* v_res_1030_; 
v_sz_boxed_1028_ = lean_unbox_usize(v_sz_1018_);
lean_dec(v_sz_1018_);
v_i_boxed_1029_ = lean_unbox_usize(v_i_1019_);
lean_dec(v_i_1019_);
v_res_1030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1016_, v_as_1017_, v_sz_boxed_1028_, v_i_boxed_1029_, v_b_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v_as_1017_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object* v_config_1031_, lean_object* v_self_1032_, lean_object* v_____r_1033_, lean_object* v_job_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_extraDepTargets_1042_; size_t v_sz_1043_; size_t v___x_1044_; lean_object* v___x_1045_; 
v_extraDepTargets_1042_ = lean_ctor_get(v_config_1031_, 2);
v_sz_1043_ = lean_array_size(v_extraDepTargets_1042_);
v___x_1044_ = ((size_t)0ULL);
v___x_1045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1032_, v_extraDepTargets_1042_, v_sz_1043_, v___x_1044_, v_job_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object* v_config_1046_, lean_object* v_self_1047_, lean_object* v_____r_1048_, lean_object* v_job_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(v_config_1046_, v_self_1047_, v_____r_1048_, v_job_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v_config_1046_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(uint8_t v___x_1058_, lean_object* v_self_1059_, lean_object* v_job_1060_, lean_object* v___f_1061_, lean_object* v___x_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
if (v___x_1058_ == 0)
{
lean_object* v___x_1070_; 
lean_inc_ref(v___y_1063_);
v___x_1070_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1059_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v_a_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
v_a_1072_ = lean_ctor_get(v___x_1070_, 1);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1070_, 2);
v___x_1073_ = l_Lake_Job_add___redArg(v_job_1060_, v_a_1071_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1066_);
lean_inc(v___y_1065_);
lean_inc(v___y_1064_);
v___x_1074_ = lean_apply_9(v___f_1061_, v___x_1062_, v___x_1073_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v_a_1072_, lean_box(0));
return v___x_1074_;
}
else
{
lean_dec_ref(v___y_1063_);
lean_dec_ref(v___f_1061_);
lean_dec_ref(v_job_1060_);
return v___x_1070_;
}
}
else
{
lean_object* v___x_1075_; 
lean_dec_ref(v_self_1059_);
lean_inc_ref(v___y_1067_);
lean_inc(v___y_1066_);
lean_inc(v___y_1065_);
lean_inc(v___y_1064_);
v___x_1075_ = lean_apply_9(v___f_1061_, v___x_1062_, v_job_1060_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, lean_box(0));
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* v___x_1076_, lean_object* v_self_1077_, lean_object* v_job_1078_, lean_object* v___f_1079_, lean_object* v___x_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
uint8_t v___x_4162__boxed_1088_; lean_object* v_res_1089_; 
v___x_4162__boxed_1088_ = lean_unbox(v___x_1076_);
v_res_1089_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(v___x_4162__boxed_1088_, v_self_1077_, v_job_1078_, v___f_1079_, v___x_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec(v___y_1082_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object* v_self_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_wsIdx_1100_; lean_object* v_baseName_1101_; lean_object* v_config_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v_job_1122_; uint8_t v___x_1123_; lean_object* v___x_1124_; lean_object* v___y_1125_; lean_object* v___x_1126_; 
v_wsIdx_1100_ = lean_ctor_get(v_self_1092_, 0);
v_baseName_1101_ = lean_ctor_get(v_self_1092_, 1);
v_config_1102_ = lean_ctor_get(v_self_1092_, 6);
lean_inc_ref(v_self_1092_);
lean_inc_ref(v_config_1102_);
v___f_1103_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1103_, 0, v_config_1102_);
lean_closure_set(v___f_1103_, 1, v_self_1092_);
v___x_1104_ = l_Lake_instDataKindUnit;
v___x_1105_ = 1;
lean_inc(v_baseName_1101_);
v___x_1106_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1101_, v___x_1105_);
v___x_1107_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0));
v___x_1108_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1));
v___x_1109_ = lean_string_append(v___x_1108_, v___x_1106_);
v___x_1110_ = lean_string_append(v___x_1109_, v___x_1107_);
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_box(0);
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1115_ = 0;
v___x_1116_ = 0;
v___x_1117_ = l_Lake_BuildTrace_nil(v___x_1110_);
v___x_1118_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1118_, 0, v___x_1114_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
lean_ctor_set(v___x_1118_, 2, v___x_1113_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*3, v___x_1115_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*3 + 1, v___x_1116_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1111_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_task_pure(v___x_1119_);
v___x_1121_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_job_1122_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_1122_, 0, v___x_1120_);
lean_ctor_set(v_job_1122_, 1, v___x_1112_);
lean_ctor_set(v_job_1122_, 2, v___x_1121_);
lean_ctor_set_uint8(v_job_1122_, sizeof(void*)*3, v___x_1116_);
v___x_1123_ = lean_nat_dec_eq(v_wsIdx_1100_, v___x_1113_);
v___x_1124_ = lean_box(v___x_1123_);
v___y_1125_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 12, 5);
lean_closure_set(v___y_1125_, 0, v___x_1124_);
lean_closure_set(v___y_1125_, 1, v_self_1092_);
lean_closure_set(v___y_1125_, 2, v_job_1122_);
lean_closure_set(v___y_1125_, 3, v___f_1103_);
lean_closure_set(v___y_1125_, 4, v___x_1111_);
v___x_1126_ = l_Lake_ensureJob___redArg(v___x_1104_, v___y_1125_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1152_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_a_1128_ = lean_ctor_get(v___x_1126_, 1);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1130_ = v___x_1126_;
v_isShared_1131_ = v_isSharedCheck_1152_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1152_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v_task_1132_; lean_object* v_kind_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1150_; 
v_task_1132_ = lean_ctor_get(v_a_1127_, 0);
v_kind_1133_ = lean_ctor_get(v_a_1127_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_a_1127_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; 
v_unused_1151_ = lean_ctor_get(v_a_1127_, 2);
lean_dec(v_unused_1151_);
v___x_1135_ = v_a_1127_;
v_isShared_1136_ = v_isSharedCheck_1150_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_kind_1133_);
lean_inc(v_task_1132_);
lean_dec(v_a_1127_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1150_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v_registeredJobs_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v_job_1141_; 
v_registeredJobs_1137_ = lean_ctor_get(v_a_1097_, 3);
v___x_1138_ = lean_st_ref_take(v_registeredJobs_1137_);
v___x_1139_ = lean_string_append(v___x_1106_, v___x_1107_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 2, v___x_1139_);
v_job_1141_ = v___x_1135_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_task_1132_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_kind_1133_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v___x_1139_);
v_job_1141_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_ctor_set_uint8(v_job_1141_, sizeof(void*)*3, v___x_1116_);
lean_inc_ref(v_job_1141_);
v___x_1142_ = l_Lake_Job_toOpaque___redArg(v_job_1141_);
v___x_1143_ = lean_array_push(v___x_1138_, v___x_1142_);
v___x_1144_ = lean_st_ref_put(v_registeredJobs_1137_, v___x_1143_);
v___x_1145_ = l_Lake_Job_renew___redArg(v_job_1141_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1145_);
v___x_1147_ = v___x_1130_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_a_1128_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1106_);
return v___x_1126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(lean_object* v_self_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(v_self_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec(v_a_1155_);
return v_res_1161_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_box(0);
v___x_1163_ = l_Lean_Json_compress(v___x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t v_fmt_1164_){
_start:
{
if (v_fmt_1164_ == 0)
{
lean_object* v___x_1165_; 
v___x_1165_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
return v___x_1165_;
}
else
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_1167_){
_start:
{
uint8_t v_fmt_boxed_1168_; lean_object* v_res_1169_; 
v_fmt_boxed_1168_ = lean_unbox(v_fmt_1167_);
v_res_1169_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_boxed_1168_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(uint8_t v_fmt_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_1170_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object* v_fmt_1173_, lean_object* v_a_1174_){
_start:
{
uint8_t v_fmt_boxed_1175_; lean_object* v_res_1176_; 
v_fmt_boxed_1175_ = lean_unbox(v_fmt_1173_);
v_res_1176_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(v_fmt_boxed_1175_, v_a_1174_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v___y_1177_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v___y_67__boxed_1182_; lean_object* v_res_1183_; 
v___y_67__boxed_1182_ = lean_unbox(v___y_1180_);
v_res_1183_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_67__boxed_1182_, v___y_1181_);
return v_res_1183_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___f_1186_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_1187_ = 1;
v___x_1188_ = l_Lake_instDataKindUnit;
v___x_1189_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__1));
v___x_1190_ = l_Lake_Package_keyword;
v___x_1191_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
lean_ctor_set(v___x_1191_, 1, v___x_1189_);
lean_ctor_set(v___x_1191_, 2, v___x_1188_);
lean_ctor_set(v___x_1191_, 3, v___f_1186_);
lean_ctor_set_uint8(v___x_1191_, sizeof(void*)*4, v___x_1187_);
lean_ctor_set_uint8(v___x_1191_, sizeof(void*)*4 + 1, v___x_1187_);
return v___x_1191_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_obj_once(&l_Lake_Package_extraDepFacetConfig___closed__2, &l_Lake_Package_extraDepFacetConfig___closed__2_once, _init_l_Lake_Package_extraDepFacetConfig___closed__2);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object* v_self_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v_origName_1212_; lean_object* v_dir_1213_; lean_object* v_scope_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_origName_1212_ = lean_ctor_get(v_self_1208_, 3);
lean_inc(v_origName_1212_);
v_dir_1213_ = lean_ctor_get(v_self_1208_, 4);
lean_inc_ref(v_dir_1213_);
v_scope_1214_ = lean_ctor_get(v_self_1208_, 10);
lean_inc_ref(v_scope_1214_);
lean_dec_ref(v_self_1208_);
v___x_1215_ = lean_string_utf8_byte_size(v_scope_1214_);
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_nat_dec_eq(v___x_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
v___x_1219_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1218_, v_dir_1213_);
if (lean_obj_tag(v___x_1219_) == 1)
{
lean_object* v_toContext_1220_; lean_object* v_lakeEnv_1221_; lean_object* v_log_1222_; uint8_t v_action_1223_; uint8_t v_wantsRebuild_1224_; lean_object* v_trace_1225_; lean_object* v_buildTime_1226_; lean_object* v_val_1227_; lean_object* v_toolchain_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v_toContext_1220_ = lean_ctor_get(v_a_1209_, 1);
v_lakeEnv_1221_ = lean_ctor_get(v_toContext_1220_, 0);
v_log_1222_ = lean_ctor_get(v_a_1210_, 0);
v_action_1223_ = lean_ctor_get_uint8(v_a_1210_, sizeof(void*)*3);
v_wantsRebuild_1224_ = lean_ctor_get_uint8(v_a_1210_, sizeof(void*)*3 + 1);
v_trace_1225_ = lean_ctor_get(v_a_1210_, 1);
v_buildTime_1226_ = lean_ctor_get(v_a_1210_, 2);
v_val_1227_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v___x_1219_, 1);
v_toolchain_1228_ = lean_ctor_get(v_lakeEnv_1221_, 19);
v___x_1229_ = lean_string_utf8_byte_size(v_toolchain_1228_);
v___x_1230_ = lean_nat_dec_eq(v___x_1229_, v___x_1216_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1231_ = l_Lean_Name_toString(v_origName_1212_, v___x_1217_);
lean_inc_ref(v_lakeEnv_1221_);
v___x_1232_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_1221_, v_scope_1214_, v___x_1231_);
v___x_1233_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1));
v___x_1234_ = lean_string_append(v___x_1232_, v___x_1233_);
v___x_1235_ = lean_string_append(v___x_1234_, v_val_1227_);
lean_dec(v_val_1227_);
v___x_1236_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2));
v___x_1237_ = lean_string_append(v___x_1235_, v___x_1236_);
v___x_1238_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc_ref(v_toolchain_1228_);
v___x_1239_ = l_Lake_uriEncode(v_toolchain_1228_, v___x_1238_);
v___x_1240_ = lean_string_append(v___x_1237_, v___x_1239_);
lean_dec_ref(v___x_1239_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v_a_1210_);
return v___x_1241_;
}
else
{
lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1252_; 
lean_inc(v_buildTime_1226_);
lean_inc_ref(v_trace_1225_);
lean_inc_ref(v_log_1222_);
lean_dec(v_val_1227_);
lean_dec_ref(v_scope_1214_);
lean_dec(v_origName_1212_);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_a_1210_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; lean_object* v_unused_1254_; lean_object* v_unused_1255_; 
v_unused_1253_ = lean_ctor_get(v_a_1210_, 2);
lean_dec(v_unused_1253_);
v_unused_1254_ = lean_ctor_get(v_a_1210_, 1);
lean_dec(v_unused_1254_);
v_unused_1255_ = lean_ctor_get(v_a_1210_, 0);
lean_dec(v_unused_1255_);
v___x_1243_ = v_a_1210_;
v_isShared_1244_ = v_isSharedCheck_1252_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v_a_1210_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1252_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1245_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4));
v___x_1246_ = lean_array_get_size(v_log_1222_);
v___x_1247_ = lean_array_push(v_log_1222_, v___x_1245_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1247_);
v___x_1249_ = v___x_1243_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_trace_1225_);
lean_ctor_set(v_reuseFailAlloc_1251_, 2, v_buildTime_1226_);
lean_ctor_set_uint8(v_reuseFailAlloc_1251_, sizeof(void*)*3, v_action_1223_);
lean_ctor_set_uint8(v_reuseFailAlloc_1251_, sizeof(void*)*3 + 1, v_wantsRebuild_1224_);
v___x_1249_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1246_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
return v___x_1250_;
}
}
}
}
else
{
lean_object* v_log_1256_; uint8_t v_action_1257_; uint8_t v_wantsRebuild_1258_; lean_object* v_trace_1259_; lean_object* v_buildTime_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v___x_1219_);
lean_dec_ref(v_scope_1214_);
lean_dec(v_origName_1212_);
v_log_1256_ = lean_ctor_get(v_a_1210_, 0);
v_action_1257_ = lean_ctor_get_uint8(v_a_1210_, sizeof(void*)*3);
v_wantsRebuild_1258_ = lean_ctor_get_uint8(v_a_1210_, sizeof(void*)*3 + 1);
v_trace_1259_ = lean_ctor_get(v_a_1210_, 1);
v_buildTime_1260_ = lean_ctor_get(v_a_1210_, 2);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_a_1210_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1262_ = v_a_1210_;
v_isShared_1263_ = v_isSharedCheck_1271_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_buildTime_1260_);
lean_inc(v_trace_1259_);
lean_inc(v_log_1256_);
lean_dec(v_a_1210_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1271_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1264_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6));
v___x_1265_ = lean_array_get_size(v_log_1256_);
v___x_1266_ = lean_array_push(v_log_1256_, v___x_1264_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___x_1266_);
v___x_1268_ = v___x_1262_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_trace_1259_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_buildTime_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*3, v_action_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*3 + 1, v_wantsRebuild_1258_);
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
}
else
{
lean_object* v_log_1272_; uint8_t v_action_1273_; uint8_t v_wantsRebuild_1274_; lean_object* v_trace_1275_; lean_object* v_buildTime_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1287_; 
lean_dec_ref(v_scope_1214_);
lean_dec_ref(v_dir_1213_);
lean_dec(v_origName_1212_);
v_log_1272_ = lean_ctor_get(v_a_1210_, 0);
v_action_1273_ = lean_ctor_get_uint8(v_a_1210_, sizeof(void*)*3);
v_wantsRebuild_1274_ = lean_ctor_get_uint8(v_a_1210_, sizeof(void*)*3 + 1);
v_trace_1275_ = lean_ctor_get(v_a_1210_, 1);
v_buildTime_1276_ = lean_ctor_get(v_a_1210_, 2);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_a_1210_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1278_ = v_a_1210_;
v_isShared_1279_ = v_isSharedCheck_1287_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_buildTime_1276_);
lean_inc(v_trace_1275_);
lean_inc(v_log_1272_);
lean_dec(v_a_1210_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1287_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1280_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8));
v___x_1281_ = lean_array_get_size(v_log_1272_);
v___x_1282_ = lean_array_push(v_log_1272_, v___x_1280_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1282_);
v___x_1284_ = v___x_1278_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_trace_1275_);
lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_buildTime_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1286_, sizeof(void*)*3, v_action_1273_);
lean_ctor_set_uint8(v_reuseFailAlloc_1286_, sizeof(void*)*3 + 1, v_wantsRebuild_1274_);
v___x_1284_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1281_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
return v___x_1285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___boxed(lean_object* v_self_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1288_, v_a_1289_, v_a_1290_);
lean_dec_ref(v_a_1289_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object* v_self_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1293_, v_a_1298_, v_a_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object* v_self_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(v_self_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object* v_self_1320_, lean_object* v_a_1321_){
_start:
{
lean_object* v_rev_1324_; lean_object* v_log_1325_; uint8_t v_action_1326_; uint8_t v_wantsRebuild_1327_; lean_object* v_trace_1328_; lean_object* v_buildTime_1329_; lean_object* v_dir_1338_; lean_object* v_config_1339_; lean_object* v_remoteUrl_1340_; lean_object* v_buildArchive_1341_; uint8_t v___y_1343_; lean_object* v___y_1344_; uint8_t v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v_val_1348_; lean_object* v___y_1368_; lean_object* v_releaseRepo_1399_; 
v_dir_1338_ = lean_ctor_get(v_self_1320_, 4);
lean_inc_ref(v_dir_1338_);
v_config_1339_ = lean_ctor_get(v_self_1320_, 6);
lean_inc_ref(v_config_1339_);
v_remoteUrl_1340_ = lean_ctor_get(v_self_1320_, 11);
lean_inc_ref(v_remoteUrl_1340_);
v_buildArchive_1341_ = lean_ctor_get(v_self_1320_, 21);
lean_inc_ref(v_buildArchive_1341_);
lean_dec_ref(v_self_1320_);
v_releaseRepo_1399_ = lean_ctor_get(v_config_1339_, 10);
lean_inc(v_releaseRepo_1399_);
lean_dec_ref(v_config_1339_);
if (lean_obj_tag(v_releaseRepo_1399_) == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v___x_1400_ = lean_string_utf8_byte_size(v_remoteUrl_1340_);
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = lean_nat_dec_eq(v___x_1400_, v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1403_, 0, v_remoteUrl_1340_);
v___y_1368_ = v___x_1403_;
goto v___jp_1367_;
}
else
{
lean_dec_ref(v_remoteUrl_1340_);
v___y_1368_ = v_releaseRepo_1399_;
goto v___jp_1367_;
}
}
else
{
lean_dec_ref(v_remoteUrl_1340_);
v___y_1368_ = v_releaseRepo_1399_;
goto v___jp_1367_;
}
v___jp_1323_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1330_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0));
v___x_1331_ = lean_string_append(v___x_1330_, v_rev_1324_);
lean_dec_ref(v_rev_1324_);
v___x_1332_ = 3;
v___x_1333_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set_uint8(v___x_1333_, sizeof(void*)*1, v___x_1332_);
v___x_1334_ = lean_array_get_size(v_log_1325_);
v___x_1335_ = lean_array_push(v_log_1325_, v___x_1333_);
v___x_1336_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
lean_ctor_set(v___x_1336_, 1, v_trace_1328_);
lean_ctor_set(v___x_1336_, 2, v_buildTime_1329_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*3, v_action_1326_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*3 + 1, v_wantsRebuild_1327_);
v___x_1337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1334_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
return v___x_1337_;
}
v___jp_1342_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
lean_inc_ref(v_dir_1338_);
v___x_1350_ = l_Lake_GitRepo_findTag_x3f(v___x_1349_, v_dir_1338_);
if (lean_obj_tag(v___x_1350_) == 1)
{
lean_object* v_val_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_dec_ref(v_dir_1338_);
v_val_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_val_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v___x_1352_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1352_, 0, v___y_1346_);
lean_ctor_set(v___x_1352_, 1, v___y_1344_);
lean_ctor_set(v___x_1352_, 2, v___y_1347_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*3, v___y_1345_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*3 + 1, v___y_1343_);
v___x_1353_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1));
v___x_1354_ = lean_string_append(v_val_1348_, v___x_1353_);
v___x_1355_ = lean_string_append(v___x_1354_, v_val_1351_);
lean_dec(v_val_1351_);
v___x_1356_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2));
v___x_1357_ = lean_string_append(v___x_1355_, v___x_1356_);
v___x_1358_ = lean_string_append(v___x_1357_, v_buildArchive_1341_);
lean_dec_ref(v_buildArchive_1341_);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v___x_1352_);
return v___x_1359_;
}
else
{
lean_object* v___x_1360_; 
lean_dec(v___x_1350_);
lean_dec_ref(v_val_1348_);
lean_dec_ref(v_buildArchive_1341_);
v___x_1360_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1349_, v_dir_1338_);
if (lean_obj_tag(v___x_1360_) == 1)
{
lean_object* v_val_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_val_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_val_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v___x_1362_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3));
v___x_1363_ = lean_string_append(v___x_1362_, v_val_1361_);
lean_dec(v_val_1361_);
v___x_1364_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4));
v___x_1365_ = lean_string_append(v___x_1363_, v___x_1364_);
v_rev_1324_ = v___x_1365_;
v_log_1325_ = v___y_1346_;
v_action_1326_ = v___y_1345_;
v_wantsRebuild_1327_ = v___y_1343_;
v_trace_1328_ = v___y_1344_;
v_buildTime_1329_ = v___y_1347_;
goto v___jp_1323_;
}
else
{
lean_object* v___x_1366_; 
lean_dec(v___x_1360_);
v___x_1366_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_rev_1324_ = v___x_1366_;
v_log_1325_ = v___y_1346_;
v_action_1326_ = v___y_1345_;
v_wantsRebuild_1327_ = v___y_1343_;
v_trace_1328_ = v___y_1344_;
v_buildTime_1329_ = v___y_1347_;
goto v___jp_1323_;
}
}
}
v___jp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_dir_1338_);
v___x_1370_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v___x_1369_, v_dir_1338_);
if (lean_obj_tag(v___y_1368_) == 0)
{
if (lean_obj_tag(v___x_1370_) == 1)
{
lean_object* v_log_1371_; uint8_t v_action_1372_; uint8_t v_wantsRebuild_1373_; lean_object* v_trace_1374_; lean_object* v_buildTime_1375_; lean_object* v_val_1376_; 
v_log_1371_ = lean_ctor_get(v_a_1321_, 0);
lean_inc_ref(v_log_1371_);
v_action_1372_ = lean_ctor_get_uint8(v_a_1321_, sizeof(void*)*3);
v_wantsRebuild_1373_ = lean_ctor_get_uint8(v_a_1321_, sizeof(void*)*3 + 1);
v_trace_1374_ = lean_ctor_get(v_a_1321_, 1);
lean_inc_ref(v_trace_1374_);
v_buildTime_1375_ = lean_ctor_get(v_a_1321_, 2);
lean_inc(v_buildTime_1375_);
lean_dec_ref(v_a_1321_);
v_val_1376_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_val_1376_);
lean_dec_ref_known(v___x_1370_, 1);
v___y_1343_ = v_wantsRebuild_1373_;
v___y_1344_ = v_trace_1374_;
v___y_1345_ = v_action_1372_;
v___y_1346_ = v_log_1371_;
v___y_1347_ = v_buildTime_1375_;
v_val_1348_ = v_val_1376_;
goto v___jp_1342_;
}
else
{
lean_object* v_log_1377_; uint8_t v_action_1378_; uint8_t v_wantsRebuild_1379_; lean_object* v_trace_1380_; lean_object* v_buildTime_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1392_; 
lean_dec(v___x_1370_);
lean_dec_ref(v_buildArchive_1341_);
lean_dec_ref(v_dir_1338_);
v_log_1377_ = lean_ctor_get(v_a_1321_, 0);
v_action_1378_ = lean_ctor_get_uint8(v_a_1321_, sizeof(void*)*3);
v_wantsRebuild_1379_ = lean_ctor_get_uint8(v_a_1321_, sizeof(void*)*3 + 1);
v_trace_1380_ = lean_ctor_get(v_a_1321_, 1);
v_buildTime_1381_ = lean_ctor_get(v_a_1321_, 2);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_a_1321_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1383_ = v_a_1321_;
v_isShared_1384_ = v_isSharedCheck_1392_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_buildTime_1381_);
lean_inc(v_trace_1380_);
lean_inc(v_log_1377_);
lean_dec(v_a_1321_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1392_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1385_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6));
v___x_1386_ = lean_array_get_size(v_log_1377_);
v___x_1387_ = lean_array_push(v_log_1377_, v___x_1385_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1387_);
v___x_1389_ = v___x_1383_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_trace_1380_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_buildTime_1381_);
lean_ctor_set_uint8(v_reuseFailAlloc_1391_, sizeof(void*)*3, v_action_1378_);
lean_ctor_set_uint8(v_reuseFailAlloc_1391_, sizeof(void*)*3 + 1, v_wantsRebuild_1379_);
v___x_1389_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1386_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
return v___x_1390_;
}
}
}
}
else
{
lean_object* v_log_1393_; uint8_t v_action_1394_; uint8_t v_wantsRebuild_1395_; lean_object* v_trace_1396_; lean_object* v_buildTime_1397_; lean_object* v_val_1398_; 
lean_dec(v___x_1370_);
v_log_1393_ = lean_ctor_get(v_a_1321_, 0);
lean_inc_ref(v_log_1393_);
v_action_1394_ = lean_ctor_get_uint8(v_a_1321_, sizeof(void*)*3);
v_wantsRebuild_1395_ = lean_ctor_get_uint8(v_a_1321_, sizeof(void*)*3 + 1);
v_trace_1396_ = lean_ctor_get(v_a_1321_, 1);
lean_inc_ref(v_trace_1396_);
v_buildTime_1397_ = lean_ctor_get(v_a_1321_, 2);
lean_inc(v_buildTime_1397_);
lean_dec_ref(v_a_1321_);
v_val_1398_ = lean_ctor_get(v___y_1368_, 0);
lean_inc(v_val_1398_);
lean_dec_ref_known(v___y_1368_, 1);
v___y_1343_ = v_wantsRebuild_1395_;
v___y_1344_ = v_trace_1396_;
v___y_1345_ = v_action_1394_;
v___y_1346_ = v_log_1393_;
v___y_1347_ = v_buildTime_1397_;
v_val_1348_ = v_val_1398_;
goto v___jp_1342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(lean_object* v_self_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1404_, v_a_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object* v_self_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1408_, v_a_1414_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object* v_self_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(v_self_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(lean_object* v_val_1426_, lean_object* v_a_x3f_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v___x_1430_; lean_object* v_log_1431_; uint8_t v_action_1432_; uint8_t v_wantsRebuild_1433_; lean_object* v_trace_1434_; lean_object* v_buildTime_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1446_; 
v___x_1430_ = lean_io_mono_ms_now();
v_log_1431_ = lean_ctor_get(v___y_1428_, 0);
v_action_1432_ = lean_ctor_get_uint8(v___y_1428_, sizeof(void*)*3);
v_wantsRebuild_1433_ = lean_ctor_get_uint8(v___y_1428_, sizeof(void*)*3 + 1);
v_trace_1434_ = lean_ctor_get(v___y_1428_, 1);
v_buildTime_1435_ = lean_ctor_get(v___y_1428_, 2);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___y_1428_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1437_ = v___y_1428_;
v_isShared_1438_ = v_isSharedCheck_1446_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_buildTime_1435_);
lean_inc(v_trace_1434_);
lean_inc(v_log_1431_);
lean_dec(v___y_1428_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1446_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1439_ = lean_nat_sub(v___x_1430_, v_val_1426_);
lean_dec(v___x_1430_);
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_nat_add(v_buildTime_1435_, v___x_1439_);
lean_dec(v___x_1439_);
lean_dec(v_buildTime_1435_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 2, v___x_1441_);
v___x_1443_ = v___x_1437_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_log_1431_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_trace_1434_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v___x_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1445_, sizeof(void*)*3, v_action_1432_);
lean_ctor_set_uint8(v_reuseFailAlloc_1445_, sizeof(void*)*3 + 1, v_wantsRebuild_1433_);
v___x_1443_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1440_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
return v___x_1444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0___boxed(lean_object* v_val_1447_, lean_object* v_a_x3f_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v_val_1447_, v_a_x3f_1448_, v___y_1449_);
lean_dec(v_a_x3f_1448_);
lean_dec(v_val_1447_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(lean_object* v_url_1457_, lean_object* v_archiveFile_1458_, lean_object* v_headers_1459_, lean_object* v_depTrace_1460_, lean_object* v_traceFile_1461_, uint8_t v_action_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_a_1467_; lean_object* v_a_1468_; lean_object* v_log_1471_; uint8_t v_action_1472_; uint8_t v_wantsRebuild_1473_; lean_object* v_trace_1474_; lean_object* v_buildTime_1475_; lean_object* v_toBuildConfig_1481_; lean_object* v_log_1482_; uint8_t v_action_1483_; uint8_t v_wantsRebuild_1484_; lean_object* v_trace_1485_; lean_object* v_buildTime_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1576_; 
v_toBuildConfig_1481_ = lean_ctor_get(v_a_1463_, 0);
v_log_1482_ = lean_ctor_get(v_a_1464_, 0);
v_action_1483_ = lean_ctor_get_uint8(v_a_1464_, sizeof(void*)*3);
v_wantsRebuild_1484_ = lean_ctor_get_uint8(v_a_1464_, sizeof(void*)*3 + 1);
v_trace_1485_ = lean_ctor_get(v_a_1464_, 1);
v_buildTime_1486_ = lean_ctor_get(v_a_1464_, 2);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_a_1464_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1488_ = v_a_1464_;
v_isShared_1489_ = v_isSharedCheck_1576_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_buildTime_1486_);
lean_inc(v_trace_1485_);
lean_inc(v_log_1482_);
lean_dec(v_a_1464_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1576_;
goto v_resetjp_1487_;
}
v___jp_1466_:
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1469_, 0, v_a_1467_);
lean_ctor_set(v___x_1469_, 1, v_a_1468_);
return v___x_1469_;
}
v___jp_1470_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1476_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1));
v___x_1477_ = lean_array_get_size(v_log_1471_);
v___x_1478_ = lean_array_push(v_log_1471_, v___x_1476_);
v___x_1479_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v_trace_1474_);
lean_ctor_set(v___x_1479_, 2, v_buildTime_1475_);
lean_ctor_set_uint8(v___x_1479_, sizeof(void*)*3, v_action_1472_);
lean_ctor_set_uint8(v___x_1479_, sizeof(void*)*3 + 1, v_wantsRebuild_1473_);
v___x_1480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1477_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
return v___x_1480_;
}
v_resetjp_1487_:
{
uint8_t v_noBuild_1490_; uint8_t v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v_noBuild_1490_ = lean_ctor_get_uint8(v_toBuildConfig_1481_, sizeof(void*)*4 + 2);
v___x_1491_ = l_Lake_JobAction_merge(v_action_1483_, v_action_1462_);
v___x_1492_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2));
lean_inc_ref(v_traceFile_1461_);
v___x_1493_ = l_System_FilePath_addExtension(v_traceFile_1461_, v___x_1492_);
if (v_noBuild_1490_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v_a_1497_; lean_object* v_a_1498_; 
v___x_1494_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1482_);
v___x_1495_ = l_Lake_download(v_url_1457_, v_archiveFile_1458_, v_headers_1459_, v_log_1482_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1502_; lean_object* v_a_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_a_1502_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1502_);
v_a_1503_ = lean_ctor_get(v___x_1495_, 1);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1495_, 2);
v___x_1504_ = lean_array_get_size(v_log_1482_);
lean_dec_ref(v_log_1482_);
v___x_1505_ = lean_array_get_size(v_a_1503_);
v___x_1506_ = l_Array_extract___redArg(v_a_1503_, v___x_1504_, v___x_1505_);
v___x_1507_ = lean_box(0);
v___x_1508_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1460_, v___x_1507_, v___x_1506_);
v___x_1509_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1461_, v___x_1508_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1546_; 
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v___x_1509_, 0);
lean_dec(v_unused_1547_);
v___x_1511_ = v___x_1509_;
v_isShared_1512_ = v_isSharedCheck_1546_;
goto v_resetjp_1510_;
}
else
{
lean_dec(v___x_1509_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1546_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lake_removeFileIfExists(v___x_1493_);
lean_dec_ref(v___x_1493_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1536_; 
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v___x_1513_, 0);
lean_dec(v_unused_1537_);
v___x_1515_ = v___x_1513_;
v_isShared_1516_ = v_isSharedCheck_1536_;
goto v_resetjp_1514_;
}
else
{
lean_dec(v___x_1513_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1536_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v_a_1503_);
v___x_1518_ = v___x_1488_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1503_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_trace_1485_);
lean_ctor_set(v_reuseFailAlloc_1535_, 2, v_buildTime_1486_);
lean_ctor_set_uint8(v_reuseFailAlloc_1535_, sizeof(void*)*3 + 1, v_wantsRebuild_1484_);
v___x_1518_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1520_; 
lean_ctor_set_uint8(v___x_1518_, sizeof(void*)*3, v___x_1491_);
lean_inc(v_a_1502_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v_a_1502_);
v___x_1520_ = v___x_1515_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_a_1502_);
v___x_1520_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set_tag(v___x_1511_, 1);
lean_ctor_set(v___x_1511_, 0, v___x_1520_);
v___x_1522_ = v___x_1511_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
v___x_1523_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1494_, v___x_1522_, v___x_1518_);
lean_dec_ref(v___x_1522_);
lean_dec(v___x_1494_);
v_a_1524_ = lean_ctor_get(v___x_1523_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; 
v_unused_1532_ = lean_ctor_get(v___x_1523_, 0);
lean_dec(v_unused_1532_);
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v_a_1502_);
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1502_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
lean_del_object(v___x_1511_);
lean_dec(v_a_1502_);
v_a_1538_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1539_ = lean_io_error_to_string(v_a_1538_);
v___x_1540_ = 3;
v___x_1541_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set_uint8(v___x_1541_, sizeof(void*)*1, v___x_1540_);
v___x_1542_ = lean_array_push(v_a_1503_, v___x_1541_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1542_);
v___x_1544_ = v___x_1488_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_trace_1485_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_buildTime_1486_);
lean_ctor_set_uint8(v_reuseFailAlloc_1545_, sizeof(void*)*3 + 1, v_wantsRebuild_1484_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_ctor_set_uint8(v___x_1544_, sizeof(void*)*3, v___x_1491_);
v_a_1497_ = v___x_1505_;
v_a_1498_ = v___x_1544_;
goto v___jp_1496_;
}
}
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
lean_dec(v_a_1502_);
lean_dec_ref(v___x_1493_);
v_a_1548_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1509_, 1);
v___x_1549_ = lean_io_error_to_string(v_a_1548_);
v___x_1550_ = 3;
v___x_1551_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set_uint8(v___x_1551_, sizeof(void*)*1, v___x_1550_);
v___x_1552_ = lean_array_push(v_a_1503_, v___x_1551_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1552_);
v___x_1554_ = v___x_1488_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_trace_1485_);
lean_ctor_set(v_reuseFailAlloc_1555_, 2, v_buildTime_1486_);
lean_ctor_set_uint8(v_reuseFailAlloc_1555_, sizeof(void*)*3 + 1, v_wantsRebuild_1484_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_ctor_set_uint8(v___x_1554_, sizeof(void*)*3, v___x_1491_);
v_a_1497_ = v___x_1505_;
v_a_1498_ = v___x_1554_;
goto v___jp_1496_;
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v_a_1557_; lean_object* v___x_1559_; 
lean_dec_ref(v___x_1493_);
lean_dec_ref(v_log_1482_);
lean_dec_ref(v_traceFile_1461_);
v_a_1556_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_a_1556_);
v_a_1557_ = lean_ctor_get(v___x_1495_, 1);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1495_, 2);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v_a_1557_);
v___x_1559_ = v___x_1488_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1557_);
lean_ctor_set(v_reuseFailAlloc_1560_, 1, v_trace_1485_);
lean_ctor_set(v_reuseFailAlloc_1560_, 2, v_buildTime_1486_);
lean_ctor_set_uint8(v_reuseFailAlloc_1560_, sizeof(void*)*3 + 1, v_wantsRebuild_1484_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_ctor_set_uint8(v___x_1559_, sizeof(void*)*3, v___x_1491_);
v_a_1497_ = v_a_1556_;
v_a_1498_ = v___x_1559_;
goto v___jp_1496_;
}
}
v___jp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v_a_1501_; 
v___x_1499_ = lean_box(0);
v___x_1500_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1494_, v___x_1499_, v_a_1498_);
lean_dec(v___x_1494_);
v_a_1501_ = lean_ctor_get(v___x_1500_, 1);
lean_inc(v_a_1501_);
lean_dec_ref(v___x_1500_);
v_a_1467_ = v_a_1497_;
v_a_1468_ = v_a_1501_;
goto v___jp_1466_;
}
}
else
{
uint8_t v___x_1561_; 
lean_dec_ref(v_archiveFile_1458_);
lean_dec_ref(v_url_1457_);
v___x_1561_ = l_System_FilePath_pathExists(v_traceFile_1461_);
lean_dec_ref(v_traceFile_1461_);
if (v___x_1561_ == 0)
{
lean_dec_ref(v___x_1493_);
lean_del_object(v___x_1488_);
v_log_1471_ = v_log_1482_;
v_action_1472_ = v___x_1491_;
v_wantsRebuild_1473_ = v_noBuild_1490_;
v_trace_1474_ = v_trace_1485_;
v_buildTime_1475_ = v_buildTime_1486_;
goto v___jp_1470_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1562_ = lean_box(0);
v___x_1563_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1564_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1460_, v___x_1562_, v___x_1563_);
v___x_1565_ = l_Lake_BuildMetadata_writeFile(v___x_1493_, v___x_1564_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_dec_ref_known(v___x_1565_, 1);
lean_del_object(v___x_1488_);
v_log_1471_ = v_log_1482_;
v_action_1472_ = v___x_1491_;
v_wantsRebuild_1473_ = v_noBuild_1490_;
v_trace_1474_ = v_trace_1485_;
v_buildTime_1475_ = v_buildTime_1486_;
goto v___jp_1470_;
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1567_ = lean_io_error_to_string(v_a_1566_);
v___x_1568_ = 3;
v___x_1569_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1569_, 0, v___x_1567_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*1, v___x_1568_);
v___x_1570_ = lean_array_get_size(v_log_1482_);
v___x_1571_ = lean_array_push(v_log_1482_, v___x_1569_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1571_);
v___x_1573_ = v___x_1488_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_trace_1485_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_buildTime_1486_);
v___x_1573_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; 
lean_ctor_set_uint8(v___x_1573_, sizeof(void*)*3, v___x_1491_);
lean_ctor_set_uint8(v___x_1573_, sizeof(void*)*3 + 1, v_noBuild_1490_);
v___x_1574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1570_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
return v___x_1574_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___boxed(lean_object* v_url_1577_, lean_object* v_archiveFile_1578_, lean_object* v_headers_1579_, lean_object* v_depTrace_1580_, lean_object* v_traceFile_1581_, lean_object* v_action_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
uint8_t v_action_boxed_1586_; lean_object* v_res_1587_; 
v_action_boxed_1586_ = lean_unbox(v_action_1582_);
v_res_1587_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1577_, v_archiveFile_1578_, v_headers_1579_, v_depTrace_1580_, v_traceFile_1581_, v_action_boxed_1586_, v_a_1583_, v_a_1584_);
lean_dec_ref(v_a_1583_);
lean_dec_ref(v_depTrace_1580_);
lean_dec_ref(v_headers_1579_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(lean_object* v_url_1588_, lean_object* v_archiveFile_1589_, lean_object* v_headers_1590_, lean_object* v_a_1591_, lean_object* v_depTrace_1592_, lean_object* v_traceFile_1593_, uint8_t v_action_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1588_, v_archiveFile_1589_, v_headers_1590_, v_depTrace_1592_, v_traceFile_1593_, v_action_1594_, v_a_1598_, v_a_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___boxed(lean_object* v_url_1602_, lean_object* v_archiveFile_1603_, lean_object* v_headers_1604_, lean_object* v_a_1605_, lean_object* v_depTrace_1606_, lean_object* v_traceFile_1607_, lean_object* v_action_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
uint8_t v_action_boxed_1615_; lean_object* v_res_1616_; 
v_action_boxed_1615_ = lean_unbox(v_action_1608_);
v_res_1616_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(v_url_1602_, v_archiveFile_1603_, v_headers_1604_, v_a_1605_, v_depTrace_1606_, v_traceFile_1607_, v_action_boxed_1615_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
lean_dec_ref(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec_ref(v_depTrace_1606_);
lean_dec_ref(v_a_1605_);
lean_dec_ref(v_headers_1604_);
return v_res_1616_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(lean_object* v_x_1617_, lean_object* v_x_1618_){
_start:
{
if (lean_obj_tag(v_x_1617_) == 0)
{
if (lean_obj_tag(v_x_1618_) == 0)
{
uint8_t v___x_1619_; 
v___x_1619_ = 1;
return v___x_1619_;
}
else
{
uint8_t v___x_1620_; 
v___x_1620_ = 0;
return v___x_1620_;
}
}
else
{
if (lean_obj_tag(v_x_1618_) == 0)
{
uint8_t v___x_1621_; 
v___x_1621_ = 0;
return v___x_1621_;
}
else
{
lean_object* v_val_1622_; lean_object* v_val_1623_; uint64_t v___x_1624_; uint64_t v___x_1625_; uint8_t v___x_1626_; 
v_val_1622_ = lean_ctor_get(v_x_1617_, 0);
v_val_1623_ = lean_ctor_get(v_x_1618_, 0);
v___x_1624_ = lean_unbox_uint64(v_val_1622_);
v___x_1625_ = lean_unbox_uint64(v_val_1623_);
v___x_1626_ = lean_uint64_dec_eq(v___x_1624_, v___x_1625_);
return v___x_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(lean_object* v_x_1627_, lean_object* v_x_1628_){
_start:
{
uint8_t v_res_1629_; lean_object* v_r_1630_; 
v_res_1629_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v_x_1627_, v_x_1628_);
lean_dec(v_x_1628_);
lean_dec(v_x_1627_);
v_r_1630_ = lean_box(v_res_1629_);
return v_r_1630_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object* v_info_1631_, lean_object* v_self_1632_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_io_metadata(v_info_1631_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v_modified_1636_; uint8_t v___x_1637_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v_modified_1636_ = lean_ctor_get(v_a_1635_, 1);
lean_inc_ref(v_modified_1636_);
lean_dec(v_a_1635_);
v___x_1637_ = l_IO_FS_instOrdSystemTime_ord(v_self_1632_, v_modified_1636_);
lean_dec_ref(v_modified_1636_);
if (v___x_1637_ == 0)
{
uint8_t v___x_1638_; 
v___x_1638_ = 1;
return v___x_1638_;
}
else
{
uint8_t v___x_1639_; 
v___x_1639_ = 0;
return v___x_1639_;
}
}
else
{
uint8_t v___x_1640_; 
lean_dec_ref_known(v___x_1634_, 1);
v___x_1640_ = 0;
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object* v_info_1641_, lean_object* v_self_1642_, lean_object* v_a_1643_){
_start:
{
uint8_t v_res_1644_; lean_object* v_r_1645_; 
v_res_1644_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1641_, v_self_1642_);
lean_dec_ref(v_self_1642_);
lean_dec_ref(v_info_1641_);
v_r_1645_ = lean_box(v_res_1644_);
return v_r_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(lean_object* v_info_1646_, lean_object* v_depTrace_1647_, lean_object* v_depHash_1648_, lean_object* v_oldTrace_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_){
_start:
{
uint64_t v_hash_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v_hash_1653_ = lean_ctor_get_uint64(v_depTrace_1647_, sizeof(void*)*3);
v___x_1654_ = lean_box_uint64(v_hash_1653_);
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
v___x_1656_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v___x_1655_, v_depHash_1648_);
lean_dec_ref_known(v___x_1655_, 1);
if (v___x_1656_ == 0)
{
lean_object* v_toBuildConfig_1657_; uint8_t v_oldMode_1658_; 
v_toBuildConfig_1657_ = lean_ctor_get(v_a_1650_, 0);
v_oldMode_1658_ = lean_ctor_get_uint8(v_toBuildConfig_1657_, sizeof(void*)*4);
if (v_oldMode_1658_ == 0)
{
uint8_t v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = 0;
v___x_1660_ = lean_box(v___x_1659_);
v___x_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v_a_1651_);
return v___x_1661_;
}
else
{
uint8_t v___x_1662_; 
v___x_1662_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1646_, v_oldTrace_1649_);
if (v___x_1662_ == 0)
{
uint8_t v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = 0;
v___x_1664_ = lean_box(v___x_1663_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v_a_1651_);
return v___x_1665_;
}
else
{
uint8_t v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = 1;
v___x_1667_ = lean_box(v___x_1666_);
v___x_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v_a_1651_);
return v___x_1668_;
}
}
}
else
{
uint8_t v___x_1669_; 
v___x_1669_ = l_System_FilePath_pathExists(v_info_1646_);
if (v___x_1669_ == 0)
{
uint8_t v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = 0;
v___x_1671_ = lean_box(v___x_1670_);
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v_a_1651_);
return v___x_1672_;
}
else
{
uint8_t v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1673_ = 2;
v___x_1674_ = lean_box(v___x_1673_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v_a_1651_);
return v___x_1675_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(lean_object* v_info_1676_, lean_object* v_depTrace_1677_, lean_object* v_depHash_1678_, lean_object* v_oldTrace_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1676_, v_depTrace_1677_, v_depHash_1678_, v_oldTrace_1679_, v_a_1680_, v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec_ref(v_oldTrace_1679_);
lean_dec(v_depHash_1678_);
lean_dec_ref(v_depTrace_1677_);
lean_dec_ref(v_info_1676_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(lean_object* v_a_1684_, lean_object* v_info_1685_, lean_object* v_depTrace_1686_, lean_object* v_savedTrace_1687_, lean_object* v_oldTrace_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
if (lean_obj_tag(v_savedTrace_1687_) == 2)
{
lean_object* v_data_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1745_; 
v_data_1695_ = lean_ctor_get(v_savedTrace_1687_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_savedTrace_1687_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1697_ = v_savedTrace_1687_;
v_isShared_1698_ = v_isSharedCheck_1745_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_data_1695_);
lean_dec(v_savedTrace_1687_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1745_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
uint64_t v_depHash_1699_; lean_object* v_log_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
v_depHash_1699_ = lean_ctor_get_uint64(v_data_1695_, sizeof(void*)*3);
v_log_1700_ = lean_ctor_get(v_data_1695_, 2);
lean_inc_ref(v_log_1700_);
lean_dec_ref(v_data_1695_);
v___x_1701_ = lean_box_uint64(v_depHash_1699_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set_tag(v___x_1697_, 1);
lean_ctor_set(v___x_1697_, 0, v___x_1701_);
v___x_1703_ = v___x_1697_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; lean_object* v_a_1705_; lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1743_; 
v___x_1704_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1685_, v_depTrace_1686_, v___x_1703_, v_oldTrace_1688_, v_a_1692_, v_a_1693_);
lean_dec_ref(v___x_1703_);
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_a_1706_ = lean_ctor_get(v___x_1704_, 1);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1708_ = v___x_1704_;
v_isShared_1709_ = v_isSharedCheck_1743_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1743_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___y_1711_; uint8_t v___x_1715_; uint8_t v___x_1716_; uint8_t v___x_1717_; 
v___x_1715_ = 0;
v___x_1716_ = lean_unbox(v_a_1705_);
v___x_1717_ = l_Lake_instDecidableEqOutputStatus(v___x_1716_, v___x_1715_);
if (v___x_1717_ == 0)
{
lean_object* v_log_1718_; uint8_t v_action_1719_; uint8_t v_wantsRebuild_1720_; lean_object* v_trace_1721_; lean_object* v_buildTime_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1742_; 
v_log_1718_ = lean_ctor_get(v_a_1706_, 0);
v_action_1719_ = lean_ctor_get_uint8(v_a_1706_, sizeof(void*)*3);
v_wantsRebuild_1720_ = lean_ctor_get_uint8(v_a_1706_, sizeof(void*)*3 + 1);
v_trace_1721_ = lean_ctor_get(v_a_1706_, 1);
v_buildTime_1722_ = lean_ctor_get(v_a_1706_, 2);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_a_1706_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1724_ = v_a_1706_;
v_isShared_1725_ = v_isSharedCheck_1742_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_buildTime_1722_);
lean_inc(v_trace_1721_);
lean_inc(v_log_1718_);
lean_dec(v_a_1706_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1742_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
uint8_t v___x_1726_; uint8_t v___x_1727_; lean_object* v___x_1729_; 
v___x_1726_ = 2;
v___x_1727_ = l_Lake_JobAction_merge(v_action_1719_, v___x_1726_);
if (v_isShared_1725_ == 0)
{
v___x_1729_ = v___x_1724_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_log_1718_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_trace_1721_);
lean_ctor_set(v_reuseFailAlloc_1741_, 2, v_buildTime_1722_);
lean_ctor_set_uint8(v_reuseFailAlloc_1741_, sizeof(void*)*3 + 1, v_wantsRebuild_1720_);
v___x_1729_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; 
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3, v___x_1727_);
v___x_1730_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1700_, v_a_1684_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v___x_1729_);
lean_dec_ref(v_log_1700_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 1);
lean_inc(v_a_1731_);
lean_dec_ref_known(v___x_1730_, 2);
v___y_1711_ = v_a_1731_;
goto v___jp_1710_;
}
else
{
lean_object* v_a_1732_; lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_del_object(v___x_1708_);
lean_dec(v_a_1705_);
v_a_1732_ = lean_ctor_get(v___x_1730_, 0);
v_a_1733_ = lean_ctor_get(v___x_1730_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1730_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_inc(v_a_1732_);
lean_dec(v___x_1730_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1732_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_1700_);
v___y_1711_ = v_a_1706_;
goto v___jp_1710_;
}
v___jp_1710_:
{
lean_object* v___x_1713_; 
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 1, v___y_1711_);
v___x_1713_ = v___x_1708_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1705_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v___y_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_1746_; uint8_t v_oldMode_1747_; 
lean_dec(v_savedTrace_1687_);
v_toBuildConfig_1746_ = lean_ctor_get(v_a_1692_, 0);
v_oldMode_1747_ = lean_ctor_get_uint8(v_toBuildConfig_1746_, sizeof(void*)*4);
if (v_oldMode_1747_ == 0)
{
uint8_t v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1748_ = 0;
v___x_1749_ = lean_box(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v_a_1693_);
return v___x_1750_;
}
else
{
uint8_t v___x_1751_; 
v___x_1751_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1685_, v_oldTrace_1688_);
if (v___x_1751_ == 0)
{
uint8_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = 0;
v___x_1753_ = lean_box(v___x_1752_);
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set(v___x_1754_, 1, v_a_1693_);
return v___x_1754_;
}
else
{
uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1755_ = 1;
v___x_1756_ = lean_box(v___x_1755_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v_a_1693_);
return v___x_1757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object* v_a_1758_, lean_object* v_info_1759_, lean_object* v_depTrace_1760_, lean_object* v_savedTrace_1761_, lean_object* v_oldTrace_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_1758_, v_info_1759_, v_depTrace_1760_, v_savedTrace_1761_, v_oldTrace_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec(v_a_1763_);
lean_dec_ref(v_oldTrace_1762_);
lean_dec_ref(v_depTrace_1760_);
lean_dec_ref(v_info_1759_);
lean_dec_ref(v_a_1758_);
return v_res_1769_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_unsigned_to_nat(0u);
v___x_1775_ = lean_nat_to_int(v___x_1774_);
return v___x_1775_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4(void){
_start:
{
uint32_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = 0;
v___x_1777_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3);
v___x_1778_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
lean_ctor_set_uint32(v___x_1778_, sizeof(void*)*1, v___x_1776_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(lean_object* v_self_1779_, lean_object* v_url_1780_, lean_object* v_archiveFile_1781_, lean_object* v_headers_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_a_1791_; lean_object* v_a_1792_; lean_object* v___y_1795_; uint8_t v___y_1796_; lean_object* v___y_1797_; uint8_t v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; uint8_t v_a_1826_; lean_object* v_a_1827_; lean_object* v_log_1846_; uint8_t v_action_1847_; uint8_t v_wantsRebuild_1848_; lean_object* v_trace_1849_; lean_object* v_buildTime_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1889_; 
v_log_1846_ = lean_ctor_get(v_a_1788_, 0);
v_action_1847_ = lean_ctor_get_uint8(v_a_1788_, sizeof(void*)*3);
v_wantsRebuild_1848_ = lean_ctor_get_uint8(v_a_1788_, sizeof(void*)*3 + 1);
v_trace_1849_ = lean_ctor_get(v_a_1788_, 1);
v_buildTime_1850_ = lean_ctor_get(v_a_1788_, 2);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_a_1788_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1852_ = v_a_1788_;
v_isShared_1853_ = v_isSharedCheck_1889_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_buildTime_1850_);
lean_inc(v_trace_1849_);
lean_inc(v_log_1846_);
lean_dec(v_a_1788_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1889_;
goto v_resetjp_1851_;
}
v___jp_1790_:
{
lean_object* v___x_1793_; 
v___x_1793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1793_, 0, v_a_1791_);
lean_ctor_set(v___x_1793_, 1, v_a_1792_);
return v___x_1793_;
}
v___jp_1794_:
{
uint8_t v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; uint8_t v___x_1804_; 
v___x_1801_ = 1;
v___x_1802_ = l_Lake_untar(v_archiveFile_1781_, v___y_1795_, v___x_1801_, v___y_1799_);
v___x_1803_ = 3;
v___x_1804_ = l_Lake_JobAction_merge(v___y_1796_, v___x_1803_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1805_; lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1814_; 
v_a_1805_ = lean_ctor_get(v___x_1802_, 0);
v_a_1806_ = lean_ctor_get(v___x_1802_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1808_ = v___x_1802_;
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_inc(v_a_1805_);
lean_dec(v___x_1802_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1810_, 0, v_a_1806_);
lean_ctor_set(v___x_1810_, 1, v___y_1800_);
lean_ctor_set(v___x_1810_, 2, v___y_1797_);
lean_ctor_set_uint8(v___x_1810_, sizeof(void*)*3, v___x_1804_);
lean_ctor_set_uint8(v___x_1810_, sizeof(void*)*3 + 1, v___y_1798_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 1, v___x_1810_);
v___x_1812_ = v___x_1808_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1805_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v___x_1810_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
else
{
lean_object* v_a_1815_; lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1824_; 
v_a_1815_ = lean_ctor_get(v___x_1802_, 0);
v_a_1816_ = lean_ctor_get(v___x_1802_, 1);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1818_ = v___x_1802_;
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_inc(v_a_1815_);
lean_dec(v___x_1802_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1820_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1820_, 0, v_a_1816_);
lean_ctor_set(v___x_1820_, 1, v___y_1800_);
lean_ctor_set(v___x_1820_, 2, v___y_1797_);
lean_ctor_set_uint8(v___x_1820_, sizeof(void*)*3, v___x_1804_);
lean_ctor_set_uint8(v___x_1820_, sizeof(void*)*3 + 1, v___y_1798_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 1, v___x_1820_);
v___x_1822_ = v___x_1818_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1815_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
v___jp_1825_:
{
lean_object* v_config_1828_; lean_object* v_dir_1829_; lean_object* v_buildDir_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v_config_1828_ = lean_ctor_get(v_self_1779_, 6);
lean_inc_ref(v_config_1828_);
v_dir_1829_ = lean_ctor_get(v_self_1779_, 4);
lean_inc_ref(v_dir_1829_);
lean_dec_ref(v_self_1779_);
v_buildDir_1830_ = lean_ctor_get(v_config_1828_, 5);
lean_inc_ref(v_buildDir_1830_);
lean_dec_ref(v_config_1828_);
v___x_1831_ = l_System_FilePath_normalize(v_buildDir_1830_);
v___x_1832_ = l_Lake_joinRelative(v_dir_1829_, v___x_1831_);
v___x_1833_ = l_System_FilePath_pathExists(v___x_1832_);
if (v_a_1826_ == 0)
{
lean_object* v_log_1834_; uint8_t v_action_1835_; uint8_t v_wantsRebuild_1836_; lean_object* v_trace_1837_; lean_object* v_buildTime_1838_; 
v_log_1834_ = lean_ctor_get(v_a_1827_, 0);
lean_inc_ref(v_log_1834_);
v_action_1835_ = lean_ctor_get_uint8(v_a_1827_, sizeof(void*)*3);
v_wantsRebuild_1836_ = lean_ctor_get_uint8(v_a_1827_, sizeof(void*)*3 + 1);
v_trace_1837_ = lean_ctor_get(v_a_1827_, 1);
lean_inc_ref(v_trace_1837_);
v_buildTime_1838_ = lean_ctor_get(v_a_1827_, 2);
lean_inc(v_buildTime_1838_);
lean_dec_ref(v_a_1827_);
v___y_1795_ = v___x_1832_;
v___y_1796_ = v_action_1835_;
v___y_1797_ = v_buildTime_1838_;
v___y_1798_ = v_wantsRebuild_1836_;
v___y_1799_ = v_log_1834_;
v___y_1800_ = v_trace_1837_;
goto v___jp_1794_;
}
else
{
if (v___x_1833_ == 0)
{
lean_object* v_log_1839_; uint8_t v_action_1840_; uint8_t v_wantsRebuild_1841_; lean_object* v_trace_1842_; lean_object* v_buildTime_1843_; 
v_log_1839_ = lean_ctor_get(v_a_1827_, 0);
lean_inc_ref(v_log_1839_);
v_action_1840_ = lean_ctor_get_uint8(v_a_1827_, sizeof(void*)*3);
v_wantsRebuild_1841_ = lean_ctor_get_uint8(v_a_1827_, sizeof(void*)*3 + 1);
v_trace_1842_ = lean_ctor_get(v_a_1827_, 1);
lean_inc_ref(v_trace_1842_);
v_buildTime_1843_ = lean_ctor_get(v_a_1827_, 2);
lean_inc(v_buildTime_1843_);
lean_dec_ref(v_a_1827_);
v___y_1795_ = v___x_1832_;
v___y_1796_ = v_action_1840_;
v___y_1797_ = v_buildTime_1843_;
v___y_1798_ = v_wantsRebuild_1841_;
v___y_1799_ = v_log_1839_;
v___y_1800_ = v_trace_1842_;
goto v___jp_1794_;
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec_ref(v___x_1832_);
lean_dec_ref(v_archiveFile_1781_);
v___x_1844_ = lean_box(0);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v_a_1827_);
return v___x_1845_;
}
}
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v_traceFile_1855_; lean_object* v___x_1856_; 
v___x_1854_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0));
lean_inc_ref(v_archiveFile_1781_);
v_traceFile_1855_ = l_System_FilePath_addExtension(v_archiveFile_1781_, v___x_1854_);
lean_inc_ref(v_traceFile_1855_);
v___x_1856_ = l_Lake_readTraceFile(v_traceFile_1855_, v_log_1846_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v_a_1858_; lean_object* v___x_1859_; uint64_t v___x_1860_; uint64_t v___x_1861_; uint64_t v_depTrace_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
v_a_1858_ = lean_ctor_get(v___x_1856_, 1);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___x_1856_, 2);
v___x_1859_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1));
v___x_1860_ = l_Lake_Hash_nil;
v___x_1861_ = lean_string_hash(v_url_1780_);
v_depTrace_1862_ = lean_uint64_mix_hash(v___x_1860_, v___x_1861_);
v___x_1863_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2));
v___x_1864_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
v___x_1865_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1865_, 0, v___x_1863_);
lean_ctor_set(v___x_1865_, 1, v___x_1859_);
lean_ctor_set(v___x_1865_, 2, v___x_1864_);
lean_ctor_set_uint64(v___x_1865_, sizeof(void*)*3, v_depTrace_1862_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v_a_1858_);
v___x_1867_ = v___x_1852_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1858_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v_trace_1849_);
lean_ctor_set(v_reuseFailAlloc_1883_, 2, v_buildTime_1850_);
lean_ctor_set_uint8(v_reuseFailAlloc_1883_, sizeof(void*)*3, v_action_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1883_, sizeof(void*)*3 + 1, v_wantsRebuild_1848_);
v___x_1867_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_1783_, v_archiveFile_1781_, v___x_1865_, v_a_1857_, v___x_1864_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v___x_1867_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v_a_1870_; uint8_t v___x_1871_; uint8_t v___x_1872_; uint8_t v___x_1873_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
v_a_1870_ = lean_ctor_get(v___x_1868_, 1);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1868_, 2);
v___x_1871_ = 0;
v___x_1872_ = lean_unbox(v_a_1869_);
lean_dec(v_a_1869_);
v___x_1873_ = l_Lake_instDecidableEqOutputStatus(v___x_1872_, v___x_1871_);
if (v___x_1873_ == 0)
{
uint8_t v___x_1874_; 
lean_dec_ref_known(v___x_1865_, 3);
lean_dec_ref(v_traceFile_1855_);
lean_dec_ref(v_url_1780_);
v___x_1874_ = 1;
v_a_1826_ = v___x_1874_;
v_a_1827_ = v_a_1870_;
goto v___jp_1825_;
}
else
{
uint8_t v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = 4;
lean_inc_ref(v_archiveFile_1781_);
v___x_1876_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1780_, v_archiveFile_1781_, v_headers_1782_, v___x_1865_, v_traceFile_1855_, v___x_1875_, v_a_1787_, v_a_1870_);
lean_dec_ref_known(v___x_1865_, 3);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; uint8_t v___x_1878_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 1);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 2);
v___x_1878_ = 0;
v_a_1826_ = v___x_1878_;
v_a_1827_ = v_a_1877_;
goto v___jp_1825_;
}
else
{
lean_object* v_a_1879_; lean_object* v_a_1880_; 
lean_dec_ref(v_archiveFile_1781_);
lean_dec_ref(v_self_1779_);
v_a_1879_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1879_);
v_a_1880_ = lean_ctor_get(v___x_1876_, 1);
lean_inc(v_a_1880_);
lean_dec_ref_known(v___x_1876_, 2);
v_a_1791_ = v_a_1879_;
v_a_1792_ = v_a_1880_;
goto v___jp_1790_;
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v_a_1882_; 
lean_dec_ref_known(v___x_1865_, 3);
lean_dec_ref(v_traceFile_1855_);
lean_dec_ref(v_archiveFile_1781_);
lean_dec_ref(v_url_1780_);
lean_dec_ref(v_self_1779_);
v_a_1881_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1881_);
v_a_1882_ = lean_ctor_get(v___x_1868_, 1);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1868_, 2);
v_a_1791_ = v_a_1881_;
v_a_1792_ = v_a_1882_;
goto v___jp_1790_;
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v_a_1885_; lean_object* v___x_1887_; 
lean_dec_ref(v_traceFile_1855_);
lean_dec_ref(v_archiveFile_1781_);
lean_dec_ref(v_url_1780_);
lean_dec_ref(v_self_1779_);
v_a_1884_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1884_);
v_a_1885_ = lean_ctor_get(v___x_1856_, 1);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1856_, 2);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v_a_1885_);
v___x_1887_ = v___x_1852_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1885_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_trace_1849_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_buildTime_1850_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*3, v_action_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*3 + 1, v_wantsRebuild_1848_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
v_a_1791_ = v_a_1884_;
v_a_1792_ = v___x_1887_;
goto v___jp_1790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object* v_self_1890_, lean_object* v_url_1891_, lean_object* v_archiveFile_1892_, lean_object* v_headers_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_self_1890_, v_url_1891_, v_archiveFile_1892_, v_headers_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec_ref(v_headers_1893_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object* v_a_1902_, lean_object* v_info_1903_, lean_object* v_depTrace_1904_, lean_object* v_depHash_1905_, lean_object* v_oldTrace_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1903_, v_depTrace_1904_, v_depHash_1905_, v_oldTrace_1906_, v_a_1910_, v_a_1911_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object* v_a_1914_, lean_object* v_info_1915_, lean_object* v_depTrace_1916_, lean_object* v_depHash_1917_, lean_object* v_oldTrace_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_1914_, v_info_1915_, v_depTrace_1916_, v_depHash_1917_, v_oldTrace_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
lean_dec_ref(v_a_1922_);
lean_dec(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec_ref(v_oldTrace_1918_);
lean_dec(v_depHash_1917_);
lean_dec_ref(v_depTrace_1916_);
lean_dec_ref(v_info_1915_);
lean_dec_ref(v_a_1914_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_getUrl_1926_, lean_object* v_pkg_1927_, lean_object* v_archiveFile_1928_, lean_object* v_headers_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
uint8_t v_r_1938_; lean_object* v___y_1939_; lean_object* v_a_1943_; lean_object* v___x_1959_; 
lean_inc_ref(v___y_1934_);
lean_inc(v___y_1933_);
lean_inc(v___y_1932_);
lean_inc(v___y_1931_);
lean_inc_ref(v___y_1930_);
lean_inc_ref(v_pkg_1927_);
v___x_1959_ = lean_apply_8(v_getUrl_1926_, v_pkg_1927_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, lean_box(0));
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v_a_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
v_a_1961_ = lean_ctor_get(v___x_1959_, 1);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1959_, 2);
lean_inc_ref(v_pkg_1927_);
v___x_1962_ = lean_apply_1(v_archiveFile_1928_, v_pkg_1927_);
v___x_1963_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_1927_, v_a_1960_, v___x_1962_, v_headers_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v_a_1961_);
lean_dec_ref(v___y_1930_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; uint8_t v___x_1965_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 1);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___x_1963_, 2);
v___x_1965_ = 1;
v_r_1938_ = v___x_1965_;
v___y_1939_ = v_a_1964_;
goto v___jp_1937_;
}
else
{
lean_object* v_a_1966_; 
v_a_1966_ = lean_ctor_get(v___x_1963_, 1);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___x_1963_, 2);
v_a_1943_ = v_a_1966_;
goto v___jp_1942_;
}
}
else
{
lean_object* v_a_1967_; 
lean_dec_ref(v___y_1930_);
lean_dec_ref(v_archiveFile_1928_);
lean_dec_ref(v_pkg_1927_);
v_a_1967_ = lean_ctor_get(v___x_1959_, 1);
lean_inc(v_a_1967_);
lean_dec_ref_known(v___x_1959_, 2);
v_a_1943_ = v_a_1967_;
goto v___jp_1942_;
}
v___jp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = lean_box(v_r_1938_);
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set(v___x_1941_, 1, v___y_1939_);
return v___x_1941_;
}
v___jp_1942_:
{
lean_object* v_log_1944_; uint8_t v_action_1945_; uint8_t v_wantsRebuild_1946_; lean_object* v_trace_1947_; lean_object* v_buildTime_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1958_; 
v_log_1944_ = lean_ctor_get(v_a_1943_, 0);
v_action_1945_ = lean_ctor_get_uint8(v_a_1943_, sizeof(void*)*3);
v_wantsRebuild_1946_ = lean_ctor_get_uint8(v_a_1943_, sizeof(void*)*3 + 1);
v_trace_1947_ = lean_ctor_get(v_a_1943_, 1);
v_buildTime_1948_ = lean_ctor_get(v_a_1943_, 2);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_a_1943_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1950_ = v_a_1943_;
v_isShared_1951_ = v_isSharedCheck_1958_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_buildTime_1948_);
lean_inc(v_trace_1947_);
lean_inc(v_log_1944_);
lean_dec(v_a_1943_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1958_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
uint8_t v___x_1952_; uint8_t v___x_1953_; lean_object* v___x_1955_; 
v___x_1952_ = 4;
v___x_1953_ = l_Lake_JobAction_merge(v_action_1945_, v___x_1952_);
if (v_isShared_1951_ == 0)
{
v___x_1955_ = v___x_1950_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_log_1944_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_trace_1947_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v_buildTime_1948_);
lean_ctor_set_uint8(v_reuseFailAlloc_1957_, sizeof(void*)*3 + 1, v_wantsRebuild_1946_);
v___x_1955_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
uint8_t v___x_1956_; 
lean_ctor_set_uint8(v___x_1955_, sizeof(void*)*3, v___x_1953_);
v___x_1956_ = 0;
v_r_1938_ = v___x_1956_;
v___y_1939_ = v___x_1955_;
goto v___jp_1937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_getUrl_1968_, lean_object* v_pkg_1969_, lean_object* v_archiveFile_1970_, lean_object* v_headers_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(v_getUrl_1968_, v_pkg_1969_, v_archiveFile_1970_, v_headers_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v_headers_1971_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* v_getUrl_1980_, lean_object* v_archiveFile_1981_, lean_object* v_headers_1982_, lean_object* v___x_1983_, lean_object* v_facet_1984_, lean_object* v_pkg_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v___f_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_inc_ref(v_pkg_1985_);
v___f_1993_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1993_, 0, v_getUrl_1980_);
lean_closure_set(v___f_1993_, 1, v_pkg_1985_);
lean_closure_set(v___f_1993_, 2, v_archiveFile_1981_);
lean_closure_set(v___f_1993_, 3, v_headers_1982_);
v___x_1994_ = lean_unsigned_to_nat(0u);
v___x_1995_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_1983_);
v___x_1996_ = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(v___x_1996_, 0, lean_box(0));
lean_closure_set(v___x_1996_, 1, v___x_1983_);
lean_closure_set(v___x_1996_, 2, v___f_1993_);
lean_closure_set(v___x_1996_, 3, v___x_1994_);
lean_closure_set(v___x_1996_, 4, v___x_1995_);
v___x_1997_ = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM___boxed), 9, 2);
lean_closure_set(v___x_1997_, 0, lean_box(0));
lean_closure_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM___boxed), 9, 2);
lean_closure_set(v___x_1998_, 0, lean_box(0));
lean_closure_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = l_Lake_ensureJob___redArg(v___x_1983_, v___x_1998_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2032_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
v_a_2001_ = lean_ctor_get(v___x_1999_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2003_ = v___x_1999_;
v_isShared_2004_ = v_isSharedCheck_2032_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_inc(v_a_2000_);
lean_dec(v___x_1999_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2032_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v_task_2005_; lean_object* v_kind_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2030_; 
v_task_2005_ = lean_ctor_get(v_a_2000_, 0);
v_kind_2006_ = lean_ctor_get(v_a_2000_, 1);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_a_2000_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v_a_2000_, 2);
lean_dec(v_unused_2031_);
v___x_2008_ = v_a_2000_;
v_isShared_2009_ = v_isSharedCheck_2030_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_kind_2006_);
lean_inc(v_task_2005_);
lean_dec(v_a_2000_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2030_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v_registeredJobs_2010_; lean_object* v___x_2011_; lean_object* v_baseName_2012_; uint8_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v_job_2021_; 
v_registeredJobs_2010_ = lean_ctor_get(v___y_1990_, 3);
v___x_2011_ = lean_st_ref_take(v_registeredJobs_2010_);
v_baseName_2012_ = lean_ctor_get(v_pkg_1985_, 1);
lean_inc(v_baseName_2012_);
lean_dec_ref(v_pkg_1985_);
v___x_2013_ = 1;
v___x_2014_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2012_, v___x_2013_);
v___x_2015_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2016_ = lean_string_append(v___x_2014_, v___x_2015_);
v___x_2017_ = l_Lake_Name_eraseHead(v_facet_1984_);
v___x_2018_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2017_, v___x_2013_);
v___x_2019_ = lean_string_append(v___x_2016_, v___x_2018_);
lean_dec_ref(v___x_2018_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 2, v___x_2019_);
v_job_2021_ = v___x_2008_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_task_2005_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_kind_2006_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v___x_2019_);
v_job_2021_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
lean_ctor_set_uint8(v_job_2021_, sizeof(void*)*3, v___x_2013_);
lean_inc_ref(v_job_2021_);
v___x_2022_ = l_Lake_Job_toOpaque___redArg(v_job_2021_);
v___x_2023_ = lean_array_push(v___x_2011_, v___x_2022_);
v___x_2024_ = lean_st_ref_put(v_registeredJobs_2010_, v___x_2023_);
v___x_2025_ = l_Lake_Job_renew___redArg(v_job_2021_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2025_);
v___x_2027_ = v___x_2003_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_a_2001_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_1985_);
lean_dec(v_facet_1984_);
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v_getUrl_2033_, lean_object* v_archiveFile_2034_, lean_object* v_headers_2035_, lean_object* v___x_2036_, lean_object* v_facet_2037_, lean_object* v_pkg_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_2033_, v_archiveFile_2034_, v_headers_2035_, v___x_2036_, v_facet_2037_, v_pkg_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec(v___y_2040_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object* v_facet_2054_, lean_object* v_archiveFile_2055_, lean_object* v_getUrl_2056_, lean_object* v_headers_2057_){
_start:
{
lean_object* v___x_2058_; lean_object* v___f_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2058_ = l_Lake_instDataKindBool;
v___f_2059_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2059_, 0, v_getUrl_2056_);
lean_closure_set(v___f_2059_, 1, v_archiveFile_2055_);
lean_closure_set(v___f_2059_, 2, v_headers_2057_);
lean_closure_set(v___f_2059_, 3, v___x_2058_);
lean_closure_set(v___f_2059_, 4, v_facet_2054_);
v___x_2060_ = l_Lake_Package_keyword;
v___x_2061_ = 1;
v___x_2062_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_2063_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2063_, 0, v___x_2060_);
lean_ctor_set(v___x_2063_, 1, v___f_2059_);
lean_ctor_set(v___x_2063_, 2, v___x_2058_);
lean_ctor_set(v___x_2063_, 3, v___x_2062_);
lean_ctor_set_uint8(v___x_2063_, sizeof(void*)*4, v___x_2061_);
lean_ctor_set_uint8(v___x_2063_, sizeof(void*)*4 + 1, v___x_2061_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* v_facet_2064_, lean_object* v_archiveFile_2065_, lean_object* v_getUrl_2066_, lean_object* v_headers_2067_, lean_object* v_inst_2068_){
_start:
{
lean_object* v___x_2069_; lean_object* v___f_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2069_ = l_Lake_instDataKindBool;
v___f_2070_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2070_, 0, v_getUrl_2066_);
lean_closure_set(v___f_2070_, 1, v_archiveFile_2065_);
lean_closure_set(v___f_2070_, 2, v_headers_2067_);
lean_closure_set(v___f_2070_, 3, v___x_2069_);
lean_closure_set(v___f_2070_, 4, v_facet_2064_);
v___x_2071_ = l_Lake_Package_keyword;
v___x_2072_ = 1;
v___x_2073_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_2074_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2074_, 0, v___x_2071_);
lean_ctor_set(v___x_2074_, 1, v___f_2070_);
lean_ctor_set(v___x_2074_, 2, v___x_2069_);
lean_ctor_set(v___x_2074_, 3, v___x_2073_);
lean_ctor_set_uint8(v___x_2074_, sizeof(void*)*4, v___x_2072_);
lean_ctor_set_uint8(v___x_2074_, sizeof(void*)*4 + 1, v___x_2072_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_what_2076_, lean_object* v_baseName_2077_, lean_object* v_optFacet_2078_, uint8_t v_success_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_a_2088_; lean_object* v_a_2089_; 
if (v_success_2079_ == 0)
{
lean_object* v_toBuildConfig_2110_; uint8_t v_verbosity_2111_; uint8_t v___x_2112_; uint8_t v___x_2113_; 
v_toBuildConfig_2110_ = lean_ctor_get(v___y_2084_, 0);
v_verbosity_2111_ = lean_ctor_get_uint8(v_toBuildConfig_2110_, sizeof(void*)*4 + 3);
v___x_2112_ = 2;
v___x_2113_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_dec(v_optFacet_2078_);
lean_dec(v_baseName_2077_);
v___x_2114_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2088_ = v___x_2114_;
v_a_2089_ = v___y_2085_;
goto v___jp_2087_;
}
else
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2115_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2116_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2077_, v___x_2113_);
v___x_2117_ = lean_string_append(v___x_2115_, v___x_2116_);
lean_dec_ref(v___x_2116_);
v___x_2118_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2119_ = lean_string_append(v___x_2117_, v___x_2118_);
v___x_2120_ = l_Lake_Name_eraseHead(v_optFacet_2078_);
v___x_2121_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2120_, v___x_2113_);
v___x_2122_ = lean_string_append(v___x_2119_, v___x_2121_);
lean_dec_ref(v___x_2121_);
v___x_2123_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2124_ = lean_string_append(v___x_2122_, v___x_2123_);
v_a_2088_ = v___x_2124_;
v_a_2089_ = v___y_2085_;
goto v___jp_2087_;
}
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_dec(v_optFacet_2078_);
lean_dec(v_baseName_2077_);
v___x_2125_ = lean_box(0);
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
lean_ctor_set(v___x_2126_, 1, v___y_2085_);
return v___x_2126_;
}
v___jp_2087_:
{
lean_object* v_log_2090_; uint8_t v_action_2091_; uint8_t v_wantsRebuild_2092_; lean_object* v_trace_2093_; lean_object* v_buildTime_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2109_; 
v_log_2090_ = lean_ctor_get(v_a_2089_, 0);
v_action_2091_ = lean_ctor_get_uint8(v_a_2089_, sizeof(void*)*3);
v_wantsRebuild_2092_ = lean_ctor_get_uint8(v_a_2089_, sizeof(void*)*3 + 1);
v_trace_2093_ = lean_ctor_get(v_a_2089_, 1);
v_buildTime_2094_ = lean_ctor_get(v_a_2089_, 2);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_a_2089_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2096_ = v_a_2089_;
v_isShared_2097_ = v_isSharedCheck_2109_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_buildTime_2094_);
lean_inc(v_trace_2093_);
lean_inc(v_log_2090_);
lean_dec(v_a_2089_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2109_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2098_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0));
v___x_2099_ = lean_string_append(v___x_2098_, v_what_2076_);
v___x_2100_ = lean_string_append(v___x_2099_, v_a_2088_);
lean_dec_ref(v_a_2088_);
v___x_2101_ = 3;
v___x_2102_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2102_, 0, v___x_2100_);
lean_ctor_set_uint8(v___x_2102_, sizeof(void*)*1, v___x_2101_);
v___x_2103_ = lean_array_get_size(v_log_2090_);
v___x_2104_ = lean_array_push(v_log_2090_, v___x_2102_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2104_);
v___x_2106_ = v___x_2096_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2104_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_trace_2093_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_buildTime_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2108_, sizeof(void*)*3, v_action_2091_);
lean_ctor_set_uint8(v_reuseFailAlloc_2108_, sizeof(void*)*3 + 1, v_wantsRebuild_2092_);
v___x_2106_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; 
v___x_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2103_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
return v___x_2107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_what_2127_, lean_object* v_baseName_2128_, lean_object* v_optFacet_2129_, lean_object* v_success_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
uint8_t v_success_boxed_2138_; lean_object* v_res_2139_; 
v_success_boxed_2138_ = lean_unbox(v_success_2130_);
v_res_2139_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(v_what_2127_, v_baseName_2128_, v_optFacet_2129_, v_success_boxed_2138_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
lean_dec_ref(v_what_2127_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object* v___x_2140_, lean_object* v___x_2141_, lean_object* v___f_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; 
lean_inc_ref(v___y_2143_);
lean_inc_ref(v___y_2147_);
lean_inc(v___y_2146_);
lean_inc(v___y_2145_);
lean_inc(v___y_2144_);
v___x_2150_ = lean_apply_7(v___y_2143_, v___x_2140_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, lean_box(0));
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2163_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_a_2152_ = lean_ctor_get(v___x_2150_, 1);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2154_ = v___x_2150_;
v_isShared_2155_ = v_isSharedCheck_2163_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2163_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; uint8_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = 0;
v___x_2158_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2159_ = l_Lake_Job_mapM___redArg(v___x_2141_, v_a_2151_, v___f_2142_, v___x_2156_, v___x_2157_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___x_2158_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2159_);
v___x_2161_ = v___x_2154_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_a_2152_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v___y_2143_);
lean_dec_ref(v___f_2142_);
lean_dec(v___x_2141_);
v_a_2164_ = lean_ctor_get(v___x_2150_, 0);
v_a_2165_ = lean_ctor_get(v___x_2150_, 1);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2150_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_inc(v_a_2164_);
lean_dec(v___x_2150_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2164_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v___x_2173_, lean_object* v___x_2174_, lean_object* v___f_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(v___x_2173_, v___x_2174_, v___f_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec(v___y_2177_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object* v_what_2184_, lean_object* v_optFacet_2185_, lean_object* v___x_2186_, lean_object* v_facet_2187_, lean_object* v_pkg_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_baseName_2196_; lean_object* v_keyName_2197_; lean_object* v___f_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___f_2202_; lean_object* v___x_2203_; 
v_baseName_2196_ = lean_ctor_get(v_pkg_2188_, 1);
lean_inc_n(v_baseName_2196_, 2);
v_keyName_2197_ = lean_ctor_get(v_pkg_2188_, 2);
lean_inc(v_optFacet_2185_);
v___f_2198_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2198_, 0, v_what_2184_);
lean_closure_set(v___f_2198_, 1, v_baseName_2196_);
lean_closure_set(v___f_2198_, 2, v_optFacet_2185_);
lean_inc(v_keyName_2197_);
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v_keyName_2197_);
v___x_2200_ = l_Lake_Package_keyword;
v___x_2201_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2199_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
lean_ctor_set(v___x_2201_, 2, v_pkg_2188_);
lean_ctor_set(v___x_2201_, 3, v_optFacet_2185_);
lean_inc(v___x_2186_);
v___f_2202_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2202_, 0, v___x_2201_);
lean_closure_set(v___f_2202_, 1, v___x_2186_);
lean_closure_set(v___f_2202_, 2, v___f_2198_);
v___x_2203_ = l_Lake_ensureJob___redArg(v___x_2186_, v___f_2202_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2236_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_a_2205_ = lean_ctor_get(v___x_2203_, 1);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2207_ = v___x_2203_;
v_isShared_2208_ = v_isSharedCheck_2236_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2236_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v_task_2209_; lean_object* v_kind_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2234_; 
v_task_2209_ = lean_ctor_get(v_a_2204_, 0);
v_kind_2210_ = lean_ctor_get(v_a_2204_, 1);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_a_2204_);
if (v_isSharedCheck_2234_ == 0)
{
lean_object* v_unused_2235_; 
v_unused_2235_ = lean_ctor_get(v_a_2204_, 2);
lean_dec(v_unused_2235_);
v___x_2212_ = v_a_2204_;
v_isShared_2213_ = v_isSharedCheck_2234_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_kind_2210_);
lean_inc(v_task_2209_);
lean_dec(v_a_2204_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2234_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v_registeredJobs_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; lean_object* v_job_2225_; 
v_registeredJobs_2214_ = lean_ctor_get(v___y_2193_, 3);
v___x_2215_ = lean_st_ref_take(v_registeredJobs_2214_);
v___x_2216_ = 1;
v___x_2217_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2196_, v___x_2216_);
v___x_2218_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2219_ = lean_string_append(v___x_2217_, v___x_2218_);
v___x_2220_ = l_Lake_Name_eraseHead(v_facet_2187_);
v___x_2221_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2220_, v___x_2216_);
v___x_2222_ = lean_string_append(v___x_2219_, v___x_2221_);
lean_dec_ref(v___x_2221_);
v___x_2223_ = 0;
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 2, v___x_2222_);
v_job_2225_ = v___x_2212_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_task_2209_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v_kind_2210_);
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
v___x_2227_ = lean_array_push(v___x_2215_, v___x_2226_);
v___x_2228_ = lean_st_ref_put(v_registeredJobs_2214_, v___x_2227_);
v___x_2229_ = l_Lake_Job_renew___redArg(v_job_2225_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2229_);
v___x_2231_ = v___x_2207_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_a_2205_);
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
lean_dec(v_baseName_2196_);
lean_dec(v_facet_2187_);
return v___x_2203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object* v_what_2237_, lean_object* v_optFacet_2238_, lean_object* v___x_2239_, lean_object* v_facet_2240_, lean_object* v_pkg_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(v_what_2237_, v_optFacet_2238_, v___x_2239_, v_facet_2240_, v_pkg_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec(v___y_2243_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object* v_facet_2257_, lean_object* v_optFacet_2258_, lean_object* v_what_2259_){
_start:
{
lean_object* v___x_2260_; lean_object* v___f_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2260_ = l_Lake_instDataKindUnit;
v___f_2261_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2261_, 0, v_what_2259_);
lean_closure_set(v___f_2261_, 1, v_optFacet_2258_);
lean_closure_set(v___f_2261_, 2, v___x_2260_);
lean_closure_set(v___f_2261_, 3, v_facet_2257_);
v___x_2262_ = l_Lake_Package_keyword;
v___x_2263_ = 1;
v___x_2264_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2265_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2265_, 0, v___x_2262_);
lean_ctor_set(v___x_2265_, 1, v___f_2261_);
lean_ctor_set(v___x_2265_, 2, v___x_2260_);
lean_ctor_set(v___x_2265_, 3, v___x_2264_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*4, v___x_2263_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*4 + 1, v___x_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* v_facet_2266_, lean_object* v_optFacet_2267_, lean_object* v_what_2268_, lean_object* v_inst_2269_, lean_object* v_inst_2270_){
_start:
{
lean_object* v___x_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2271_ = l_Lake_instDataKindUnit;
v___f_2272_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2272_, 0, v_what_2268_);
lean_closure_set(v___f_2272_, 1, v_optFacet_2267_);
lean_closure_set(v___f_2272_, 2, v___x_2271_);
lean_closure_set(v___f_2272_, 3, v_facet_2266_);
v___x_2273_ = l_Lake_Package_keyword;
v___x_2274_ = 1;
v___x_2275_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2276_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2276_, 0, v___x_2273_);
lean_ctor_set(v___x_2276_, 1, v___f_2272_);
lean_ctor_set(v___x_2276_, 2, v___x_2271_);
lean_ctor_set(v___x_2276_, 3, v___x_2275_);
lean_ctor_set_uint8(v___x_2276_, sizeof(void*)*4, v___x_2274_);
lean_ctor_set_uint8(v___x_2276_, sizeof(void*)*4 + 1, v___x_2274_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* v_baseName_2278_, lean_object* v___x_2279_, uint8_t v_success_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_a_2289_; lean_object* v_a_2290_; 
if (v_success_2280_ == 0)
{
lean_object* v_toBuildConfig_2310_; uint8_t v_verbosity_2311_; uint8_t v___x_2312_; uint8_t v___x_2313_; 
v_toBuildConfig_2310_ = lean_ctor_get(v___y_2285_, 0);
v_verbosity_2311_ = lean_ctor_get_uint8(v_toBuildConfig_2310_, sizeof(void*)*4 + 3);
v___x_2312_ = 2;
v___x_2313_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2311_, v___x_2312_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; 
lean_dec(v___x_2279_);
lean_dec(v_baseName_2278_);
v___x_2314_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2289_ = v___x_2314_;
v_a_2290_ = v___y_2286_;
goto v___jp_2288_;
}
else
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2315_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2316_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2278_, v___x_2313_);
v___x_2317_ = lean_string_append(v___x_2315_, v___x_2316_);
lean_dec_ref(v___x_2316_);
v___x_2318_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2319_ = lean_string_append(v___x_2317_, v___x_2318_);
v___x_2320_ = l_Lake_Name_eraseHead(v___x_2279_);
v___x_2321_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2320_, v___x_2313_);
v___x_2322_ = lean_string_append(v___x_2319_, v___x_2321_);
lean_dec_ref(v___x_2321_);
v___x_2323_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2324_ = lean_string_append(v___x_2322_, v___x_2323_);
v_a_2289_ = v___x_2324_;
v_a_2290_ = v___y_2286_;
goto v___jp_2288_;
}
}
else
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_dec(v___x_2279_);
lean_dec(v_baseName_2278_);
v___x_2325_ = lean_box(0);
v___x_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
lean_ctor_set(v___x_2326_, 1, v___y_2286_);
return v___x_2326_;
}
v___jp_2288_:
{
lean_object* v_log_2291_; uint8_t v_action_2292_; uint8_t v_wantsRebuild_2293_; lean_object* v_trace_2294_; lean_object* v_buildTime_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2309_; 
v_log_2291_ = lean_ctor_get(v_a_2290_, 0);
v_action_2292_ = lean_ctor_get_uint8(v_a_2290_, sizeof(void*)*3);
v_wantsRebuild_2293_ = lean_ctor_get_uint8(v_a_2290_, sizeof(void*)*3 + 1);
v_trace_2294_ = lean_ctor_get(v_a_2290_, 1);
v_buildTime_2295_ = lean_ctor_get(v_a_2290_, 2);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_a_2290_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2297_ = v_a_2290_;
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_buildTime_2295_);
lean_inc(v_trace_2294_);
lean_inc(v_log_2291_);
lean_dec(v_a_2290_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2309_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2299_ = ((lean_object*)(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0));
v___x_2300_ = lean_string_append(v___x_2299_, v_a_2289_);
lean_dec_ref(v_a_2289_);
v___x_2301_ = 3;
v___x_2302_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2302_, 0, v___x_2300_);
lean_ctor_set_uint8(v___x_2302_, sizeof(void*)*1, v___x_2301_);
v___x_2303_ = lean_array_get_size(v_log_2291_);
v___x_2304_ = lean_array_push(v_log_2291_, v___x_2302_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2304_);
v___x_2306_ = v___x_2297_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_trace_2294_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_buildTime_2295_);
lean_ctor_set_uint8(v_reuseFailAlloc_2308_, sizeof(void*)*3, v_action_2292_);
lean_ctor_set_uint8(v_reuseFailAlloc_2308_, sizeof(void*)*3 + 1, v_wantsRebuild_2293_);
v___x_2306_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2307_; 
v___x_2307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2303_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
return v___x_2307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object* v_baseName_2327_, lean_object* v___x_2328_, lean_object* v_success_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
uint8_t v_success_boxed_2337_; lean_object* v_res_2338_; 
v_success_boxed_2337_ = lean_unbox(v_success_2329_);
v_res_2338_ = l_Lake_Package_buildCacheFacetConfig___lam__1(v_baseName_2327_, v___x_2328_, v_success_boxed_2337_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* v___x_2339_, lean_object* v___x_2340_, lean_object* v___x_2341_, lean_object* v_pkg_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_baseName_2350_; lean_object* v_keyName_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___f_2356_; lean_object* v___x_2357_; 
v_baseName_2350_ = lean_ctor_get(v_pkg_2342_, 1);
lean_inc_n(v_baseName_2350_, 2);
v_keyName_2351_ = lean_ctor_get(v_pkg_2342_, 2);
lean_inc(v___x_2339_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2352_, 0, v_baseName_2350_);
lean_closure_set(v___f_2352_, 1, v___x_2339_);
lean_inc(v_keyName_2351_);
v___x_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2353_, 0, v_keyName_2351_);
v___x_2354_ = l_Lake_Package_keyword;
v___x_2355_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2353_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
lean_ctor_set(v___x_2355_, 2, v_pkg_2342_);
lean_ctor_set(v___x_2355_, 3, v___x_2339_);
lean_inc(v___x_2340_);
v___f_2356_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2356_, 0, v___x_2355_);
lean_closure_set(v___f_2356_, 1, v___x_2340_);
lean_closure_set(v___f_2356_, 2, v___f_2352_);
v___x_2357_ = l_Lake_ensureJob___redArg(v___x_2340_, v___f_2356_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2390_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
v_a_2359_ = lean_ctor_get(v___x_2357_, 1);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2361_ = v___x_2357_;
v_isShared_2362_ = v_isSharedCheck_2390_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_inc(v_a_2358_);
lean_dec(v___x_2357_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2390_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v_task_2363_; lean_object* v_kind_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2388_; 
v_task_2363_ = lean_ctor_get(v_a_2358_, 0);
v_kind_2364_ = lean_ctor_get(v_a_2358_, 1);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_a_2358_);
if (v_isSharedCheck_2388_ == 0)
{
lean_object* v_unused_2389_; 
v_unused_2389_ = lean_ctor_get(v_a_2358_, 2);
lean_dec(v_unused_2389_);
v___x_2366_ = v_a_2358_;
v_isShared_2367_ = v_isSharedCheck_2388_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_kind_2364_);
lean_inc(v_task_2363_);
lean_dec(v_a_2358_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2388_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v_registeredJobs_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; lean_object* v_job_2379_; 
v_registeredJobs_2368_ = lean_ctor_get(v___y_2347_, 3);
v___x_2369_ = lean_st_ref_take(v_registeredJobs_2368_);
v___x_2370_ = 1;
v___x_2371_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2350_, v___x_2370_);
v___x_2372_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2373_ = lean_string_append(v___x_2371_, v___x_2372_);
v___x_2374_ = l_Lake_Name_eraseHead(v___x_2341_);
v___x_2375_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2374_, v___x_2370_);
v___x_2376_ = lean_string_append(v___x_2373_, v___x_2375_);
lean_dec_ref(v___x_2375_);
v___x_2377_ = 0;
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 2, v___x_2376_);
v_job_2379_ = v___x_2366_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_task_2363_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_kind_2364_);
lean_ctor_set(v_reuseFailAlloc_2387_, 2, v___x_2376_);
v_job_2379_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
lean_ctor_set_uint8(v_job_2379_, sizeof(void*)*3, v___x_2377_);
lean_inc_ref(v_job_2379_);
v___x_2380_ = l_Lake_Job_toOpaque___redArg(v_job_2379_);
v___x_2381_ = lean_array_push(v___x_2369_, v___x_2380_);
v___x_2382_ = lean_st_ref_put(v_registeredJobs_2368_, v___x_2381_);
v___x_2383_ = l_Lake_Job_renew___redArg(v_job_2379_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2383_);
v___x_2385_ = v___x_2361_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_a_2359_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2350_);
lean_dec(v___x_2341_);
return v___x_2357_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object* v___x_2391_, lean_object* v___x_2392_, lean_object* v___x_2393_, lean_object* v_pkg_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lake_Package_buildCacheFacetConfig___lam__2(v___x_2391_, v___x_2392_, v___x_2393_, v_pkg_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec(v___y_2396_);
return v_res_2402_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___f_2406_; 
v___x_2403_ = l_Lake_Package_buildCacheFacet;
v___x_2404_ = l_Lake_instDataKindUnit;
v___x_2405_ = l_Lake_Package_optBuildCacheFacet;
v___f_2406_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2406_, 0, v___x_2405_);
lean_closure_set(v___f_2406_, 1, v___x_2404_);
lean_closure_set(v___f_2406_, 2, v___x_2403_);
return v___f_2406_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2407_; uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___f_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___f_2407_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2408_ = 1;
v___x_2409_ = l_Lake_instDataKindUnit;
v___f_2410_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__0, &l_Lake_Package_buildCacheFacetConfig___closed__0_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__0);
v___x_2411_ = l_Lake_Package_keyword;
v___x_2412_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
lean_ctor_set(v___x_2412_, 1, v___f_2410_);
lean_ctor_set(v___x_2412_, 2, v___x_2409_);
lean_ctor_set(v___x_2412_, 3, v___f_2407_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*4, v___x_2408_);
lean_ctor_set_uint8(v___x_2412_, sizeof(void*)*4 + 1, v___x_2408_);
return v___x_2412_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig(void){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__1, &l_Lake_Package_buildCacheFacetConfig___closed__1_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__1);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* v_pkg_2415_, lean_object* v___x_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
uint8_t v_r_2425_; lean_object* v___y_2426_; lean_object* v_a_2430_; lean_object* v___x_2446_; 
lean_inc_ref(v_pkg_2415_);
v___x_2446_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_pkg_2415_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v_a_2448_; lean_object* v_dir_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
v_a_2448_ = lean_ctor_get(v___x_2446_, 1);
lean_inc(v_a_2448_);
lean_dec_ref_known(v___x_2446_, 2);
v_dir_2449_ = lean_ctor_get(v_pkg_2415_, 4);
v___x_2450_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_2449_);
v___x_2451_ = l_Lake_joinRelative(v_dir_2449_, v___x_2450_);
v___x_2452_ = ((lean_object*)(l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0));
v___x_2453_ = l_Lake_joinRelative(v___x_2451_, v___x_2452_);
v___x_2454_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2415_, v_a_2447_, v___x_2453_, v___x_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v_a_2448_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; uint8_t v___x_2456_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 1);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 2);
v___x_2456_ = 1;
v_r_2425_ = v___x_2456_;
v___y_2426_ = v_a_2455_;
goto v___jp_2424_;
}
else
{
lean_object* v_a_2457_; 
v_a_2457_ = lean_ctor_get(v___x_2454_, 1);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2454_, 2);
v_a_2430_ = v_a_2457_;
goto v___jp_2429_;
}
}
else
{
lean_object* v_a_2458_; 
lean_dec_ref(v_pkg_2415_);
v_a_2458_ = lean_ctor_get(v___x_2446_, 1);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2446_, 2);
v_a_2430_ = v_a_2458_;
goto v___jp_2429_;
}
v___jp_2424_:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = lean_box(v_r_2425_);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set(v___x_2428_, 1, v___y_2426_);
return v___x_2428_;
}
v___jp_2429_:
{
lean_object* v_log_2431_; uint8_t v_action_2432_; uint8_t v_wantsRebuild_2433_; lean_object* v_trace_2434_; lean_object* v_buildTime_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2445_; 
v_log_2431_ = lean_ctor_get(v_a_2430_, 0);
v_action_2432_ = lean_ctor_get_uint8(v_a_2430_, sizeof(void*)*3);
v_wantsRebuild_2433_ = lean_ctor_get_uint8(v_a_2430_, sizeof(void*)*3 + 1);
v_trace_2434_ = lean_ctor_get(v_a_2430_, 1);
v_buildTime_2435_ = lean_ctor_get(v_a_2430_, 2);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_a_2430_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2437_ = v_a_2430_;
v_isShared_2438_ = v_isSharedCheck_2445_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_buildTime_2435_);
lean_inc(v_trace_2434_);
lean_inc(v_log_2431_);
lean_dec(v_a_2430_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2445_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
uint8_t v___x_2439_; uint8_t v___x_2440_; lean_object* v___x_2442_; 
v___x_2439_ = 4;
v___x_2440_ = l_Lake_JobAction_merge(v_action_2432_, v___x_2439_);
if (v_isShared_2438_ == 0)
{
v___x_2442_ = v___x_2437_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_log_2431_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_trace_2434_);
lean_ctor_set(v_reuseFailAlloc_2444_, 2, v_buildTime_2435_);
lean_ctor_set_uint8(v_reuseFailAlloc_2444_, sizeof(void*)*3 + 1, v_wantsRebuild_2433_);
v___x_2442_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
uint8_t v___x_2443_; 
lean_ctor_set_uint8(v___x_2442_, sizeof(void*)*3, v___x_2440_);
v___x_2443_ = 0;
v_r_2425_ = v___x_2443_;
v___y_2426_ = v___x_2442_;
goto v___jp_2424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* v_pkg_2459_, lean_object* v___x_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lake_Package_optBarrelFacetConfig___lam__0(v_pkg_2459_, v___x_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v___x_2460_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* v___x_2469_, lean_object* v___f_2470_, lean_object* v___x_2471_, lean_object* v___x_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = l_Lake_Job_async___redArg(v___x_2469_, v___f_2470_, v___x_2471_, v___x_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v___y_2478_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object* v___x_2482_, lean_object* v___f_2483_, lean_object* v___x_2484_, lean_object* v___x_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lake_Package_optBarrelFacetConfig___lam__1(v___x_2482_, v___f_2483_, v___x_2484_, v___x_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec(v___y_2487_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* v___x_2494_, lean_object* v___x_2495_, lean_object* v___x_2496_, lean_object* v_pkg_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v___f_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___f_2508_; lean_object* v___x_2509_; 
lean_inc_ref(v_pkg_2497_);
v___f_2505_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2505_, 0, v_pkg_2497_);
lean_closure_set(v___f_2505_, 1, v___x_2494_);
v___x_2506_ = lean_unsigned_to_nat(0u);
v___x_2507_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2495_);
v___f_2508_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2508_, 0, v___x_2495_);
lean_closure_set(v___f_2508_, 1, v___f_2505_);
lean_closure_set(v___f_2508_, 2, v___x_2506_);
lean_closure_set(v___f_2508_, 3, v___x_2507_);
v___x_2509_ = l_Lake_ensureJob___redArg(v___x_2495_, v___f_2508_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2542_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_a_2511_ = lean_ctor_get(v___x_2509_, 1);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2513_ = v___x_2509_;
v_isShared_2514_ = v_isSharedCheck_2542_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2542_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v_task_2515_; lean_object* v_kind_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2540_; 
v_task_2515_ = lean_ctor_get(v_a_2510_, 0);
v_kind_2516_ = lean_ctor_get(v_a_2510_, 1);
v_isSharedCheck_2540_ = !lean_is_exclusive(v_a_2510_);
if (v_isSharedCheck_2540_ == 0)
{
lean_object* v_unused_2541_; 
v_unused_2541_ = lean_ctor_get(v_a_2510_, 2);
lean_dec(v_unused_2541_);
v___x_2518_ = v_a_2510_;
v_isShared_2519_ = v_isSharedCheck_2540_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_kind_2516_);
lean_inc(v_task_2515_);
lean_dec(v_a_2510_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2540_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v_registeredJobs_2520_; lean_object* v___x_2521_; lean_object* v_baseName_2522_; uint8_t v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v_job_2531_; 
v_registeredJobs_2520_ = lean_ctor_get(v___y_2502_, 3);
v___x_2521_ = lean_st_ref_take(v_registeredJobs_2520_);
v_baseName_2522_ = lean_ctor_get(v_pkg_2497_, 1);
lean_inc(v_baseName_2522_);
lean_dec_ref(v_pkg_2497_);
v___x_2523_ = 1;
v___x_2524_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2522_, v___x_2523_);
v___x_2525_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2526_ = lean_string_append(v___x_2524_, v___x_2525_);
v___x_2527_ = l_Lake_Name_eraseHead(v___x_2496_);
v___x_2528_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2527_, v___x_2523_);
v___x_2529_ = lean_string_append(v___x_2526_, v___x_2528_);
lean_dec_ref(v___x_2528_);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 2, v___x_2529_);
v_job_2531_ = v___x_2518_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_task_2515_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_kind_2516_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v___x_2529_);
v_job_2531_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2537_; 
lean_ctor_set_uint8(v_job_2531_, sizeof(void*)*3, v___x_2523_);
lean_inc_ref(v_job_2531_);
v___x_2532_ = l_Lake_Job_toOpaque___redArg(v_job_2531_);
v___x_2533_ = lean_array_push(v___x_2521_, v___x_2532_);
v___x_2534_ = lean_st_ref_put(v_registeredJobs_2520_, v___x_2533_);
v___x_2535_ = l_Lake_Job_renew___redArg(v_job_2531_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v___x_2535_);
v___x_2537_ = v___x_2513_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2538_, 1, v_a_2511_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_2497_);
lean_dec(v___x_2496_);
return v___x_2509_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object* v___x_2543_, lean_object* v___x_2544_, lean_object* v___x_2545_, lean_object* v_pkg_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lake_Package_optBarrelFacetConfig___lam__2(v___x_2543_, v___x_2544_, v___x_2545_, v_pkg_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec(v___y_2548_);
return v_res_2554_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___f_2558_; 
v___x_2555_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_2556_ = l_Lake_instDataKindBool;
v___x_2557_ = l_Lake_Reservoir_lakeHeaders;
v___f_2558_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2558_, 0, v___x_2557_);
lean_closure_set(v___f_2558_, 1, v___x_2556_);
lean_closure_set(v___f_2558_, 2, v___x_2555_);
return v___f_2558_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2559_; uint8_t v___x_2560_; lean_object* v___x_2561_; lean_object* v___f_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___f_2559_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_2560_ = 1;
v___x_2561_ = l_Lake_instDataKindBool;
v___f_2562_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__0, &l_Lake_Package_optBarrelFacetConfig___closed__0_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__0);
v___x_2563_ = l_Lake_Package_keyword;
v___x_2564_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
lean_ctor_set(v___x_2564_, 1, v___f_2562_);
lean_ctor_set(v___x_2564_, 2, v___x_2561_);
lean_ctor_set(v___x_2564_, 3, v___f_2559_);
lean_ctor_set_uint8(v___x_2564_, sizeof(void*)*4, v___x_2560_);
lean_ctor_set_uint8(v___x_2564_, sizeof(void*)*4 + 1, v___x_2560_);
return v___x_2564_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig(void){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__1, &l_Lake_Package_optBarrelFacetConfig___closed__1_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__1);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* v_baseName_2567_, lean_object* v___x_2568_, uint8_t v_success_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_a_2578_; lean_object* v_a_2579_; 
if (v_success_2569_ == 0)
{
lean_object* v_toBuildConfig_2599_; uint8_t v_verbosity_2600_; uint8_t v___x_2601_; uint8_t v___x_2602_; 
v_toBuildConfig_2599_ = lean_ctor_get(v___y_2574_, 0);
v_verbosity_2600_ = lean_ctor_get_uint8(v_toBuildConfig_2599_, sizeof(void*)*4 + 3);
v___x_2601_ = 2;
v___x_2602_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2600_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_object* v___x_2603_; 
lean_dec(v___x_2568_);
lean_dec(v_baseName_2567_);
v___x_2603_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2578_ = v___x_2603_;
v_a_2579_ = v___y_2575_;
goto v___jp_2577_;
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2604_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2605_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2567_, v___x_2602_);
v___x_2606_ = lean_string_append(v___x_2604_, v___x_2605_);
lean_dec_ref(v___x_2605_);
v___x_2607_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2608_ = lean_string_append(v___x_2606_, v___x_2607_);
v___x_2609_ = l_Lake_Name_eraseHead(v___x_2568_);
v___x_2610_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2609_, v___x_2602_);
v___x_2611_ = lean_string_append(v___x_2608_, v___x_2610_);
lean_dec_ref(v___x_2610_);
v___x_2612_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2613_ = lean_string_append(v___x_2611_, v___x_2612_);
v_a_2578_ = v___x_2613_;
v_a_2579_ = v___y_2575_;
goto v___jp_2577_;
}
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_dec(v___x_2568_);
lean_dec(v_baseName_2567_);
v___x_2614_ = lean_box(0);
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
lean_ctor_set(v___x_2615_, 1, v___y_2575_);
return v___x_2615_;
}
v___jp_2577_:
{
lean_object* v_log_2580_; uint8_t v_action_2581_; uint8_t v_wantsRebuild_2582_; lean_object* v_trace_2583_; lean_object* v_buildTime_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2598_; 
v_log_2580_ = lean_ctor_get(v_a_2579_, 0);
v_action_2581_ = lean_ctor_get_uint8(v_a_2579_, sizeof(void*)*3);
v_wantsRebuild_2582_ = lean_ctor_get_uint8(v_a_2579_, sizeof(void*)*3 + 1);
v_trace_2583_ = lean_ctor_get(v_a_2579_, 1);
v_buildTime_2584_ = lean_ctor_get(v_a_2579_, 2);
v_isSharedCheck_2598_ = !lean_is_exclusive(v_a_2579_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2586_ = v_a_2579_;
v_isShared_2587_ = v_isSharedCheck_2598_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_buildTime_2584_);
lean_inc(v_trace_2583_);
lean_inc(v_log_2580_);
lean_dec(v_a_2579_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2598_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2588_ = ((lean_object*)(l_Lake_Package_barrelFacetConfig___lam__1___closed__0));
v___x_2589_ = lean_string_append(v___x_2588_, v_a_2578_);
lean_dec_ref(v_a_2578_);
v___x_2590_ = 3;
v___x_2591_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2591_, 0, v___x_2589_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*1, v___x_2590_);
v___x_2592_ = lean_array_get_size(v_log_2580_);
v___x_2593_ = lean_array_push(v_log_2580_, v___x_2591_);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v___x_2593_);
v___x_2595_ = v___x_2586_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_trace_2583_);
lean_ctor_set(v_reuseFailAlloc_2597_, 2, v_buildTime_2584_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*3, v_action_2581_);
lean_ctor_set_uint8(v_reuseFailAlloc_2597_, sizeof(void*)*3 + 1, v_wantsRebuild_2582_);
v___x_2595_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2596_; 
v___x_2596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2592_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
return v___x_2596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object* v_baseName_2616_, lean_object* v___x_2617_, lean_object* v_success_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
uint8_t v_success_boxed_2626_; lean_object* v_res_2627_; 
v_success_boxed_2626_ = lean_unbox(v_success_2618_);
v_res_2627_ = l_Lake_Package_barrelFacetConfig___lam__1(v_baseName_2616_, v___x_2617_, v_success_boxed_2626_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* v___x_2628_, lean_object* v___x_2629_, lean_object* v___x_2630_, lean_object* v_pkg_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_baseName_2639_; lean_object* v_keyName_2640_; lean_object* v___f_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___f_2645_; lean_object* v___x_2646_; 
v_baseName_2639_ = lean_ctor_get(v_pkg_2631_, 1);
lean_inc_n(v_baseName_2639_, 2);
v_keyName_2640_ = lean_ctor_get(v_pkg_2631_, 2);
lean_inc(v___x_2628_);
v___f_2641_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2641_, 0, v_baseName_2639_);
lean_closure_set(v___f_2641_, 1, v___x_2628_);
lean_inc(v_keyName_2640_);
v___x_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2642_, 0, v_keyName_2640_);
v___x_2643_ = l_Lake_Package_keyword;
v___x_2644_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2642_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
lean_ctor_set(v___x_2644_, 2, v_pkg_2631_);
lean_ctor_set(v___x_2644_, 3, v___x_2628_);
lean_inc(v___x_2629_);
v___f_2645_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2645_, 0, v___x_2644_);
lean_closure_set(v___f_2645_, 1, v___x_2629_);
lean_closure_set(v___f_2645_, 2, v___f_2641_);
v___x_2646_ = l_Lake_ensureJob___redArg(v___x_2629_, v___f_2645_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2679_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
v_a_2648_ = lean_ctor_get(v___x_2646_, 1);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2650_ = v___x_2646_;
v_isShared_2651_ = v_isSharedCheck_2679_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_inc(v_a_2647_);
lean_dec(v___x_2646_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2679_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v_task_2652_; lean_object* v_kind_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2677_; 
v_task_2652_ = lean_ctor_get(v_a_2647_, 0);
v_kind_2653_ = lean_ctor_get(v_a_2647_, 1);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_a_2647_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; 
v_unused_2678_ = lean_ctor_get(v_a_2647_, 2);
lean_dec(v_unused_2678_);
v___x_2655_ = v_a_2647_;
v_isShared_2656_ = v_isSharedCheck_2677_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_kind_2653_);
lean_inc(v_task_2652_);
lean_dec(v_a_2647_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2677_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_registeredJobs_2657_; lean_object* v___x_2658_; uint8_t v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; lean_object* v_job_2668_; 
v_registeredJobs_2657_ = lean_ctor_get(v___y_2636_, 3);
v___x_2658_ = lean_st_ref_take(v_registeredJobs_2657_);
v___x_2659_ = 1;
v___x_2660_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2639_, v___x_2659_);
v___x_2661_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2662_ = lean_string_append(v___x_2660_, v___x_2661_);
v___x_2663_ = l_Lake_Name_eraseHead(v___x_2630_);
v___x_2664_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2663_, v___x_2659_);
v___x_2665_ = lean_string_append(v___x_2662_, v___x_2664_);
lean_dec_ref(v___x_2664_);
v___x_2666_ = 0;
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 2, v___x_2665_);
v_job_2668_ = v___x_2655_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_task_2652_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_kind_2653_);
lean_ctor_set(v_reuseFailAlloc_2676_, 2, v___x_2665_);
v_job_2668_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
lean_ctor_set_uint8(v_job_2668_, sizeof(void*)*3, v___x_2666_);
lean_inc_ref(v_job_2668_);
v___x_2669_ = l_Lake_Job_toOpaque___redArg(v_job_2668_);
v___x_2670_ = lean_array_push(v___x_2658_, v___x_2669_);
v___x_2671_ = lean_st_ref_put(v_registeredJobs_2657_, v___x_2670_);
v___x_2672_ = l_Lake_Job_renew___redArg(v_job_2668_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 0, v___x_2672_);
v___x_2674_ = v___x_2650_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_a_2648_);
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
else
{
lean_dec(v_baseName_2639_);
lean_dec(v___x_2630_);
return v___x_2646_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object* v___x_2680_, lean_object* v___x_2681_, lean_object* v___x_2682_, lean_object* v_pkg_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Lake_Package_barrelFacetConfig___lam__2(v___x_2680_, v___x_2681_, v___x_2682_, v_pkg_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v___y_2685_);
return v_res_2691_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___f_2695_; 
v___x_2692_ = l_Lake_Package_reservoirBarrelFacet;
v___x_2693_ = l_Lake_instDataKindUnit;
v___x_2694_ = l_Lake_Package_optReservoirBarrelFacet;
v___f_2695_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2695_, 0, v___x_2694_);
lean_closure_set(v___f_2695_, 1, v___x_2693_);
lean_closure_set(v___f_2695_, 2, v___x_2692_);
return v___f_2695_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2696_; uint8_t v___x_2697_; lean_object* v___x_2698_; lean_object* v___f_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___f_2696_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2697_ = 1;
v___x_2698_ = l_Lake_instDataKindUnit;
v___f_2699_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__0, &l_Lake_Package_barrelFacetConfig___closed__0_once, _init_l_Lake_Package_barrelFacetConfig___closed__0);
v___x_2700_ = l_Lake_Package_keyword;
v___x_2701_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
lean_ctor_set(v___x_2701_, 1, v___f_2699_);
lean_ctor_set(v___x_2701_, 2, v___x_2698_);
lean_ctor_set(v___x_2701_, 3, v___f_2696_);
lean_ctor_set_uint8(v___x_2701_, sizeof(void*)*4, v___x_2697_);
lean_ctor_set_uint8(v___x_2701_, sizeof(void*)*4 + 1, v___x_2697_);
return v___x_2701_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig(void){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__1, &l_Lake_Package_barrelFacetConfig___closed__1_once, _init_l_Lake_Package_barrelFacetConfig___closed__1);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object* v_pkg_2703_, lean_object* v___x_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
uint8_t v_r_2713_; lean_object* v___y_2714_; lean_object* v_a_2718_; lean_object* v___x_2734_; 
lean_inc_ref(v_pkg_2703_);
v___x_2734_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_pkg_2703_, v___y_2710_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v_a_2736_; lean_object* v_dir_2737_; lean_object* v_buildArchive_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
v_a_2736_ = lean_ctor_get(v___x_2734_, 1);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2734_, 2);
v_dir_2737_ = lean_ctor_get(v_pkg_2703_, 4);
v_buildArchive_2738_ = lean_ctor_get(v_pkg_2703_, 21);
v___x_2739_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_2737_);
v___x_2740_ = l_Lake_joinRelative(v_dir_2737_, v___x_2739_);
lean_inc_ref(v_buildArchive_2738_);
v___x_2741_ = l_Lake_joinRelative(v___x_2740_, v_buildArchive_2738_);
v___x_2742_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2703_, v_a_2735_, v___x_2741_, v___x_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v_a_2736_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; uint8_t v___x_2744_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 1);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2742_, 2);
v___x_2744_ = 1;
v_r_2713_ = v___x_2744_;
v___y_2714_ = v_a_2743_;
goto v___jp_2712_;
}
else
{
lean_object* v_a_2745_; 
v_a_2745_ = lean_ctor_get(v___x_2742_, 1);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2742_, 2);
v_a_2718_ = v_a_2745_;
goto v___jp_2717_;
}
}
else
{
lean_object* v_a_2746_; 
lean_dec_ref(v_pkg_2703_);
v_a_2746_ = lean_ctor_get(v___x_2734_, 1);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___x_2734_, 2);
v_a_2718_ = v_a_2746_;
goto v___jp_2717_;
}
v___jp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = lean_box(v_r_2713_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
lean_ctor_set(v___x_2716_, 1, v___y_2714_);
return v___x_2716_;
}
v___jp_2717_:
{
lean_object* v_log_2719_; uint8_t v_action_2720_; uint8_t v_wantsRebuild_2721_; lean_object* v_trace_2722_; lean_object* v_buildTime_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2733_; 
v_log_2719_ = lean_ctor_get(v_a_2718_, 0);
v_action_2720_ = lean_ctor_get_uint8(v_a_2718_, sizeof(void*)*3);
v_wantsRebuild_2721_ = lean_ctor_get_uint8(v_a_2718_, sizeof(void*)*3 + 1);
v_trace_2722_ = lean_ctor_get(v_a_2718_, 1);
v_buildTime_2723_ = lean_ctor_get(v_a_2718_, 2);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_a_2718_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2725_ = v_a_2718_;
v_isShared_2726_ = v_isSharedCheck_2733_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_buildTime_2723_);
lean_inc(v_trace_2722_);
lean_inc(v_log_2719_);
lean_dec(v_a_2718_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2733_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
uint8_t v___x_2727_; uint8_t v___x_2728_; lean_object* v___x_2730_; 
v___x_2727_ = 4;
v___x_2728_ = l_Lake_JobAction_merge(v_action_2720_, v___x_2727_);
if (v_isShared_2726_ == 0)
{
v___x_2730_ = v___x_2725_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_log_2719_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v_trace_2722_);
lean_ctor_set(v_reuseFailAlloc_2732_, 2, v_buildTime_2723_);
lean_ctor_set_uint8(v_reuseFailAlloc_2732_, sizeof(void*)*3 + 1, v_wantsRebuild_2721_);
v___x_2730_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
uint8_t v___x_2731_; 
lean_ctor_set_uint8(v___x_2730_, sizeof(void*)*3, v___x_2728_);
v___x_2731_ = 0;
v_r_2713_ = v___x_2731_;
v___y_2714_ = v___x_2730_;
goto v___jp_2712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object* v_pkg_2747_, lean_object* v___x_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(v_pkg_2747_, v___x_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec_ref(v___x_2748_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object* v___x_2757_, lean_object* v___x_2758_, lean_object* v___x_2759_, lean_object* v___x_2760_, lean_object* v_pkg_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v___f_2769_; lean_object* v___x_2770_; lean_object* v___f_2771_; lean_object* v___x_2772_; 
lean_inc_ref(v_pkg_2761_);
v___f_2769_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2769_, 0, v_pkg_2761_);
lean_closure_set(v___f_2769_, 1, v___x_2757_);
v___x_2770_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2758_);
v___f_2771_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2771_, 0, v___x_2758_);
lean_closure_set(v___f_2771_, 1, v___f_2769_);
lean_closure_set(v___f_2771_, 2, v___x_2759_);
lean_closure_set(v___f_2771_, 3, v___x_2770_);
v___x_2772_ = l_Lake_ensureJob___redArg(v___x_2758_, v___f_2771_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2805_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
v_a_2774_ = lean_ctor_get(v___x_2772_, 1);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2776_ = v___x_2772_;
v_isShared_2777_ = v_isSharedCheck_2805_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_inc(v_a_2773_);
lean_dec(v___x_2772_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2805_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v_task_2778_; lean_object* v_kind_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2803_; 
v_task_2778_ = lean_ctor_get(v_a_2773_, 0);
v_kind_2779_ = lean_ctor_get(v_a_2773_, 1);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_a_2773_);
if (v_isSharedCheck_2803_ == 0)
{
lean_object* v_unused_2804_; 
v_unused_2804_ = lean_ctor_get(v_a_2773_, 2);
lean_dec(v_unused_2804_);
v___x_2781_ = v_a_2773_;
v_isShared_2782_ = v_isSharedCheck_2803_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_kind_2779_);
lean_inc(v_task_2778_);
lean_dec(v_a_2773_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2803_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v_registeredJobs_2783_; lean_object* v___x_2784_; lean_object* v_baseName_2785_; uint8_t v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v_job_2794_; 
v_registeredJobs_2783_ = lean_ctor_get(v___y_2766_, 3);
v___x_2784_ = lean_st_ref_take(v_registeredJobs_2783_);
v_baseName_2785_ = lean_ctor_get(v_pkg_2761_, 1);
lean_inc(v_baseName_2785_);
lean_dec_ref(v_pkg_2761_);
v___x_2786_ = 1;
v___x_2787_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2785_, v___x_2786_);
v___x_2788_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2789_ = lean_string_append(v___x_2787_, v___x_2788_);
v___x_2790_ = l_Lake_Name_eraseHead(v___x_2760_);
v___x_2791_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2790_, v___x_2786_);
v___x_2792_ = lean_string_append(v___x_2789_, v___x_2791_);
lean_dec_ref(v___x_2791_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 2, v___x_2792_);
v_job_2794_ = v___x_2781_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_task_2778_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_kind_2779_);
lean_ctor_set(v_reuseFailAlloc_2802_, 2, v___x_2792_);
v_job_2794_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
lean_ctor_set_uint8(v_job_2794_, sizeof(void*)*3, v___x_2786_);
lean_inc_ref(v_job_2794_);
v___x_2795_ = l_Lake_Job_toOpaque___redArg(v_job_2794_);
v___x_2796_ = lean_array_push(v___x_2784_, v___x_2795_);
v___x_2797_ = lean_st_ref_put(v_registeredJobs_2783_, v___x_2796_);
v___x_2798_ = l_Lake_Job_renew___redArg(v_job_2794_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v___x_2798_);
v___x_2800_ = v___x_2776_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_a_2774_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_2761_);
lean_dec(v___x_2760_);
return v___x_2772_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_2806_, lean_object* v___x_2807_, lean_object* v___x_2808_, lean_object* v___x_2809_, lean_object* v_pkg_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(v___x_2806_, v___x_2807_, v___x_2808_, v___x_2809_, v_pkg_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec(v___y_2812_);
return v_res_2818_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___f_2825_; 
v___x_2821_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_2822_ = lean_unsigned_to_nat(0u);
v___x_2823_ = l_Lake_instDataKindBool;
v___x_2824_ = ((lean_object*)(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0));
v___f_2825_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2825_, 0, v___x_2824_);
lean_closure_set(v___f_2825_, 1, v___x_2823_);
lean_closure_set(v___f_2825_, 2, v___x_2822_);
lean_closure_set(v___f_2825_, 3, v___x_2821_);
return v___f_2825_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2826_; uint8_t v___x_2827_; lean_object* v___x_2828_; lean_object* v___f_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___f_2826_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_2827_ = 1;
v___x_2828_ = l_Lake_instDataKindBool;
v___f_2829_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__1, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1);
v___x_2830_ = l_Lake_Package_keyword;
v___x_2831_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2831_, 0, v___x_2830_);
lean_ctor_set(v___x_2831_, 1, v___f_2829_);
lean_ctor_set(v___x_2831_, 2, v___x_2828_);
lean_ctor_set(v___x_2831_, 3, v___f_2826_);
lean_ctor_set_uint8(v___x_2831_, sizeof(void*)*4, v___x_2827_);
lean_ctor_set_uint8(v___x_2831_, sizeof(void*)*4 + 1, v___x_2827_);
return v___x_2831_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_2832_; 
v___x_2832_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__2, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* v_baseName_2834_, lean_object* v___x_2835_, uint8_t v_success_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v_a_2845_; lean_object* v_a_2846_; 
if (v_success_2836_ == 0)
{
lean_object* v_toBuildConfig_2866_; uint8_t v_verbosity_2867_; uint8_t v___x_2868_; uint8_t v___x_2869_; 
v_toBuildConfig_2866_ = lean_ctor_get(v___y_2841_, 0);
v_verbosity_2867_ = lean_ctor_get_uint8(v_toBuildConfig_2866_, sizeof(void*)*4 + 3);
v___x_2868_ = 2;
v___x_2869_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2867_, v___x_2868_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; 
lean_dec(v___x_2835_);
lean_dec(v_baseName_2834_);
v___x_2870_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2845_ = v___x_2870_;
v_a_2846_ = v___y_2842_;
goto v___jp_2844_;
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2871_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2872_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2834_, v___x_2869_);
v___x_2873_ = lean_string_append(v___x_2871_, v___x_2872_);
lean_dec_ref(v___x_2872_);
v___x_2874_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2875_ = lean_string_append(v___x_2873_, v___x_2874_);
v___x_2876_ = l_Lake_Name_eraseHead(v___x_2835_);
v___x_2877_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2876_, v___x_2869_);
v___x_2878_ = lean_string_append(v___x_2875_, v___x_2877_);
lean_dec_ref(v___x_2877_);
v___x_2879_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2880_ = lean_string_append(v___x_2878_, v___x_2879_);
v_a_2845_ = v___x_2880_;
v_a_2846_ = v___y_2842_;
goto v___jp_2844_;
}
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
lean_dec(v___x_2835_);
lean_dec(v_baseName_2834_);
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v___y_2842_);
return v___x_2882_;
}
v___jp_2844_:
{
lean_object* v_log_2847_; uint8_t v_action_2848_; uint8_t v_wantsRebuild_2849_; lean_object* v_trace_2850_; lean_object* v_buildTime_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2865_; 
v_log_2847_ = lean_ctor_get(v_a_2846_, 0);
v_action_2848_ = lean_ctor_get_uint8(v_a_2846_, sizeof(void*)*3);
v_wantsRebuild_2849_ = lean_ctor_get_uint8(v_a_2846_, sizeof(void*)*3 + 1);
v_trace_2850_ = lean_ctor_get(v_a_2846_, 1);
v_buildTime_2851_ = lean_ctor_get(v_a_2846_, 2);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_a_2846_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2853_ = v_a_2846_;
v_isShared_2854_ = v_isSharedCheck_2865_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_buildTime_2851_);
lean_inc(v_trace_2850_);
lean_inc(v_log_2847_);
lean_dec(v_a_2846_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2865_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2862_; 
v___x_2855_ = ((lean_object*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0));
v___x_2856_ = lean_string_append(v___x_2855_, v_a_2845_);
lean_dec_ref(v_a_2845_);
v___x_2857_ = 3;
v___x_2858_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2858_, 0, v___x_2856_);
lean_ctor_set_uint8(v___x_2858_, sizeof(void*)*1, v___x_2857_);
v___x_2859_ = lean_array_get_size(v_log_2847_);
v___x_2860_ = lean_array_push(v_log_2847_, v___x_2858_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2860_);
v___x_2862_ = v___x_2853_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_trace_2850_);
lean_ctor_set(v_reuseFailAlloc_2864_, 2, v_buildTime_2851_);
lean_ctor_set_uint8(v_reuseFailAlloc_2864_, sizeof(void*)*3, v_action_2848_);
lean_ctor_set_uint8(v_reuseFailAlloc_2864_, sizeof(void*)*3 + 1, v_wantsRebuild_2849_);
v___x_2862_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2863_; 
v___x_2863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2859_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
return v___x_2863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object* v_baseName_2883_, lean_object* v___x_2884_, lean_object* v_success_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
uint8_t v_success_boxed_2893_; lean_object* v_res_2894_; 
v_success_boxed_2893_ = lean_unbox(v_success_2885_);
v_res_2894_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(v_baseName_2883_, v___x_2884_, v_success_boxed_2893_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* v___x_2895_, lean_object* v___x_2896_, lean_object* v___x_2897_, lean_object* v_pkg_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_baseName_2906_; lean_object* v_keyName_2907_; lean_object* v___f_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___f_2912_; lean_object* v___x_2913_; 
v_baseName_2906_ = lean_ctor_get(v_pkg_2898_, 1);
lean_inc_n(v_baseName_2906_, 2);
v_keyName_2907_ = lean_ctor_get(v_pkg_2898_, 2);
lean_inc(v___x_2895_);
v___f_2908_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2908_, 0, v_baseName_2906_);
lean_closure_set(v___f_2908_, 1, v___x_2895_);
lean_inc(v_keyName_2907_);
v___x_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2909_, 0, v_keyName_2907_);
v___x_2910_ = l_Lake_Package_keyword;
v___x_2911_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2909_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
lean_ctor_set(v___x_2911_, 2, v_pkg_2898_);
lean_ctor_set(v___x_2911_, 3, v___x_2895_);
lean_inc(v___x_2896_);
v___f_2912_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2912_, 0, v___x_2911_);
lean_closure_set(v___f_2912_, 1, v___x_2896_);
lean_closure_set(v___f_2912_, 2, v___f_2908_);
v___x_2913_ = l_Lake_ensureJob___redArg(v___x_2896_, v___f_2912_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2946_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
v_a_2915_ = lean_ctor_get(v___x_2913_, 1);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2917_ = v___x_2913_;
v_isShared_2918_ = v_isSharedCheck_2946_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_inc(v_a_2914_);
lean_dec(v___x_2913_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2946_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v_task_2919_; lean_object* v_kind_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2944_; 
v_task_2919_ = lean_ctor_get(v_a_2914_, 0);
v_kind_2920_ = lean_ctor_get(v_a_2914_, 1);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_a_2914_);
if (v_isSharedCheck_2944_ == 0)
{
lean_object* v_unused_2945_; 
v_unused_2945_ = lean_ctor_get(v_a_2914_, 2);
lean_dec(v_unused_2945_);
v___x_2922_ = v_a_2914_;
v_isShared_2923_ = v_isSharedCheck_2944_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_kind_2920_);
lean_inc(v_task_2919_);
lean_dec(v_a_2914_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2944_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v_registeredJobs_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; lean_object* v_job_2935_; 
v_registeredJobs_2924_ = lean_ctor_get(v___y_2903_, 3);
v___x_2925_ = lean_st_ref_take(v_registeredJobs_2924_);
v___x_2926_ = 1;
v___x_2927_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2906_, v___x_2926_);
v___x_2928_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2929_ = lean_string_append(v___x_2927_, v___x_2928_);
v___x_2930_ = l_Lake_Name_eraseHead(v___x_2897_);
v___x_2931_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2930_, v___x_2926_);
v___x_2932_ = lean_string_append(v___x_2929_, v___x_2931_);
lean_dec_ref(v___x_2931_);
v___x_2933_ = 0;
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 2, v___x_2932_);
v_job_2935_ = v___x_2922_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_task_2919_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_kind_2920_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v___x_2932_);
v_job_2935_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2941_; 
lean_ctor_set_uint8(v_job_2935_, sizeof(void*)*3, v___x_2933_);
lean_inc_ref(v_job_2935_);
v___x_2936_ = l_Lake_Job_toOpaque___redArg(v_job_2935_);
v___x_2937_ = lean_array_push(v___x_2925_, v___x_2936_);
v___x_2938_ = lean_st_ref_put(v_registeredJobs_2924_, v___x_2937_);
v___x_2939_ = l_Lake_Job_renew___redArg(v_job_2935_);
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 0, v___x_2939_);
v___x_2941_ = v___x_2917_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_a_2915_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2906_);
lean_dec(v___x_2897_);
return v___x_2913_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_2947_, lean_object* v___x_2948_, lean_object* v___x_2949_, lean_object* v_pkg_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(v___x_2947_, v___x_2948_, v___x_2949_, v_pkg_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec(v___y_2952_);
return v_res_2958_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___f_2962_; 
v___x_2959_ = l_Lake_Package_gitHubReleaseFacet;
v___x_2960_ = l_Lake_instDataKindUnit;
v___x_2961_ = l_Lake_Package_optGitHubReleaseFacet;
v___f_2962_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2962_, 0, v___x_2961_);
lean_closure_set(v___f_2962_, 1, v___x_2960_);
lean_closure_set(v___f_2962_, 2, v___x_2959_);
return v___f_2962_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2963_; uint8_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___f_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___f_2963_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2964_ = 1;
v___x_2965_ = l_Lake_instDataKindUnit;
v___f_2966_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__0, &l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0);
v___x_2967_ = l_Lake_Package_keyword;
v___x_2968_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
lean_ctor_set(v___x_2968_, 1, v___f_2966_);
lean_ctor_set(v___x_2968_, 2, v___x_2965_);
lean_ctor_set(v___x_2968_, 3, v___f_2963_);
lean_ctor_set_uint8(v___x_2968_, sizeof(void*)*4, v___x_2964_);
lean_ctor_set_uint8(v___x_2968_, sizeof(void*)*4 + 1, v___x_2964_);
return v___x_2968_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__1, &l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* v_build_2970_, uint8_t v_x_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_log_2979_; uint8_t v_action_2980_; uint8_t v_wantsRebuild_2981_; lean_object* v_buildTime_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2991_; 
v_log_2979_ = lean_ctor_get(v___y_2977_, 0);
v_action_2980_ = lean_ctor_get_uint8(v___y_2977_, sizeof(void*)*3);
v_wantsRebuild_2981_ = lean_ctor_get_uint8(v___y_2977_, sizeof(void*)*3 + 1);
v_buildTime_2982_ = lean_ctor_get(v___y_2977_, 2);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___y_2977_);
if (v_isSharedCheck_2991_ == 0)
{
lean_object* v_unused_2992_; 
v_unused_2992_ = lean_ctor_get(v___y_2977_, 1);
lean_dec(v_unused_2992_);
v___x_2984_ = v___y_2977_;
v_isShared_2985_ = v_isSharedCheck_2991_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_buildTime_2982_);
lean_inc(v_log_2979_);
lean_dec(v___y_2977_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2991_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2986_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 1, v___x_2986_);
v___x_2988_ = v___x_2984_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_log_2979_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v___x_2986_);
lean_ctor_set(v_reuseFailAlloc_2990_, 2, v_buildTime_2982_);
lean_ctor_set_uint8(v_reuseFailAlloc_2990_, sizeof(void*)*3, v_action_2980_);
lean_ctor_set_uint8(v_reuseFailAlloc_2990_, sizeof(void*)*3 + 1, v_wantsRebuild_2981_);
v___x_2988_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v___x_2989_; 
lean_inc_ref(v___y_2976_);
lean_inc(v___y_2975_);
lean_inc(v___y_2974_);
lean_inc(v___y_2973_);
v___x_2989_ = lean_apply_7(v_build_2970_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___x_2988_, lean_box(0));
return v___x_2989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* v_build_2993_, lean_object* v_x_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
uint8_t v_x_1923__boxed_3002_; lean_object* v_res_3003_; 
v_x_1923__boxed_3002_ = lean_unbox(v_x_2994_);
v_res_3003_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(v_build_2993_, v_x_1923__boxed_3002_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec(v___y_2996_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* v_self_3004_, lean_object* v_build_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v_wsIdx_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v_wsIdx_3013_ = lean_ctor_get(v_self_3004_, 0);
v___x_3014_ = lean_unsigned_to_nat(0u);
v___x_3015_ = lean_nat_dec_eq(v_wsIdx_3013_, v___x_3014_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; 
lean_inc_ref(v_a_3006_);
v___x_3016_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3004_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3029_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
v_a_3018_ = lean_ctor_get(v___x_3016_, 1);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3020_ = v___x_3016_;
v_isShared_3021_ = v_isSharedCheck_3029_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_inc(v_a_3017_);
lean_dec(v___x_3016_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3029_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___f_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3027_; 
v___f_3022_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3022_, 0, v_build_3005_);
v___x_3023_ = lean_box(0);
v___x_3024_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3025_ = l_Lake_Job_bindM___redArg(v___x_3023_, v_a_3017_, v___f_3022_, v___x_3014_, v___x_3015_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v___x_3024_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v___x_3025_);
v___x_3027_ = v___x_3020_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3025_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v_a_3018_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec_ref(v_a_3006_);
lean_dec_ref(v_build_3005_);
v_a_3030_ = lean_ctor_get(v___x_3016_, 0);
v_a_3031_ = lean_ctor_get(v___x_3016_, 1);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3016_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_inc(v_a_3030_);
lean_dec(v___x_3016_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3030_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
else
{
uint8_t v___x_3039_; uint8_t v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
lean_dec_ref(v_self_3004_);
v___x_3039_ = 0;
v___x_3040_ = 0;
v___x_3041_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3042_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3042_, 0, v_a_3011_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
lean_ctor_set(v___x_3042_, 2, v___x_3014_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*3, v___x_3039_);
lean_ctor_set_uint8(v___x_3042_, sizeof(void*)*3 + 1, v___x_3040_);
lean_inc_ref(v_a_3010_);
lean_inc(v_a_3009_);
lean_inc(v_a_3008_);
lean_inc(v_a_3007_);
v___x_3043_ = lean_apply_7(v_build_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v___x_3042_, lean_box(0));
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3053_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 1);
v_a_3045_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3047_ = v___x_3043_;
v_isShared_3048_ = v_isSharedCheck_3053_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3044_);
lean_inc(v_a_3045_);
lean_dec(v___x_3043_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3053_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v_log_3049_; lean_object* v___x_3051_; 
v_log_3049_ = lean_ctor_get(v_a_3044_, 0);
lean_inc_ref(v_log_3049_);
lean_dec(v_a_3044_);
if (v_isShared_3048_ == 0)
{
lean_ctor_set(v___x_3047_, 1, v_log_3049_);
v___x_3051_ = v___x_3047_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3045_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v_log_3049_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3063_; 
v_a_3054_ = lean_ctor_get(v___x_3043_, 1);
v_a_3055_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3057_ = v___x_3043_;
v_isShared_3058_ = v_isSharedCheck_3063_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3054_);
lean_inc(v_a_3055_);
lean_dec(v___x_3043_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3063_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v_log_3059_; lean_object* v___x_3061_; 
v_log_3059_ = lean_ctor_get(v_a_3054_, 0);
lean_inc_ref(v_log_3059_);
lean_dec(v_a_3054_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 1, v_log_3059_);
v___x_3061_ = v___x_3057_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3055_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v_log_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___boxed(lean_object* v_self_3064_, lean_object* v_build_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3064_, v_build_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
lean_dec_ref(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec(v_a_3067_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* v_00_u03b1_3074_, lean_object* v_self_3075_, lean_object* v_build_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3075_, v_build_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___boxed(lean_object* v_00_u03b1_3085_, lean_object* v_self_3086_, lean_object* v_build_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lake_Package_afterBuildCacheAsync(v_00_u03b1_3085_, v_self_3086_, v_build_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_a_3091_);
lean_dec(v_a_3090_);
lean_dec(v_a_3089_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* v_build_3096_, uint8_t v_x_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v_log_3105_; uint8_t v_action_3106_; uint8_t v_wantsRebuild_3107_; lean_object* v_buildTime_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3117_; 
v_log_3105_ = lean_ctor_get(v___y_3103_, 0);
v_action_3106_ = lean_ctor_get_uint8(v___y_3103_, sizeof(void*)*3);
v_wantsRebuild_3107_ = lean_ctor_get_uint8(v___y_3103_, sizeof(void*)*3 + 1);
v_buildTime_3108_ = lean_ctor_get(v___y_3103_, 2);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___y_3103_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v___y_3103_, 1);
lean_dec(v_unused_3118_);
v___x_3110_ = v___y_3103_;
v_isShared_3111_ = v_isSharedCheck_3117_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_buildTime_3108_);
lean_inc(v_log_3105_);
lean_dec(v___y_3103_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3117_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3112_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 1, v___x_3112_);
v___x_3114_ = v___x_3110_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_log_3105_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v___x_3112_);
lean_ctor_set(v_reuseFailAlloc_3116_, 2, v_buildTime_3108_);
lean_ctor_set_uint8(v_reuseFailAlloc_3116_, sizeof(void*)*3, v_action_3106_);
lean_ctor_set_uint8(v_reuseFailAlloc_3116_, sizeof(void*)*3 + 1, v_wantsRebuild_3107_);
v___x_3114_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3115_; 
lean_inc_ref(v___y_3102_);
lean_inc(v___y_3101_);
lean_inc(v___y_3100_);
lean_inc(v___y_3099_);
v___x_3115_ = lean_apply_7(v_build_3096_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___x_3114_, lean_box(0));
return v___x_3115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* v_build_3119_, lean_object* v_x_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
uint8_t v_x_1946__boxed_3128_; lean_object* v_res_3129_; 
v_x_1946__boxed_3128_ = lean_unbox(v_x_3120_);
v_res_3129_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(v_build_3119_, v_x_1946__boxed_3128_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec(v___y_3122_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* v_self_3130_, lean_object* v_build_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_){
_start:
{
lean_object* v_wsIdx_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
v_wsIdx_3139_ = lean_ctor_get(v_self_3130_, 0);
v___x_3140_ = lean_unsigned_to_nat(0u);
v___x_3141_ = lean_nat_dec_eq(v_wsIdx_3139_, v___x_3140_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; 
lean_inc_ref(v_a_3132_);
v___x_3142_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3130_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3155_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
v_a_3144_ = lean_ctor_get(v___x_3142_, 1);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3146_ = v___x_3142_;
v_isShared_3147_ = v_isSharedCheck_3155_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_inc(v_a_3143_);
lean_dec(v___x_3142_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3155_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___f_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3153_; 
v___f_3148_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3148_, 0, v_build_3131_);
v___x_3149_ = lean_box(0);
v___x_3150_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3151_ = l_Lake_Job_mapM___redArg(v___x_3149_, v_a_3143_, v___f_3148_, v___x_3140_, v___x_3141_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v___x_3150_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v___x_3151_);
v___x_3153_ = v___x_3146_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3151_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_a_3144_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
lean_dec_ref(v_a_3132_);
lean_dec_ref(v_build_3131_);
v_a_3156_ = lean_ctor_get(v___x_3142_, 0);
v_a_3157_ = lean_ctor_get(v___x_3142_, 1);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3142_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_inc(v_a_3156_);
lean_dec(v___x_3142_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3156_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
else
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
lean_dec_ref(v_self_3130_);
v___x_3165_ = lean_box(0);
v___x_3166_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_3167_ = l_Lake_Job_async___redArg(v___x_3165_, v_build_3131_, v___x_3140_, v___x_3166_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_);
v___x_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
lean_ctor_set(v___x_3168_, 1, v_a_3137_);
return v___x_3168_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___boxed(lean_object* v_self_3169_, lean_object* v_build_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3169_, v_build_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_);
lean_dec_ref(v_a_3175_);
lean_dec(v_a_3174_);
lean_dec(v_a_3173_);
lean_dec(v_a_3172_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* v_00_u03b1_3179_, lean_object* v_self_3180_, lean_object* v_build_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3180_, v_build_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___boxed(lean_object* v_00_u03b1_3190_, lean_object* v_self_3191_, lean_object* v_build_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l_Lake_Package_afterBuildCacheSync(v_00_u03b1_3190_, v_self_3191_, v_build_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec(v_a_3194_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(lean_object* v_k_3201_, lean_object* v_v_3202_, lean_object* v_t_3203_){
_start:
{
if (lean_obj_tag(v_t_3203_) == 0)
{
lean_object* v_size_3204_; lean_object* v_k_3205_; lean_object* v_v_3206_; lean_object* v_l_3207_; lean_object* v_r_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3488_; 
v_size_3204_ = lean_ctor_get(v_t_3203_, 0);
v_k_3205_ = lean_ctor_get(v_t_3203_, 1);
v_v_3206_ = lean_ctor_get(v_t_3203_, 2);
v_l_3207_ = lean_ctor_get(v_t_3203_, 3);
v_r_3208_ = lean_ctor_get(v_t_3203_, 4);
v_isSharedCheck_3488_ = !lean_is_exclusive(v_t_3203_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3210_ = v_t_3203_;
v_isShared_3211_ = v_isSharedCheck_3488_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_r_3208_);
lean_inc(v_l_3207_);
lean_inc(v_v_3206_);
lean_inc(v_k_3205_);
lean_inc(v_size_3204_);
lean_dec(v_t_3203_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3488_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
uint8_t v___x_3212_; 
v___x_3212_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3201_, v_k_3205_);
switch(v___x_3212_)
{
case 0:
{
lean_object* v_impl_3213_; lean_object* v___x_3214_; 
lean_dec(v_size_3204_);
v_impl_3213_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3201_, v_v_3202_, v_l_3207_);
v___x_3214_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3208_) == 0)
{
lean_object* v_size_3215_; lean_object* v_size_3216_; lean_object* v_k_3217_; lean_object* v_v_3218_; lean_object* v_l_3219_; lean_object* v_r_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; 
v_size_3215_ = lean_ctor_get(v_r_3208_, 0);
v_size_3216_ = lean_ctor_get(v_impl_3213_, 0);
lean_inc(v_size_3216_);
v_k_3217_ = lean_ctor_get(v_impl_3213_, 1);
lean_inc(v_k_3217_);
v_v_3218_ = lean_ctor_get(v_impl_3213_, 2);
lean_inc(v_v_3218_);
v_l_3219_ = lean_ctor_get(v_impl_3213_, 3);
lean_inc(v_l_3219_);
v_r_3220_ = lean_ctor_get(v_impl_3213_, 4);
lean_inc(v_r_3220_);
v___x_3221_ = lean_unsigned_to_nat(3u);
v___x_3222_ = lean_nat_mul(v___x_3221_, v_size_3215_);
v___x_3223_ = lean_nat_dec_lt(v___x_3222_, v_size_3216_);
lean_dec(v___x_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3227_; 
lean_dec(v_r_3220_);
lean_dec(v_l_3219_);
lean_dec(v_v_3218_);
lean_dec(v_k_3217_);
v___x_3224_ = lean_nat_add(v___x_3214_, v_size_3216_);
lean_dec(v_size_3216_);
v___x_3225_ = lean_nat_add(v___x_3224_, v_size_3215_);
lean_dec(v___x_3224_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 3, v_impl_3213_);
lean_ctor_set(v___x_3210_, 0, v___x_3225_);
v___x_3227_ = v___x_3210_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3225_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v_impl_3213_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v_r_3208_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
else
{
lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3294_; 
v_isSharedCheck_3294_ = !lean_is_exclusive(v_impl_3213_);
if (v_isSharedCheck_3294_ == 0)
{
lean_object* v_unused_3295_; lean_object* v_unused_3296_; lean_object* v_unused_3297_; lean_object* v_unused_3298_; lean_object* v_unused_3299_; 
v_unused_3295_ = lean_ctor_get(v_impl_3213_, 4);
lean_dec(v_unused_3295_);
v_unused_3296_ = lean_ctor_get(v_impl_3213_, 3);
lean_dec(v_unused_3296_);
v_unused_3297_ = lean_ctor_get(v_impl_3213_, 2);
lean_dec(v_unused_3297_);
v_unused_3298_ = lean_ctor_get(v_impl_3213_, 1);
lean_dec(v_unused_3298_);
v_unused_3299_ = lean_ctor_get(v_impl_3213_, 0);
lean_dec(v_unused_3299_);
v___x_3230_ = v_impl_3213_;
v_isShared_3231_ = v_isSharedCheck_3294_;
goto v_resetjp_3229_;
}
else
{
lean_dec(v_impl_3213_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3294_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v_size_3232_; lean_object* v_size_3233_; lean_object* v_k_3234_; lean_object* v_v_3235_; lean_object* v_l_3236_; lean_object* v_r_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; uint8_t v___x_3240_; 
v_size_3232_ = lean_ctor_get(v_l_3219_, 0);
v_size_3233_ = lean_ctor_get(v_r_3220_, 0);
v_k_3234_ = lean_ctor_get(v_r_3220_, 1);
v_v_3235_ = lean_ctor_get(v_r_3220_, 2);
v_l_3236_ = lean_ctor_get(v_r_3220_, 3);
v_r_3237_ = lean_ctor_get(v_r_3220_, 4);
v___x_3238_ = lean_unsigned_to_nat(2u);
v___x_3239_ = lean_nat_mul(v___x_3238_, v_size_3232_);
v___x_3240_ = lean_nat_dec_lt(v_size_3233_, v___x_3239_);
lean_dec(v___x_3239_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3269_; 
lean_inc(v_r_3237_);
lean_inc(v_l_3236_);
lean_inc(v_v_3235_);
lean_inc(v_k_3234_);
v_isSharedCheck_3269_ = !lean_is_exclusive(v_r_3220_);
if (v_isSharedCheck_3269_ == 0)
{
lean_object* v_unused_3270_; lean_object* v_unused_3271_; lean_object* v_unused_3272_; lean_object* v_unused_3273_; lean_object* v_unused_3274_; 
v_unused_3270_ = lean_ctor_get(v_r_3220_, 4);
lean_dec(v_unused_3270_);
v_unused_3271_ = lean_ctor_get(v_r_3220_, 3);
lean_dec(v_unused_3271_);
v_unused_3272_ = lean_ctor_get(v_r_3220_, 2);
lean_dec(v_unused_3272_);
v_unused_3273_ = lean_ctor_get(v_r_3220_, 1);
lean_dec(v_unused_3273_);
v_unused_3274_ = lean_ctor_get(v_r_3220_, 0);
lean_dec(v_unused_3274_);
v___x_3242_ = v_r_3220_;
v_isShared_3243_ = v_isSharedCheck_3269_;
goto v_resetjp_3241_;
}
else
{
lean_dec(v_r_3220_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3269_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___x_3257_; lean_object* v___y_3259_; 
v___x_3244_ = lean_nat_add(v___x_3214_, v_size_3216_);
lean_dec(v_size_3216_);
v___x_3245_ = lean_nat_add(v___x_3244_, v_size_3215_);
lean_dec(v___x_3244_);
v___x_3257_ = lean_nat_add(v___x_3214_, v_size_3232_);
if (lean_obj_tag(v_l_3236_) == 0)
{
lean_object* v_size_3267_; 
v_size_3267_ = lean_ctor_get(v_l_3236_, 0);
lean_inc(v_size_3267_);
v___y_3259_ = v_size_3267_;
goto v___jp_3258_;
}
else
{
lean_object* v___x_3268_; 
v___x_3268_ = lean_unsigned_to_nat(0u);
v___y_3259_ = v___x_3268_;
goto v___jp_3258_;
}
v___jp_3246_:
{
lean_object* v___x_3250_; lean_object* v___x_3252_; 
v___x_3250_ = lean_nat_add(v___y_3247_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec(v___y_3247_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 4, v_r_3208_);
lean_ctor_set(v___x_3242_, 3, v_r_3237_);
lean_ctor_set(v___x_3242_, 2, v_v_3206_);
lean_ctor_set(v___x_3242_, 1, v_k_3205_);
lean_ctor_set(v___x_3242_, 0, v___x_3250_);
v___x_3252_ = v___x_3242_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3250_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3256_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3256_, 3, v_r_3237_);
lean_ctor_set(v_reuseFailAlloc_3256_, 4, v_r_3208_);
v___x_3252_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3254_; 
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 4, v___x_3252_);
lean_ctor_set(v___x_3230_, 3, v___y_3248_);
lean_ctor_set(v___x_3230_, 2, v_v_3235_);
lean_ctor_set(v___x_3230_, 1, v_k_3234_);
lean_ctor_set(v___x_3230_, 0, v___x_3245_);
v___x_3254_ = v___x_3230_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v_k_3234_);
lean_ctor_set(v_reuseFailAlloc_3255_, 2, v_v_3235_);
lean_ctor_set(v_reuseFailAlloc_3255_, 3, v___y_3248_);
lean_ctor_set(v_reuseFailAlloc_3255_, 4, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
v___jp_3258_:
{
lean_object* v___x_3260_; lean_object* v___x_3262_; 
v___x_3260_ = lean_nat_add(v___x_3257_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec(v___x_3257_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 4, v_l_3236_);
lean_ctor_set(v___x_3210_, 3, v_l_3219_);
lean_ctor_set(v___x_3210_, 2, v_v_3218_);
lean_ctor_set(v___x_3210_, 1, v_k_3217_);
lean_ctor_set(v___x_3210_, 0, v___x_3260_);
v___x_3262_ = v___x_3210_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3260_);
lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_k_3217_);
lean_ctor_set(v_reuseFailAlloc_3266_, 2, v_v_3218_);
lean_ctor_set(v_reuseFailAlloc_3266_, 3, v_l_3219_);
lean_ctor_set(v_reuseFailAlloc_3266_, 4, v_l_3236_);
v___x_3262_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
lean_object* v___x_3263_; 
v___x_3263_ = lean_nat_add(v___x_3214_, v_size_3215_);
if (lean_obj_tag(v_r_3237_) == 0)
{
lean_object* v_size_3264_; 
v_size_3264_ = lean_ctor_get(v_r_3237_, 0);
lean_inc(v_size_3264_);
v___y_3247_ = v___x_3263_;
v___y_3248_ = v___x_3262_;
v___y_3249_ = v_size_3264_;
goto v___jp_3246_;
}
else
{
lean_object* v___x_3265_; 
v___x_3265_ = lean_unsigned_to_nat(0u);
v___y_3247_ = v___x_3263_;
v___y_3248_ = v___x_3262_;
v___y_3249_ = v___x_3265_;
goto v___jp_3246_;
}
}
}
}
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3280_; 
lean_del_object(v___x_3210_);
v___x_3275_ = lean_nat_add(v___x_3214_, v_size_3216_);
lean_dec(v_size_3216_);
v___x_3276_ = lean_nat_add(v___x_3275_, v_size_3215_);
lean_dec(v___x_3275_);
v___x_3277_ = lean_nat_add(v___x_3214_, v_size_3215_);
v___x_3278_ = lean_nat_add(v___x_3277_, v_size_3233_);
lean_dec(v___x_3277_);
lean_inc_ref(v_r_3208_);
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 4, v_r_3208_);
lean_ctor_set(v___x_3230_, 3, v_r_3220_);
lean_ctor_set(v___x_3230_, 2, v_v_3206_);
lean_ctor_set(v___x_3230_, 1, v_k_3205_);
lean_ctor_set(v___x_3230_, 0, v___x_3278_);
v___x_3280_ = v___x_3230_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___x_3278_);
lean_ctor_set(v_reuseFailAlloc_3293_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3293_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3293_, 3, v_r_3220_);
lean_ctor_set(v_reuseFailAlloc_3293_, 4, v_r_3208_);
v___x_3280_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
v_isSharedCheck_3287_ = !lean_is_exclusive(v_r_3208_);
if (v_isSharedCheck_3287_ == 0)
{
lean_object* v_unused_3288_; lean_object* v_unused_3289_; lean_object* v_unused_3290_; lean_object* v_unused_3291_; lean_object* v_unused_3292_; 
v_unused_3288_ = lean_ctor_get(v_r_3208_, 4);
lean_dec(v_unused_3288_);
v_unused_3289_ = lean_ctor_get(v_r_3208_, 3);
lean_dec(v_unused_3289_);
v_unused_3290_ = lean_ctor_get(v_r_3208_, 2);
lean_dec(v_unused_3290_);
v_unused_3291_ = lean_ctor_get(v_r_3208_, 1);
lean_dec(v_unused_3291_);
v_unused_3292_ = lean_ctor_get(v_r_3208_, 0);
lean_dec(v_unused_3292_);
v___x_3282_ = v_r_3208_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_dec(v_r_3208_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 4, v___x_3280_);
lean_ctor_set(v___x_3282_, 3, v_l_3219_);
lean_ctor_set(v___x_3282_, 2, v_v_3218_);
lean_ctor_set(v___x_3282_, 1, v_k_3217_);
lean_ctor_set(v___x_3282_, 0, v___x_3276_);
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3276_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_k_3217_);
lean_ctor_set(v_reuseFailAlloc_3286_, 2, v_v_3218_);
lean_ctor_set(v_reuseFailAlloc_3286_, 3, v_l_3219_);
lean_ctor_set(v_reuseFailAlloc_3286_, 4, v___x_3280_);
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
}
}
}
else
{
lean_object* v_l_3300_; 
v_l_3300_ = lean_ctor_get(v_impl_3213_, 3);
lean_inc(v_l_3300_);
if (lean_obj_tag(v_l_3300_) == 0)
{
lean_object* v_r_3301_; lean_object* v_k_3302_; lean_object* v_v_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3314_; 
v_r_3301_ = lean_ctor_get(v_impl_3213_, 4);
v_k_3302_ = lean_ctor_get(v_impl_3213_, 1);
v_v_3303_ = lean_ctor_get(v_impl_3213_, 2);
v_isSharedCheck_3314_ = !lean_is_exclusive(v_impl_3213_);
if (v_isSharedCheck_3314_ == 0)
{
lean_object* v_unused_3315_; lean_object* v_unused_3316_; 
v_unused_3315_ = lean_ctor_get(v_impl_3213_, 3);
lean_dec(v_unused_3315_);
v_unused_3316_ = lean_ctor_get(v_impl_3213_, 0);
lean_dec(v_unused_3316_);
v___x_3305_ = v_impl_3213_;
v_isShared_3306_ = v_isSharedCheck_3314_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_r_3301_);
lean_inc(v_v_3303_);
lean_inc(v_k_3302_);
lean_dec(v_impl_3213_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3314_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3307_; lean_object* v___x_3309_; 
v___x_3307_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3301_);
if (v_isShared_3306_ == 0)
{
lean_ctor_set(v___x_3305_, 3, v_r_3301_);
lean_ctor_set(v___x_3305_, 2, v_v_3206_);
lean_ctor_set(v___x_3305_, 1, v_k_3205_);
lean_ctor_set(v___x_3305_, 0, v___x_3214_);
v___x_3309_ = v___x_3305_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3313_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3313_, 3, v_r_3301_);
lean_ctor_set(v_reuseFailAlloc_3313_, 4, v_r_3301_);
v___x_3309_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
lean_object* v___x_3311_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 4, v___x_3309_);
lean_ctor_set(v___x_3210_, 3, v_l_3300_);
lean_ctor_set(v___x_3210_, 2, v_v_3303_);
lean_ctor_set(v___x_3210_, 1, v_k_3302_);
lean_ctor_set(v___x_3210_, 0, v___x_3307_);
v___x_3311_ = v___x_3210_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3307_);
lean_ctor_set(v_reuseFailAlloc_3312_, 1, v_k_3302_);
lean_ctor_set(v_reuseFailAlloc_3312_, 2, v_v_3303_);
lean_ctor_set(v_reuseFailAlloc_3312_, 3, v_l_3300_);
lean_ctor_set(v_reuseFailAlloc_3312_, 4, v___x_3309_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
else
{
lean_object* v_r_3317_; 
v_r_3317_ = lean_ctor_get(v_impl_3213_, 4);
lean_inc(v_r_3317_);
if (lean_obj_tag(v_r_3317_) == 0)
{
lean_object* v_k_3318_; lean_object* v_v_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3342_; 
v_k_3318_ = lean_ctor_get(v_impl_3213_, 1);
v_v_3319_ = lean_ctor_get(v_impl_3213_, 2);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_impl_3213_);
if (v_isSharedCheck_3342_ == 0)
{
lean_object* v_unused_3343_; lean_object* v_unused_3344_; lean_object* v_unused_3345_; 
v_unused_3343_ = lean_ctor_get(v_impl_3213_, 4);
lean_dec(v_unused_3343_);
v_unused_3344_ = lean_ctor_get(v_impl_3213_, 3);
lean_dec(v_unused_3344_);
v_unused_3345_ = lean_ctor_get(v_impl_3213_, 0);
lean_dec(v_unused_3345_);
v___x_3321_ = v_impl_3213_;
v_isShared_3322_ = v_isSharedCheck_3342_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_v_3319_);
lean_inc(v_k_3318_);
lean_dec(v_impl_3213_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3342_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v_k_3323_; lean_object* v_v_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3338_; 
v_k_3323_ = lean_ctor_get(v_r_3317_, 1);
v_v_3324_ = lean_ctor_get(v_r_3317_, 2);
v_isSharedCheck_3338_ = !lean_is_exclusive(v_r_3317_);
if (v_isSharedCheck_3338_ == 0)
{
lean_object* v_unused_3339_; lean_object* v_unused_3340_; lean_object* v_unused_3341_; 
v_unused_3339_ = lean_ctor_get(v_r_3317_, 4);
lean_dec(v_unused_3339_);
v_unused_3340_ = lean_ctor_get(v_r_3317_, 3);
lean_dec(v_unused_3340_);
v_unused_3341_ = lean_ctor_get(v_r_3317_, 0);
lean_dec(v_unused_3341_);
v___x_3326_ = v_r_3317_;
v_isShared_3327_ = v_isSharedCheck_3338_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_v_3324_);
lean_inc(v_k_3323_);
lean_dec(v_r_3317_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3338_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3328_; lean_object* v___x_3330_; 
v___x_3328_ = lean_unsigned_to_nat(3u);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 4, v_l_3300_);
lean_ctor_set(v___x_3326_, 3, v_l_3300_);
lean_ctor_set(v___x_3326_, 2, v_v_3319_);
lean_ctor_set(v___x_3326_, 1, v_k_3318_);
lean_ctor_set(v___x_3326_, 0, v___x_3214_);
v___x_3330_ = v___x_3326_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3337_, 1, v_k_3318_);
lean_ctor_set(v_reuseFailAlloc_3337_, 2, v_v_3319_);
lean_ctor_set(v_reuseFailAlloc_3337_, 3, v_l_3300_);
lean_ctor_set(v_reuseFailAlloc_3337_, 4, v_l_3300_);
v___x_3330_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3332_; 
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 4, v_l_3300_);
lean_ctor_set(v___x_3321_, 2, v_v_3206_);
lean_ctor_set(v___x_3321_, 1, v_k_3205_);
lean_ctor_set(v___x_3321_, 0, v___x_3214_);
v___x_3332_ = v___x_3321_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3336_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3336_, 3, v_l_3300_);
lean_ctor_set(v_reuseFailAlloc_3336_, 4, v_l_3300_);
v___x_3332_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
lean_object* v___x_3334_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 4, v___x_3332_);
lean_ctor_set(v___x_3210_, 3, v___x_3330_);
lean_ctor_set(v___x_3210_, 2, v_v_3324_);
lean_ctor_set(v___x_3210_, 1, v_k_3323_);
lean_ctor_set(v___x_3210_, 0, v___x_3328_);
v___x_3334_ = v___x_3210_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_k_3323_);
lean_ctor_set(v_reuseFailAlloc_3335_, 2, v_v_3324_);
lean_ctor_set(v_reuseFailAlloc_3335_, 3, v___x_3330_);
lean_ctor_set(v_reuseFailAlloc_3335_, 4, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3346_ = lean_unsigned_to_nat(2u);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 4, v_r_3317_);
lean_ctor_set(v___x_3210_, 3, v_impl_3213_);
lean_ctor_set(v___x_3210_, 0, v___x_3346_);
v___x_3348_ = v___x_3210_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3349_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3349_, 3, v_impl_3213_);
lean_ctor_set(v_reuseFailAlloc_3349_, 4, v_r_3317_);
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
case 1:
{
lean_object* v___x_3351_; 
lean_dec(v_v_3206_);
lean_dec(v_k_3205_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 2, v_v_3202_);
lean_ctor_set(v___x_3210_, 1, v_k_3201_);
v___x_3351_ = v___x_3210_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_size_3204_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_k_3201_);
lean_ctor_set(v_reuseFailAlloc_3352_, 2, v_v_3202_);
lean_ctor_set(v_reuseFailAlloc_3352_, 3, v_l_3207_);
lean_ctor_set(v_reuseFailAlloc_3352_, 4, v_r_3208_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
default: 
{
lean_object* v_impl_3353_; lean_object* v___x_3354_; 
lean_dec(v_size_3204_);
v_impl_3353_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3201_, v_v_3202_, v_r_3208_);
v___x_3354_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3207_) == 0)
{
lean_object* v_size_3355_; lean_object* v_size_3356_; lean_object* v_k_3357_; lean_object* v_v_3358_; lean_object* v_l_3359_; lean_object* v_r_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_size_3355_ = lean_ctor_get(v_l_3207_, 0);
v_size_3356_ = lean_ctor_get(v_impl_3353_, 0);
lean_inc(v_size_3356_);
v_k_3357_ = lean_ctor_get(v_impl_3353_, 1);
lean_inc(v_k_3357_);
v_v_3358_ = lean_ctor_get(v_impl_3353_, 2);
lean_inc(v_v_3358_);
v_l_3359_ = lean_ctor_get(v_impl_3353_, 3);
lean_inc(v_l_3359_);
v_r_3360_ = lean_ctor_get(v_impl_3353_, 4);
lean_inc(v_r_3360_);
v___x_3361_ = lean_unsigned_to_nat(3u);
v___x_3362_ = lean_nat_mul(v___x_3361_, v_size_3355_);
v___x_3363_ = lean_nat_dec_lt(v___x_3362_, v_size_3356_);
lean_dec(v___x_3362_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3367_; 
lean_dec(v_r_3360_);
lean_dec(v_l_3359_);
lean_dec(v_v_3358_);
lean_dec(v_k_3357_);
v___x_3364_ = lean_nat_add(v___x_3354_, v_size_3355_);
v___x_3365_ = lean_nat_add(v___x_3364_, v_size_3356_);
lean_dec(v_size_3356_);
lean_dec(v___x_3364_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 4, v_impl_3353_);
lean_ctor_set(v___x_3210_, 0, v___x_3365_);
v___x_3367_ = v___x_3210_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3365_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3368_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3368_, 3, v_l_3207_);
lean_ctor_set(v_reuseFailAlloc_3368_, 4, v_impl_3353_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
else
{
lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3432_; 
v_isSharedCheck_3432_ = !lean_is_exclusive(v_impl_3353_);
if (v_isSharedCheck_3432_ == 0)
{
lean_object* v_unused_3433_; lean_object* v_unused_3434_; lean_object* v_unused_3435_; lean_object* v_unused_3436_; lean_object* v_unused_3437_; 
v_unused_3433_ = lean_ctor_get(v_impl_3353_, 4);
lean_dec(v_unused_3433_);
v_unused_3434_ = lean_ctor_get(v_impl_3353_, 3);
lean_dec(v_unused_3434_);
v_unused_3435_ = lean_ctor_get(v_impl_3353_, 2);
lean_dec(v_unused_3435_);
v_unused_3436_ = lean_ctor_get(v_impl_3353_, 1);
lean_dec(v_unused_3436_);
v_unused_3437_ = lean_ctor_get(v_impl_3353_, 0);
lean_dec(v_unused_3437_);
v___x_3370_ = v_impl_3353_;
v_isShared_3371_ = v_isSharedCheck_3432_;
goto v_resetjp_3369_;
}
else
{
lean_dec(v_impl_3353_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3432_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v_size_3372_; lean_object* v_k_3373_; lean_object* v_v_3374_; lean_object* v_l_3375_; lean_object* v_r_3376_; lean_object* v_size_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
v_size_3372_ = lean_ctor_get(v_l_3359_, 0);
v_k_3373_ = lean_ctor_get(v_l_3359_, 1);
v_v_3374_ = lean_ctor_get(v_l_3359_, 2);
v_l_3375_ = lean_ctor_get(v_l_3359_, 3);
v_r_3376_ = lean_ctor_get(v_l_3359_, 4);
v_size_3377_ = lean_ctor_get(v_r_3360_, 0);
v___x_3378_ = lean_unsigned_to_nat(2u);
v___x_3379_ = lean_nat_mul(v___x_3378_, v_size_3377_);
v___x_3380_ = lean_nat_dec_lt(v_size_3372_, v___x_3379_);
lean_dec(v___x_3379_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3408_; 
lean_inc(v_r_3376_);
lean_inc(v_l_3375_);
lean_inc(v_v_3374_);
lean_inc(v_k_3373_);
v_isSharedCheck_3408_ = !lean_is_exclusive(v_l_3359_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; lean_object* v_unused_3410_; lean_object* v_unused_3411_; lean_object* v_unused_3412_; lean_object* v_unused_3413_; 
v_unused_3409_ = lean_ctor_get(v_l_3359_, 4);
lean_dec(v_unused_3409_);
v_unused_3410_ = lean_ctor_get(v_l_3359_, 3);
lean_dec(v_unused_3410_);
v_unused_3411_ = lean_ctor_get(v_l_3359_, 2);
lean_dec(v_unused_3411_);
v_unused_3412_ = lean_ctor_get(v_l_3359_, 1);
lean_dec(v_unused_3412_);
v_unused_3413_ = lean_ctor_get(v_l_3359_, 0);
lean_dec(v_unused_3413_);
v___x_3382_ = v_l_3359_;
v_isShared_3383_ = v_isSharedCheck_3408_;
goto v_resetjp_3381_;
}
else
{
lean_dec(v_l_3359_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3408_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3398_; 
v___x_3384_ = lean_nat_add(v___x_3354_, v_size_3355_);
v___x_3385_ = lean_nat_add(v___x_3384_, v_size_3356_);
lean_dec(v_size_3356_);
if (lean_obj_tag(v_l_3375_) == 0)
{
lean_object* v_size_3406_; 
v_size_3406_ = lean_ctor_get(v_l_3375_, 0);
lean_inc(v_size_3406_);
v___y_3398_ = v_size_3406_;
goto v___jp_3397_;
}
else
{
lean_object* v___x_3407_; 
v___x_3407_ = lean_unsigned_to_nat(0u);
v___y_3398_ = v___x_3407_;
goto v___jp_3397_;
}
v___jp_3386_:
{
lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3390_ = lean_nat_add(v___y_3388_, v___y_3389_);
lean_dec(v___y_3389_);
lean_dec(v___y_3388_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 4, v_r_3360_);
lean_ctor_set(v___x_3382_, 3, v_r_3376_);
lean_ctor_set(v___x_3382_, 2, v_v_3358_);
lean_ctor_set(v___x_3382_, 1, v_k_3357_);
lean_ctor_set(v___x_3382_, 0, v___x_3390_);
v___x_3392_ = v___x_3382_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3390_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_k_3357_);
lean_ctor_set(v_reuseFailAlloc_3396_, 2, v_v_3358_);
lean_ctor_set(v_reuseFailAlloc_3396_, 3, v_r_3376_);
lean_ctor_set(v_reuseFailAlloc_3396_, 4, v_r_3360_);
v___x_3392_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3394_; 
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 4, v___x_3392_);
lean_ctor_set(v___x_3370_, 3, v___y_3387_);
lean_ctor_set(v___x_3370_, 2, v_v_3374_);
lean_ctor_set(v___x_3370_, 1, v_k_3373_);
lean_ctor_set(v___x_3370_, 0, v___x_3385_);
v___x_3394_ = v___x_3370_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3385_);
lean_ctor_set(v_reuseFailAlloc_3395_, 1, v_k_3373_);
lean_ctor_set(v_reuseFailAlloc_3395_, 2, v_v_3374_);
lean_ctor_set(v_reuseFailAlloc_3395_, 3, v___y_3387_);
lean_ctor_set(v_reuseFailAlloc_3395_, 4, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
v___jp_3397_:
{
lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3399_ = lean_nat_add(v___x_3384_, v___y_3398_);
lean_dec(v___y_3398_);
lean_dec(v___x_3384_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 4, v_l_3375_);
lean_ctor_set(v___x_3210_, 0, v___x_3399_);
v___x_3401_ = v___x_3210_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3405_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3405_, 3, v_l_3207_);
lean_ctor_set(v_reuseFailAlloc_3405_, 4, v_l_3375_);
v___x_3401_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3402_; 
v___x_3402_ = lean_nat_add(v___x_3354_, v_size_3377_);
if (lean_obj_tag(v_r_3376_) == 0)
{
lean_object* v_size_3403_; 
v_size_3403_ = lean_ctor_get(v_r_3376_, 0);
lean_inc(v_size_3403_);
v___y_3387_ = v___x_3401_;
v___y_3388_ = v___x_3402_;
v___y_3389_ = v_size_3403_;
goto v___jp_3386_;
}
else
{
lean_object* v___x_3404_; 
v___x_3404_ = lean_unsigned_to_nat(0u);
v___y_3387_ = v___x_3401_;
v___y_3388_ = v___x_3402_;
v___y_3389_ = v___x_3404_;
goto v___jp_3386_;
}
}
}
}
}
else
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3418_; 
lean_del_object(v___x_3210_);
v___x_3414_ = lean_nat_add(v___x_3354_, v_size_3355_);
v___x_3415_ = lean_nat_add(v___x_3414_, v_size_3356_);
lean_dec(v_size_3356_);
v___x_3416_ = lean_nat_add(v___x_3414_, v_size_3372_);
lean_dec(v___x_3414_);
lean_inc_ref(v_l_3207_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 4, v_l_3359_);
lean_ctor_set(v___x_3370_, 3, v_l_3207_);
lean_ctor_set(v___x_3370_, 2, v_v_3206_);
lean_ctor_set(v___x_3370_, 1, v_k_3205_);
lean_ctor_set(v___x_3370_, 0, v___x_3416_);
v___x_3418_ = v___x_3370_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3416_);
lean_ctor_set(v_reuseFailAlloc_3431_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3431_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3431_, 3, v_l_3207_);
lean_ctor_set(v_reuseFailAlloc_3431_, 4, v_l_3359_);
v___x_3418_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
v_isSharedCheck_3425_ = !lean_is_exclusive(v_l_3207_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; lean_object* v_unused_3427_; lean_object* v_unused_3428_; lean_object* v_unused_3429_; lean_object* v_unused_3430_; 
v_unused_3426_ = lean_ctor_get(v_l_3207_, 4);
lean_dec(v_unused_3426_);
v_unused_3427_ = lean_ctor_get(v_l_3207_, 3);
lean_dec(v_unused_3427_);
v_unused_3428_ = lean_ctor_get(v_l_3207_, 2);
lean_dec(v_unused_3428_);
v_unused_3429_ = lean_ctor_get(v_l_3207_, 1);
lean_dec(v_unused_3429_);
v_unused_3430_ = lean_ctor_get(v_l_3207_, 0);
lean_dec(v_unused_3430_);
v___x_3420_ = v_l_3207_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_dec(v_l_3207_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 4, v_r_3360_);
lean_ctor_set(v___x_3420_, 3, v___x_3418_);
lean_ctor_set(v___x_3420_, 2, v_v_3358_);
lean_ctor_set(v___x_3420_, 1, v_k_3357_);
lean_ctor_set(v___x_3420_, 0, v___x_3415_);
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_k_3357_);
lean_ctor_set(v_reuseFailAlloc_3424_, 2, v_v_3358_);
lean_ctor_set(v_reuseFailAlloc_3424_, 3, v___x_3418_);
lean_ctor_set(v_reuseFailAlloc_3424_, 4, v_r_3360_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3438_; 
v_l_3438_ = lean_ctor_get(v_impl_3353_, 3);
lean_inc(v_l_3438_);
if (lean_obj_tag(v_l_3438_) == 0)
{
lean_object* v_r_3439_; lean_object* v_k_3440_; lean_object* v_v_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3464_; 
v_r_3439_ = lean_ctor_get(v_impl_3353_, 4);
v_k_3440_ = lean_ctor_get(v_impl_3353_, 1);
v_v_3441_ = lean_ctor_get(v_impl_3353_, 2);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_impl_3353_);
if (v_isSharedCheck_3464_ == 0)
{
lean_object* v_unused_3465_; lean_object* v_unused_3466_; 
v_unused_3465_ = lean_ctor_get(v_impl_3353_, 3);
lean_dec(v_unused_3465_);
v_unused_3466_ = lean_ctor_get(v_impl_3353_, 0);
lean_dec(v_unused_3466_);
v___x_3443_ = v_impl_3353_;
v_isShared_3444_ = v_isSharedCheck_3464_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_r_3439_);
lean_inc(v_v_3441_);
lean_inc(v_k_3440_);
lean_dec(v_impl_3353_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3464_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v_k_3445_; lean_object* v_v_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3460_; 
v_k_3445_ = lean_ctor_get(v_l_3438_, 1);
v_v_3446_ = lean_ctor_get(v_l_3438_, 2);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_l_3438_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; lean_object* v_unused_3462_; lean_object* v_unused_3463_; 
v_unused_3461_ = lean_ctor_get(v_l_3438_, 4);
lean_dec(v_unused_3461_);
v_unused_3462_ = lean_ctor_get(v_l_3438_, 3);
lean_dec(v_unused_3462_);
v_unused_3463_ = lean_ctor_get(v_l_3438_, 0);
lean_dec(v_unused_3463_);
v___x_3448_ = v_l_3438_;
v_isShared_3449_ = v_isSharedCheck_3460_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_v_3446_);
lean_inc(v_k_3445_);
lean_dec(v_l_3438_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3460_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; lean_object* v___x_3452_; 
v___x_3450_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3439_, 2);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 4, v_r_3439_);
lean_ctor_set(v___x_3448_, 3, v_r_3439_);
lean_ctor_set(v___x_3448_, 2, v_v_3206_);
lean_ctor_set(v___x_3448_, 1, v_k_3205_);
lean_ctor_set(v___x_3448_, 0, v___x_3354_);
v___x_3452_ = v___x_3448_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3354_);
lean_ctor_set(v_reuseFailAlloc_3459_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3459_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3459_, 3, v_r_3439_);
lean_ctor_set(v_reuseFailAlloc_3459_, 4, v_r_3439_);
v___x_3452_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3454_; 
lean_inc(v_r_3439_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 3, v_r_3439_);
lean_ctor_set(v___x_3443_, 0, v___x_3354_);
v___x_3454_ = v___x_3443_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3354_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v_k_3440_);
lean_ctor_set(v_reuseFailAlloc_3458_, 2, v_v_3441_);
lean_ctor_set(v_reuseFailAlloc_3458_, 3, v_r_3439_);
lean_ctor_set(v_reuseFailAlloc_3458_, 4, v_r_3439_);
v___x_3454_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_object* v___x_3456_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 4, v___x_3454_);
lean_ctor_set(v___x_3210_, 3, v___x_3452_);
lean_ctor_set(v___x_3210_, 2, v_v_3446_);
lean_ctor_set(v___x_3210_, 1, v_k_3445_);
lean_ctor_set(v___x_3210_, 0, v___x_3450_);
v___x_3456_ = v___x_3210_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3450_);
lean_ctor_set(v_reuseFailAlloc_3457_, 1, v_k_3445_);
lean_ctor_set(v_reuseFailAlloc_3457_, 2, v_v_3446_);
lean_ctor_set(v_reuseFailAlloc_3457_, 3, v___x_3452_);
lean_ctor_set(v_reuseFailAlloc_3457_, 4, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
}
else
{
lean_object* v_r_3467_; 
v_r_3467_ = lean_ctor_get(v_impl_3353_, 4);
lean_inc(v_r_3467_);
if (lean_obj_tag(v_r_3467_) == 0)
{
lean_object* v_k_3468_; lean_object* v_v_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3480_; 
v_k_3468_ = lean_ctor_get(v_impl_3353_, 1);
v_v_3469_ = lean_ctor_get(v_impl_3353_, 2);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_impl_3353_);
if (v_isSharedCheck_3480_ == 0)
{
lean_object* v_unused_3481_; lean_object* v_unused_3482_; lean_object* v_unused_3483_; 
v_unused_3481_ = lean_ctor_get(v_impl_3353_, 4);
lean_dec(v_unused_3481_);
v_unused_3482_ = lean_ctor_get(v_impl_3353_, 3);
lean_dec(v_unused_3482_);
v_unused_3483_ = lean_ctor_get(v_impl_3353_, 0);
lean_dec(v_unused_3483_);
v___x_3471_ = v_impl_3353_;
v_isShared_3472_ = v_isSharedCheck_3480_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_v_3469_);
lean_inc(v_k_3468_);
lean_dec(v_impl_3353_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3480_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3473_; lean_object* v___x_3475_; 
v___x_3473_ = lean_unsigned_to_nat(3u);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 4, v_l_3438_);
lean_ctor_set(v___x_3471_, 2, v_v_3206_);
lean_ctor_set(v___x_3471_, 1, v_k_3205_);
lean_ctor_set(v___x_3471_, 0, v___x_3354_);
v___x_3475_ = v___x_3471_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3354_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3479_, 3, v_l_3438_);
lean_ctor_set(v_reuseFailAlloc_3479_, 4, v_l_3438_);
v___x_3475_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
lean_object* v___x_3477_; 
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 4, v_r_3467_);
lean_ctor_set(v___x_3210_, 3, v___x_3475_);
lean_ctor_set(v___x_3210_, 2, v_v_3469_);
lean_ctor_set(v___x_3210_, 1, v_k_3468_);
lean_ctor_set(v___x_3210_, 0, v___x_3473_);
v___x_3477_ = v___x_3210_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3473_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_k_3468_);
lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_v_3469_);
lean_ctor_set(v_reuseFailAlloc_3478_, 3, v___x_3475_);
lean_ctor_set(v_reuseFailAlloc_3478_, 4, v_r_3467_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3484_ = lean_unsigned_to_nat(2u);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 4, v_impl_3353_);
lean_ctor_set(v___x_3210_, 3, v_r_3467_);
lean_ctor_set(v___x_3210_, 0, v___x_3484_);
v___x_3486_ = v___x_3210_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3487_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3487_, 3, v_r_3467_);
lean_ctor_set(v_reuseFailAlloc_3487_, 4, v_impl_3353_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
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
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = lean_unsigned_to_nat(1u);
v___x_3490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v_k_3201_);
lean_ctor_set(v___x_3490_, 2, v_v_3202_);
lean_ctor_set(v___x_3490_, 3, v_t_3203_);
lean_ctor_set(v___x_3490_, 4, v_t_3203_);
return v___x_3490_;
}
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3491_ = lean_box(1);
v___x_3492_ = l_Lake_Package_depsFacetConfig;
v___x_3493_ = l_Lake_Package_depsFacet;
v___x_3494_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3493_, v___x_3492_, v___x_3491_);
return v___x_3494_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3495_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__0, &l_Lake_Package_initFacetConfigs___closed__0_once, _init_l_Lake_Package_initFacetConfigs___closed__0);
v___x_3496_ = l_Lake_Package_transDepsFacetConfig;
v___x_3497_ = l_Lake_Package_transDepsFacet;
v___x_3498_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3497_, v___x_3496_, v___x_3495_);
return v___x_3498_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3499_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__1, &l_Lake_Package_initFacetConfigs___closed__1_once, _init_l_Lake_Package_initFacetConfigs___closed__1);
v___x_3500_ = l_Lake_Package_extraDepFacetConfig;
v___x_3501_ = l_Lake_Package_extraDepFacet;
v___x_3502_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3501_, v___x_3500_, v___x_3499_);
return v___x_3502_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3503_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__2, &l_Lake_Package_initFacetConfigs___closed__2_once, _init_l_Lake_Package_initFacetConfigs___closed__2);
v___x_3504_ = l_Lake_Package_optBuildCacheFacetConfig;
v___x_3505_ = l_Lake_Package_optBuildCacheFacet;
v___x_3506_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3505_, v___x_3504_, v___x_3503_);
return v___x_3506_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3507_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__3, &l_Lake_Package_initFacetConfigs___closed__3_once, _init_l_Lake_Package_initFacetConfigs___closed__3);
v___x_3508_ = l_Lake_Package_buildCacheFacetConfig;
v___x_3509_ = l_Lake_Package_buildCacheFacet;
v___x_3510_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3509_, v___x_3508_, v___x_3507_);
return v___x_3510_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3511_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__4, &l_Lake_Package_initFacetConfigs___closed__4_once, _init_l_Lake_Package_initFacetConfigs___closed__4);
v___x_3512_ = l_Lake_Package_optBarrelFacetConfig;
v___x_3513_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3514_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3513_, v___x_3512_, v___x_3511_);
return v___x_3514_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3515_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__5, &l_Lake_Package_initFacetConfigs___closed__5_once, _init_l_Lake_Package_initFacetConfigs___closed__5);
v___x_3516_ = l_Lake_Package_barrelFacetConfig;
v___x_3517_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3518_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3517_, v___x_3516_, v___x_3515_);
return v___x_3518_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3519_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__6, &l_Lake_Package_initFacetConfigs___closed__6_once, _init_l_Lake_Package_initFacetConfigs___closed__6);
v___x_3520_ = l_Lake_Package_optGitHubReleaseFacetConfig;
v___x_3521_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3522_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3521_, v___x_3520_, v___x_3519_);
return v___x_3522_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3523_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__7, &l_Lake_Package_initFacetConfigs___closed__7_once, _init_l_Lake_Package_initFacetConfigs___closed__7);
v___x_3524_ = l_Lake_Package_gitHubReleaseFacetConfig;
v___x_3525_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3526_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3525_, v___x_3524_, v___x_3523_);
return v___x_3526_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs(void){
_start:
{
lean_object* v___x_3527_; 
v___x_3527_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__8, &l_Lake_Package_initFacetConfigs___closed__8_once, _init_l_Lake_Package_initFacetConfigs___closed__8);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3528_, lean_object* v_k_3529_, lean_object* v_v_3530_, lean_object* v_t_3531_, lean_object* v_hl_3532_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3529_, v_v_3530_, v_t_3531_);
return v___x_3533_;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs(void){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_Lake_Package_initFacetConfigs;
return v___x_3534_;
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
