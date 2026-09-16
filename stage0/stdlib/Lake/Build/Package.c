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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_Verbosity_ctorIdx(uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lake_Package_optReservoirBarrelFacet;
lean_object* l_Lake_Name_eraseHead(lean_object*);
extern lean_object* l_Lake_Package_optGitHubReleaseFacet;
extern lean_object* l_Lake_instDataKindUnit;
lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_add___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildMetadata_writeFile(lean_object*, lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Json_compress(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern lean_object* l_Lake_Package_transDepsFacet;
lean_object* l_Lake_Job_await___redArg(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
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
static lean_object* _init_l_Lake_Package_transDepsFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_509_; lean_object* v___f_510_; uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_509_ = 1;
v___f_510_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__0));
v___x_511_ = 0;
v___x_512_ = lean_box(0);
v___x_513_ = ((lean_object*)(l_Lake_Package_transDepsFacetConfig___closed__0));
v___x_514_ = l_Lake_Package_keyword;
v___x_515_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v___x_513_);
lean_ctor_set(v___x_515_, 2, v___x_512_);
lean_ctor_set(v___x_515_, 3, v___f_510_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*4, v___x_511_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*4 + 1, v___x_509_);
return v___x_515_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig(void){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = lean_obj_once(&l_Lake_Package_transDepsFacetConfig___closed__1, &l_Lake_Package_transDepsFacetConfig___closed__1_once, _init_l_Lake_Package_transDepsFacetConfig___closed__1);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object* v_self_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_config_525_; uint8_t v_preferReleaseBuild_526_; 
v_config_525_ = lean_ctor_get(v_self_517_, 6);
v_preferReleaseBuild_526_ = lean_ctor_get_uint8(v_config_525_, sizeof(void*)*28 + 2);
if (v_preferReleaseBuild_526_ == 0)
{
lean_object* v_keyName_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_keyName_527_ = lean_ctor_get(v_self_517_, 2);
v___x_528_ = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(v_keyName_527_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_keyName_527_);
v___x_530_ = l_Lake_Package_keyword;
v___x_531_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
lean_ctor_set(v___x_531_, 2, v_self_517_);
lean_ctor_set(v___x_531_, 3, v___x_528_);
lean_inc_ref(v_a_522_);
lean_inc(v_a_521_);
lean_inc(v_a_520_);
lean_inc(v_a_519_);
v___x_532_ = lean_apply_7(v_a_518_, v___x_531_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, lean_box(0));
return v___x_532_;
}
else
{
lean_object* v_keyName_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_keyName_533_ = lean_ctor_get(v_self_517_, 2);
v___x_534_ = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(v_keyName_533_);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v_keyName_533_);
v___x_536_ = l_Lake_Package_keyword;
v___x_537_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
lean_ctor_set(v___x_537_, 2, v_self_517_);
lean_ctor_set(v___x_537_, 3, v___x_534_);
lean_inc_ref(v_a_522_);
lean_inc(v_a_521_);
lean_inc(v_a_520_);
lean_inc(v_a_519_);
v___x_538_ = lean_apply_7(v_a_518_, v___x_537_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, lean_box(0));
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___boxed(lean_object* v_self_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(v_self_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec(v_a_542_);
lean_dec(v_a_541_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t v_fmt_550_, uint8_t v_a_551_){
_start:
{
if (v_fmt_550_ == 0)
{
if (v_a_551_ == 0)
{
lean_object* v___x_552_; 
v___x_552_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0));
return v___x_552_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1));
return v___x_553_;
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_554_, 0, v_a_551_);
v___x_555_ = l_Lean_Json_compress(v___x_554_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object* v_fmt_556_, lean_object* v_a_557_){
_start:
{
uint8_t v_fmt_boxed_558_; uint8_t v_a_boxed_559_; lean_object* v_res_560_; 
v_fmt_boxed_558_ = lean_unbox(v_fmt_556_);
v_a_boxed_559_ = lean_unbox(v_a_557_);
v_res_560_ = l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(v_fmt_boxed_558_, v_a_boxed_559_);
return v_res_560_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_563_; uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___f_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___f_563_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_564_ = 1;
v___x_565_ = l_Lake_instDataKindBool;
v___f_566_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__0));
v___x_567_ = l_Lake_Package_keyword;
v___x_568_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___f_566_);
lean_ctor_set(v___x_568_, 2, v___x_565_);
lean_ctor_set(v___x_568_, 3, v___f_563_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*4, v___x_564_);
lean_ctor_set_uint8(v___x_568_, sizeof(void*)*4 + 1, v___x_564_);
return v___x_568_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig(void){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = lean_obj_once(&l_Lake_Package_optBuildCacheFacetConfig___closed__2, &l_Lake_Package_optBuildCacheFacetConfig___closed__2_once, _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(lean_object* v_self_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___y_581_; uint8_t v___y_582_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_605_; uint8_t v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v_toContext_612_; lean_object* v_lakeEnv_613_; uint8_t v_noCache_614_; lean_object* v_toolchain_615_; uint8_t v_a_617_; lean_object* v_a_618_; 
v_toContext_612_ = lean_ctor_get(v_a_577_, 1);
v_lakeEnv_613_ = lean_ctor_get(v_toContext_612_, 0);
v_noCache_614_ = lean_ctor_get_uint8(v_lakeEnv_613_, sizeof(void*)*20);
v_toolchain_615_ = lean_ctor_get(v_lakeEnv_613_, 19);
if (v_noCache_614_ == 0)
{
uint8_t v___x_633_; 
v___x_633_ = 1;
v_a_617_ = v___x_633_;
v_a_618_ = v_a_578_;
goto v___jp_616_;
}
else
{
uint8_t v___x_634_; 
v___x_634_ = 0;
v_a_617_ = v___x_634_;
v_a_618_ = v_a_578_;
goto v___jp_616_;
}
v___jp_580_:
{
uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_583_ = 1;
v___x_584_ = lean_box(0);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_587_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_588_ = 0;
v___x_589_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_590_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_590_, 0, v___x_586_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
lean_ctor_set(v___x_590_, 2, v___x_585_);
lean_ctor_set_uint8(v___x_590_, sizeof(void*)*3, v___x_588_);
lean_ctor_set_uint8(v___x_590_, sizeof(void*)*3 + 1, v___y_582_);
v___x_591_ = lean_box(v___x_583_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___x_590_);
v___x_593_ = lean_task_pure(v___x_592_);
v___x_594_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_584_);
lean_ctor_set(v___x_594_, 2, v___x_587_);
lean_ctor_set_uint8(v___x_594_, sizeof(void*)*3, v___y_582_);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___y_581_);
return v___x_595_;
}
v___jp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_599_ = l_Lake_Package_optBuildCacheFacet;
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v___y_598_);
v___x_601_ = l_Lake_Package_keyword;
v___x_602_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
lean_ctor_set(v___x_602_, 2, v_self_572_);
lean_ctor_set(v___x_602_, 3, v___x_599_);
lean_inc_ref(v_a_577_);
lean_inc(v_a_576_);
lean_inc(v_a_575_);
lean_inc(v_a_574_);
v___x_603_ = lean_apply_7(v_a_573_, v___x_602_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v___y_597_, lean_box(0));
return v___x_603_;
}
v___jp_604_:
{
lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_609_ = lean_string_utf8_byte_size(v___y_608_);
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = lean_nat_dec_eq(v___x_609_, v___x_610_);
if (v___x_611_ == 0)
{
v___y_597_ = v___y_605_;
v___y_598_ = v___y_607_;
goto v___jp_596_;
}
else
{
lean_dec(v___y_607_);
lean_dec_ref(v_a_573_);
lean_dec_ref(v_self_572_);
v___y_581_ = v___y_605_;
v___y_582_ = v___y_606_;
goto v___jp_580_;
}
}
v___jp_616_:
{
lean_object* v_config_619_; lean_object* v_keyName_620_; lean_object* v_dir_621_; lean_object* v_scope_622_; lean_object* v_buildDir_623_; uint8_t v_preferReleaseBuild_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v_config_619_ = lean_ctor_get(v_self_572_, 6);
v_keyName_620_ = lean_ctor_get(v_self_572_, 2);
v_dir_621_ = lean_ctor_get(v_self_572_, 4);
v_scope_622_ = lean_ctor_get(v_self_572_, 10);
v_buildDir_623_ = lean_ctor_get(v_config_619_, 5);
v_preferReleaseBuild_624_ = lean_ctor_get_uint8(v_config_619_, sizeof(void*)*28 + 2);
lean_inc_ref(v_buildDir_623_);
v___x_625_ = l_System_FilePath_normalize(v_buildDir_623_);
lean_inc_ref(v_dir_621_);
v___x_626_ = l_Lake_joinRelative(v_dir_621_, v___x_625_);
v___x_627_ = l_System_FilePath_pathExists(v___x_626_);
lean_dec_ref(v___x_626_);
if (v_a_617_ == 0)
{
lean_dec_ref(v_a_573_);
lean_dec_ref(v_self_572_);
v___y_581_ = v_a_618_;
v___y_582_ = v_a_617_;
goto v___jp_580_;
}
else
{
if (v___x_627_ == 0)
{
if (v_preferReleaseBuild_624_ == 0)
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0));
v___x_629_ = lean_string_dec_eq(v_scope_622_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1));
v___x_631_ = lean_string_dec_eq(v_scope_622_, v___x_630_);
if (v___x_631_ == 0)
{
lean_dec_ref(v_a_573_);
lean_dec_ref(v_self_572_);
v___y_581_ = v_a_618_;
v___y_582_ = v___x_631_;
goto v___jp_580_;
}
else
{
lean_inc(v_keyName_620_);
v___y_605_ = v_a_618_;
v___y_606_ = v_preferReleaseBuild_624_;
v___y_607_ = v_keyName_620_;
v___y_608_ = v_toolchain_615_;
goto v___jp_604_;
}
}
else
{
lean_inc(v_keyName_620_);
v___y_605_ = v_a_618_;
v___y_606_ = v_preferReleaseBuild_624_;
v___y_607_ = v_keyName_620_;
v___y_608_ = v_toolchain_615_;
goto v___jp_604_;
}
}
else
{
lean_inc(v_keyName_620_);
v___y_597_ = v_a_618_;
v___y_598_ = v_keyName_620_;
goto v___jp_596_;
}
}
else
{
uint8_t v___x_632_; 
lean_dec_ref(v_a_573_);
lean_dec_ref(v_self_572_);
v___x_632_ = 0;
v___y_581_ = v_a_618_;
v___y_582_ = v___x_632_;
goto v___jp_580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___boxed(lean_object* v_self_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec(v_a_638_);
lean_dec(v_a_637_);
return v_res_643_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0(void){
_start:
{
uint8_t v___x_644_; lean_object* v___x_645_; 
v___x_644_ = 2;
v___x_645_ = l_Lake_Verbosity_ctorIdx(v___x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object* v_self_650_, lean_object* v_facet_651_, lean_object* v_a_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_toBuildConfig_655_; uint8_t v_verbosity_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_toBuildConfig_655_ = lean_ctor_get(v_a_652_, 0);
v_verbosity_656_ = lean_ctor_get_uint8(v_toBuildConfig_655_, sizeof(void*)*4 + 4);
v___x_657_ = l_Lake_Verbosity_ctorIdx(v_verbosity_656_);
v___x_658_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_659_ = lean_nat_dec_eq(v___x_657_, v___x_658_);
lean_dec(v___x_657_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec(v_facet_651_);
lean_dec_ref(v_self_650_);
v___x_660_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v_a_653_);
return v___x_661_;
}
else
{
lean_object* v_baseName_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_baseName_662_ = lean_ctor_get(v_self_650_, 1);
lean_inc(v_baseName_662_);
lean_dec_ref(v_self_650_);
v___x_663_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_664_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_662_, v___x_659_);
v___x_665_ = lean_string_append(v___x_663_, v___x_664_);
lean_dec_ref(v___x_664_);
v___x_666_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_667_ = lean_string_append(v___x_665_, v___x_666_);
v___x_668_ = l_Lake_Name_eraseHead(v_facet_651_);
v___x_669_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_668_, v___x_659_);
v___x_670_ = lean_string_append(v___x_667_, v___x_669_);
lean_dec_ref(v___x_669_);
v___x_671_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_672_ = lean_string_append(v___x_670_, v___x_671_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v_a_653_);
return v___x_673_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* v_self_674_, lean_object* v_facet_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(v_self_674_, v_facet_675_, v_a_676_, v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* v_self_680_, lean_object* v_facet_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_toBuildConfig_689_; uint8_t v_verbosity_690_; lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v_toBuildConfig_689_ = lean_ctor_get(v_a_686_, 0);
v_verbosity_690_ = lean_ctor_get_uint8(v_toBuildConfig_689_, sizeof(void*)*4 + 4);
v___x_691_ = l_Lake_Verbosity_ctorIdx(v_verbosity_690_);
v___x_692_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_693_ = lean_nat_dec_eq(v___x_691_, v___x_692_);
lean_dec(v___x_691_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
lean_dec(v_facet_681_);
lean_dec_ref(v_self_680_);
v___x_694_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_a_687_);
return v___x_695_;
}
else
{
lean_object* v_baseName_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_baseName_696_ = lean_ctor_get(v_self_680_, 1);
lean_inc(v_baseName_696_);
lean_dec_ref(v_self_680_);
v___x_697_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_698_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_696_, v___x_693_);
v___x_699_ = lean_string_append(v___x_697_, v___x_698_);
lean_dec_ref(v___x_698_);
v___x_700_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_701_ = lean_string_append(v___x_699_, v___x_700_);
v___x_702_ = l_Lake_Name_eraseHead(v_facet_681_);
v___x_703_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_702_, v___x_693_);
v___x_704_ = lean_string_append(v___x_701_, v___x_703_);
lean_dec_ref(v___x_703_);
v___x_705_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_706_ = lean_string_append(v___x_704_, v___x_705_);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v_a_687_);
return v___x_707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* v_self_708_, lean_object* v_facet_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(v_self_708_, v_facet_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
return v_res_717_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_721_ = l_Lake_Name_eraseHead(v___x_720_);
return v___x_721_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_723_ = l_Lake_Name_eraseHead(v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(lean_object* v_self_724_, uint8_t v_success_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_a_734_; lean_object* v_a_735_; lean_object* v_a_756_; lean_object* v_a_757_; 
if (v_success_725_ == 0)
{
lean_object* v_config_777_; uint8_t v_preferReleaseBuild_778_; 
v_config_777_ = lean_ctor_get(v_self_724_, 6);
v_preferReleaseBuild_778_ = lean_ctor_get_uint8(v_config_777_, sizeof(void*)*28 + 2);
if (v_preferReleaseBuild_778_ == 0)
{
lean_object* v_toBuildConfig_779_; lean_object* v_baseName_780_; uint8_t v_verbosity_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_toBuildConfig_779_ = lean_ctor_get(v___y_730_, 0);
v_baseName_780_ = lean_ctor_get(v_self_724_, 1);
lean_inc(v_baseName_780_);
lean_dec_ref(v_self_724_);
v_verbosity_781_ = lean_ctor_get_uint8(v_toBuildConfig_779_, sizeof(void*)*4 + 4);
v___x_782_ = l_Lake_Verbosity_ctorIdx(v_verbosity_781_);
v___x_783_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_784_ = lean_nat_dec_eq(v___x_782_, v___x_783_);
lean_dec(v___x_782_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec(v_baseName_780_);
v___x_785_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_734_ = v___x_785_;
v_a_735_ = v___y_731_;
goto v___jp_733_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_786_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_787_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_780_, v___x_784_);
v___x_788_ = lean_string_append(v___x_786_, v___x_787_);
lean_dec_ref(v___x_787_);
v___x_789_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_790_ = lean_string_append(v___x_788_, v___x_789_);
v___x_791_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2);
v___x_792_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_791_, v___x_784_);
v___x_793_ = lean_string_append(v___x_790_, v___x_792_);
lean_dec_ref(v___x_792_);
v___x_794_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_795_ = lean_string_append(v___x_793_, v___x_794_);
v_a_734_ = v___x_795_;
v_a_735_ = v___y_731_;
goto v___jp_733_;
}
}
else
{
lean_object* v_toBuildConfig_796_; lean_object* v_baseName_797_; uint8_t v_verbosity_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v_toBuildConfig_796_ = lean_ctor_get(v___y_730_, 0);
v_baseName_797_ = lean_ctor_get(v_self_724_, 1);
lean_inc(v_baseName_797_);
lean_dec_ref(v_self_724_);
v_verbosity_798_ = lean_ctor_get_uint8(v_toBuildConfig_796_, sizeof(void*)*4 + 4);
v___x_799_ = l_Lake_Verbosity_ctorIdx(v_verbosity_798_);
v___x_800_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_801_ = lean_nat_dec_eq(v___x_799_, v___x_800_);
lean_dec(v___x_799_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; 
lean_dec(v_baseName_797_);
v___x_802_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_756_ = v___x_802_;
v_a_757_ = v___y_731_;
goto v___jp_755_;
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_803_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_804_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_797_, v___x_801_);
v___x_805_ = lean_string_append(v___x_803_, v___x_804_);
lean_dec_ref(v___x_804_);
v___x_806_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_807_ = lean_string_append(v___x_805_, v___x_806_);
v___x_808_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
v___x_809_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_808_, v___x_801_);
v___x_810_ = lean_string_append(v___x_807_, v___x_809_);
lean_dec_ref(v___x_809_);
v___x_811_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_812_ = lean_string_append(v___x_810_, v___x_811_);
v_a_756_ = v___x_812_;
v_a_757_ = v___y_731_;
goto v___jp_755_;
}
}
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; 
lean_dec_ref(v_self_724_);
v___x_813_ = lean_box(0);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___y_731_);
return v___x_814_;
}
v___jp_733_:
{
lean_object* v_log_736_; uint8_t v_action_737_; uint8_t v_wantsRebuild_738_; lean_object* v_trace_739_; lean_object* v_buildTime_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_754_; 
v_log_736_ = lean_ctor_get(v_a_735_, 0);
v_action_737_ = lean_ctor_get_uint8(v_a_735_, sizeof(void*)*3);
v_wantsRebuild_738_ = lean_ctor_get_uint8(v_a_735_, sizeof(void*)*3 + 1);
v_trace_739_ = lean_ctor_get(v_a_735_, 1);
v_buildTime_740_ = lean_ctor_get(v_a_735_, 2);
v_isSharedCheck_754_ = !lean_is_exclusive(v_a_735_);
if (v_isSharedCheck_754_ == 0)
{
v___x_742_ = v_a_735_;
v_isShared_743_ = v_isSharedCheck_754_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_buildTime_740_);
lean_inc(v_trace_739_);
lean_inc(v_log_736_);
lean_dec(v_a_735_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_754_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_744_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0));
v___x_745_ = lean_string_append(v___x_744_, v_a_734_);
lean_dec_ref(v_a_734_);
v___x_746_ = 0;
v___x_747_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*1, v___x_746_);
v___x_748_ = lean_box(0);
v___x_749_ = lean_array_push(v_log_736_, v___x_747_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_749_);
v___x_751_ = v___x_742_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_trace_739_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v_buildTime_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*3, v_action_737_);
lean_ctor_set_uint8(v_reuseFailAlloc_753_, sizeof(void*)*3 + 1, v_wantsRebuild_738_);
v___x_751_ = v_reuseFailAlloc_753_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; 
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_748_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
return v___x_752_;
}
}
}
v___jp_755_:
{
lean_object* v_log_758_; uint8_t v_action_759_; uint8_t v_wantsRebuild_760_; lean_object* v_trace_761_; lean_object* v_buildTime_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_776_; 
v_log_758_ = lean_ctor_get(v_a_757_, 0);
v_action_759_ = lean_ctor_get_uint8(v_a_757_, sizeof(void*)*3);
v_wantsRebuild_760_ = lean_ctor_get_uint8(v_a_757_, sizeof(void*)*3 + 1);
v_trace_761_ = lean_ctor_get(v_a_757_, 1);
v_buildTime_762_ = lean_ctor_get(v_a_757_, 2);
v_isSharedCheck_776_ = !lean_is_exclusive(v_a_757_);
if (v_isSharedCheck_776_ == 0)
{
v___x_764_ = v_a_757_;
v_isShared_765_ = v_isSharedCheck_776_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_buildTime_762_);
lean_inc(v_trace_761_);
lean_inc(v_log_758_);
lean_dec(v_a_757_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_776_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_766_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1));
v___x_767_ = lean_string_append(v___x_766_, v_a_756_);
lean_dec_ref(v_a_756_);
v___x_768_ = 2;
v___x_769_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set_uint8(v___x_769_, sizeof(void*)*1, v___x_768_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_array_push(v_log_758_, v___x_769_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_771_);
v___x_773_ = v___x_764_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_trace_761_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_buildTime_762_);
lean_ctor_set_uint8(v_reuseFailAlloc_775_, sizeof(void*)*3, v_action_759_);
lean_ctor_set_uint8(v_reuseFailAlloc_775_, sizeof(void*)*3 + 1, v_wantsRebuild_760_);
v___x_773_ = v_reuseFailAlloc_775_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; 
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_770_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
return v___x_774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* v_self_815_, lean_object* v_success_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
uint8_t v_success_boxed_824_; lean_object* v_res_825_; 
v_success_boxed_824_ = lean_unbox(v_success_816_);
v_res_825_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(v_self_815_, v_success_boxed_824_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* v_self_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_834_; 
lean_inc_ref(v_a_827_);
lean_inc_ref(v_self_826_);
v___x_834_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_849_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_a_836_ = lean_ctor_get(v___x_834_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_849_ == 0)
{
v___x_838_ = v___x_834_;
v_isShared_839_ = v_isSharedCheck_849_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_849_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___f_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___f_840_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(v___f_840_, 0, v_self_826_);
v___x_841_ = l_Lake_instDataKindUnit;
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = 0;
v___x_844_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_845_ = l_Lake_Job_mapM___redArg(v___x_841_, v_a_835_, v___f_840_, v___x_842_, v___x_843_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v___x_844_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_845_);
v___x_847_ = v___x_838_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v_a_836_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_object* v_a_850_; lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref(v_a_827_);
lean_dec_ref(v_self_826_);
v_a_850_ = lean_ctor_get(v___x_834_, 0);
v_a_851_ = lean_ctor_get(v___x_834_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_834_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_inc(v_a_850_);
lean_dec(v___x_834_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_850_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(lean_object* v_self_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec(v_a_862_);
lean_dec(v_a_861_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* v_self_868_, lean_object* v_as_869_, size_t v_sz_870_, size_t v_i_871_, lean_object* v_b_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v___x_880_; 
v___x_880_ = lean_usize_dec_lt(v_i_871_, v_sz_870_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
lean_dec_ref(v___y_873_);
lean_dec_ref(v_self_868_);
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v_b_872_);
lean_ctor_set(v___x_881_, 1, v___y_878_);
return v___x_881_;
}
else
{
lean_object* v_a_882_; lean_object* v___x_883_; 
v_a_882_ = lean_array_uget_borrowed(v_as_869_, v_i_871_);
lean_inc_ref(v___y_873_);
lean_inc(v_a_882_);
lean_inc_ref(v_self_868_);
v___x_883_ = l_Lake_Package_fetchTargetJob(v_self_868_, v_a_882_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v_a_885_; lean_object* v___x_886_; size_t v___x_887_; size_t v___x_888_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
v_a_885_ = lean_ctor_get(v___x_883_, 1);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_883_, 2);
v___x_886_ = l_Lake_Job_mix___redArg(v_b_872_, v_a_884_);
v___x_887_ = ((size_t)1ULL);
v___x_888_ = lean_usize_add(v_i_871_, v___x_887_);
v_i_871_ = v___x_888_;
v_b_872_ = v___x_886_;
v___y_878_ = v_a_885_;
goto _start;
}
else
{
lean_object* v_a_890_; lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v___y_873_);
lean_dec_ref(v_b_872_);
lean_dec_ref(v_self_868_);
v_a_890_ = lean_ctor_get(v___x_883_, 0);
v_a_891_ = lean_ctor_get(v___x_883_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_883_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_inc(v_a_890_);
lean_dec(v___x_883_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_890_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* v_self_899_, lean_object* v_as_900_, lean_object* v_sz_901_, lean_object* v_i_902_, lean_object* v_b_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
size_t v_sz_boxed_911_; size_t v_i_boxed_912_; lean_object* v_res_913_; 
v_sz_boxed_911_ = lean_unbox_usize(v_sz_901_);
lean_dec(v_sz_901_);
v_i_boxed_912_ = lean_unbox_usize(v_i_902_);
lean_dec(v_i_902_);
v_res_913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_899_, v_as_900_, v_sz_boxed_911_, v_i_boxed_912_, v_b_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v_as_900_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object* v_config_914_, lean_object* v_self_915_, lean_object* v_____r_916_, lean_object* v_job_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_extraDepTargets_925_; size_t v_sz_926_; size_t v___x_927_; lean_object* v___x_928_; 
v_extraDepTargets_925_ = lean_ctor_get(v_config_914_, 2);
v_sz_926_ = lean_array_size(v_extraDepTargets_925_);
v___x_927_ = ((size_t)0ULL);
v___x_928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_915_, v_extraDepTargets_925_, v_sz_926_, v___x_927_, v_job_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object* v_config_929_, lean_object* v_self_930_, lean_object* v_____r_931_, lean_object* v_job_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(v_config_929_, v_self_930_, v_____r_931_, v_job_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v_config_929_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(uint8_t v___x_941_, lean_object* v_self_942_, lean_object* v_job_943_, lean_object* v___f_944_, lean_object* v___x_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
if (v___x_941_ == 0)
{
lean_object* v___x_953_; 
lean_inc_ref(v___y_946_);
v___x_953_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_942_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v_a_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
v_a_955_ = lean_ctor_get(v___x_953_, 1);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_953_, 2);
v___x_956_ = l_Lake_Job_add___redArg(v_job_943_, v_a_954_);
lean_inc_ref(v___y_950_);
lean_inc(v___y_949_);
lean_inc(v___y_948_);
lean_inc(v___y_947_);
v___x_957_ = lean_apply_9(v___f_944_, v___x_945_, v___x_956_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v_a_955_, lean_box(0));
return v___x_957_;
}
else
{
lean_dec_ref(v___y_946_);
lean_dec_ref(v___f_944_);
lean_dec_ref(v_job_943_);
return v___x_953_;
}
}
else
{
lean_object* v___x_958_; 
lean_dec_ref(v_self_942_);
lean_inc_ref(v___y_950_);
lean_inc(v___y_949_);
lean_inc(v___y_948_);
lean_inc(v___y_947_);
v___x_958_ = lean_apply_9(v___f_944_, v___x_945_, v_job_943_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, lean_box(0));
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* v___x_959_, lean_object* v_self_960_, lean_object* v_job_961_, lean_object* v___f_962_, lean_object* v___x_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
uint8_t v___x_4121__boxed_971_; lean_object* v_res_972_; 
v___x_4121__boxed_971_ = lean_unbox(v___x_959_);
v_res_972_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(v___x_4121__boxed_971_, v_self_960_, v_job_961_, v___f_962_, v___x_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v___y_965_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object* v_self_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_wsIdx_983_; lean_object* v_baseName_984_; lean_object* v_config_985_; lean_object* v___f_986_; lean_object* v___x_987_; uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v_job_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___y_1008_; lean_object* v___x_1009_; 
v_wsIdx_983_ = lean_ctor_get(v_self_975_, 0);
v_baseName_984_ = lean_ctor_get(v_self_975_, 1);
v_config_985_ = lean_ctor_get(v_self_975_, 6);
lean_inc_ref(v_self_975_);
lean_inc_ref(v_config_985_);
v___f_986_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed), 11, 2);
lean_closure_set(v___f_986_, 0, v_config_985_);
lean_closure_set(v___f_986_, 1, v_self_975_);
v___x_987_ = l_Lake_instDataKindUnit;
v___x_988_ = 1;
lean_inc(v_baseName_984_);
v___x_989_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_984_, v___x_988_);
v___x_990_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0));
v___x_991_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1));
v___x_992_ = lean_string_append(v___x_991_, v___x_989_);
v___x_993_ = lean_string_append(v___x_992_, v___x_990_);
v___x_994_ = lean_box(0);
v___x_995_ = lean_box(0);
v___x_996_ = lean_unsigned_to_nat(0u);
v___x_997_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_998_ = 0;
v___x_999_ = 0;
v___x_1000_ = l_Lake_BuildTrace_nil(v___x_993_);
v___x_1001_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1001_, 0, v___x_997_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
lean_ctor_set(v___x_1001_, 2, v___x_996_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*3, v___x_998_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*3 + 1, v___x_999_);
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_994_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_task_pure(v___x_1002_);
v___x_1004_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_job_1005_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_1005_, 0, v___x_1003_);
lean_ctor_set(v_job_1005_, 1, v___x_995_);
lean_ctor_set(v_job_1005_, 2, v___x_1004_);
lean_ctor_set_uint8(v_job_1005_, sizeof(void*)*3, v___x_999_);
v___x_1006_ = lean_nat_dec_eq(v_wsIdx_983_, v___x_996_);
v___x_1007_ = lean_box(v___x_1006_);
v___y_1008_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 12, 5);
lean_closure_set(v___y_1008_, 0, v___x_1007_);
lean_closure_set(v___y_1008_, 1, v_self_975_);
lean_closure_set(v___y_1008_, 2, v_job_1005_);
lean_closure_set(v___y_1008_, 3, v___f_986_);
lean_closure_set(v___y_1008_, 4, v___x_994_);
v___x_1009_ = l_Lake_ensureJob___redArg(v___x_987_, v___y_1008_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1035_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_a_1011_ = lean_ctor_get(v___x_1009_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1013_ = v___x_1009_;
v_isShared_1014_ = v_isSharedCheck_1035_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1035_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v_task_1015_; lean_object* v_kind_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1033_; 
v_task_1015_ = lean_ctor_get(v_a_1010_, 0);
v_kind_1016_ = lean_ctor_get(v_a_1010_, 1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_a_1010_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; 
v_unused_1034_ = lean_ctor_get(v_a_1010_, 2);
lean_dec(v_unused_1034_);
v___x_1018_ = v_a_1010_;
v_isShared_1019_ = v_isSharedCheck_1033_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_kind_1016_);
lean_inc(v_task_1015_);
lean_dec(v_a_1010_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1033_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_registeredJobs_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v_job_1024_; 
v_registeredJobs_1020_ = lean_ctor_get(v_a_980_, 4);
v___x_1021_ = lean_st_ref_take(v_registeredJobs_1020_);
v___x_1022_ = lean_string_append(v___x_989_, v___x_990_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 2, v___x_1022_);
v_job_1024_ = v___x_1018_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_task_1015_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_kind_1016_);
lean_ctor_set(v_reuseFailAlloc_1032_, 2, v___x_1022_);
v_job_1024_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
lean_ctor_set_uint8(v_job_1024_, sizeof(void*)*3, v___x_999_);
lean_inc_ref(v_job_1024_);
v___x_1025_ = l_Lake_Job_toOpaque___redArg(v_job_1024_);
v___x_1026_ = lean_array_push(v___x_1021_, v___x_1025_);
v___x_1027_ = lean_st_ref_put(v_registeredJobs_1020_, v___x_1026_);
v___x_1028_ = l_Lake_Job_renew___redArg(v_job_1024_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1028_);
v___x_1030_ = v___x_1013_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_a_1011_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_989_);
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(lean_object* v_self_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(v_self_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec(v_a_1038_);
return v_res_1044_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_box(0);
v___x_1046_ = l_Lean_Json_compress(v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t v_fmt_1047_){
_start:
{
if (v_fmt_1047_ == 0)
{
lean_object* v___x_1048_; 
v___x_1048_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
return v___x_1048_;
}
else
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_1050_){
_start:
{
uint8_t v_fmt_boxed_1051_; lean_object* v_res_1052_; 
v_fmt_boxed_1051_ = lean_unbox(v_fmt_1050_);
v_res_1052_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_boxed_1051_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(uint8_t v_fmt_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_1053_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object* v_fmt_1056_, lean_object* v_a_1057_){
_start:
{
uint8_t v_fmt_boxed_1058_; lean_object* v_res_1059_; 
v_fmt_boxed_1058_ = lean_unbox(v_fmt_1056_);
v_res_1059_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(v_fmt_boxed_1058_, v_a_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v___y_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
uint8_t v___y_67__boxed_1065_; lean_object* v_res_1066_; 
v___y_67__boxed_1065_ = lean_unbox(v___y_1063_);
v_res_1066_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_67__boxed_1065_, v___y_1064_);
return v_res_1066_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1069_; uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___f_1069_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_1070_ = 1;
v___x_1071_ = l_Lake_instDataKindUnit;
v___x_1072_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__1));
v___x_1073_ = l_Lake_Package_keyword;
v___x_1074_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___x_1072_);
lean_ctor_set(v___x_1074_, 2, v___x_1071_);
lean_ctor_set(v___x_1074_, 3, v___f_1069_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*4, v___x_1070_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*4 + 1, v___x_1070_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_obj_once(&l_Lake_Package_extraDepFacetConfig___closed__2, &l_Lake_Package_extraDepFacetConfig___closed__2_once, _init_l_Lake_Package_extraDepFacetConfig___closed__2);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object* v_self_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v_origName_1095_; lean_object* v_dir_1096_; lean_object* v_scope_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v_origName_1095_ = lean_ctor_get(v_self_1091_, 3);
lean_inc(v_origName_1095_);
v_dir_1096_ = lean_ctor_get(v_self_1091_, 4);
lean_inc_ref(v_dir_1096_);
v_scope_1097_ = lean_ctor_get(v_self_1091_, 10);
lean_inc_ref(v_scope_1097_);
lean_dec_ref(v_self_1091_);
v___x_1098_ = lean_string_utf8_byte_size(v_scope_1097_);
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = lean_nat_dec_eq(v___x_1098_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
v___x_1102_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1101_, v_dir_1096_);
if (lean_obj_tag(v___x_1102_) == 1)
{
lean_object* v_toContext_1103_; lean_object* v_lakeEnv_1104_; lean_object* v_log_1105_; uint8_t v_action_1106_; uint8_t v_wantsRebuild_1107_; lean_object* v_trace_1108_; lean_object* v_buildTime_1109_; lean_object* v_val_1110_; lean_object* v_toolchain_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v_toContext_1103_ = lean_ctor_get(v_a_1092_, 1);
v_lakeEnv_1104_ = lean_ctor_get(v_toContext_1103_, 0);
v_log_1105_ = lean_ctor_get(v_a_1093_, 0);
v_action_1106_ = lean_ctor_get_uint8(v_a_1093_, sizeof(void*)*3);
v_wantsRebuild_1107_ = lean_ctor_get_uint8(v_a_1093_, sizeof(void*)*3 + 1);
v_trace_1108_ = lean_ctor_get(v_a_1093_, 1);
v_buildTime_1109_ = lean_ctor_get(v_a_1093_, 2);
v_val_1110_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_val_1110_);
lean_dec_ref_known(v___x_1102_, 1);
v_toolchain_1111_ = lean_ctor_get(v_lakeEnv_1104_, 19);
v___x_1112_ = lean_string_utf8_byte_size(v_toolchain_1111_);
v___x_1113_ = lean_nat_dec_eq(v___x_1112_, v___x_1099_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1114_ = l_Lean_Name_toString(v_origName_1095_, v___x_1100_);
lean_inc_ref(v_lakeEnv_1104_);
v___x_1115_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_1104_, v_scope_1097_, v___x_1114_);
v___x_1116_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1));
v___x_1117_ = lean_string_append(v___x_1115_, v___x_1116_);
v___x_1118_ = lean_string_append(v___x_1117_, v_val_1110_);
lean_dec(v_val_1110_);
v___x_1119_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2));
v___x_1120_ = lean_string_append(v___x_1118_, v___x_1119_);
v___x_1121_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc_ref(v_toolchain_1111_);
v___x_1122_ = l_Lake_uriEncode(v_toolchain_1111_, v___x_1121_);
v___x_1123_ = lean_string_append(v___x_1120_, v___x_1122_);
lean_dec_ref(v___x_1122_);
v___x_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1123_);
lean_ctor_set(v___x_1124_, 1, v_a_1093_);
return v___x_1124_;
}
else
{
lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1135_; 
lean_inc(v_buildTime_1109_);
lean_inc_ref(v_trace_1108_);
lean_inc_ref(v_log_1105_);
lean_dec(v_val_1110_);
lean_dec_ref(v_scope_1097_);
lean_dec(v_origName_1095_);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_a_1093_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; lean_object* v_unused_1137_; lean_object* v_unused_1138_; 
v_unused_1136_ = lean_ctor_get(v_a_1093_, 2);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v_a_1093_, 1);
lean_dec(v_unused_1137_);
v_unused_1138_ = lean_ctor_get(v_a_1093_, 0);
lean_dec(v_unused_1138_);
v___x_1126_ = v_a_1093_;
v_isShared_1127_ = v_isSharedCheck_1135_;
goto v_resetjp_1125_;
}
else
{
lean_dec(v_a_1093_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1135_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1128_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4));
v___x_1129_ = lean_array_get_size(v_log_1105_);
v___x_1130_ = lean_array_push(v_log_1105_, v___x_1128_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1130_);
v___x_1132_ = v___x_1126_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_trace_1108_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_buildTime_1109_);
lean_ctor_set_uint8(v_reuseFailAlloc_1134_, sizeof(void*)*3, v_action_1106_);
lean_ctor_set_uint8(v_reuseFailAlloc_1134_, sizeof(void*)*3 + 1, v_wantsRebuild_1107_);
v___x_1132_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1129_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
return v___x_1133_;
}
}
}
}
else
{
lean_object* v_log_1139_; uint8_t v_action_1140_; uint8_t v_wantsRebuild_1141_; lean_object* v_trace_1142_; lean_object* v_buildTime_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v___x_1102_);
lean_dec_ref(v_scope_1097_);
lean_dec(v_origName_1095_);
v_log_1139_ = lean_ctor_get(v_a_1093_, 0);
v_action_1140_ = lean_ctor_get_uint8(v_a_1093_, sizeof(void*)*3);
v_wantsRebuild_1141_ = lean_ctor_get_uint8(v_a_1093_, sizeof(void*)*3 + 1);
v_trace_1142_ = lean_ctor_get(v_a_1093_, 1);
v_buildTime_1143_ = lean_ctor_get(v_a_1093_, 2);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_a_1093_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1145_ = v_a_1093_;
v_isShared_1146_ = v_isSharedCheck_1154_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_buildTime_1143_);
lean_inc(v_trace_1142_);
lean_inc(v_log_1139_);
lean_dec(v_a_1093_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1154_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1147_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6));
v___x_1148_ = lean_array_get_size(v_log_1139_);
v___x_1149_ = lean_array_push(v_log_1139_, v___x_1147_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1149_);
v___x_1151_ = v___x_1145_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_trace_1142_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_buildTime_1143_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, sizeof(void*)*3, v_action_1140_);
lean_ctor_set_uint8(v_reuseFailAlloc_1153_, sizeof(void*)*3 + 1, v_wantsRebuild_1141_);
v___x_1151_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1148_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
return v___x_1152_;
}
}
}
}
else
{
lean_object* v_log_1155_; uint8_t v_action_1156_; uint8_t v_wantsRebuild_1157_; lean_object* v_trace_1158_; lean_object* v_buildTime_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v_scope_1097_);
lean_dec_ref(v_dir_1096_);
lean_dec(v_origName_1095_);
v_log_1155_ = lean_ctor_get(v_a_1093_, 0);
v_action_1156_ = lean_ctor_get_uint8(v_a_1093_, sizeof(void*)*3);
v_wantsRebuild_1157_ = lean_ctor_get_uint8(v_a_1093_, sizeof(void*)*3 + 1);
v_trace_1158_ = lean_ctor_get(v_a_1093_, 1);
v_buildTime_1159_ = lean_ctor_get(v_a_1093_, 2);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_a_1093_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1161_ = v_a_1093_;
v_isShared_1162_ = v_isSharedCheck_1170_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_buildTime_1159_);
lean_inc(v_trace_1158_);
lean_inc(v_log_1155_);
lean_dec(v_a_1093_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1170_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1163_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8));
v___x_1164_ = lean_array_get_size(v_log_1155_);
v___x_1165_ = lean_array_push(v_log_1155_, v___x_1163_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1165_);
v___x_1167_ = v___x_1161_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_trace_1158_);
lean_ctor_set(v_reuseFailAlloc_1169_, 2, v_buildTime_1159_);
lean_ctor_set_uint8(v_reuseFailAlloc_1169_, sizeof(void*)*3, v_action_1156_);
lean_ctor_set_uint8(v_reuseFailAlloc_1169_, sizeof(void*)*3 + 1, v_wantsRebuild_1157_);
v___x_1167_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1164_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___boxed(lean_object* v_self_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1171_, v_a_1172_, v_a_1173_);
lean_dec_ref(v_a_1172_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object* v_self_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1176_, v_a_1181_, v_a_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object* v_self_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(v_self_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object* v_self_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_rev_1207_; lean_object* v_log_1208_; uint8_t v_action_1209_; uint8_t v_wantsRebuild_1210_; lean_object* v_trace_1211_; lean_object* v_buildTime_1212_; lean_object* v_dir_1221_; lean_object* v_config_1222_; lean_object* v_remoteUrl_1223_; lean_object* v_buildArchive_1224_; lean_object* v___y_1226_; uint8_t v___y_1227_; lean_object* v___y_1228_; uint8_t v___y_1229_; lean_object* v___y_1230_; lean_object* v_val_1231_; lean_object* v___y_1251_; lean_object* v_releaseRepo_1282_; 
v_dir_1221_ = lean_ctor_get(v_self_1203_, 4);
lean_inc_ref(v_dir_1221_);
v_config_1222_ = lean_ctor_get(v_self_1203_, 6);
lean_inc_ref(v_config_1222_);
v_remoteUrl_1223_ = lean_ctor_get(v_self_1203_, 11);
lean_inc_ref(v_remoteUrl_1223_);
v_buildArchive_1224_ = lean_ctor_get(v_self_1203_, 21);
lean_inc_ref(v_buildArchive_1224_);
lean_dec_ref(v_self_1203_);
v_releaseRepo_1282_ = lean_ctor_get(v_config_1222_, 10);
lean_inc(v_releaseRepo_1282_);
lean_dec_ref(v_config_1222_);
if (lean_obj_tag(v_releaseRepo_1282_) == 0)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1283_ = lean_string_utf8_byte_size(v_remoteUrl_1223_);
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = lean_nat_dec_eq(v___x_1283_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1286_, 0, v_remoteUrl_1223_);
v___y_1251_ = v___x_1286_;
goto v___jp_1250_;
}
else
{
lean_dec_ref(v_remoteUrl_1223_);
v___y_1251_ = v_releaseRepo_1282_;
goto v___jp_1250_;
}
}
else
{
lean_dec_ref(v_remoteUrl_1223_);
v___y_1251_ = v_releaseRepo_1282_;
goto v___jp_1250_;
}
v___jp_1206_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1213_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0));
v___x_1214_ = lean_string_append(v___x_1213_, v_rev_1207_);
lean_dec_ref(v_rev_1207_);
v___x_1215_ = 3;
v___x_1216_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1216_, 0, v___x_1214_);
lean_ctor_set_uint8(v___x_1216_, sizeof(void*)*1, v___x_1215_);
v___x_1217_ = lean_array_get_size(v_log_1208_);
v___x_1218_ = lean_array_push(v_log_1208_, v___x_1216_);
v___x_1219_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v_trace_1211_);
lean_ctor_set(v___x_1219_, 2, v_buildTime_1212_);
lean_ctor_set_uint8(v___x_1219_, sizeof(void*)*3, v_action_1209_);
lean_ctor_set_uint8(v___x_1219_, sizeof(void*)*3 + 1, v_wantsRebuild_1210_);
v___x_1220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1217_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
return v___x_1220_;
}
v___jp_1225_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
lean_inc_ref(v_dir_1221_);
v___x_1233_ = l_Lake_GitRepo_findTag_x3f(v___x_1232_, v_dir_1221_);
if (lean_obj_tag(v___x_1233_) == 1)
{
lean_object* v_val_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_dec_ref(v_dir_1221_);
v_val_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_val_1234_);
lean_dec_ref_known(v___x_1233_, 1);
v___x_1235_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1235_, 0, v___y_1228_);
lean_ctor_set(v___x_1235_, 1, v___y_1226_);
lean_ctor_set(v___x_1235_, 2, v___y_1230_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*3, v___y_1227_);
lean_ctor_set_uint8(v___x_1235_, sizeof(void*)*3 + 1, v___y_1229_);
v___x_1236_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1));
v___x_1237_ = lean_string_append(v_val_1231_, v___x_1236_);
v___x_1238_ = lean_string_append(v___x_1237_, v_val_1234_);
lean_dec(v_val_1234_);
v___x_1239_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2));
v___x_1240_ = lean_string_append(v___x_1238_, v___x_1239_);
v___x_1241_ = lean_string_append(v___x_1240_, v_buildArchive_1224_);
lean_dec_ref(v_buildArchive_1224_);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v___x_1235_);
return v___x_1242_;
}
else
{
lean_object* v___x_1243_; 
lean_dec(v___x_1233_);
lean_dec_ref(v_val_1231_);
lean_dec_ref(v_buildArchive_1224_);
v___x_1243_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1232_, v_dir_1221_);
if (lean_obj_tag(v___x_1243_) == 1)
{
lean_object* v_val_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_val_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1244_);
lean_dec_ref_known(v___x_1243_, 1);
v___x_1245_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3));
v___x_1246_ = lean_string_append(v___x_1245_, v_val_1244_);
lean_dec(v_val_1244_);
v___x_1247_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4));
v___x_1248_ = lean_string_append(v___x_1246_, v___x_1247_);
v_rev_1207_ = v___x_1248_;
v_log_1208_ = v___y_1228_;
v_action_1209_ = v___y_1227_;
v_wantsRebuild_1210_ = v___y_1229_;
v_trace_1211_ = v___y_1226_;
v_buildTime_1212_ = v___y_1230_;
goto v___jp_1206_;
}
else
{
lean_object* v___x_1249_; 
lean_dec(v___x_1243_);
v___x_1249_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_rev_1207_ = v___x_1249_;
v_log_1208_ = v___y_1228_;
v_action_1209_ = v___y_1227_;
v_wantsRebuild_1210_ = v___y_1229_;
v_trace_1211_ = v___y_1226_;
v_buildTime_1212_ = v___y_1230_;
goto v___jp_1206_;
}
}
}
v___jp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_dir_1221_);
v___x_1253_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v___x_1252_, v_dir_1221_);
if (lean_obj_tag(v___y_1251_) == 0)
{
if (lean_obj_tag(v___x_1253_) == 1)
{
lean_object* v_log_1254_; uint8_t v_action_1255_; uint8_t v_wantsRebuild_1256_; lean_object* v_trace_1257_; lean_object* v_buildTime_1258_; lean_object* v_val_1259_; 
v_log_1254_ = lean_ctor_get(v_a_1204_, 0);
lean_inc_ref(v_log_1254_);
v_action_1255_ = lean_ctor_get_uint8(v_a_1204_, sizeof(void*)*3);
v_wantsRebuild_1256_ = lean_ctor_get_uint8(v_a_1204_, sizeof(void*)*3 + 1);
v_trace_1257_ = lean_ctor_get(v_a_1204_, 1);
lean_inc_ref(v_trace_1257_);
v_buildTime_1258_ = lean_ctor_get(v_a_1204_, 2);
lean_inc(v_buildTime_1258_);
lean_dec_ref(v_a_1204_);
v_val_1259_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_val_1259_);
lean_dec_ref_known(v___x_1253_, 1);
v___y_1226_ = v_trace_1257_;
v___y_1227_ = v_action_1255_;
v___y_1228_ = v_log_1254_;
v___y_1229_ = v_wantsRebuild_1256_;
v___y_1230_ = v_buildTime_1258_;
v_val_1231_ = v_val_1259_;
goto v___jp_1225_;
}
else
{
lean_object* v_log_1260_; uint8_t v_action_1261_; uint8_t v_wantsRebuild_1262_; lean_object* v_trace_1263_; lean_object* v_buildTime_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v___x_1253_);
lean_dec_ref(v_buildArchive_1224_);
lean_dec_ref(v_dir_1221_);
v_log_1260_ = lean_ctor_get(v_a_1204_, 0);
v_action_1261_ = lean_ctor_get_uint8(v_a_1204_, sizeof(void*)*3);
v_wantsRebuild_1262_ = lean_ctor_get_uint8(v_a_1204_, sizeof(void*)*3 + 1);
v_trace_1263_ = lean_ctor_get(v_a_1204_, 1);
v_buildTime_1264_ = lean_ctor_get(v_a_1204_, 2);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_a_1204_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1266_ = v_a_1204_;
v_isShared_1267_ = v_isSharedCheck_1275_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_buildTime_1264_);
lean_inc(v_trace_1263_);
lean_inc(v_log_1260_);
lean_dec(v_a_1204_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1275_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1268_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6));
v___x_1269_ = lean_array_get_size(v_log_1260_);
v___x_1270_ = lean_array_push(v_log_1260_, v___x_1268_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1270_);
v___x_1272_ = v___x_1266_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1270_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_trace_1263_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_buildTime_1264_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*3, v_action_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1274_, sizeof(void*)*3 + 1, v_wantsRebuild_1262_);
v___x_1272_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1269_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
return v___x_1273_;
}
}
}
}
else
{
lean_object* v_log_1276_; uint8_t v_action_1277_; uint8_t v_wantsRebuild_1278_; lean_object* v_trace_1279_; lean_object* v_buildTime_1280_; lean_object* v_val_1281_; 
lean_dec(v___x_1253_);
v_log_1276_ = lean_ctor_get(v_a_1204_, 0);
lean_inc_ref(v_log_1276_);
v_action_1277_ = lean_ctor_get_uint8(v_a_1204_, sizeof(void*)*3);
v_wantsRebuild_1278_ = lean_ctor_get_uint8(v_a_1204_, sizeof(void*)*3 + 1);
v_trace_1279_ = lean_ctor_get(v_a_1204_, 1);
lean_inc_ref(v_trace_1279_);
v_buildTime_1280_ = lean_ctor_get(v_a_1204_, 2);
lean_inc(v_buildTime_1280_);
lean_dec_ref(v_a_1204_);
v_val_1281_ = lean_ctor_get(v___y_1251_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v___y_1251_, 1);
v___y_1226_ = v_trace_1279_;
v___y_1227_ = v_action_1277_;
v___y_1228_ = v_log_1276_;
v___y_1229_ = v_wantsRebuild_1278_;
v___y_1230_ = v_buildTime_1280_;
v_val_1231_ = v_val_1281_;
goto v___jp_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(lean_object* v_self_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1287_, v_a_1288_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object* v_self_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1291_, v_a_1297_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object* v_self_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(v_self_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(lean_object* v_val_1309_, lean_object* v_a_x3f_1310_, lean_object* v___y_1311_){
_start:
{
lean_object* v___x_1313_; lean_object* v_log_1314_; uint8_t v_action_1315_; uint8_t v_wantsRebuild_1316_; lean_object* v_trace_1317_; lean_object* v_buildTime_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1329_; 
v___x_1313_ = lean_io_mono_ms_now();
v_log_1314_ = lean_ctor_get(v___y_1311_, 0);
v_action_1315_ = lean_ctor_get_uint8(v___y_1311_, sizeof(void*)*3);
v_wantsRebuild_1316_ = lean_ctor_get_uint8(v___y_1311_, sizeof(void*)*3 + 1);
v_trace_1317_ = lean_ctor_get(v___y_1311_, 1);
v_buildTime_1318_ = lean_ctor_get(v___y_1311_, 2);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___y_1311_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1320_ = v___y_1311_;
v_isShared_1321_ = v_isSharedCheck_1329_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_buildTime_1318_);
lean_inc(v_trace_1317_);
lean_inc(v_log_1314_);
lean_dec(v___y_1311_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1329_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1322_ = lean_nat_sub(v___x_1313_, v_val_1309_);
lean_dec(v___x_1313_);
v___x_1323_ = lean_box(0);
v___x_1324_ = lean_nat_add(v_buildTime_1318_, v___x_1322_);
lean_dec(v___x_1322_);
lean_dec(v_buildTime_1318_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 2, v___x_1324_);
v___x_1326_ = v___x_1320_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_log_1314_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_trace_1317_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v___x_1324_);
lean_ctor_set_uint8(v_reuseFailAlloc_1328_, sizeof(void*)*3, v_action_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1328_, sizeof(void*)*3 + 1, v_wantsRebuild_1316_);
v___x_1326_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1323_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
return v___x_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0___boxed(lean_object* v_val_1330_, lean_object* v_a_x3f_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v_val_1330_, v_a_x3f_1331_, v___y_1332_);
lean_dec(v_a_x3f_1331_);
lean_dec(v_val_1330_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(lean_object* v_url_1340_, lean_object* v_archiveFile_1341_, lean_object* v_headers_1342_, lean_object* v_depTrace_1343_, lean_object* v_traceFile_1344_, uint8_t v_action_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_){
_start:
{
lean_object* v_a_1350_; lean_object* v_a_1351_; lean_object* v_log_1354_; uint8_t v_action_1355_; uint8_t v_wantsRebuild_1356_; lean_object* v_trace_1357_; lean_object* v_buildTime_1358_; lean_object* v_toBuildConfig_1364_; lean_object* v_log_1365_; uint8_t v_action_1366_; uint8_t v_wantsRebuild_1367_; lean_object* v_trace_1368_; lean_object* v_buildTime_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1459_; 
v_toBuildConfig_1364_ = lean_ctor_get(v_a_1346_, 0);
v_log_1365_ = lean_ctor_get(v_a_1347_, 0);
v_action_1366_ = lean_ctor_get_uint8(v_a_1347_, sizeof(void*)*3);
v_wantsRebuild_1367_ = lean_ctor_get_uint8(v_a_1347_, sizeof(void*)*3 + 1);
v_trace_1368_ = lean_ctor_get(v_a_1347_, 1);
v_buildTime_1369_ = lean_ctor_get(v_a_1347_, 2);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_a_1347_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1371_ = v_a_1347_;
v_isShared_1372_ = v_isSharedCheck_1459_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_buildTime_1369_);
lean_inc(v_trace_1368_);
lean_inc(v_log_1365_);
lean_dec(v_a_1347_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1459_;
goto v_resetjp_1370_;
}
v___jp_1349_:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_a_1350_);
lean_ctor_set(v___x_1352_, 1, v_a_1351_);
return v___x_1352_;
}
v___jp_1353_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1359_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1));
v___x_1360_ = lean_array_get_size(v_log_1354_);
v___x_1361_ = lean_array_push(v_log_1354_, v___x_1359_);
v___x_1362_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v_trace_1357_);
lean_ctor_set(v___x_1362_, 2, v_buildTime_1358_);
lean_ctor_set_uint8(v___x_1362_, sizeof(void*)*3, v_action_1355_);
lean_ctor_set_uint8(v___x_1362_, sizeof(void*)*3 + 1, v_wantsRebuild_1356_);
v___x_1363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1360_);
lean_ctor_set(v___x_1363_, 1, v___x_1362_);
return v___x_1363_;
}
v_resetjp_1370_:
{
uint8_t v_noBuild_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_noBuild_1373_ = lean_ctor_get_uint8(v_toBuildConfig_1364_, sizeof(void*)*4 + 2);
v___x_1374_ = l_Lake_JobAction_merge(v_action_1366_, v_action_1345_);
v___x_1375_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2));
lean_inc_ref(v_traceFile_1344_);
v___x_1376_ = l_System_FilePath_addExtension(v_traceFile_1344_, v___x_1375_);
if (v_noBuild_1373_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v_a_1380_; lean_object* v_a_1381_; 
v___x_1377_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1365_);
v___x_1378_ = l_Lake_download(v_url_1340_, v_archiveFile_1341_, v_headers_1342_, v_log_1365_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1385_; lean_object* v_a_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v_a_1385_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1385_);
v_a_1386_ = lean_ctor_get(v___x_1378_, 1);
lean_inc(v_a_1386_);
lean_dec_ref_known(v___x_1378_, 2);
v___x_1387_ = lean_array_get_size(v_log_1365_);
lean_dec_ref(v_log_1365_);
v___x_1388_ = lean_array_get_size(v_a_1386_);
v___x_1389_ = l_Array_extract___redArg(v_a_1386_, v___x_1387_, v___x_1388_);
v___x_1390_ = lean_box(0);
v___x_1391_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1343_, v___x_1390_, v___x_1389_);
v___x_1392_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1344_, v___x_1391_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1429_; 
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1392_, 0);
lean_dec(v_unused_1430_);
v___x_1394_ = v___x_1392_;
v_isShared_1395_ = v_isSharedCheck_1429_;
goto v_resetjp_1393_;
}
else
{
lean_dec(v___x_1392_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1429_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lake_removeFileIfExists(v___x_1376_);
lean_dec_ref(v___x_1376_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1419_; 
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; 
v_unused_1420_ = lean_ctor_get(v___x_1396_, 0);
lean_dec(v_unused_1420_);
v___x_1398_ = v___x_1396_;
v_isShared_1399_ = v_isSharedCheck_1419_;
goto v_resetjp_1397_;
}
else
{
lean_dec(v___x_1396_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1419_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v_a_1386_);
v___x_1401_ = v___x_1371_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1386_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_trace_1368_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_buildTime_1369_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*3 + 1, v_wantsRebuild_1367_);
v___x_1401_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1403_; 
lean_ctor_set_uint8(v___x_1401_, sizeof(void*)*3, v___x_1374_);
lean_inc(v_a_1385_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v_a_1385_);
v___x_1403_ = v___x_1398_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1385_);
v___x_1403_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1405_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set_tag(v___x_1394_, 1);
lean_ctor_set(v___x_1394_, 0, v___x_1403_);
v___x_1405_ = v___x_1394_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
v___x_1406_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1377_, v___x_1405_, v___x_1401_);
lean_dec_ref(v___x_1405_);
lean_dec(v___x_1377_);
v_a_1407_ = lean_ctor_get(v___x_1406_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v___x_1406_, 0);
lean_dec(v_unused_1415_);
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v_a_1385_);
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1385_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
lean_del_object(v___x_1394_);
lean_dec(v_a_1385_);
v_a_1421_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1396_, 1);
v___x_1422_ = lean_io_error_to_string(v_a_1421_);
v___x_1423_ = 3;
v___x_1424_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_ctor_set_uint8(v___x_1424_, sizeof(void*)*1, v___x_1423_);
v___x_1425_ = lean_array_push(v_a_1386_, v___x_1424_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1425_);
v___x_1427_ = v___x_1371_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_trace_1368_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_buildTime_1369_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*3 + 1, v_wantsRebuild_1367_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_ctor_set_uint8(v___x_1427_, sizeof(void*)*3, v___x_1374_);
v_a_1380_ = v___x_1388_;
v_a_1381_ = v___x_1427_;
goto v___jp_1379_;
}
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
lean_dec(v_a_1385_);
lean_dec_ref(v___x_1376_);
v_a_1431_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1392_, 1);
v___x_1432_ = lean_io_error_to_string(v_a_1431_);
v___x_1433_ = 3;
v___x_1434_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*1, v___x_1433_);
v___x_1435_ = lean_array_push(v_a_1386_, v___x_1434_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1435_);
v___x_1437_ = v___x_1371_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_trace_1368_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v_buildTime_1369_);
lean_ctor_set_uint8(v_reuseFailAlloc_1438_, sizeof(void*)*3 + 1, v_wantsRebuild_1367_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_ctor_set_uint8(v___x_1437_, sizeof(void*)*3, v___x_1374_);
v_a_1380_ = v___x_1388_;
v_a_1381_ = v___x_1437_;
goto v___jp_1379_;
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v_a_1440_; lean_object* v___x_1442_; 
lean_dec_ref(v___x_1376_);
lean_dec_ref(v_log_1365_);
lean_dec_ref(v_traceFile_1344_);
v_a_1439_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1439_);
v_a_1440_ = lean_ctor_get(v___x_1378_, 1);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1378_, 2);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v_a_1440_);
v___x_1442_ = v___x_1371_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1440_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_trace_1368_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_buildTime_1369_);
lean_ctor_set_uint8(v_reuseFailAlloc_1443_, sizeof(void*)*3 + 1, v_wantsRebuild_1367_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_ctor_set_uint8(v___x_1442_, sizeof(void*)*3, v___x_1374_);
v_a_1380_ = v_a_1439_;
v_a_1381_ = v___x_1442_;
goto v___jp_1379_;
}
}
v___jp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v_a_1384_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1377_, v___x_1382_, v_a_1381_);
lean_dec(v___x_1377_);
v_a_1384_ = lean_ctor_get(v___x_1383_, 1);
lean_inc(v_a_1384_);
lean_dec_ref(v___x_1383_);
v_a_1350_ = v_a_1380_;
v_a_1351_ = v_a_1384_;
goto v___jp_1349_;
}
}
else
{
uint8_t v___x_1444_; 
lean_dec_ref(v_archiveFile_1341_);
lean_dec_ref(v_url_1340_);
v___x_1444_ = l_System_FilePath_pathExists(v_traceFile_1344_);
lean_dec_ref(v_traceFile_1344_);
if (v___x_1444_ == 0)
{
lean_dec_ref(v___x_1376_);
lean_del_object(v___x_1371_);
v_log_1354_ = v_log_1365_;
v_action_1355_ = v___x_1374_;
v_wantsRebuild_1356_ = v_noBuild_1373_;
v_trace_1357_ = v_trace_1368_;
v_buildTime_1358_ = v_buildTime_1369_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1445_ = lean_box(0);
v___x_1446_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1447_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1343_, v___x_1445_, v___x_1446_);
v___x_1448_ = l_Lake_BuildMetadata_writeFile(v___x_1376_, v___x_1447_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_dec_ref_known(v___x_1448_, 1);
lean_del_object(v___x_1371_);
v_log_1354_ = v_log_1365_;
v_action_1355_ = v___x_1374_;
v_wantsRebuild_1356_ = v_noBuild_1373_;
v_trace_1357_ = v_trace_1368_;
v_buildTime_1358_ = v_buildTime_1369_;
goto v___jp_1353_;
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
v___x_1450_ = lean_io_error_to_string(v_a_1449_);
v___x_1451_ = 3;
v___x_1452_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set_uint8(v___x_1452_, sizeof(void*)*1, v___x_1451_);
v___x_1453_ = lean_array_get_size(v_log_1365_);
v___x_1454_ = lean_array_push(v_log_1365_, v___x_1452_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1454_);
v___x_1456_ = v___x_1371_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_trace_1368_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_buildTime_1369_);
v___x_1456_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1457_; 
lean_ctor_set_uint8(v___x_1456_, sizeof(void*)*3, v___x_1374_);
lean_ctor_set_uint8(v___x_1456_, sizeof(void*)*3 + 1, v_noBuild_1373_);
v___x_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1453_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
return v___x_1457_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___boxed(lean_object* v_url_1460_, lean_object* v_archiveFile_1461_, lean_object* v_headers_1462_, lean_object* v_depTrace_1463_, lean_object* v_traceFile_1464_, lean_object* v_action_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
uint8_t v_action_boxed_1469_; lean_object* v_res_1470_; 
v_action_boxed_1469_ = lean_unbox(v_action_1465_);
v_res_1470_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1460_, v_archiveFile_1461_, v_headers_1462_, v_depTrace_1463_, v_traceFile_1464_, v_action_boxed_1469_, v_a_1466_, v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec_ref(v_depTrace_1463_);
lean_dec_ref(v_headers_1462_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(lean_object* v_url_1471_, lean_object* v_archiveFile_1472_, lean_object* v_headers_1473_, lean_object* v_a_1474_, lean_object* v_depTrace_1475_, lean_object* v_traceFile_1476_, uint8_t v_action_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1471_, v_archiveFile_1472_, v_headers_1473_, v_depTrace_1475_, v_traceFile_1476_, v_action_1477_, v_a_1481_, v_a_1482_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___boxed(lean_object* v_url_1485_, lean_object* v_archiveFile_1486_, lean_object* v_headers_1487_, lean_object* v_a_1488_, lean_object* v_depTrace_1489_, lean_object* v_traceFile_1490_, lean_object* v_action_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
uint8_t v_action_boxed_1498_; lean_object* v_res_1499_; 
v_action_boxed_1498_ = lean_unbox(v_action_1491_);
v_res_1499_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(v_url_1485_, v_archiveFile_1486_, v_headers_1487_, v_a_1488_, v_depTrace_1489_, v_traceFile_1490_, v_action_boxed_1498_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec_ref(v_depTrace_1489_);
lean_dec_ref(v_a_1488_);
lean_dec_ref(v_headers_1487_);
return v_res_1499_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
if (lean_obj_tag(v_x_1500_) == 0)
{
if (lean_obj_tag(v_x_1501_) == 0)
{
uint8_t v___x_1502_; 
v___x_1502_ = 1;
return v___x_1502_;
}
else
{
uint8_t v___x_1503_; 
v___x_1503_ = 0;
return v___x_1503_;
}
}
else
{
if (lean_obj_tag(v_x_1501_) == 0)
{
uint8_t v___x_1504_; 
v___x_1504_ = 0;
return v___x_1504_;
}
else
{
lean_object* v_val_1505_; lean_object* v_val_1506_; uint64_t v___x_1507_; uint64_t v___x_1508_; uint8_t v___x_1509_; 
v_val_1505_ = lean_ctor_get(v_x_1500_, 0);
v_val_1506_ = lean_ctor_get(v_x_1501_, 0);
v___x_1507_ = lean_unbox_uint64(v_val_1505_);
v___x_1508_ = lean_unbox_uint64(v_val_1506_);
v___x_1509_ = lean_uint64_dec_eq(v___x_1507_, v___x_1508_);
return v___x_1509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(lean_object* v_x_1510_, lean_object* v_x_1511_){
_start:
{
uint8_t v_res_1512_; lean_object* v_r_1513_; 
v_res_1512_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v_x_1510_, v_x_1511_);
lean_dec(v_x_1511_);
lean_dec(v_x_1510_);
v_r_1513_ = lean_box(v_res_1512_);
return v_r_1513_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object* v_info_1514_, lean_object* v_self_1515_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_io_metadata(v_info_1514_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v_modified_1519_; uint8_t v___x_1520_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v_modified_1519_ = lean_ctor_get(v_a_1518_, 1);
lean_inc_ref(v_modified_1519_);
lean_dec(v_a_1518_);
v___x_1520_ = l_IO_FS_instOrdSystemTime_ord(v_self_1515_, v_modified_1519_);
lean_dec_ref(v_modified_1519_);
if (v___x_1520_ == 0)
{
uint8_t v___x_1521_; 
v___x_1521_ = 1;
return v___x_1521_;
}
else
{
uint8_t v___x_1522_; 
v___x_1522_ = 0;
return v___x_1522_;
}
}
else
{
uint8_t v___x_1523_; 
lean_dec_ref_known(v___x_1517_, 1);
v___x_1523_ = 0;
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object* v_info_1524_, lean_object* v_self_1525_, lean_object* v_a_1526_){
_start:
{
uint8_t v_res_1527_; lean_object* v_r_1528_; 
v_res_1527_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1524_, v_self_1525_);
lean_dec_ref(v_self_1525_);
lean_dec_ref(v_info_1524_);
v_r_1528_ = lean_box(v_res_1527_);
return v_r_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(lean_object* v_info_1529_, lean_object* v_depTrace_1530_, lean_object* v_depHash_1531_, lean_object* v_oldTrace_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
uint64_t v_hash_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v_hash_1536_ = lean_ctor_get_uint64(v_depTrace_1530_, sizeof(void*)*3);
v___x_1537_ = lean_box_uint64(v_hash_1536_);
v___x_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
v___x_1539_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v___x_1538_, v_depHash_1531_);
lean_dec_ref_known(v___x_1538_, 1);
if (v___x_1539_ == 0)
{
lean_object* v_toBuildConfig_1540_; uint8_t v_oldMode_1541_; 
v_toBuildConfig_1540_ = lean_ctor_get(v_a_1533_, 0);
v_oldMode_1541_ = lean_ctor_get_uint8(v_toBuildConfig_1540_, sizeof(void*)*4);
if (v_oldMode_1541_ == 0)
{
uint8_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = 0;
v___x_1543_ = lean_box(v___x_1542_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v_a_1534_);
return v___x_1544_;
}
else
{
uint8_t v___x_1545_; 
v___x_1545_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1529_, v_oldTrace_1532_);
if (v___x_1545_ == 0)
{
uint8_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = 0;
v___x_1547_ = lean_box(v___x_1546_);
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
lean_ctor_set(v___x_1548_, 1, v_a_1534_);
return v___x_1548_;
}
else
{
uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = 1;
v___x_1550_ = lean_box(v___x_1549_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v_a_1534_);
return v___x_1551_;
}
}
}
else
{
uint8_t v___x_1552_; 
v___x_1552_ = l_System_FilePath_pathExists(v_info_1529_);
if (v___x_1552_ == 0)
{
uint8_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = 0;
v___x_1554_ = lean_box(v___x_1553_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v_a_1534_);
return v___x_1555_;
}
else
{
uint8_t v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = 2;
v___x_1557_ = lean_box(v___x_1556_);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v_a_1534_);
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(lean_object* v_info_1559_, lean_object* v_depTrace_1560_, lean_object* v_depHash_1561_, lean_object* v_oldTrace_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1559_, v_depTrace_1560_, v_depHash_1561_, v_oldTrace_1562_, v_a_1563_, v_a_1564_);
lean_dec_ref(v_a_1563_);
lean_dec_ref(v_oldTrace_1562_);
lean_dec(v_depHash_1561_);
lean_dec_ref(v_depTrace_1560_);
lean_dec_ref(v_info_1559_);
return v_res_1566_;
}
}
static lean_object* _init_l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0(void){
_start:
{
uint8_t v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = 0;
v___x_1568_ = l_Lake_OutputStatus_ctorIdx(v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(lean_object* v_a_1569_, lean_object* v_info_1570_, lean_object* v_depTrace_1571_, lean_object* v_savedTrace_1572_, lean_object* v_oldTrace_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
if (lean_obj_tag(v_savedTrace_1572_) == 2)
{
lean_object* v_data_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1631_; 
v_data_1580_ = lean_ctor_get(v_savedTrace_1572_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_savedTrace_1572_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1582_ = v_savedTrace_1572_;
v_isShared_1583_ = v_isSharedCheck_1631_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_data_1580_);
lean_dec(v_savedTrace_1572_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1631_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
uint64_t v_depHash_1584_; lean_object* v_log_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v_depHash_1584_ = lean_ctor_get_uint64(v_data_1580_, sizeof(void*)*3);
v_log_1585_ = lean_ctor_get(v_data_1580_, 2);
lean_inc_ref(v_log_1585_);
lean_dec_ref(v_data_1580_);
v___x_1586_ = lean_box_uint64(v_depHash_1584_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set_tag(v___x_1582_, 1);
lean_ctor_set(v___x_1582_, 0, v___x_1586_);
v___x_1588_ = v___x_1582_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; lean_object* v_a_1590_; lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1629_; 
v___x_1589_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1570_, v_depTrace_1571_, v___x_1588_, v_oldTrace_1573_, v_a_1577_, v_a_1578_);
lean_dec_ref(v___x_1588_);
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_a_1591_ = lean_ctor_get(v___x_1589_, 1);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1593_ = v___x_1589_;
v_isShared_1594_ = v_isSharedCheck_1629_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1629_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___y_1596_; uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v___x_1600_ = lean_unbox(v_a_1590_);
v___x_1601_ = l_Lake_OutputStatus_ctorIdx(v___x_1600_);
v___x_1602_ = lean_obj_once(&l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0, &l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0_once, _init_l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0);
v___x_1603_ = lean_nat_dec_eq(v___x_1601_, v___x_1602_);
lean_dec(v___x_1601_);
if (v___x_1603_ == 0)
{
lean_object* v_log_1604_; uint8_t v_action_1605_; uint8_t v_wantsRebuild_1606_; lean_object* v_trace_1607_; lean_object* v_buildTime_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1628_; 
v_log_1604_ = lean_ctor_get(v_a_1591_, 0);
v_action_1605_ = lean_ctor_get_uint8(v_a_1591_, sizeof(void*)*3);
v_wantsRebuild_1606_ = lean_ctor_get_uint8(v_a_1591_, sizeof(void*)*3 + 1);
v_trace_1607_ = lean_ctor_get(v_a_1591_, 1);
v_buildTime_1608_ = lean_ctor_get(v_a_1591_, 2);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_a_1591_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1610_ = v_a_1591_;
v_isShared_1611_ = v_isSharedCheck_1628_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_buildTime_1608_);
lean_inc(v_trace_1607_);
lean_inc(v_log_1604_);
lean_dec(v_a_1591_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1628_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
uint8_t v___x_1612_; uint8_t v___x_1613_; lean_object* v___x_1615_; 
v___x_1612_ = 2;
v___x_1613_ = l_Lake_JobAction_merge(v_action_1605_, v___x_1612_);
if (v_isShared_1611_ == 0)
{
v___x_1615_ = v___x_1610_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_log_1604_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_trace_1607_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_buildTime_1608_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*3 + 1, v_wantsRebuild_1606_);
v___x_1615_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; 
lean_ctor_set_uint8(v___x_1615_, sizeof(void*)*3, v___x_1613_);
v___x_1616_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1585_, v_a_1569_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v___x_1615_);
lean_dec_ref(v_log_1585_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 1);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 2);
v___y_1596_ = v_a_1617_;
goto v___jp_1595_;
}
else
{
lean_object* v_a_1618_; lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_del_object(v___x_1593_);
lean_dec(v_a_1590_);
v_a_1618_ = lean_ctor_get(v___x_1616_, 0);
v_a_1619_ = lean_ctor_get(v___x_1616_, 1);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1616_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_inc(v_a_1618_);
lean_dec(v___x_1616_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1618_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_1585_);
v___y_1596_ = v_a_1591_;
goto v___jp_1595_;
}
v___jp_1595_:
{
lean_object* v___x_1598_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 1, v___y_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1590_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___y_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_1632_; uint8_t v_oldMode_1633_; 
lean_dec(v_savedTrace_1572_);
v_toBuildConfig_1632_ = lean_ctor_get(v_a_1577_, 0);
v_oldMode_1633_ = lean_ctor_get_uint8(v_toBuildConfig_1632_, sizeof(void*)*4);
if (v_oldMode_1633_ == 0)
{
uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = 0;
v___x_1635_ = lean_box(v___x_1634_);
v___x_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v_a_1578_);
return v___x_1636_;
}
else
{
uint8_t v___x_1637_; 
v___x_1637_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1570_, v_oldTrace_1573_);
if (v___x_1637_ == 0)
{
uint8_t v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1638_ = 0;
v___x_1639_ = lean_box(v___x_1638_);
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_ctor_set(v___x_1640_, 1, v_a_1578_);
return v___x_1640_;
}
else
{
uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1641_ = 1;
v___x_1642_ = lean_box(v___x_1641_);
v___x_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v_a_1578_);
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object* v_a_1644_, lean_object* v_info_1645_, lean_object* v_depTrace_1646_, lean_object* v_savedTrace_1647_, lean_object* v_oldTrace_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_1644_, v_info_1645_, v_depTrace_1646_, v_savedTrace_1647_, v_oldTrace_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec_ref(v_oldTrace_1648_);
lean_dec_ref(v_depTrace_1646_);
lean_dec_ref(v_info_1645_);
lean_dec_ref(v_a_1644_);
return v_res_1655_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_unsigned_to_nat(0u);
v___x_1661_ = lean_nat_to_int(v___x_1660_);
return v___x_1661_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4(void){
_start:
{
uint32_t v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1662_ = 0;
v___x_1663_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3);
v___x_1664_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
lean_ctor_set_uint32(v___x_1664_, sizeof(void*)*1, v___x_1662_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(lean_object* v_self_1665_, lean_object* v_url_1666_, lean_object* v_archiveFile_1667_, lean_object* v_headers_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v_a_1677_; lean_object* v_a_1678_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; uint8_t v___y_1684_; uint8_t v___y_1685_; lean_object* v___y_1686_; uint8_t v_a_1712_; lean_object* v_a_1713_; lean_object* v_log_1732_; uint8_t v_action_1733_; uint8_t v_wantsRebuild_1734_; lean_object* v_trace_1735_; lean_object* v_buildTime_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1776_; 
v_log_1732_ = lean_ctor_get(v_a_1674_, 0);
v_action_1733_ = lean_ctor_get_uint8(v_a_1674_, sizeof(void*)*3);
v_wantsRebuild_1734_ = lean_ctor_get_uint8(v_a_1674_, sizeof(void*)*3 + 1);
v_trace_1735_ = lean_ctor_get(v_a_1674_, 1);
v_buildTime_1736_ = lean_ctor_get(v_a_1674_, 2);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_a_1674_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1738_ = v_a_1674_;
v_isShared_1739_ = v_isSharedCheck_1776_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_buildTime_1736_);
lean_inc(v_trace_1735_);
lean_inc(v_log_1732_);
lean_dec(v_a_1674_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1776_;
goto v_resetjp_1737_;
}
v___jp_1676_:
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1679_, 0, v_a_1677_);
lean_ctor_set(v___x_1679_, 1, v_a_1678_);
return v___x_1679_;
}
v___jp_1680_:
{
uint8_t v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; uint8_t v___x_1690_; 
v___x_1687_ = 1;
v___x_1688_ = l_Lake_untar(v_archiveFile_1667_, v___y_1683_, v___x_1687_, v___y_1686_);
v___x_1689_ = 3;
v___x_1690_ = l_Lake_JobAction_merge(v___y_1685_, v___x_1689_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1691_; lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1700_; 
v_a_1691_ = lean_ctor_get(v___x_1688_, 0);
v_a_1692_ = lean_ctor_get(v___x_1688_, 1);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1694_ = v___x_1688_;
v_isShared_1695_ = v_isSharedCheck_1700_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_inc(v_a_1691_);
lean_dec(v___x_1688_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1700_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1696_, 0, v_a_1692_);
lean_ctor_set(v___x_1696_, 1, v___y_1682_);
lean_ctor_set(v___x_1696_, 2, v___y_1681_);
lean_ctor_set_uint8(v___x_1696_, sizeof(void*)*3, v___x_1690_);
lean_ctor_set_uint8(v___x_1696_, sizeof(void*)*3 + 1, v___y_1684_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 1, v___x_1696_);
v___x_1698_ = v___x_1694_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1691_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1710_; 
v_a_1701_ = lean_ctor_get(v___x_1688_, 0);
v_a_1702_ = lean_ctor_get(v___x_1688_, 1);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1704_ = v___x_1688_;
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_inc(v_a_1701_);
lean_dec(v___x_1688_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1706_, 0, v_a_1702_);
lean_ctor_set(v___x_1706_, 1, v___y_1682_);
lean_ctor_set(v___x_1706_, 2, v___y_1681_);
lean_ctor_set_uint8(v___x_1706_, sizeof(void*)*3, v___x_1690_);
lean_ctor_set_uint8(v___x_1706_, sizeof(void*)*3 + 1, v___y_1684_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v___x_1706_);
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1701_);
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
v___jp_1711_:
{
lean_object* v_config_1714_; lean_object* v_dir_1715_; lean_object* v_buildDir_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v_config_1714_ = lean_ctor_get(v_self_1665_, 6);
lean_inc_ref(v_config_1714_);
v_dir_1715_ = lean_ctor_get(v_self_1665_, 4);
lean_inc_ref(v_dir_1715_);
lean_dec_ref(v_self_1665_);
v_buildDir_1716_ = lean_ctor_get(v_config_1714_, 5);
lean_inc_ref(v_buildDir_1716_);
lean_dec_ref(v_config_1714_);
v___x_1717_ = l_System_FilePath_normalize(v_buildDir_1716_);
v___x_1718_ = l_Lake_joinRelative(v_dir_1715_, v___x_1717_);
v___x_1719_ = l_System_FilePath_pathExists(v___x_1718_);
if (v_a_1712_ == 0)
{
lean_object* v_log_1720_; uint8_t v_action_1721_; uint8_t v_wantsRebuild_1722_; lean_object* v_trace_1723_; lean_object* v_buildTime_1724_; 
v_log_1720_ = lean_ctor_get(v_a_1713_, 0);
lean_inc_ref(v_log_1720_);
v_action_1721_ = lean_ctor_get_uint8(v_a_1713_, sizeof(void*)*3);
v_wantsRebuild_1722_ = lean_ctor_get_uint8(v_a_1713_, sizeof(void*)*3 + 1);
v_trace_1723_ = lean_ctor_get(v_a_1713_, 1);
lean_inc_ref(v_trace_1723_);
v_buildTime_1724_ = lean_ctor_get(v_a_1713_, 2);
lean_inc(v_buildTime_1724_);
lean_dec_ref(v_a_1713_);
v___y_1681_ = v_buildTime_1724_;
v___y_1682_ = v_trace_1723_;
v___y_1683_ = v___x_1718_;
v___y_1684_ = v_wantsRebuild_1722_;
v___y_1685_ = v_action_1721_;
v___y_1686_ = v_log_1720_;
goto v___jp_1680_;
}
else
{
if (v___x_1719_ == 0)
{
lean_object* v_log_1725_; uint8_t v_action_1726_; uint8_t v_wantsRebuild_1727_; lean_object* v_trace_1728_; lean_object* v_buildTime_1729_; 
v_log_1725_ = lean_ctor_get(v_a_1713_, 0);
lean_inc_ref(v_log_1725_);
v_action_1726_ = lean_ctor_get_uint8(v_a_1713_, sizeof(void*)*3);
v_wantsRebuild_1727_ = lean_ctor_get_uint8(v_a_1713_, sizeof(void*)*3 + 1);
v_trace_1728_ = lean_ctor_get(v_a_1713_, 1);
lean_inc_ref(v_trace_1728_);
v_buildTime_1729_ = lean_ctor_get(v_a_1713_, 2);
lean_inc(v_buildTime_1729_);
lean_dec_ref(v_a_1713_);
v___y_1681_ = v_buildTime_1729_;
v___y_1682_ = v_trace_1728_;
v___y_1683_ = v___x_1718_;
v___y_1684_ = v_wantsRebuild_1727_;
v___y_1685_ = v_action_1726_;
v___y_1686_ = v_log_1725_;
goto v___jp_1680_;
}
else
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec_ref(v___x_1718_);
lean_dec_ref(v_archiveFile_1667_);
v___x_1730_ = lean_box(0);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
lean_ctor_set(v___x_1731_, 1, v_a_1713_);
return v___x_1731_;
}
}
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; lean_object* v_traceFile_1741_; lean_object* v___x_1742_; 
v___x_1740_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0));
lean_inc_ref(v_archiveFile_1667_);
v_traceFile_1741_ = l_System_FilePath_addExtension(v_archiveFile_1667_, v___x_1740_);
lean_inc_ref(v_traceFile_1741_);
v___x_1742_ = l_Lake_readTraceFile(v_traceFile_1741_, v_log_1732_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v_a_1744_; lean_object* v___x_1745_; uint64_t v___x_1746_; uint64_t v___x_1747_; uint64_t v_depTrace_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1753_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
v_a_1744_ = lean_ctor_get(v___x_1742_, 1);
lean_inc(v_a_1744_);
lean_dec_ref_known(v___x_1742_, 2);
v___x_1745_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1));
v___x_1746_ = l_Lake_Hash_nil;
v___x_1747_ = lean_string_hash(v_url_1666_);
v_depTrace_1748_ = lean_uint64_mix_hash(v___x_1746_, v___x_1747_);
v___x_1749_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2));
v___x_1750_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
v___x_1751_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1751_, 0, v___x_1749_);
lean_ctor_set(v___x_1751_, 1, v___x_1745_);
lean_ctor_set(v___x_1751_, 2, v___x_1750_);
lean_ctor_set_uint64(v___x_1751_, sizeof(void*)*3, v_depTrace_1748_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v_a_1744_);
v___x_1753_ = v___x_1738_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1744_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_trace_1735_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_buildTime_1736_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*3, v_action_1733_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*3 + 1, v_wantsRebuild_1734_);
v___x_1753_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_1669_, v_archiveFile_1667_, v___x_1751_, v_a_1743_, v___x_1750_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v___x_1753_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v_a_1756_; uint8_t v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
v_a_1756_ = lean_ctor_get(v___x_1754_, 1);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1754_, 2);
v___x_1757_ = lean_unbox(v_a_1755_);
lean_dec(v_a_1755_);
v___x_1758_ = l_Lake_OutputStatus_ctorIdx(v___x_1757_);
v___x_1759_ = lean_obj_once(&l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0, &l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0_once, _init_l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0);
v___x_1760_ = lean_nat_dec_eq(v___x_1758_, v___x_1759_);
lean_dec(v___x_1758_);
if (v___x_1760_ == 0)
{
uint8_t v___x_1761_; 
lean_dec_ref_known(v___x_1751_, 3);
lean_dec_ref(v_traceFile_1741_);
lean_dec_ref(v_url_1666_);
v___x_1761_ = 1;
v_a_1712_ = v___x_1761_;
v_a_1713_ = v_a_1756_;
goto v___jp_1711_;
}
else
{
uint8_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = 4;
lean_inc_ref(v_archiveFile_1667_);
v___x_1763_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1666_, v_archiveFile_1667_, v_headers_1668_, v___x_1751_, v_traceFile_1741_, v___x_1762_, v_a_1673_, v_a_1756_);
lean_dec_ref_known(v___x_1751_, 3);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; uint8_t v___x_1765_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 1);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 2);
v___x_1765_ = 0;
v_a_1712_ = v___x_1765_;
v_a_1713_ = v_a_1764_;
goto v___jp_1711_;
}
else
{
lean_object* v_a_1766_; lean_object* v_a_1767_; 
lean_dec_ref(v_archiveFile_1667_);
lean_dec_ref(v_self_1665_);
v_a_1766_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1766_);
v_a_1767_ = lean_ctor_get(v___x_1763_, 1);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1763_, 2);
v_a_1677_ = v_a_1766_;
v_a_1678_ = v_a_1767_;
goto v___jp_1676_;
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v_a_1769_; 
lean_dec_ref_known(v___x_1751_, 3);
lean_dec_ref(v_traceFile_1741_);
lean_dec_ref(v_archiveFile_1667_);
lean_dec_ref(v_url_1666_);
lean_dec_ref(v_self_1665_);
v_a_1768_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1768_);
v_a_1769_ = lean_ctor_get(v___x_1754_, 1);
lean_inc(v_a_1769_);
lean_dec_ref_known(v___x_1754_, 2);
v_a_1677_ = v_a_1768_;
v_a_1678_ = v_a_1769_;
goto v___jp_1676_;
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v_a_1772_; lean_object* v___x_1774_; 
lean_dec_ref(v_traceFile_1741_);
lean_dec_ref(v_archiveFile_1667_);
lean_dec_ref(v_url_1666_);
lean_dec_ref(v_self_1665_);
v_a_1771_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1771_);
v_a_1772_ = lean_ctor_get(v___x_1742_, 1);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1742_, 2);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v_a_1772_);
v___x_1774_ = v___x_1738_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1772_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_trace_1735_);
lean_ctor_set(v_reuseFailAlloc_1775_, 2, v_buildTime_1736_);
lean_ctor_set_uint8(v_reuseFailAlloc_1775_, sizeof(void*)*3, v_action_1733_);
lean_ctor_set_uint8(v_reuseFailAlloc_1775_, sizeof(void*)*3 + 1, v_wantsRebuild_1734_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
v_a_1677_ = v_a_1771_;
v_a_1678_ = v___x_1774_;
goto v___jp_1676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object* v_self_1777_, lean_object* v_url_1778_, lean_object* v_archiveFile_1779_, lean_object* v_headers_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_self_1777_, v_url_1778_, v_archiveFile_1779_, v_headers_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec_ref(v_headers_1780_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object* v_a_1789_, lean_object* v_info_1790_, lean_object* v_depTrace_1791_, lean_object* v_depHash_1792_, lean_object* v_oldTrace_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1790_, v_depTrace_1791_, v_depHash_1792_, v_oldTrace_1793_, v_a_1797_, v_a_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object* v_a_1801_, lean_object* v_info_1802_, lean_object* v_depTrace_1803_, lean_object* v_depHash_1804_, lean_object* v_oldTrace_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_1801_, v_info_1802_, v_depTrace_1803_, v_depHash_1804_, v_oldTrace_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec_ref(v_oldTrace_1805_);
lean_dec(v_depHash_1804_);
lean_dec_ref(v_depTrace_1803_);
lean_dec_ref(v_info_1802_);
lean_dec_ref(v_a_1801_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_getUrl_1813_, lean_object* v_pkg_1814_, lean_object* v_archiveFile_1815_, lean_object* v_headers_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
uint8_t v_r_1825_; lean_object* v___y_1826_; lean_object* v_a_1830_; lean_object* v___x_1846_; 
lean_inc_ref(v___y_1821_);
lean_inc(v___y_1820_);
lean_inc(v___y_1819_);
lean_inc(v___y_1818_);
lean_inc_ref(v___y_1817_);
lean_inc_ref(v_pkg_1814_);
v___x_1846_ = lean_apply_8(v_getUrl_1813_, v_pkg_1814_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, lean_box(0));
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
v_a_1848_ = lean_ctor_get(v___x_1846_, 1);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1846_, 2);
lean_inc_ref(v_pkg_1814_);
v___x_1849_ = lean_apply_1(v_archiveFile_1815_, v_pkg_1814_);
v___x_1850_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_1814_, v_a_1847_, v___x_1849_, v_headers_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v_a_1848_);
lean_dec_ref(v___y_1817_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; uint8_t v___x_1852_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 1);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1850_, 2);
v___x_1852_ = 1;
v_r_1825_ = v___x_1852_;
v___y_1826_ = v_a_1851_;
goto v___jp_1824_;
}
else
{
lean_object* v_a_1853_; 
v_a_1853_ = lean_ctor_get(v___x_1850_, 1);
lean_inc(v_a_1853_);
lean_dec_ref_known(v___x_1850_, 2);
v_a_1830_ = v_a_1853_;
goto v___jp_1829_;
}
}
else
{
lean_object* v_a_1854_; 
lean_dec_ref(v___y_1817_);
lean_dec_ref(v_archiveFile_1815_);
lean_dec_ref(v_pkg_1814_);
v_a_1854_ = lean_ctor_get(v___x_1846_, 1);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1846_, 2);
v_a_1830_ = v_a_1854_;
goto v___jp_1829_;
}
v___jp_1824_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_box(v_r_1825_);
v___x_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___y_1826_);
return v___x_1828_;
}
v___jp_1829_:
{
lean_object* v_log_1831_; uint8_t v_action_1832_; uint8_t v_wantsRebuild_1833_; lean_object* v_trace_1834_; lean_object* v_buildTime_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1845_; 
v_log_1831_ = lean_ctor_get(v_a_1830_, 0);
v_action_1832_ = lean_ctor_get_uint8(v_a_1830_, sizeof(void*)*3);
v_wantsRebuild_1833_ = lean_ctor_get_uint8(v_a_1830_, sizeof(void*)*3 + 1);
v_trace_1834_ = lean_ctor_get(v_a_1830_, 1);
v_buildTime_1835_ = lean_ctor_get(v_a_1830_, 2);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_a_1830_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1837_ = v_a_1830_;
v_isShared_1838_ = v_isSharedCheck_1845_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_buildTime_1835_);
lean_inc(v_trace_1834_);
lean_inc(v_log_1831_);
lean_dec(v_a_1830_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1845_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
uint8_t v___x_1839_; uint8_t v___x_1840_; lean_object* v___x_1842_; 
v___x_1839_ = 4;
v___x_1840_ = l_Lake_JobAction_merge(v_action_1832_, v___x_1839_);
if (v_isShared_1838_ == 0)
{
v___x_1842_ = v___x_1837_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_log_1831_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_trace_1834_);
lean_ctor_set(v_reuseFailAlloc_1844_, 2, v_buildTime_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1844_, sizeof(void*)*3 + 1, v_wantsRebuild_1833_);
v___x_1842_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
uint8_t v___x_1843_; 
lean_ctor_set_uint8(v___x_1842_, sizeof(void*)*3, v___x_1840_);
v___x_1843_ = 0;
v_r_1825_ = v___x_1843_;
v___y_1826_ = v___x_1842_;
goto v___jp_1824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_getUrl_1855_, lean_object* v_pkg_1856_, lean_object* v_archiveFile_1857_, lean_object* v_headers_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(v_getUrl_1855_, v_pkg_1856_, v_archiveFile_1857_, v_headers_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v_headers_1858_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* v_getUrl_1867_, lean_object* v_archiveFile_1868_, lean_object* v_headers_1869_, lean_object* v___x_1870_, lean_object* v_facet_1871_, lean_object* v_pkg_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___f_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_inc_ref(v_pkg_1872_);
v___f_1880_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1880_, 0, v_getUrl_1867_);
lean_closure_set(v___f_1880_, 1, v_pkg_1872_);
lean_closure_set(v___f_1880_, 2, v_archiveFile_1868_);
lean_closure_set(v___f_1880_, 3, v_headers_1869_);
v___x_1881_ = lean_unsigned_to_nat(0u);
v___x_1882_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_1870_);
v___x_1883_ = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(v___x_1883_, 0, lean_box(0));
lean_closure_set(v___x_1883_, 1, v___x_1870_);
lean_closure_set(v___x_1883_, 2, v___f_1880_);
lean_closure_set(v___x_1883_, 3, v___x_1881_);
lean_closure_set(v___x_1883_, 4, v___x_1882_);
v___x_1884_ = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM___boxed), 9, 2);
lean_closure_set(v___x_1884_, 0, lean_box(0));
lean_closure_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM___boxed), 9, 2);
lean_closure_set(v___x_1885_, 0, lean_box(0));
lean_closure_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = l_Lake_ensureJob___redArg(v___x_1870_, v___x_1885_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1919_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_a_1888_ = lean_ctor_get(v___x_1886_, 1);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1890_ = v___x_1886_;
v_isShared_1891_ = v_isSharedCheck_1919_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1919_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v_task_1892_; lean_object* v_kind_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1917_; 
v_task_1892_ = lean_ctor_get(v_a_1887_, 0);
v_kind_1893_ = lean_ctor_get(v_a_1887_, 1);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_a_1887_);
if (v_isSharedCheck_1917_ == 0)
{
lean_object* v_unused_1918_; 
v_unused_1918_ = lean_ctor_get(v_a_1887_, 2);
lean_dec(v_unused_1918_);
v___x_1895_ = v_a_1887_;
v_isShared_1896_ = v_isSharedCheck_1917_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_kind_1893_);
lean_inc(v_task_1892_);
lean_dec(v_a_1887_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1917_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v_registeredJobs_1897_; lean_object* v___x_1898_; lean_object* v_baseName_1899_; uint8_t v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v_job_1908_; 
v_registeredJobs_1897_ = lean_ctor_get(v___y_1877_, 4);
v___x_1898_ = lean_st_ref_take(v_registeredJobs_1897_);
v_baseName_1899_ = lean_ctor_get(v_pkg_1872_, 1);
lean_inc(v_baseName_1899_);
lean_dec_ref(v_pkg_1872_);
v___x_1900_ = 1;
v___x_1901_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1899_, v___x_1900_);
v___x_1902_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1903_ = lean_string_append(v___x_1901_, v___x_1902_);
v___x_1904_ = l_Lake_Name_eraseHead(v_facet_1871_);
v___x_1905_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1904_, v___x_1900_);
v___x_1906_ = lean_string_append(v___x_1903_, v___x_1905_);
lean_dec_ref(v___x_1905_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 2, v___x_1906_);
v_job_1908_ = v___x_1895_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_task_1892_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_kind_1893_);
lean_ctor_set(v_reuseFailAlloc_1916_, 2, v___x_1906_);
v_job_1908_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
lean_ctor_set_uint8(v_job_1908_, sizeof(void*)*3, v___x_1900_);
lean_inc_ref(v_job_1908_);
v___x_1909_ = l_Lake_Job_toOpaque___redArg(v_job_1908_);
v___x_1910_ = lean_array_push(v___x_1898_, v___x_1909_);
v___x_1911_ = lean_st_ref_put(v_registeredJobs_1897_, v___x_1910_);
v___x_1912_ = l_Lake_Job_renew___redArg(v_job_1908_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1912_);
v___x_1914_ = v___x_1890_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_a_1888_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_1872_);
lean_dec(v_facet_1871_);
return v___x_1886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v_getUrl_1920_, lean_object* v_archiveFile_1921_, lean_object* v_headers_1922_, lean_object* v___x_1923_, lean_object* v_facet_1924_, lean_object* v_pkg_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_1920_, v_archiveFile_1921_, v_headers_1922_, v___x_1923_, v_facet_1924_, v_pkg_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec(v___y_1927_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object* v_facet_1941_, lean_object* v_archiveFile_1942_, lean_object* v_getUrl_1943_, lean_object* v_headers_1944_){
_start:
{
lean_object* v___x_1945_; lean_object* v___f_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1945_ = l_Lake_instDataKindBool;
v___f_1946_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_1946_, 0, v_getUrl_1943_);
lean_closure_set(v___f_1946_, 1, v_archiveFile_1942_);
lean_closure_set(v___f_1946_, 2, v_headers_1944_);
lean_closure_set(v___f_1946_, 3, v___x_1945_);
lean_closure_set(v___f_1946_, 4, v_facet_1941_);
v___x_1947_ = l_Lake_Package_keyword;
v___x_1948_ = 1;
v___x_1949_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_1950_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1950_, 0, v___x_1947_);
lean_ctor_set(v___x_1950_, 1, v___f_1946_);
lean_ctor_set(v___x_1950_, 2, v___x_1945_);
lean_ctor_set(v___x_1950_, 3, v___x_1949_);
lean_ctor_set_uint8(v___x_1950_, sizeof(void*)*4, v___x_1948_);
lean_ctor_set_uint8(v___x_1950_, sizeof(void*)*4 + 1, v___x_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* v_facet_1951_, lean_object* v_archiveFile_1952_, lean_object* v_getUrl_1953_, lean_object* v_headers_1954_, lean_object* v_inst_1955_){
_start:
{
lean_object* v___x_1956_; lean_object* v___f_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1956_ = l_Lake_instDataKindBool;
v___f_1957_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_1957_, 0, v_getUrl_1953_);
lean_closure_set(v___f_1957_, 1, v_archiveFile_1952_);
lean_closure_set(v___f_1957_, 2, v_headers_1954_);
lean_closure_set(v___f_1957_, 3, v___x_1956_);
lean_closure_set(v___f_1957_, 4, v_facet_1951_);
v___x_1958_ = l_Lake_Package_keyword;
v___x_1959_ = 1;
v___x_1960_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_1961_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1961_, 0, v___x_1958_);
lean_ctor_set(v___x_1961_, 1, v___f_1957_);
lean_ctor_set(v___x_1961_, 2, v___x_1956_);
lean_ctor_set(v___x_1961_, 3, v___x_1960_);
lean_ctor_set_uint8(v___x_1961_, sizeof(void*)*4, v___x_1959_);
lean_ctor_set_uint8(v___x_1961_, sizeof(void*)*4 + 1, v___x_1959_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_what_1963_, lean_object* v_baseName_1964_, lean_object* v_optFacet_1965_, uint8_t v_success_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_a_1975_; lean_object* v_a_1976_; 
if (v_success_1966_ == 0)
{
lean_object* v_toBuildConfig_1997_; uint8_t v_verbosity_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v_toBuildConfig_1997_ = lean_ctor_get(v___y_1971_, 0);
v_verbosity_1998_ = lean_ctor_get_uint8(v_toBuildConfig_1997_, sizeof(void*)*4 + 4);
v___x_1999_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1998_);
v___x_2000_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_2001_ = lean_nat_dec_eq(v___x_1999_, v___x_2000_);
lean_dec(v___x_1999_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; 
lean_dec(v_optFacet_1965_);
lean_dec(v_baseName_1964_);
v___x_2002_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_1975_ = v___x_2002_;
v_a_1976_ = v___y_1972_;
goto v___jp_1974_;
}
else
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2003_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2004_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1964_, v___x_2001_);
v___x_2005_ = lean_string_append(v___x_2003_, v___x_2004_);
lean_dec_ref(v___x_2004_);
v___x_2006_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2007_ = lean_string_append(v___x_2005_, v___x_2006_);
v___x_2008_ = l_Lake_Name_eraseHead(v_optFacet_1965_);
v___x_2009_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2008_, v___x_2001_);
v___x_2010_ = lean_string_append(v___x_2007_, v___x_2009_);
lean_dec_ref(v___x_2009_);
v___x_2011_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_2012_ = lean_string_append(v___x_2010_, v___x_2011_);
v_a_1975_ = v___x_2012_;
v_a_1976_ = v___y_1972_;
goto v___jp_1974_;
}
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec(v_optFacet_1965_);
lean_dec(v_baseName_1964_);
v___x_2013_ = lean_box(0);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v___y_1972_);
return v___x_2014_;
}
v___jp_1974_:
{
lean_object* v_log_1977_; uint8_t v_action_1978_; uint8_t v_wantsRebuild_1979_; lean_object* v_trace_1980_; lean_object* v_buildTime_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1996_; 
v_log_1977_ = lean_ctor_get(v_a_1976_, 0);
v_action_1978_ = lean_ctor_get_uint8(v_a_1976_, sizeof(void*)*3);
v_wantsRebuild_1979_ = lean_ctor_get_uint8(v_a_1976_, sizeof(void*)*3 + 1);
v_trace_1980_ = lean_ctor_get(v_a_1976_, 1);
v_buildTime_1981_ = lean_ctor_get(v_a_1976_, 2);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_a_1976_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1983_ = v_a_1976_;
v_isShared_1984_ = v_isSharedCheck_1996_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_buildTime_1981_);
lean_inc(v_trace_1980_);
lean_inc(v_log_1977_);
lean_dec(v_a_1976_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1996_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1985_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0));
v___x_1986_ = lean_string_append(v___x_1985_, v_what_1963_);
v___x_1987_ = lean_string_append(v___x_1986_, v_a_1975_);
lean_dec_ref(v_a_1975_);
v___x_1988_ = 3;
v___x_1989_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set_uint8(v___x_1989_, sizeof(void*)*1, v___x_1988_);
v___x_1990_ = lean_array_get_size(v_log_1977_);
v___x_1991_ = lean_array_push(v_log_1977_, v___x_1989_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1991_);
v___x_1993_ = v___x_1983_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_trace_1980_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v_buildTime_1981_);
lean_ctor_set_uint8(v_reuseFailAlloc_1995_, sizeof(void*)*3, v_action_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1995_, sizeof(void*)*3 + 1, v_wantsRebuild_1979_);
v___x_1993_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
lean_object* v___x_1994_; 
v___x_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1990_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
return v___x_1994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_what_2015_, lean_object* v_baseName_2016_, lean_object* v_optFacet_2017_, lean_object* v_success_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
uint8_t v_success_boxed_2026_; lean_object* v_res_2027_; 
v_success_boxed_2026_ = lean_unbox(v_success_2018_);
v_res_2027_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(v_what_2015_, v_baseName_2016_, v_optFacet_2017_, v_success_boxed_2026_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec_ref(v_what_2015_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object* v___x_2028_, lean_object* v___x_2029_, lean_object* v___f_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2038_; 
lean_inc_ref(v___y_2031_);
lean_inc_ref(v___y_2035_);
lean_inc(v___y_2034_);
lean_inc(v___y_2033_);
lean_inc(v___y_2032_);
v___x_2038_ = lean_apply_7(v___y_2031_, v___x_2028_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, lean_box(0));
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2051_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
v_a_2040_ = lean_ctor_get(v___x_2038_, 1);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2042_ = v___x_2038_;
v_isShared_2043_ = v_isSharedCheck_2051_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_inc(v_a_2039_);
lean_dec(v___x_2038_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2051_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; uint8_t v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = 0;
v___x_2046_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2047_ = l_Lake_Job_mapM___redArg(v___x_2029_, v_a_2039_, v___f_2030_, v___x_2044_, v___x_2045_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___x_2046_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2047_);
v___x_2049_ = v___x_2042_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_a_2040_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec_ref(v___y_2031_);
lean_dec_ref(v___f_2030_);
lean_dec(v___x_2029_);
v_a_2052_ = lean_ctor_get(v___x_2038_, 0);
v_a_2053_ = lean_ctor_get(v___x_2038_, 1);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2038_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_inc(v_a_2052_);
lean_dec(v___x_2038_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2052_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v___x_2061_, lean_object* v___x_2062_, lean_object* v___f_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(v___x_2061_, v___x_2062_, v___f_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec(v___y_2065_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object* v_what_2072_, lean_object* v_optFacet_2073_, lean_object* v___x_2074_, lean_object* v_facet_2075_, lean_object* v_pkg_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_baseName_2084_; lean_object* v_keyName_2085_; lean_object* v___f_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___f_2090_; lean_object* v___x_2091_; 
v_baseName_2084_ = lean_ctor_get(v_pkg_2076_, 1);
lean_inc_n(v_baseName_2084_, 2);
v_keyName_2085_ = lean_ctor_get(v_pkg_2076_, 2);
lean_inc(v_optFacet_2073_);
v___f_2086_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2086_, 0, v_what_2072_);
lean_closure_set(v___f_2086_, 1, v_baseName_2084_);
lean_closure_set(v___f_2086_, 2, v_optFacet_2073_);
lean_inc(v_keyName_2085_);
v___x_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2087_, 0, v_keyName_2085_);
v___x_2088_ = l_Lake_Package_keyword;
v___x_2089_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2087_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
lean_ctor_set(v___x_2089_, 2, v_pkg_2076_);
lean_ctor_set(v___x_2089_, 3, v_optFacet_2073_);
lean_inc(v___x_2074_);
v___f_2090_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2090_, 0, v___x_2089_);
lean_closure_set(v___f_2090_, 1, v___x_2074_);
lean_closure_set(v___f_2090_, 2, v___f_2086_);
v___x_2091_ = l_Lake_ensureJob___redArg(v___x_2074_, v___f_2090_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2124_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_a_2093_ = lean_ctor_get(v___x_2091_, 1);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2095_ = v___x_2091_;
v_isShared_2096_ = v_isSharedCheck_2124_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2124_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v_task_2097_; lean_object* v_kind_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2122_; 
v_task_2097_ = lean_ctor_get(v_a_2092_, 0);
v_kind_2098_ = lean_ctor_get(v_a_2092_, 1);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_a_2092_);
if (v_isSharedCheck_2122_ == 0)
{
lean_object* v_unused_2123_; 
v_unused_2123_ = lean_ctor_get(v_a_2092_, 2);
lean_dec(v_unused_2123_);
v___x_2100_ = v_a_2092_;
v_isShared_2101_ = v_isSharedCheck_2122_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_kind_2098_);
lean_inc(v_task_2097_);
lean_dec(v_a_2092_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2122_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v_registeredJobs_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; lean_object* v_job_2113_; 
v_registeredJobs_2102_ = lean_ctor_get(v___y_2081_, 4);
v___x_2103_ = lean_st_ref_take(v_registeredJobs_2102_);
v___x_2104_ = 1;
v___x_2105_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2084_, v___x_2104_);
v___x_2106_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2107_ = lean_string_append(v___x_2105_, v___x_2106_);
v___x_2108_ = l_Lake_Name_eraseHead(v_facet_2075_);
v___x_2109_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2108_, v___x_2104_);
v___x_2110_ = lean_string_append(v___x_2107_, v___x_2109_);
lean_dec_ref(v___x_2109_);
v___x_2111_ = 0;
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 2, v___x_2110_);
v_job_2113_ = v___x_2100_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_task_2097_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_kind_2098_);
lean_ctor_set(v_reuseFailAlloc_2121_, 2, v___x_2110_);
v_job_2113_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
lean_ctor_set_uint8(v_job_2113_, sizeof(void*)*3, v___x_2111_);
lean_inc_ref(v_job_2113_);
v___x_2114_ = l_Lake_Job_toOpaque___redArg(v_job_2113_);
v___x_2115_ = lean_array_push(v___x_2103_, v___x_2114_);
v___x_2116_ = lean_st_ref_put(v_registeredJobs_2102_, v___x_2115_);
v___x_2117_ = l_Lake_Job_renew___redArg(v_job_2113_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2117_);
v___x_2119_ = v___x_2095_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
lean_ctor_set(v_reuseFailAlloc_2120_, 1, v_a_2093_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2084_);
lean_dec(v_facet_2075_);
return v___x_2091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object* v_what_2125_, lean_object* v_optFacet_2126_, lean_object* v___x_2127_, lean_object* v_facet_2128_, lean_object* v_pkg_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(v_what_2125_, v_optFacet_2126_, v___x_2127_, v_facet_2128_, v_pkg_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec(v___y_2131_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object* v_facet_2145_, lean_object* v_optFacet_2146_, lean_object* v_what_2147_){
_start:
{
lean_object* v___x_2148_; lean_object* v___f_2149_; lean_object* v___x_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2148_ = l_Lake_instDataKindUnit;
v___f_2149_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2149_, 0, v_what_2147_);
lean_closure_set(v___f_2149_, 1, v_optFacet_2146_);
lean_closure_set(v___f_2149_, 2, v___x_2148_);
lean_closure_set(v___f_2149_, 3, v_facet_2145_);
v___x_2150_ = l_Lake_Package_keyword;
v___x_2151_ = 1;
v___x_2152_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2153_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2153_, 0, v___x_2150_);
lean_ctor_set(v___x_2153_, 1, v___f_2149_);
lean_ctor_set(v___x_2153_, 2, v___x_2148_);
lean_ctor_set(v___x_2153_, 3, v___x_2152_);
lean_ctor_set_uint8(v___x_2153_, sizeof(void*)*4, v___x_2151_);
lean_ctor_set_uint8(v___x_2153_, sizeof(void*)*4 + 1, v___x_2151_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* v_facet_2154_, lean_object* v_optFacet_2155_, lean_object* v_what_2156_, lean_object* v_inst_2157_, lean_object* v_inst_2158_){
_start:
{
lean_object* v___x_2159_; lean_object* v___f_2160_; lean_object* v___x_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2159_ = l_Lake_instDataKindUnit;
v___f_2160_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2160_, 0, v_what_2156_);
lean_closure_set(v___f_2160_, 1, v_optFacet_2155_);
lean_closure_set(v___f_2160_, 2, v___x_2159_);
lean_closure_set(v___f_2160_, 3, v_facet_2154_);
v___x_2161_ = l_Lake_Package_keyword;
v___x_2162_ = 1;
v___x_2163_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2164_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2164_, 0, v___x_2161_);
lean_ctor_set(v___x_2164_, 1, v___f_2160_);
lean_ctor_set(v___x_2164_, 2, v___x_2159_);
lean_ctor_set(v___x_2164_, 3, v___x_2163_);
lean_ctor_set_uint8(v___x_2164_, sizeof(void*)*4, v___x_2162_);
lean_ctor_set_uint8(v___x_2164_, sizeof(void*)*4 + 1, v___x_2162_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* v_baseName_2166_, lean_object* v___x_2167_, uint8_t v_success_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v_a_2177_; lean_object* v_a_2178_; 
if (v_success_2168_ == 0)
{
lean_object* v_toBuildConfig_2198_; uint8_t v_verbosity_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; uint8_t v___x_2202_; 
v_toBuildConfig_2198_ = lean_ctor_get(v___y_2173_, 0);
v_verbosity_2199_ = lean_ctor_get_uint8(v_toBuildConfig_2198_, sizeof(void*)*4 + 4);
v___x_2200_ = l_Lake_Verbosity_ctorIdx(v_verbosity_2199_);
v___x_2201_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_2202_ = lean_nat_dec_eq(v___x_2200_, v___x_2201_);
lean_dec(v___x_2200_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; 
lean_dec(v___x_2167_);
lean_dec(v_baseName_2166_);
v___x_2203_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_2177_ = v___x_2203_;
v_a_2178_ = v___y_2174_;
goto v___jp_2176_;
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2204_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2205_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2166_, v___x_2202_);
v___x_2206_ = lean_string_append(v___x_2204_, v___x_2205_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2208_ = lean_string_append(v___x_2206_, v___x_2207_);
v___x_2209_ = l_Lake_Name_eraseHead(v___x_2167_);
v___x_2210_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2209_, v___x_2202_);
v___x_2211_ = lean_string_append(v___x_2208_, v___x_2210_);
lean_dec_ref(v___x_2210_);
v___x_2212_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_2213_ = lean_string_append(v___x_2211_, v___x_2212_);
v_a_2177_ = v___x_2213_;
v_a_2178_ = v___y_2174_;
goto v___jp_2176_;
}
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
lean_dec(v___x_2167_);
lean_dec(v_baseName_2166_);
v___x_2214_ = lean_box(0);
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v___y_2174_);
return v___x_2215_;
}
v___jp_2176_:
{
lean_object* v_log_2179_; uint8_t v_action_2180_; uint8_t v_wantsRebuild_2181_; lean_object* v_trace_2182_; lean_object* v_buildTime_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2197_; 
v_log_2179_ = lean_ctor_get(v_a_2178_, 0);
v_action_2180_ = lean_ctor_get_uint8(v_a_2178_, sizeof(void*)*3);
v_wantsRebuild_2181_ = lean_ctor_get_uint8(v_a_2178_, sizeof(void*)*3 + 1);
v_trace_2182_ = lean_ctor_get(v_a_2178_, 1);
v_buildTime_2183_ = lean_ctor_get(v_a_2178_, 2);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_a_2178_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2185_ = v_a_2178_;
v_isShared_2186_ = v_isSharedCheck_2197_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_buildTime_2183_);
lean_inc(v_trace_2182_);
lean_inc(v_log_2179_);
lean_dec(v_a_2178_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2197_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2187_ = ((lean_object*)(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0));
v___x_2188_ = lean_string_append(v___x_2187_, v_a_2177_);
lean_dec_ref(v_a_2177_);
v___x_2189_ = 3;
v___x_2190_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
lean_ctor_set_uint8(v___x_2190_, sizeof(void*)*1, v___x_2189_);
v___x_2191_ = lean_array_get_size(v_log_2179_);
v___x_2192_ = lean_array_push(v_log_2179_, v___x_2190_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2192_);
v___x_2194_ = v___x_2185_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_trace_2182_);
lean_ctor_set(v_reuseFailAlloc_2196_, 2, v_buildTime_2183_);
lean_ctor_set_uint8(v_reuseFailAlloc_2196_, sizeof(void*)*3, v_action_2180_);
lean_ctor_set_uint8(v_reuseFailAlloc_2196_, sizeof(void*)*3 + 1, v_wantsRebuild_2181_);
v___x_2194_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2191_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
return v___x_2195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object* v_baseName_2216_, lean_object* v___x_2217_, lean_object* v_success_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
uint8_t v_success_boxed_2226_; lean_object* v_res_2227_; 
v_success_boxed_2226_ = lean_unbox(v_success_2218_);
v_res_2227_ = l_Lake_Package_buildCacheFacetConfig___lam__1(v_baseName_2216_, v___x_2217_, v_success_boxed_2226_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* v___x_2228_, lean_object* v___x_2229_, lean_object* v___x_2230_, lean_object* v_pkg_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_baseName_2239_; lean_object* v_keyName_2240_; lean_object* v___f_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___f_2245_; lean_object* v___x_2246_; 
v_baseName_2239_ = lean_ctor_get(v_pkg_2231_, 1);
lean_inc_n(v_baseName_2239_, 2);
v_keyName_2240_ = lean_ctor_get(v_pkg_2231_, 2);
lean_inc(v___x_2228_);
v___f_2241_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2241_, 0, v_baseName_2239_);
lean_closure_set(v___f_2241_, 1, v___x_2228_);
lean_inc(v_keyName_2240_);
v___x_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2242_, 0, v_keyName_2240_);
v___x_2243_ = l_Lake_Package_keyword;
v___x_2244_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2242_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
lean_ctor_set(v___x_2244_, 2, v_pkg_2231_);
lean_ctor_set(v___x_2244_, 3, v___x_2228_);
lean_inc(v___x_2229_);
v___f_2245_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2245_, 0, v___x_2244_);
lean_closure_set(v___f_2245_, 1, v___x_2229_);
lean_closure_set(v___f_2245_, 2, v___f_2241_);
v___x_2246_ = l_Lake_ensureJob___redArg(v___x_2229_, v___f_2245_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2279_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_a_2248_ = lean_ctor_get(v___x_2246_, 1);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2250_ = v___x_2246_;
v_isShared_2251_ = v_isSharedCheck_2279_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2279_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v_task_2252_; lean_object* v_kind_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2277_; 
v_task_2252_ = lean_ctor_get(v_a_2247_, 0);
v_kind_2253_ = lean_ctor_get(v_a_2247_, 1);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_a_2247_);
if (v_isSharedCheck_2277_ == 0)
{
lean_object* v_unused_2278_; 
v_unused_2278_ = lean_ctor_get(v_a_2247_, 2);
lean_dec(v_unused_2278_);
v___x_2255_ = v_a_2247_;
v_isShared_2256_ = v_isSharedCheck_2277_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_kind_2253_);
lean_inc(v_task_2252_);
lean_dec(v_a_2247_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2277_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v_registeredJobs_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; lean_object* v_job_2268_; 
v_registeredJobs_2257_ = lean_ctor_get(v___y_2236_, 4);
v___x_2258_ = lean_st_ref_take(v_registeredJobs_2257_);
v___x_2259_ = 1;
v___x_2260_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2239_, v___x_2259_);
v___x_2261_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2262_ = lean_string_append(v___x_2260_, v___x_2261_);
v___x_2263_ = l_Lake_Name_eraseHead(v___x_2230_);
v___x_2264_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2263_, v___x_2259_);
v___x_2265_ = lean_string_append(v___x_2262_, v___x_2264_);
lean_dec_ref(v___x_2264_);
v___x_2266_ = 0;
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 2, v___x_2265_);
v_job_2268_ = v___x_2255_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_task_2252_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_kind_2253_);
lean_ctor_set(v_reuseFailAlloc_2276_, 2, v___x_2265_);
v_job_2268_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
lean_ctor_set_uint8(v_job_2268_, sizeof(void*)*3, v___x_2266_);
lean_inc_ref(v_job_2268_);
v___x_2269_ = l_Lake_Job_toOpaque___redArg(v_job_2268_);
v___x_2270_ = lean_array_push(v___x_2258_, v___x_2269_);
v___x_2271_ = lean_st_ref_put(v_registeredJobs_2257_, v___x_2270_);
v___x_2272_ = l_Lake_Job_renew___redArg(v_job_2268_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2272_);
v___x_2274_ = v___x_2250_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_a_2248_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2239_);
lean_dec(v___x_2230_);
return v___x_2246_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object* v___x_2280_, lean_object* v___x_2281_, lean_object* v___x_2282_, lean_object* v_pkg_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lake_Package_buildCacheFacetConfig___lam__2(v___x_2280_, v___x_2281_, v___x_2282_, v_pkg_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec(v___y_2285_);
return v_res_2291_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___f_2295_; 
v___x_2292_ = l_Lake_Package_buildCacheFacet;
v___x_2293_ = l_Lake_instDataKindUnit;
v___x_2294_ = l_Lake_Package_optBuildCacheFacet;
v___f_2295_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2295_, 0, v___x_2294_);
lean_closure_set(v___f_2295_, 1, v___x_2293_);
lean_closure_set(v___f_2295_, 2, v___x_2292_);
return v___f_2295_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2296_; uint8_t v___x_2297_; lean_object* v___x_2298_; lean_object* v___f_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___f_2296_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2297_ = 1;
v___x_2298_ = l_Lake_instDataKindUnit;
v___f_2299_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__0, &l_Lake_Package_buildCacheFacetConfig___closed__0_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__0);
v___x_2300_ = l_Lake_Package_keyword;
v___x_2301_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
lean_ctor_set(v___x_2301_, 1, v___f_2299_);
lean_ctor_set(v___x_2301_, 2, v___x_2298_);
lean_ctor_set(v___x_2301_, 3, v___f_2296_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*4, v___x_2297_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*4 + 1, v___x_2297_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig(void){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__1, &l_Lake_Package_buildCacheFacetConfig___closed__1_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__1);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* v_pkg_2304_, lean_object* v___x_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
uint8_t v_r_2314_; lean_object* v___y_2315_; lean_object* v_a_2319_; lean_object* v___x_2335_; 
lean_inc_ref(v_pkg_2304_);
v___x_2335_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_pkg_2304_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v_a_2337_; lean_object* v_dir_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
v_a_2337_ = lean_ctor_get(v___x_2335_, 1);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2335_, 2);
v_dir_2338_ = lean_ctor_get(v_pkg_2304_, 4);
v___x_2339_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_2338_);
v___x_2340_ = l_Lake_joinRelative(v_dir_2338_, v___x_2339_);
v___x_2341_ = ((lean_object*)(l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0));
v___x_2342_ = l_Lake_joinRelative(v___x_2340_, v___x_2341_);
v___x_2343_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2304_, v_a_2336_, v___x_2342_, v___x_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v_a_2337_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; uint8_t v___x_2345_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 1);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 2);
v___x_2345_ = 1;
v_r_2314_ = v___x_2345_;
v___y_2315_ = v_a_2344_;
goto v___jp_2313_;
}
else
{
lean_object* v_a_2346_; 
v_a_2346_ = lean_ctor_get(v___x_2343_, 1);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2343_, 2);
v_a_2319_ = v_a_2346_;
goto v___jp_2318_;
}
}
else
{
lean_object* v_a_2347_; 
lean_dec_ref(v_pkg_2304_);
v_a_2347_ = lean_ctor_get(v___x_2335_, 1);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2335_, 2);
v_a_2319_ = v_a_2347_;
goto v___jp_2318_;
}
v___jp_2313_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = lean_box(v_r_2314_);
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
lean_ctor_set(v___x_2317_, 1, v___y_2315_);
return v___x_2317_;
}
v___jp_2318_:
{
lean_object* v_log_2320_; uint8_t v_action_2321_; uint8_t v_wantsRebuild_2322_; lean_object* v_trace_2323_; lean_object* v_buildTime_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2334_; 
v_log_2320_ = lean_ctor_get(v_a_2319_, 0);
v_action_2321_ = lean_ctor_get_uint8(v_a_2319_, sizeof(void*)*3);
v_wantsRebuild_2322_ = lean_ctor_get_uint8(v_a_2319_, sizeof(void*)*3 + 1);
v_trace_2323_ = lean_ctor_get(v_a_2319_, 1);
v_buildTime_2324_ = lean_ctor_get(v_a_2319_, 2);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_a_2319_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2326_ = v_a_2319_;
v_isShared_2327_ = v_isSharedCheck_2334_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_buildTime_2324_);
lean_inc(v_trace_2323_);
lean_inc(v_log_2320_);
lean_dec(v_a_2319_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2334_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
uint8_t v___x_2328_; uint8_t v___x_2329_; lean_object* v___x_2331_; 
v___x_2328_ = 4;
v___x_2329_ = l_Lake_JobAction_merge(v_action_2321_, v___x_2328_);
if (v_isShared_2327_ == 0)
{
v___x_2331_ = v___x_2326_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_log_2320_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_trace_2323_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_buildTime_2324_);
lean_ctor_set_uint8(v_reuseFailAlloc_2333_, sizeof(void*)*3 + 1, v_wantsRebuild_2322_);
v___x_2331_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
uint8_t v___x_2332_; 
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*3, v___x_2329_);
v___x_2332_ = 0;
v_r_2314_ = v___x_2332_;
v___y_2315_ = v___x_2331_;
goto v___jp_2313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* v_pkg_2348_, lean_object* v___x_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_Lake_Package_optBarrelFacetConfig___lam__0(v_pkg_2348_, v___x_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec_ref(v___x_2349_);
return v_res_2357_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* v___x_2358_, lean_object* v___f_2359_, lean_object* v___x_2360_, lean_object* v___x_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = l_Lake_Job_async___redArg(v___x_2358_, v___f_2359_, v___x_2360_, v___x_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
v___x_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
lean_ctor_set(v___x_2370_, 1, v___y_2367_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object* v___x_2371_, lean_object* v___f_2372_, lean_object* v___x_2373_, lean_object* v___x_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lake_Package_optBarrelFacetConfig___lam__1(v___x_2371_, v___f_2372_, v___x_2373_, v___x_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec(v___y_2376_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* v___x_2383_, lean_object* v___x_2384_, lean_object* v___x_2385_, lean_object* v_pkg_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___f_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___f_2397_; lean_object* v___x_2398_; 
lean_inc_ref(v_pkg_2386_);
v___f_2394_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2394_, 0, v_pkg_2386_);
lean_closure_set(v___f_2394_, 1, v___x_2383_);
v___x_2395_ = lean_unsigned_to_nat(0u);
v___x_2396_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2384_);
v___f_2397_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2397_, 0, v___x_2384_);
lean_closure_set(v___f_2397_, 1, v___f_2394_);
lean_closure_set(v___f_2397_, 2, v___x_2395_);
lean_closure_set(v___f_2397_, 3, v___x_2396_);
v___x_2398_ = l_Lake_ensureJob___redArg(v___x_2384_, v___f_2397_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2431_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
v_a_2400_ = lean_ctor_get(v___x_2398_, 1);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2402_ = v___x_2398_;
v_isShared_2403_ = v_isSharedCheck_2431_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_inc(v_a_2399_);
lean_dec(v___x_2398_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2431_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v_task_2404_; lean_object* v_kind_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2429_; 
v_task_2404_ = lean_ctor_get(v_a_2399_, 0);
v_kind_2405_ = lean_ctor_get(v_a_2399_, 1);
v_isSharedCheck_2429_ = !lean_is_exclusive(v_a_2399_);
if (v_isSharedCheck_2429_ == 0)
{
lean_object* v_unused_2430_; 
v_unused_2430_ = lean_ctor_get(v_a_2399_, 2);
lean_dec(v_unused_2430_);
v___x_2407_ = v_a_2399_;
v_isShared_2408_ = v_isSharedCheck_2429_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_kind_2405_);
lean_inc(v_task_2404_);
lean_dec(v_a_2399_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2429_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v_registeredJobs_2409_; lean_object* v___x_2410_; lean_object* v_baseName_2411_; uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v_job_2420_; 
v_registeredJobs_2409_ = lean_ctor_get(v___y_2391_, 4);
v___x_2410_ = lean_st_ref_take(v_registeredJobs_2409_);
v_baseName_2411_ = lean_ctor_get(v_pkg_2386_, 1);
lean_inc(v_baseName_2411_);
lean_dec_ref(v_pkg_2386_);
v___x_2412_ = 1;
v___x_2413_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2411_, v___x_2412_);
v___x_2414_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2415_ = lean_string_append(v___x_2413_, v___x_2414_);
v___x_2416_ = l_Lake_Name_eraseHead(v___x_2385_);
v___x_2417_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2416_, v___x_2412_);
v___x_2418_ = lean_string_append(v___x_2415_, v___x_2417_);
lean_dec_ref(v___x_2417_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 2, v___x_2418_);
v_job_2420_ = v___x_2407_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_task_2404_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_kind_2405_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v___x_2418_);
v_job_2420_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
lean_ctor_set_uint8(v_job_2420_, sizeof(void*)*3, v___x_2412_);
lean_inc_ref(v_job_2420_);
v___x_2421_ = l_Lake_Job_toOpaque___redArg(v_job_2420_);
v___x_2422_ = lean_array_push(v___x_2410_, v___x_2421_);
v___x_2423_ = lean_st_ref_put(v_registeredJobs_2409_, v___x_2422_);
v___x_2424_ = l_Lake_Job_renew___redArg(v_job_2420_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2424_);
v___x_2426_ = v___x_2402_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_a_2400_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_2386_);
lean_dec(v___x_2385_);
return v___x_2398_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object* v___x_2432_, lean_object* v___x_2433_, lean_object* v___x_2434_, lean_object* v_pkg_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lake_Package_optBarrelFacetConfig___lam__2(v___x_2432_, v___x_2433_, v___x_2434_, v_pkg_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec(v___y_2437_);
return v_res_2443_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___f_2447_; 
v___x_2444_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_2445_ = l_Lake_instDataKindBool;
v___x_2446_ = l_Lake_Reservoir_lakeHeaders;
v___f_2447_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2447_, 0, v___x_2446_);
lean_closure_set(v___f_2447_, 1, v___x_2445_);
lean_closure_set(v___f_2447_, 2, v___x_2444_);
return v___f_2447_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2448_; uint8_t v___x_2449_; lean_object* v___x_2450_; lean_object* v___f_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___f_2448_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_2449_ = 1;
v___x_2450_ = l_Lake_instDataKindBool;
v___f_2451_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__0, &l_Lake_Package_optBarrelFacetConfig___closed__0_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__0);
v___x_2452_ = l_Lake_Package_keyword;
v___x_2453_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
lean_ctor_set(v___x_2453_, 1, v___f_2451_);
lean_ctor_set(v___x_2453_, 2, v___x_2450_);
lean_ctor_set(v___x_2453_, 3, v___f_2448_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*4, v___x_2449_);
lean_ctor_set_uint8(v___x_2453_, sizeof(void*)*4 + 1, v___x_2449_);
return v___x_2453_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig(void){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__1, &l_Lake_Package_optBarrelFacetConfig___closed__1_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__1);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* v_baseName_2456_, lean_object* v___x_2457_, uint8_t v_success_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_a_2467_; lean_object* v_a_2468_; 
if (v_success_2458_ == 0)
{
lean_object* v_toBuildConfig_2488_; uint8_t v_verbosity_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v_toBuildConfig_2488_ = lean_ctor_get(v___y_2463_, 0);
v_verbosity_2489_ = lean_ctor_get_uint8(v_toBuildConfig_2488_, sizeof(void*)*4 + 4);
v___x_2490_ = l_Lake_Verbosity_ctorIdx(v_verbosity_2489_);
v___x_2491_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_2492_ = lean_nat_dec_eq(v___x_2490_, v___x_2491_);
lean_dec(v___x_2490_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; 
lean_dec(v___x_2457_);
lean_dec(v_baseName_2456_);
v___x_2493_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_2467_ = v___x_2493_;
v_a_2468_ = v___y_2464_;
goto v___jp_2466_;
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2494_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2495_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2456_, v___x_2492_);
v___x_2496_ = lean_string_append(v___x_2494_, v___x_2495_);
lean_dec_ref(v___x_2495_);
v___x_2497_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2498_ = lean_string_append(v___x_2496_, v___x_2497_);
v___x_2499_ = l_Lake_Name_eraseHead(v___x_2457_);
v___x_2500_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2499_, v___x_2492_);
v___x_2501_ = lean_string_append(v___x_2498_, v___x_2500_);
lean_dec_ref(v___x_2500_);
v___x_2502_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_2503_ = lean_string_append(v___x_2501_, v___x_2502_);
v_a_2467_ = v___x_2503_;
v_a_2468_ = v___y_2464_;
goto v___jp_2466_;
}
}
else
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_dec(v___x_2457_);
lean_dec(v_baseName_2456_);
v___x_2504_ = lean_box(0);
v___x_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
lean_ctor_set(v___x_2505_, 1, v___y_2464_);
return v___x_2505_;
}
v___jp_2466_:
{
lean_object* v_log_2469_; uint8_t v_action_2470_; uint8_t v_wantsRebuild_2471_; lean_object* v_trace_2472_; lean_object* v_buildTime_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2487_; 
v_log_2469_ = lean_ctor_get(v_a_2468_, 0);
v_action_2470_ = lean_ctor_get_uint8(v_a_2468_, sizeof(void*)*3);
v_wantsRebuild_2471_ = lean_ctor_get_uint8(v_a_2468_, sizeof(void*)*3 + 1);
v_trace_2472_ = lean_ctor_get(v_a_2468_, 1);
v_buildTime_2473_ = lean_ctor_get(v_a_2468_, 2);
v_isSharedCheck_2487_ = !lean_is_exclusive(v_a_2468_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2475_ = v_a_2468_;
v_isShared_2476_ = v_isSharedCheck_2487_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_buildTime_2473_);
lean_inc(v_trace_2472_);
lean_inc(v_log_2469_);
lean_dec(v_a_2468_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2487_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2477_ = ((lean_object*)(l_Lake_Package_barrelFacetConfig___lam__1___closed__0));
v___x_2478_ = lean_string_append(v___x_2477_, v_a_2467_);
lean_dec_ref(v_a_2467_);
v___x_2479_ = 3;
v___x_2480_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2480_, 0, v___x_2478_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*1, v___x_2479_);
v___x_2481_ = lean_array_get_size(v_log_2469_);
v___x_2482_ = lean_array_push(v_log_2469_, v___x_2480_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2482_);
v___x_2484_ = v___x_2475_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2482_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_trace_2472_);
lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_buildTime_2473_);
lean_ctor_set_uint8(v_reuseFailAlloc_2486_, sizeof(void*)*3, v_action_2470_);
lean_ctor_set_uint8(v_reuseFailAlloc_2486_, sizeof(void*)*3 + 1, v_wantsRebuild_2471_);
v___x_2484_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2481_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
return v___x_2485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object* v_baseName_2506_, lean_object* v___x_2507_, lean_object* v_success_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
uint8_t v_success_boxed_2516_; lean_object* v_res_2517_; 
v_success_boxed_2516_ = lean_unbox(v_success_2508_);
v_res_2517_ = l_Lake_Package_barrelFacetConfig___lam__1(v_baseName_2506_, v___x_2507_, v_success_boxed_2516_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* v___x_2518_, lean_object* v___x_2519_, lean_object* v___x_2520_, lean_object* v_pkg_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_baseName_2529_; lean_object* v_keyName_2530_; lean_object* v___f_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___f_2535_; lean_object* v___x_2536_; 
v_baseName_2529_ = lean_ctor_get(v_pkg_2521_, 1);
lean_inc_n(v_baseName_2529_, 2);
v_keyName_2530_ = lean_ctor_get(v_pkg_2521_, 2);
lean_inc(v___x_2518_);
v___f_2531_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2531_, 0, v_baseName_2529_);
lean_closure_set(v___f_2531_, 1, v___x_2518_);
lean_inc(v_keyName_2530_);
v___x_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2532_, 0, v_keyName_2530_);
v___x_2533_ = l_Lake_Package_keyword;
v___x_2534_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2532_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
lean_ctor_set(v___x_2534_, 2, v_pkg_2521_);
lean_ctor_set(v___x_2534_, 3, v___x_2518_);
lean_inc(v___x_2519_);
v___f_2535_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2535_, 0, v___x_2534_);
lean_closure_set(v___f_2535_, 1, v___x_2519_);
lean_closure_set(v___f_2535_, 2, v___f_2531_);
v___x_2536_ = l_Lake_ensureJob___redArg(v___x_2519_, v___f_2535_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2569_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_a_2538_ = lean_ctor_get(v___x_2536_, 1);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2540_ = v___x_2536_;
v_isShared_2541_ = v_isSharedCheck_2569_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2569_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v_task_2542_; lean_object* v_kind_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2567_; 
v_task_2542_ = lean_ctor_get(v_a_2537_, 0);
v_kind_2543_ = lean_ctor_get(v_a_2537_, 1);
v_isSharedCheck_2567_ = !lean_is_exclusive(v_a_2537_);
if (v_isSharedCheck_2567_ == 0)
{
lean_object* v_unused_2568_; 
v_unused_2568_ = lean_ctor_get(v_a_2537_, 2);
lean_dec(v_unused_2568_);
v___x_2545_ = v_a_2537_;
v_isShared_2546_ = v_isSharedCheck_2567_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_kind_2543_);
lean_inc(v_task_2542_);
lean_dec(v_a_2537_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2567_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v_registeredJobs_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; lean_object* v_job_2558_; 
v_registeredJobs_2547_ = lean_ctor_get(v___y_2526_, 4);
v___x_2548_ = lean_st_ref_take(v_registeredJobs_2547_);
v___x_2549_ = 1;
v___x_2550_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2529_, v___x_2549_);
v___x_2551_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2552_ = lean_string_append(v___x_2550_, v___x_2551_);
v___x_2553_ = l_Lake_Name_eraseHead(v___x_2520_);
v___x_2554_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2553_, v___x_2549_);
v___x_2555_ = lean_string_append(v___x_2552_, v___x_2554_);
lean_dec_ref(v___x_2554_);
v___x_2556_ = 0;
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 2, v___x_2555_);
v_job_2558_ = v___x_2545_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_task_2542_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_kind_2543_);
lean_ctor_set(v_reuseFailAlloc_2566_, 2, v___x_2555_);
v_job_2558_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2564_; 
lean_ctor_set_uint8(v_job_2558_, sizeof(void*)*3, v___x_2556_);
lean_inc_ref(v_job_2558_);
v___x_2559_ = l_Lake_Job_toOpaque___redArg(v_job_2558_);
v___x_2560_ = lean_array_push(v___x_2548_, v___x_2559_);
v___x_2561_ = lean_st_ref_put(v_registeredJobs_2547_, v___x_2560_);
v___x_2562_ = l_Lake_Job_renew___redArg(v_job_2558_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 0, v___x_2562_);
v___x_2564_ = v___x_2540_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_a_2538_);
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
else
{
lean_dec(v_baseName_2529_);
lean_dec(v___x_2520_);
return v___x_2536_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object* v___x_2570_, lean_object* v___x_2571_, lean_object* v___x_2572_, lean_object* v_pkg_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lake_Package_barrelFacetConfig___lam__2(v___x_2570_, v___x_2571_, v___x_2572_, v_pkg_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec(v___y_2575_);
return v_res_2581_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___f_2585_; 
v___x_2582_ = l_Lake_Package_reservoirBarrelFacet;
v___x_2583_ = l_Lake_instDataKindUnit;
v___x_2584_ = l_Lake_Package_optReservoirBarrelFacet;
v___f_2585_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2585_, 0, v___x_2584_);
lean_closure_set(v___f_2585_, 1, v___x_2583_);
lean_closure_set(v___f_2585_, 2, v___x_2582_);
return v___f_2585_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2586_; uint8_t v___x_2587_; lean_object* v___x_2588_; lean_object* v___f_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___f_2586_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2587_ = 1;
v___x_2588_ = l_Lake_instDataKindUnit;
v___f_2589_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__0, &l_Lake_Package_barrelFacetConfig___closed__0_once, _init_l_Lake_Package_barrelFacetConfig___closed__0);
v___x_2590_ = l_Lake_Package_keyword;
v___x_2591_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
lean_ctor_set(v___x_2591_, 1, v___f_2589_);
lean_ctor_set(v___x_2591_, 2, v___x_2588_);
lean_ctor_set(v___x_2591_, 3, v___f_2586_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*4, v___x_2587_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*4 + 1, v___x_2587_);
return v___x_2591_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig(void){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__1, &l_Lake_Package_barrelFacetConfig___closed__1_once, _init_l_Lake_Package_barrelFacetConfig___closed__1);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object* v_pkg_2593_, lean_object* v___x_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
uint8_t v_r_2603_; lean_object* v___y_2604_; lean_object* v_a_2608_; lean_object* v___x_2624_; 
lean_inc_ref(v_pkg_2593_);
v___x_2624_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_pkg_2593_, v___y_2600_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v_a_2626_; lean_object* v_dir_2627_; lean_object* v_buildArchive_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
v_a_2626_ = lean_ctor_get(v___x_2624_, 1);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2624_, 2);
v_dir_2627_ = lean_ctor_get(v_pkg_2593_, 4);
v_buildArchive_2628_ = lean_ctor_get(v_pkg_2593_, 21);
v___x_2629_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_2627_);
v___x_2630_ = l_Lake_joinRelative(v_dir_2627_, v___x_2629_);
lean_inc_ref(v_buildArchive_2628_);
v___x_2631_ = l_Lake_joinRelative(v___x_2630_, v_buildArchive_2628_);
v___x_2632_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2593_, v_a_2625_, v___x_2631_, v___x_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v_a_2626_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; uint8_t v___x_2634_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 1);
lean_inc(v_a_2633_);
lean_dec_ref_known(v___x_2632_, 2);
v___x_2634_ = 1;
v_r_2603_ = v___x_2634_;
v___y_2604_ = v_a_2633_;
goto v___jp_2602_;
}
else
{
lean_object* v_a_2635_; 
v_a_2635_ = lean_ctor_get(v___x_2632_, 1);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2632_, 2);
v_a_2608_ = v_a_2635_;
goto v___jp_2607_;
}
}
else
{
lean_object* v_a_2636_; 
lean_dec_ref(v_pkg_2593_);
v_a_2636_ = lean_ctor_get(v___x_2624_, 1);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2624_, 2);
v_a_2608_ = v_a_2636_;
goto v___jp_2607_;
}
v___jp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = lean_box(v_r_2603_);
v___x_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
lean_ctor_set(v___x_2606_, 1, v___y_2604_);
return v___x_2606_;
}
v___jp_2607_:
{
lean_object* v_log_2609_; uint8_t v_action_2610_; uint8_t v_wantsRebuild_2611_; lean_object* v_trace_2612_; lean_object* v_buildTime_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2623_; 
v_log_2609_ = lean_ctor_get(v_a_2608_, 0);
v_action_2610_ = lean_ctor_get_uint8(v_a_2608_, sizeof(void*)*3);
v_wantsRebuild_2611_ = lean_ctor_get_uint8(v_a_2608_, sizeof(void*)*3 + 1);
v_trace_2612_ = lean_ctor_get(v_a_2608_, 1);
v_buildTime_2613_ = lean_ctor_get(v_a_2608_, 2);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_a_2608_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2615_ = v_a_2608_;
v_isShared_2616_ = v_isSharedCheck_2623_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_buildTime_2613_);
lean_inc(v_trace_2612_);
lean_inc(v_log_2609_);
lean_dec(v_a_2608_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2623_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
uint8_t v___x_2617_; uint8_t v___x_2618_; lean_object* v___x_2620_; 
v___x_2617_ = 4;
v___x_2618_ = l_Lake_JobAction_merge(v_action_2610_, v___x_2617_);
if (v_isShared_2616_ == 0)
{
v___x_2620_ = v___x_2615_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_log_2609_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_trace_2612_);
lean_ctor_set(v_reuseFailAlloc_2622_, 2, v_buildTime_2613_);
lean_ctor_set_uint8(v_reuseFailAlloc_2622_, sizeof(void*)*3 + 1, v_wantsRebuild_2611_);
v___x_2620_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
uint8_t v___x_2621_; 
lean_ctor_set_uint8(v___x_2620_, sizeof(void*)*3, v___x_2618_);
v___x_2621_ = 0;
v_r_2603_ = v___x_2621_;
v___y_2604_ = v___x_2620_;
goto v___jp_2602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object* v_pkg_2637_, lean_object* v___x_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(v_pkg_2637_, v___x_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec_ref(v___x_2638_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object* v___x_2647_, lean_object* v___x_2648_, lean_object* v___x_2649_, lean_object* v___x_2650_, lean_object* v_pkg_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___f_2659_; lean_object* v___x_2660_; lean_object* v___f_2661_; lean_object* v___x_2662_; 
lean_inc_ref(v_pkg_2651_);
v___f_2659_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2659_, 0, v_pkg_2651_);
lean_closure_set(v___f_2659_, 1, v___x_2647_);
v___x_2660_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2648_);
v___f_2661_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2661_, 0, v___x_2648_);
lean_closure_set(v___f_2661_, 1, v___f_2659_);
lean_closure_set(v___f_2661_, 2, v___x_2649_);
lean_closure_set(v___f_2661_, 3, v___x_2660_);
v___x_2662_ = l_Lake_ensureJob___redArg(v___x_2648_, v___f_2661_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2695_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_a_2664_ = lean_ctor_get(v___x_2662_, 1);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2666_ = v___x_2662_;
v_isShared_2667_ = v_isSharedCheck_2695_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2695_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_task_2668_; lean_object* v_kind_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2693_; 
v_task_2668_ = lean_ctor_get(v_a_2663_, 0);
v_kind_2669_ = lean_ctor_get(v_a_2663_, 1);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_a_2663_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v_a_2663_, 2);
lean_dec(v_unused_2694_);
v___x_2671_ = v_a_2663_;
v_isShared_2672_ = v_isSharedCheck_2693_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_kind_2669_);
lean_inc(v_task_2668_);
lean_dec(v_a_2663_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2693_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v_registeredJobs_2673_; lean_object* v___x_2674_; lean_object* v_baseName_2675_; uint8_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v_job_2684_; 
v_registeredJobs_2673_ = lean_ctor_get(v___y_2656_, 4);
v___x_2674_ = lean_st_ref_take(v_registeredJobs_2673_);
v_baseName_2675_ = lean_ctor_get(v_pkg_2651_, 1);
lean_inc(v_baseName_2675_);
lean_dec_ref(v_pkg_2651_);
v___x_2676_ = 1;
v___x_2677_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2675_, v___x_2676_);
v___x_2678_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2679_ = lean_string_append(v___x_2677_, v___x_2678_);
v___x_2680_ = l_Lake_Name_eraseHead(v___x_2650_);
v___x_2681_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2680_, v___x_2676_);
v___x_2682_ = lean_string_append(v___x_2679_, v___x_2681_);
lean_dec_ref(v___x_2681_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 2, v___x_2682_);
v_job_2684_ = v___x_2671_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_task_2668_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_kind_2669_);
lean_ctor_set(v_reuseFailAlloc_2692_, 2, v___x_2682_);
v_job_2684_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
lean_ctor_set_uint8(v_job_2684_, sizeof(void*)*3, v___x_2676_);
lean_inc_ref(v_job_2684_);
v___x_2685_ = l_Lake_Job_toOpaque___redArg(v_job_2684_);
v___x_2686_ = lean_array_push(v___x_2674_, v___x_2685_);
v___x_2687_ = lean_st_ref_put(v_registeredJobs_2673_, v___x_2686_);
v___x_2688_ = l_Lake_Job_renew___redArg(v_job_2684_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2688_);
v___x_2690_ = v___x_2666_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_a_2664_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_2651_);
lean_dec(v___x_2650_);
return v___x_2662_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_2696_, lean_object* v___x_2697_, lean_object* v___x_2698_, lean_object* v___x_2699_, lean_object* v_pkg_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(v___x_2696_, v___x_2697_, v___x_2698_, v___x_2699_, v_pkg_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec(v___y_2702_);
return v_res_2708_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___f_2715_; 
v___x_2711_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_2712_ = lean_unsigned_to_nat(0u);
v___x_2713_ = l_Lake_instDataKindBool;
v___x_2714_ = ((lean_object*)(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0));
v___f_2715_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2715_, 0, v___x_2714_);
lean_closure_set(v___f_2715_, 1, v___x_2713_);
lean_closure_set(v___f_2715_, 2, v___x_2712_);
lean_closure_set(v___f_2715_, 3, v___x_2711_);
return v___f_2715_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2716_; uint8_t v___x_2717_; lean_object* v___x_2718_; lean_object* v___f_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___f_2716_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_2717_ = 1;
v___x_2718_ = l_Lake_instDataKindBool;
v___f_2719_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__1, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1);
v___x_2720_ = l_Lake_Package_keyword;
v___x_2721_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
lean_ctor_set(v___x_2721_, 1, v___f_2719_);
lean_ctor_set(v___x_2721_, 2, v___x_2718_);
lean_ctor_set(v___x_2721_, 3, v___f_2716_);
lean_ctor_set_uint8(v___x_2721_, sizeof(void*)*4, v___x_2717_);
lean_ctor_set_uint8(v___x_2721_, sizeof(void*)*4 + 1, v___x_2717_);
return v___x_2721_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__2, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* v_baseName_2724_, lean_object* v___x_2725_, uint8_t v_success_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_a_2735_; lean_object* v_a_2736_; 
if (v_success_2726_ == 0)
{
lean_object* v_toBuildConfig_2756_; uint8_t v_verbosity_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v_toBuildConfig_2756_ = lean_ctor_get(v___y_2731_, 0);
v_verbosity_2757_ = lean_ctor_get_uint8(v_toBuildConfig_2756_, sizeof(void*)*4 + 4);
v___x_2758_ = l_Lake_Verbosity_ctorIdx(v_verbosity_2757_);
v___x_2759_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_2760_ = lean_nat_dec_eq(v___x_2758_, v___x_2759_);
lean_dec(v___x_2758_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; 
lean_dec(v___x_2725_);
lean_dec(v_baseName_2724_);
v___x_2761_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_2735_ = v___x_2761_;
v_a_2736_ = v___y_2732_;
goto v___jp_2734_;
}
else
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2762_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2763_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2724_, v___x_2760_);
v___x_2764_ = lean_string_append(v___x_2762_, v___x_2763_);
lean_dec_ref(v___x_2763_);
v___x_2765_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2766_ = lean_string_append(v___x_2764_, v___x_2765_);
v___x_2767_ = l_Lake_Name_eraseHead(v___x_2725_);
v___x_2768_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2767_, v___x_2760_);
v___x_2769_ = lean_string_append(v___x_2766_, v___x_2768_);
lean_dec_ref(v___x_2768_);
v___x_2770_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_2771_ = lean_string_append(v___x_2769_, v___x_2770_);
v_a_2735_ = v___x_2771_;
v_a_2736_ = v___y_2732_;
goto v___jp_2734_;
}
}
else
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_dec(v___x_2725_);
lean_dec(v_baseName_2724_);
v___x_2772_ = lean_box(0);
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2772_);
lean_ctor_set(v___x_2773_, 1, v___y_2732_);
return v___x_2773_;
}
v___jp_2734_:
{
lean_object* v_log_2737_; uint8_t v_action_2738_; uint8_t v_wantsRebuild_2739_; lean_object* v_trace_2740_; lean_object* v_buildTime_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2755_; 
v_log_2737_ = lean_ctor_get(v_a_2736_, 0);
v_action_2738_ = lean_ctor_get_uint8(v_a_2736_, sizeof(void*)*3);
v_wantsRebuild_2739_ = lean_ctor_get_uint8(v_a_2736_, sizeof(void*)*3 + 1);
v_trace_2740_ = lean_ctor_get(v_a_2736_, 1);
v_buildTime_2741_ = lean_ctor_get(v_a_2736_, 2);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_a_2736_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2743_ = v_a_2736_;
v_isShared_2744_ = v_isSharedCheck_2755_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_buildTime_2741_);
lean_inc(v_trace_2740_);
lean_inc(v_log_2737_);
lean_dec(v_a_2736_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2755_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; uint8_t v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2745_ = ((lean_object*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0));
v___x_2746_ = lean_string_append(v___x_2745_, v_a_2735_);
lean_dec_ref(v_a_2735_);
v___x_2747_ = 3;
v___x_2748_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*1, v___x_2747_);
v___x_2749_ = lean_array_get_size(v_log_2737_);
v___x_2750_ = lean_array_push(v_log_2737_, v___x_2748_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v___x_2750_);
v___x_2752_ = v___x_2743_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2754_, 1, v_trace_2740_);
lean_ctor_set(v_reuseFailAlloc_2754_, 2, v_buildTime_2741_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, sizeof(void*)*3, v_action_2738_);
lean_ctor_set_uint8(v_reuseFailAlloc_2754_, sizeof(void*)*3 + 1, v_wantsRebuild_2739_);
v___x_2752_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; 
v___x_2753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2749_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
return v___x_2753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object* v_baseName_2774_, lean_object* v___x_2775_, lean_object* v_success_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
uint8_t v_success_boxed_2784_; lean_object* v_res_2785_; 
v_success_boxed_2784_ = lean_unbox(v_success_2776_);
v_res_2785_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(v_baseName_2774_, v___x_2775_, v_success_boxed_2784_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* v___x_2786_, lean_object* v___x_2787_, lean_object* v___x_2788_, lean_object* v_pkg_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_baseName_2797_; lean_object* v_keyName_2798_; lean_object* v___f_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___f_2803_; lean_object* v___x_2804_; 
v_baseName_2797_ = lean_ctor_get(v_pkg_2789_, 1);
lean_inc_n(v_baseName_2797_, 2);
v_keyName_2798_ = lean_ctor_get(v_pkg_2789_, 2);
lean_inc(v___x_2786_);
v___f_2799_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2799_, 0, v_baseName_2797_);
lean_closure_set(v___f_2799_, 1, v___x_2786_);
lean_inc(v_keyName_2798_);
v___x_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2800_, 0, v_keyName_2798_);
v___x_2801_ = l_Lake_Package_keyword;
v___x_2802_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
lean_ctor_set(v___x_2802_, 2, v_pkg_2789_);
lean_ctor_set(v___x_2802_, 3, v___x_2786_);
lean_inc(v___x_2787_);
v___f_2803_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2803_, 0, v___x_2802_);
lean_closure_set(v___f_2803_, 1, v___x_2787_);
lean_closure_set(v___f_2803_, 2, v___f_2799_);
v___x_2804_ = l_Lake_ensureJob___redArg(v___x_2787_, v___f_2803_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2837_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
v_a_2806_ = lean_ctor_get(v___x_2804_, 1);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2808_ = v___x_2804_;
v_isShared_2809_ = v_isSharedCheck_2837_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_inc(v_a_2805_);
lean_dec(v___x_2804_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2837_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v_task_2810_; lean_object* v_kind_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2835_; 
v_task_2810_ = lean_ctor_get(v_a_2805_, 0);
v_kind_2811_ = lean_ctor_get(v_a_2805_, 1);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_a_2805_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; 
v_unused_2836_ = lean_ctor_get(v_a_2805_, 2);
lean_dec(v_unused_2836_);
v___x_2813_ = v_a_2805_;
v_isShared_2814_ = v_isSharedCheck_2835_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_kind_2811_);
lean_inc(v_task_2810_);
lean_dec(v_a_2805_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2835_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v_registeredJobs_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; lean_object* v_job_2826_; 
v_registeredJobs_2815_ = lean_ctor_get(v___y_2794_, 4);
v___x_2816_ = lean_st_ref_take(v_registeredJobs_2815_);
v___x_2817_ = 1;
v___x_2818_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2797_, v___x_2817_);
v___x_2819_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2820_ = lean_string_append(v___x_2818_, v___x_2819_);
v___x_2821_ = l_Lake_Name_eraseHead(v___x_2788_);
v___x_2822_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2821_, v___x_2817_);
v___x_2823_ = lean_string_append(v___x_2820_, v___x_2822_);
lean_dec_ref(v___x_2822_);
v___x_2824_ = 0;
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 2, v___x_2823_);
v_job_2826_ = v___x_2813_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_task_2810_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v_kind_2811_);
lean_ctor_set(v_reuseFailAlloc_2834_, 2, v___x_2823_);
v_job_2826_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2832_; 
lean_ctor_set_uint8(v_job_2826_, sizeof(void*)*3, v___x_2824_);
lean_inc_ref(v_job_2826_);
v___x_2827_ = l_Lake_Job_toOpaque___redArg(v_job_2826_);
v___x_2828_ = lean_array_push(v___x_2816_, v___x_2827_);
v___x_2829_ = lean_st_ref_put(v_registeredJobs_2815_, v___x_2828_);
v___x_2830_ = l_Lake_Job_renew___redArg(v_job_2826_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v___x_2830_);
v___x_2832_ = v___x_2808_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2830_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_a_2806_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2797_);
lean_dec(v___x_2788_);
return v___x_2804_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_2838_, lean_object* v___x_2839_, lean_object* v___x_2840_, lean_object* v_pkg_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(v___x_2838_, v___x_2839_, v___x_2840_, v_pkg_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec(v___y_2843_);
return v_res_2849_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___f_2853_; 
v___x_2850_ = l_Lake_Package_gitHubReleaseFacet;
v___x_2851_ = l_Lake_instDataKindUnit;
v___x_2852_ = l_Lake_Package_optGitHubReleaseFacet;
v___f_2853_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2853_, 0, v___x_2852_);
lean_closure_set(v___f_2853_, 1, v___x_2851_);
lean_closure_set(v___f_2853_, 2, v___x_2850_);
return v___f_2853_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2854_; uint8_t v___x_2855_; lean_object* v___x_2856_; lean_object* v___f_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___f_2854_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2855_ = 1;
v___x_2856_ = l_Lake_instDataKindUnit;
v___f_2857_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__0, &l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0);
v___x_2858_ = l_Lake_Package_keyword;
v___x_2859_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
lean_ctor_set(v___x_2859_, 1, v___f_2857_);
lean_ctor_set(v___x_2859_, 2, v___x_2856_);
lean_ctor_set(v___x_2859_, 3, v___f_2854_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*4, v___x_2855_);
lean_ctor_set_uint8(v___x_2859_, sizeof(void*)*4 + 1, v___x_2855_);
return v___x_2859_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__1, &l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* v_build_2861_, uint8_t v_x_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_log_2870_; uint8_t v_action_2871_; uint8_t v_wantsRebuild_2872_; lean_object* v_buildTime_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2882_; 
v_log_2870_ = lean_ctor_get(v___y_2868_, 0);
v_action_2871_ = lean_ctor_get_uint8(v___y_2868_, sizeof(void*)*3);
v_wantsRebuild_2872_ = lean_ctor_get_uint8(v___y_2868_, sizeof(void*)*3 + 1);
v_buildTime_2873_ = lean_ctor_get(v___y_2868_, 2);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___y_2868_);
if (v_isSharedCheck_2882_ == 0)
{
lean_object* v_unused_2883_; 
v_unused_2883_ = lean_ctor_get(v___y_2868_, 1);
lean_dec(v_unused_2883_);
v___x_2875_ = v___y_2868_;
v_isShared_2876_ = v_isSharedCheck_2882_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_buildTime_2873_);
lean_inc(v_log_2870_);
lean_dec(v___y_2868_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2882_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; lean_object* v___x_2879_; 
v___x_2877_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 1, v___x_2877_);
v___x_2879_ = v___x_2875_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_log_2870_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2881_, 2, v_buildTime_2873_);
lean_ctor_set_uint8(v_reuseFailAlloc_2881_, sizeof(void*)*3, v_action_2871_);
lean_ctor_set_uint8(v_reuseFailAlloc_2881_, sizeof(void*)*3 + 1, v_wantsRebuild_2872_);
v___x_2879_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
lean_object* v___x_2880_; 
lean_inc_ref(v___y_2867_);
lean_inc(v___y_2866_);
lean_inc(v___y_2865_);
lean_inc(v___y_2864_);
v___x_2880_ = lean_apply_7(v_build_2861_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___x_2879_, lean_box(0));
return v___x_2880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* v_build_2884_, lean_object* v_x_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
uint8_t v_x_1602__boxed_2893_; lean_object* v_res_2894_; 
v_x_1602__boxed_2893_ = lean_unbox(v_x_2885_);
v_res_2894_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(v_build_2884_, v_x_1602__boxed_2893_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec(v___y_2887_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* v_self_2895_, lean_object* v_build_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v_wsIdx_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v_wsIdx_2904_ = lean_ctor_get(v_self_2895_, 0);
v___x_2905_ = lean_unsigned_to_nat(0u);
v___x_2906_ = lean_nat_dec_eq(v_wsIdx_2904_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; 
lean_inc_ref(v_a_2897_);
v___x_2907_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_2895_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2920_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
v_a_2909_ = lean_ctor_get(v___x_2907_, 1);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2911_ = v___x_2907_;
v_isShared_2912_ = v_isSharedCheck_2920_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_inc(v_a_2908_);
lean_dec(v___x_2907_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2920_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___f_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___f_2913_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2913_, 0, v_build_2896_);
v___x_2914_ = lean_box(0);
v___x_2915_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2916_ = l_Lake_Job_bindM___redArg(v___x_2914_, v_a_2908_, v___f_2913_, v___x_2905_, v___x_2906_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v___x_2915_);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 0, v___x_2916_);
v___x_2918_ = v___x_2911_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_a_2909_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec_ref(v_a_2897_);
lean_dec_ref(v_build_2896_);
v_a_2921_ = lean_ctor_get(v___x_2907_, 0);
v_a_2922_ = lean_ctor_get(v___x_2907_, 1);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2907_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_inc(v_a_2921_);
lean_dec(v___x_2907_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2921_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
uint8_t v___x_2930_; uint8_t v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_dec_ref(v_self_2895_);
v___x_2930_ = 0;
v___x_2931_ = 0;
v___x_2932_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2933_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2933_, 0, v_a_2902_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
lean_ctor_set(v___x_2933_, 2, v___x_2905_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3, v___x_2930_);
lean_ctor_set_uint8(v___x_2933_, sizeof(void*)*3 + 1, v___x_2931_);
lean_inc_ref(v_a_2901_);
lean_inc(v_a_2900_);
lean_inc(v_a_2899_);
lean_inc(v_a_2898_);
v___x_2934_ = lean_apply_7(v_build_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v___x_2933_, lean_box(0));
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2944_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 1);
v_a_2936_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2938_ = v___x_2934_;
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2935_);
lean_inc(v_a_2936_);
lean_dec(v___x_2934_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v_log_2940_; lean_object* v___x_2942_; 
v_log_2940_ = lean_ctor_get(v_a_2935_, 0);
lean_inc_ref(v_log_2940_);
lean_dec(v_a_2935_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 1, v_log_2940_);
v___x_2942_ = v___x_2938_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2936_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_log_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2954_; 
v_a_2945_ = lean_ctor_get(v___x_2934_, 1);
v_a_2946_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2948_ = v___x_2934_;
v_isShared_2949_ = v_isSharedCheck_2954_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2945_);
lean_inc(v_a_2946_);
lean_dec(v___x_2934_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2954_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v_log_2950_; lean_object* v___x_2952_; 
v_log_2950_ = lean_ctor_get(v_a_2945_, 0);
lean_inc_ref(v_log_2950_);
lean_dec(v_a_2945_);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 1, v_log_2950_);
v___x_2952_ = v___x_2948_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2946_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_log_2950_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___boxed(lean_object* v_self_2955_, lean_object* v_build_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_2955_, v_build_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec(v_a_2960_);
lean_dec(v_a_2959_);
lean_dec(v_a_2958_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* v_00_u03b1_2965_, lean_object* v_self_2966_, lean_object* v_build_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_2966_, v_build_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___boxed(lean_object* v_00_u03b1_2976_, lean_object* v_self_2977_, lean_object* v_build_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Lake_Package_afterBuildCacheAsync(v_00_u03b1_2976_, v_self_2977_, v_build_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec(v_a_2981_);
lean_dec(v_a_2980_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* v_build_2987_, uint8_t v_x_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v_log_2996_; uint8_t v_action_2997_; uint8_t v_wantsRebuild_2998_; lean_object* v_buildTime_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3008_; 
v_log_2996_ = lean_ctor_get(v___y_2994_, 0);
v_action_2997_ = lean_ctor_get_uint8(v___y_2994_, sizeof(void*)*3);
v_wantsRebuild_2998_ = lean_ctor_get_uint8(v___y_2994_, sizeof(void*)*3 + 1);
v_buildTime_2999_ = lean_ctor_get(v___y_2994_, 2);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___y_2994_);
if (v_isSharedCheck_3008_ == 0)
{
lean_object* v_unused_3009_; 
v_unused_3009_ = lean_ctor_get(v___y_2994_, 1);
lean_dec(v_unused_3009_);
v___x_3001_ = v___y_2994_;
v_isShared_3002_ = v_isSharedCheck_3008_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_buildTime_2999_);
lean_inc(v_log_2996_);
lean_dec(v___y_2994_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3008_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_3003_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 1, v___x_3003_);
v___x_3005_ = v___x_3001_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_log_2996_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3007_, 2, v_buildTime_2999_);
lean_ctor_set_uint8(v_reuseFailAlloc_3007_, sizeof(void*)*3, v_action_2997_);
lean_ctor_set_uint8(v_reuseFailAlloc_3007_, sizeof(void*)*3 + 1, v_wantsRebuild_2998_);
v___x_3005_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; 
lean_inc_ref(v___y_2993_);
lean_inc(v___y_2992_);
lean_inc(v___y_2991_);
lean_inc(v___y_2990_);
v___x_3006_ = lean_apply_7(v_build_2987_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___x_3005_, lean_box(0));
return v___x_3006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* v_build_3010_, lean_object* v_x_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
uint8_t v_x_1631__boxed_3019_; lean_object* v_res_3020_; 
v_x_1631__boxed_3019_ = lean_unbox(v_x_3011_);
v_res_3020_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(v_build_3010_, v_x_1631__boxed_3019_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec(v___y_3013_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* v_self_3021_, lean_object* v_build_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v_wsIdx_3030_; lean_object* v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; 
v_wsIdx_3030_ = lean_ctor_get(v_self_3021_, 0);
v___x_3031_ = lean_unsigned_to_nat(0u);
v___x_3032_ = lean_nat_dec_eq(v_wsIdx_3030_, v___x_3031_);
v___x_3033_ = lean_box(0);
if (v___x_3032_ == 0)
{
lean_object* v___x_3034_; 
lean_inc_ref(v_a_3023_);
v___x_3034_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3021_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3046_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
v_a_3036_ = lean_ctor_get(v___x_3034_, 1);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3038_ = v___x_3034_;
v_isShared_3039_ = v_isSharedCheck_3046_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_inc(v_a_3035_);
lean_dec(v___x_3034_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3046_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___f_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3044_; 
v___f_3040_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3040_, 0, v_build_3022_);
v___x_3041_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3042_ = l_Lake_Job_mapM___redArg(v___x_3033_, v_a_3035_, v___f_3040_, v___x_3031_, v___x_3032_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v___x_3041_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3042_);
v___x_3044_ = v___x_3038_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3042_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v_a_3036_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec_ref(v_a_3023_);
lean_dec_ref(v_build_3022_);
v_a_3047_ = lean_ctor_get(v___x_3034_, 0);
v_a_3048_ = lean_ctor_get(v___x_3034_, 1);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3034_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_inc(v_a_3047_);
lean_dec(v___x_3034_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3047_);
lean_ctor_set(v_reuseFailAlloc_3054_, 1, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
else
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_dec_ref(v_self_3021_);
v___x_3056_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_3057_ = l_Lake_Job_async___redArg(v___x_3033_, v_build_3022_, v___x_3031_, v___x_3056_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
lean_ctor_set(v___x_3058_, 1, v_a_3028_);
return v___x_3058_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___boxed(lean_object* v_self_3059_, lean_object* v_build_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3059_, v_build_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
lean_dec_ref(v_a_3065_);
lean_dec(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec(v_a_3062_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* v_00_u03b1_3069_, lean_object* v_self_3070_, lean_object* v_build_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3070_, v_build_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___boxed(lean_object* v_00_u03b1_3080_, lean_object* v_self_3081_, lean_object* v_build_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Lake_Package_afterBuildCacheSync(v_00_u03b1_3080_, v_self_3081_, v_build_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec(v_a_3085_);
lean_dec(v_a_3084_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(lean_object* v_k_3091_, lean_object* v_v_3092_, lean_object* v_t_3093_){
_start:
{
if (lean_obj_tag(v_t_3093_) == 0)
{
lean_object* v_size_3094_; lean_object* v_k_3095_; lean_object* v_v_3096_; lean_object* v_l_3097_; lean_object* v_r_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3378_; 
v_size_3094_ = lean_ctor_get(v_t_3093_, 0);
v_k_3095_ = lean_ctor_get(v_t_3093_, 1);
v_v_3096_ = lean_ctor_get(v_t_3093_, 2);
v_l_3097_ = lean_ctor_get(v_t_3093_, 3);
v_r_3098_ = lean_ctor_get(v_t_3093_, 4);
v_isSharedCheck_3378_ = !lean_is_exclusive(v_t_3093_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3100_ = v_t_3093_;
v_isShared_3101_ = v_isSharedCheck_3378_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_r_3098_);
lean_inc(v_l_3097_);
lean_inc(v_v_3096_);
lean_inc(v_k_3095_);
lean_inc(v_size_3094_);
lean_dec(v_t_3093_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3378_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
uint8_t v___x_3102_; 
v___x_3102_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3091_, v_k_3095_);
switch(v___x_3102_)
{
case 0:
{
lean_object* v_impl_3103_; lean_object* v___x_3104_; 
lean_dec(v_size_3094_);
v_impl_3103_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3091_, v_v_3092_, v_l_3097_);
v___x_3104_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3098_) == 0)
{
lean_object* v_size_3105_; lean_object* v_size_3106_; lean_object* v_k_3107_; lean_object* v_v_3108_; lean_object* v_l_3109_; lean_object* v_r_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; uint8_t v___x_3113_; 
v_size_3105_ = lean_ctor_get(v_r_3098_, 0);
v_size_3106_ = lean_ctor_get(v_impl_3103_, 0);
lean_inc(v_size_3106_);
v_k_3107_ = lean_ctor_get(v_impl_3103_, 1);
lean_inc(v_k_3107_);
v_v_3108_ = lean_ctor_get(v_impl_3103_, 2);
lean_inc(v_v_3108_);
v_l_3109_ = lean_ctor_get(v_impl_3103_, 3);
lean_inc(v_l_3109_);
v_r_3110_ = lean_ctor_get(v_impl_3103_, 4);
lean_inc(v_r_3110_);
v___x_3111_ = lean_unsigned_to_nat(3u);
v___x_3112_ = lean_nat_mul(v___x_3111_, v_size_3105_);
v___x_3113_ = lean_nat_dec_lt(v___x_3112_, v_size_3106_);
lean_dec(v___x_3112_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3117_; 
lean_dec(v_r_3110_);
lean_dec(v_l_3109_);
lean_dec(v_v_3108_);
lean_dec(v_k_3107_);
v___x_3114_ = lean_nat_add(v___x_3104_, v_size_3106_);
lean_dec(v_size_3106_);
v___x_3115_ = lean_nat_add(v___x_3114_, v_size_3105_);
lean_dec(v___x_3114_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 3, v_impl_3103_);
lean_ctor_set(v___x_3100_, 0, v___x_3115_);
v___x_3117_ = v___x_3100_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3118_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3118_, 3, v_impl_3103_);
lean_ctor_set(v_reuseFailAlloc_3118_, 4, v_r_3098_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
else
{
lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3184_; 
v_isSharedCheck_3184_ = !lean_is_exclusive(v_impl_3103_);
if (v_isSharedCheck_3184_ == 0)
{
lean_object* v_unused_3185_; lean_object* v_unused_3186_; lean_object* v_unused_3187_; lean_object* v_unused_3188_; lean_object* v_unused_3189_; 
v_unused_3185_ = lean_ctor_get(v_impl_3103_, 4);
lean_dec(v_unused_3185_);
v_unused_3186_ = lean_ctor_get(v_impl_3103_, 3);
lean_dec(v_unused_3186_);
v_unused_3187_ = lean_ctor_get(v_impl_3103_, 2);
lean_dec(v_unused_3187_);
v_unused_3188_ = lean_ctor_get(v_impl_3103_, 1);
lean_dec(v_unused_3188_);
v_unused_3189_ = lean_ctor_get(v_impl_3103_, 0);
lean_dec(v_unused_3189_);
v___x_3120_ = v_impl_3103_;
v_isShared_3121_ = v_isSharedCheck_3184_;
goto v_resetjp_3119_;
}
else
{
lean_dec(v_impl_3103_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3184_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v_size_3122_; lean_object* v_size_3123_; lean_object* v_k_3124_; lean_object* v_v_3125_; lean_object* v_l_3126_; lean_object* v_r_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; 
v_size_3122_ = lean_ctor_get(v_l_3109_, 0);
v_size_3123_ = lean_ctor_get(v_r_3110_, 0);
v_k_3124_ = lean_ctor_get(v_r_3110_, 1);
v_v_3125_ = lean_ctor_get(v_r_3110_, 2);
v_l_3126_ = lean_ctor_get(v_r_3110_, 3);
v_r_3127_ = lean_ctor_get(v_r_3110_, 4);
v___x_3128_ = lean_unsigned_to_nat(2u);
v___x_3129_ = lean_nat_mul(v___x_3128_, v_size_3122_);
v___x_3130_ = lean_nat_dec_lt(v_size_3123_, v___x_3129_);
lean_dec(v___x_3129_);
if (v___x_3130_ == 0)
{
lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3159_; 
lean_inc(v_r_3127_);
lean_inc(v_l_3126_);
lean_inc(v_v_3125_);
lean_inc(v_k_3124_);
v_isSharedCheck_3159_ = !lean_is_exclusive(v_r_3110_);
if (v_isSharedCheck_3159_ == 0)
{
lean_object* v_unused_3160_; lean_object* v_unused_3161_; lean_object* v_unused_3162_; lean_object* v_unused_3163_; lean_object* v_unused_3164_; 
v_unused_3160_ = lean_ctor_get(v_r_3110_, 4);
lean_dec(v_unused_3160_);
v_unused_3161_ = lean_ctor_get(v_r_3110_, 3);
lean_dec(v_unused_3161_);
v_unused_3162_ = lean_ctor_get(v_r_3110_, 2);
lean_dec(v_unused_3162_);
v_unused_3163_ = lean_ctor_get(v_r_3110_, 1);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_r_3110_, 0);
lean_dec(v_unused_3164_);
v___x_3132_ = v_r_3110_;
v_isShared_3133_ = v_isSharedCheck_3159_;
goto v_resetjp_3131_;
}
else
{
lean_dec(v_r_3110_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3159_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___x_3147_; lean_object* v___y_3149_; 
v___x_3134_ = lean_nat_add(v___x_3104_, v_size_3106_);
lean_dec(v_size_3106_);
v___x_3135_ = lean_nat_add(v___x_3134_, v_size_3105_);
lean_dec(v___x_3134_);
v___x_3147_ = lean_nat_add(v___x_3104_, v_size_3122_);
if (lean_obj_tag(v_l_3126_) == 0)
{
lean_object* v_size_3157_; 
v_size_3157_ = lean_ctor_get(v_l_3126_, 0);
lean_inc(v_size_3157_);
v___y_3149_ = v_size_3157_;
goto v___jp_3148_;
}
else
{
lean_object* v___x_3158_; 
v___x_3158_ = lean_unsigned_to_nat(0u);
v___y_3149_ = v___x_3158_;
goto v___jp_3148_;
}
v___jp_3136_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3140_ = lean_nat_add(v___y_3138_, v___y_3139_);
lean_dec(v___y_3139_);
lean_dec(v___y_3138_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 4, v_r_3098_);
lean_ctor_set(v___x_3132_, 3, v_r_3127_);
lean_ctor_set(v___x_3132_, 2, v_v_3096_);
lean_ctor_set(v___x_3132_, 1, v_k_3095_);
lean_ctor_set(v___x_3132_, 0, v___x_3140_);
v___x_3142_ = v___x_3132_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3140_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3146_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3146_, 3, v_r_3127_);
lean_ctor_set(v_reuseFailAlloc_3146_, 4, v_r_3098_);
v___x_3142_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v___x_3144_; 
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 4, v___x_3142_);
lean_ctor_set(v___x_3120_, 3, v___y_3137_);
lean_ctor_set(v___x_3120_, 2, v_v_3125_);
lean_ctor_set(v___x_3120_, 1, v_k_3124_);
lean_ctor_set(v___x_3120_, 0, v___x_3135_);
v___x_3144_ = v___x_3120_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3135_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_k_3124_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v_v_3125_);
lean_ctor_set(v_reuseFailAlloc_3145_, 3, v___y_3137_);
lean_ctor_set(v_reuseFailAlloc_3145_, 4, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
v___jp_3148_:
{
lean_object* v___x_3150_; lean_object* v___x_3152_; 
v___x_3150_ = lean_nat_add(v___x_3147_, v___y_3149_);
lean_dec(v___y_3149_);
lean_dec(v___x_3147_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v_l_3126_);
lean_ctor_set(v___x_3100_, 3, v_l_3109_);
lean_ctor_set(v___x_3100_, 2, v_v_3108_);
lean_ctor_set(v___x_3100_, 1, v_k_3107_);
lean_ctor_set(v___x_3100_, 0, v___x_3150_);
v___x_3152_ = v___x_3100_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3150_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v_k_3107_);
lean_ctor_set(v_reuseFailAlloc_3156_, 2, v_v_3108_);
lean_ctor_set(v_reuseFailAlloc_3156_, 3, v_l_3109_);
lean_ctor_set(v_reuseFailAlloc_3156_, 4, v_l_3126_);
v___x_3152_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
lean_object* v___x_3153_; 
v___x_3153_ = lean_nat_add(v___x_3104_, v_size_3105_);
if (lean_obj_tag(v_r_3127_) == 0)
{
lean_object* v_size_3154_; 
v_size_3154_ = lean_ctor_get(v_r_3127_, 0);
lean_inc(v_size_3154_);
v___y_3137_ = v___x_3152_;
v___y_3138_ = v___x_3153_;
v___y_3139_ = v_size_3154_;
goto v___jp_3136_;
}
else
{
lean_object* v___x_3155_; 
v___x_3155_ = lean_unsigned_to_nat(0u);
v___y_3137_ = v___x_3152_;
v___y_3138_ = v___x_3153_;
v___y_3139_ = v___x_3155_;
goto v___jp_3136_;
}
}
}
}
}
else
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3170_; 
lean_del_object(v___x_3100_);
v___x_3165_ = lean_nat_add(v___x_3104_, v_size_3106_);
lean_dec(v_size_3106_);
v___x_3166_ = lean_nat_add(v___x_3165_, v_size_3105_);
lean_dec(v___x_3165_);
v___x_3167_ = lean_nat_add(v___x_3104_, v_size_3105_);
v___x_3168_ = lean_nat_add(v___x_3167_, v_size_3123_);
lean_dec(v___x_3167_);
lean_inc_ref(v_r_3098_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 4, v_r_3098_);
lean_ctor_set(v___x_3120_, 3, v_r_3110_);
lean_ctor_set(v___x_3120_, 2, v_v_3096_);
lean_ctor_set(v___x_3120_, 1, v_k_3095_);
lean_ctor_set(v___x_3120_, 0, v___x_3168_);
v___x_3170_ = v___x_3120_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3168_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3183_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3183_, 3, v_r_3110_);
lean_ctor_set(v_reuseFailAlloc_3183_, 4, v_r_3098_);
v___x_3170_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
v_isSharedCheck_3177_ = !lean_is_exclusive(v_r_3098_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; lean_object* v_unused_3179_; lean_object* v_unused_3180_; lean_object* v_unused_3181_; lean_object* v_unused_3182_; 
v_unused_3178_ = lean_ctor_get(v_r_3098_, 4);
lean_dec(v_unused_3178_);
v_unused_3179_ = lean_ctor_get(v_r_3098_, 3);
lean_dec(v_unused_3179_);
v_unused_3180_ = lean_ctor_get(v_r_3098_, 2);
lean_dec(v_unused_3180_);
v_unused_3181_ = lean_ctor_get(v_r_3098_, 1);
lean_dec(v_unused_3181_);
v_unused_3182_ = lean_ctor_get(v_r_3098_, 0);
lean_dec(v_unused_3182_);
v___x_3172_ = v_r_3098_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_dec(v_r_3098_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 4, v___x_3170_);
lean_ctor_set(v___x_3172_, 3, v_l_3109_);
lean_ctor_set(v___x_3172_, 2, v_v_3108_);
lean_ctor_set(v___x_3172_, 1, v_k_3107_);
lean_ctor_set(v___x_3172_, 0, v___x_3166_);
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3166_);
lean_ctor_set(v_reuseFailAlloc_3176_, 1, v_k_3107_);
lean_ctor_set(v_reuseFailAlloc_3176_, 2, v_v_3108_);
lean_ctor_set(v_reuseFailAlloc_3176_, 3, v_l_3109_);
lean_ctor_set(v_reuseFailAlloc_3176_, 4, v___x_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3190_; 
v_l_3190_ = lean_ctor_get(v_impl_3103_, 3);
lean_inc(v_l_3190_);
if (lean_obj_tag(v_l_3190_) == 0)
{
lean_object* v_r_3191_; lean_object* v_k_3192_; lean_object* v_v_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3204_; 
v_r_3191_ = lean_ctor_get(v_impl_3103_, 4);
v_k_3192_ = lean_ctor_get(v_impl_3103_, 1);
v_v_3193_ = lean_ctor_get(v_impl_3103_, 2);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_impl_3103_);
if (v_isSharedCheck_3204_ == 0)
{
lean_object* v_unused_3205_; lean_object* v_unused_3206_; 
v_unused_3205_ = lean_ctor_get(v_impl_3103_, 3);
lean_dec(v_unused_3205_);
v_unused_3206_ = lean_ctor_get(v_impl_3103_, 0);
lean_dec(v_unused_3206_);
v___x_3195_ = v_impl_3103_;
v_isShared_3196_ = v_isSharedCheck_3204_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_r_3191_);
lean_inc(v_v_3193_);
lean_inc(v_k_3192_);
lean_dec(v_impl_3103_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3204_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3197_; lean_object* v___x_3199_; 
v___x_3197_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3191_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 3, v_r_3191_);
lean_ctor_set(v___x_3195_, 2, v_v_3096_);
lean_ctor_set(v___x_3195_, 1, v_k_3095_);
lean_ctor_set(v___x_3195_, 0, v___x_3104_);
v___x_3199_ = v___x_3195_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3203_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3203_, 3, v_r_3191_);
lean_ctor_set(v_reuseFailAlloc_3203_, 4, v_r_3191_);
v___x_3199_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3201_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v___x_3199_);
lean_ctor_set(v___x_3100_, 3, v_l_3190_);
lean_ctor_set(v___x_3100_, 2, v_v_3193_);
lean_ctor_set(v___x_3100_, 1, v_k_3192_);
lean_ctor_set(v___x_3100_, 0, v___x_3197_);
v___x_3201_ = v___x_3100_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v_k_3192_);
lean_ctor_set(v_reuseFailAlloc_3202_, 2, v_v_3193_);
lean_ctor_set(v_reuseFailAlloc_3202_, 3, v_l_3190_);
lean_ctor_set(v_reuseFailAlloc_3202_, 4, v___x_3199_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
else
{
lean_object* v_r_3207_; 
v_r_3207_ = lean_ctor_get(v_impl_3103_, 4);
lean_inc(v_r_3207_);
if (lean_obj_tag(v_r_3207_) == 0)
{
lean_object* v_k_3208_; lean_object* v_v_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3232_; 
v_k_3208_ = lean_ctor_get(v_impl_3103_, 1);
v_v_3209_ = lean_ctor_get(v_impl_3103_, 2);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_impl_3103_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; lean_object* v_unused_3234_; lean_object* v_unused_3235_; 
v_unused_3233_ = lean_ctor_get(v_impl_3103_, 4);
lean_dec(v_unused_3233_);
v_unused_3234_ = lean_ctor_get(v_impl_3103_, 3);
lean_dec(v_unused_3234_);
v_unused_3235_ = lean_ctor_get(v_impl_3103_, 0);
lean_dec(v_unused_3235_);
v___x_3211_ = v_impl_3103_;
v_isShared_3212_ = v_isSharedCheck_3232_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_v_3209_);
lean_inc(v_k_3208_);
lean_dec(v_impl_3103_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3232_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v_k_3213_; lean_object* v_v_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3228_; 
v_k_3213_ = lean_ctor_get(v_r_3207_, 1);
v_v_3214_ = lean_ctor_get(v_r_3207_, 2);
v_isSharedCheck_3228_ = !lean_is_exclusive(v_r_3207_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; lean_object* v_unused_3230_; lean_object* v_unused_3231_; 
v_unused_3229_ = lean_ctor_get(v_r_3207_, 4);
lean_dec(v_unused_3229_);
v_unused_3230_ = lean_ctor_get(v_r_3207_, 3);
lean_dec(v_unused_3230_);
v_unused_3231_ = lean_ctor_get(v_r_3207_, 0);
lean_dec(v_unused_3231_);
v___x_3216_ = v_r_3207_;
v_isShared_3217_ = v_isSharedCheck_3228_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_v_3214_);
lean_inc(v_k_3213_);
lean_dec(v_r_3207_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3228_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; lean_object* v___x_3220_; 
v___x_3218_ = lean_unsigned_to_nat(3u);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 4, v_l_3190_);
lean_ctor_set(v___x_3216_, 3, v_l_3190_);
lean_ctor_set(v___x_3216_, 2, v_v_3209_);
lean_ctor_set(v___x_3216_, 1, v_k_3208_);
lean_ctor_set(v___x_3216_, 0, v___x_3104_);
v___x_3220_ = v___x_3216_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_k_3208_);
lean_ctor_set(v_reuseFailAlloc_3227_, 2, v_v_3209_);
lean_ctor_set(v_reuseFailAlloc_3227_, 3, v_l_3190_);
lean_ctor_set(v_reuseFailAlloc_3227_, 4, v_l_3190_);
v___x_3220_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
lean_object* v___x_3222_; 
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 4, v_l_3190_);
lean_ctor_set(v___x_3211_, 2, v_v_3096_);
lean_ctor_set(v___x_3211_, 1, v_k_3095_);
lean_ctor_set(v___x_3211_, 0, v___x_3104_);
v___x_3222_ = v___x_3211_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3226_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3226_, 3, v_l_3190_);
lean_ctor_set(v_reuseFailAlloc_3226_, 4, v_l_3190_);
v___x_3222_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3224_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v___x_3222_);
lean_ctor_set(v___x_3100_, 3, v___x_3220_);
lean_ctor_set(v___x_3100_, 2, v_v_3214_);
lean_ctor_set(v___x_3100_, 1, v_k_3213_);
lean_ctor_set(v___x_3100_, 0, v___x_3218_);
v___x_3224_ = v___x_3100_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3218_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_k_3213_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v_v_3214_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v___x_3220_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v___x_3222_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
}
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3236_ = lean_unsigned_to_nat(2u);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v_r_3207_);
lean_ctor_set(v___x_3100_, 3, v_impl_3103_);
lean_ctor_set(v___x_3100_, 0, v___x_3236_);
v___x_3238_ = v___x_3100_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3239_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3239_, 3, v_impl_3103_);
lean_ctor_set(v_reuseFailAlloc_3239_, 4, v_r_3207_);
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
}
case 1:
{
lean_object* v___x_3241_; 
lean_dec(v_v_3096_);
lean_dec(v_k_3095_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 2, v_v_3092_);
lean_ctor_set(v___x_3100_, 1, v_k_3091_);
v___x_3241_ = v___x_3100_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_size_3094_);
lean_ctor_set(v_reuseFailAlloc_3242_, 1, v_k_3091_);
lean_ctor_set(v_reuseFailAlloc_3242_, 2, v_v_3092_);
lean_ctor_set(v_reuseFailAlloc_3242_, 3, v_l_3097_);
lean_ctor_set(v_reuseFailAlloc_3242_, 4, v_r_3098_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
default: 
{
lean_object* v_impl_3243_; lean_object* v___x_3244_; 
lean_dec(v_size_3094_);
v_impl_3243_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3091_, v_v_3092_, v_r_3098_);
v___x_3244_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3097_) == 0)
{
lean_object* v_size_3245_; lean_object* v_size_3246_; lean_object* v_k_3247_; lean_object* v_v_3248_; lean_object* v_l_3249_; lean_object* v_r_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; uint8_t v___x_3253_; 
v_size_3245_ = lean_ctor_get(v_l_3097_, 0);
v_size_3246_ = lean_ctor_get(v_impl_3243_, 0);
lean_inc(v_size_3246_);
v_k_3247_ = lean_ctor_get(v_impl_3243_, 1);
lean_inc(v_k_3247_);
v_v_3248_ = lean_ctor_get(v_impl_3243_, 2);
lean_inc(v_v_3248_);
v_l_3249_ = lean_ctor_get(v_impl_3243_, 3);
lean_inc(v_l_3249_);
v_r_3250_ = lean_ctor_get(v_impl_3243_, 4);
lean_inc(v_r_3250_);
v___x_3251_ = lean_unsigned_to_nat(3u);
v___x_3252_ = lean_nat_mul(v___x_3251_, v_size_3245_);
v___x_3253_ = lean_nat_dec_lt(v___x_3252_, v_size_3246_);
lean_dec(v___x_3252_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3257_; 
lean_dec(v_r_3250_);
lean_dec(v_l_3249_);
lean_dec(v_v_3248_);
lean_dec(v_k_3247_);
v___x_3254_ = lean_nat_add(v___x_3244_, v_size_3245_);
v___x_3255_ = lean_nat_add(v___x_3254_, v_size_3246_);
lean_dec(v_size_3246_);
lean_dec(v___x_3254_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v_impl_3243_);
lean_ctor_set(v___x_3100_, 0, v___x_3255_);
v___x_3257_ = v___x_3100_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3255_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3258_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3258_, 3, v_l_3097_);
lean_ctor_set(v_reuseFailAlloc_3258_, 4, v_impl_3243_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
else
{
lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3322_; 
v_isSharedCheck_3322_ = !lean_is_exclusive(v_impl_3243_);
if (v_isSharedCheck_3322_ == 0)
{
lean_object* v_unused_3323_; lean_object* v_unused_3324_; lean_object* v_unused_3325_; lean_object* v_unused_3326_; lean_object* v_unused_3327_; 
v_unused_3323_ = lean_ctor_get(v_impl_3243_, 4);
lean_dec(v_unused_3323_);
v_unused_3324_ = lean_ctor_get(v_impl_3243_, 3);
lean_dec(v_unused_3324_);
v_unused_3325_ = lean_ctor_get(v_impl_3243_, 2);
lean_dec(v_unused_3325_);
v_unused_3326_ = lean_ctor_get(v_impl_3243_, 1);
lean_dec(v_unused_3326_);
v_unused_3327_ = lean_ctor_get(v_impl_3243_, 0);
lean_dec(v_unused_3327_);
v___x_3260_ = v_impl_3243_;
v_isShared_3261_ = v_isSharedCheck_3322_;
goto v_resetjp_3259_;
}
else
{
lean_dec(v_impl_3243_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3322_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v_size_3262_; lean_object* v_k_3263_; lean_object* v_v_3264_; lean_object* v_l_3265_; lean_object* v_r_3266_; lean_object* v_size_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; uint8_t v___x_3270_; 
v_size_3262_ = lean_ctor_get(v_l_3249_, 0);
v_k_3263_ = lean_ctor_get(v_l_3249_, 1);
v_v_3264_ = lean_ctor_get(v_l_3249_, 2);
v_l_3265_ = lean_ctor_get(v_l_3249_, 3);
v_r_3266_ = lean_ctor_get(v_l_3249_, 4);
v_size_3267_ = lean_ctor_get(v_r_3250_, 0);
v___x_3268_ = lean_unsigned_to_nat(2u);
v___x_3269_ = lean_nat_mul(v___x_3268_, v_size_3267_);
v___x_3270_ = lean_nat_dec_lt(v_size_3262_, v___x_3269_);
lean_dec(v___x_3269_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3298_; 
lean_inc(v_r_3266_);
lean_inc(v_l_3265_);
lean_inc(v_v_3264_);
lean_inc(v_k_3263_);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_l_3249_);
if (v_isSharedCheck_3298_ == 0)
{
lean_object* v_unused_3299_; lean_object* v_unused_3300_; lean_object* v_unused_3301_; lean_object* v_unused_3302_; lean_object* v_unused_3303_; 
v_unused_3299_ = lean_ctor_get(v_l_3249_, 4);
lean_dec(v_unused_3299_);
v_unused_3300_ = lean_ctor_get(v_l_3249_, 3);
lean_dec(v_unused_3300_);
v_unused_3301_ = lean_ctor_get(v_l_3249_, 2);
lean_dec(v_unused_3301_);
v_unused_3302_ = lean_ctor_get(v_l_3249_, 1);
lean_dec(v_unused_3302_);
v_unused_3303_ = lean_ctor_get(v_l_3249_, 0);
lean_dec(v_unused_3303_);
v___x_3272_ = v_l_3249_;
v_isShared_3273_ = v_isSharedCheck_3298_;
goto v_resetjp_3271_;
}
else
{
lean_dec(v_l_3249_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3298_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3288_; 
v___x_3274_ = lean_nat_add(v___x_3244_, v_size_3245_);
v___x_3275_ = lean_nat_add(v___x_3274_, v_size_3246_);
lean_dec(v_size_3246_);
if (lean_obj_tag(v_l_3265_) == 0)
{
lean_object* v_size_3296_; 
v_size_3296_ = lean_ctor_get(v_l_3265_, 0);
lean_inc(v_size_3296_);
v___y_3288_ = v_size_3296_;
goto v___jp_3287_;
}
else
{
lean_object* v___x_3297_; 
v___x_3297_ = lean_unsigned_to_nat(0u);
v___y_3288_ = v___x_3297_;
goto v___jp_3287_;
}
v___jp_3276_:
{
lean_object* v___x_3280_; lean_object* v___x_3282_; 
v___x_3280_ = lean_nat_add(v___y_3278_, v___y_3279_);
lean_dec(v___y_3279_);
lean_dec(v___y_3278_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 4, v_r_3250_);
lean_ctor_set(v___x_3272_, 3, v_r_3266_);
lean_ctor_set(v___x_3272_, 2, v_v_3248_);
lean_ctor_set(v___x_3272_, 1, v_k_3247_);
lean_ctor_set(v___x_3272_, 0, v___x_3280_);
v___x_3282_ = v___x_3272_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v_k_3247_);
lean_ctor_set(v_reuseFailAlloc_3286_, 2, v_v_3248_);
lean_ctor_set(v_reuseFailAlloc_3286_, 3, v_r_3266_);
lean_ctor_set(v_reuseFailAlloc_3286_, 4, v_r_3250_);
v___x_3282_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
lean_object* v___x_3284_; 
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 4, v___x_3282_);
lean_ctor_set(v___x_3260_, 3, v___y_3277_);
lean_ctor_set(v___x_3260_, 2, v_v_3264_);
lean_ctor_set(v___x_3260_, 1, v_k_3263_);
lean_ctor_set(v___x_3260_, 0, v___x_3275_);
v___x_3284_ = v___x_3260_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v___x_3275_);
lean_ctor_set(v_reuseFailAlloc_3285_, 1, v_k_3263_);
lean_ctor_set(v_reuseFailAlloc_3285_, 2, v_v_3264_);
lean_ctor_set(v_reuseFailAlloc_3285_, 3, v___y_3277_);
lean_ctor_set(v_reuseFailAlloc_3285_, 4, v___x_3282_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
v___jp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3291_; 
v___x_3289_ = lean_nat_add(v___x_3274_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec(v___x_3274_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v_l_3265_);
lean_ctor_set(v___x_3100_, 0, v___x_3289_);
v___x_3291_ = v___x_3100_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3289_);
lean_ctor_set(v_reuseFailAlloc_3295_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3295_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3295_, 3, v_l_3097_);
lean_ctor_set(v_reuseFailAlloc_3295_, 4, v_l_3265_);
v___x_3291_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
lean_object* v___x_3292_; 
v___x_3292_ = lean_nat_add(v___x_3244_, v_size_3267_);
if (lean_obj_tag(v_r_3266_) == 0)
{
lean_object* v_size_3293_; 
v_size_3293_ = lean_ctor_get(v_r_3266_, 0);
lean_inc(v_size_3293_);
v___y_3277_ = v___x_3291_;
v___y_3278_ = v___x_3292_;
v___y_3279_ = v_size_3293_;
goto v___jp_3276_;
}
else
{
lean_object* v___x_3294_; 
v___x_3294_ = lean_unsigned_to_nat(0u);
v___y_3277_ = v___x_3291_;
v___y_3278_ = v___x_3292_;
v___y_3279_ = v___x_3294_;
goto v___jp_3276_;
}
}
}
}
}
else
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
lean_del_object(v___x_3100_);
v___x_3304_ = lean_nat_add(v___x_3244_, v_size_3245_);
v___x_3305_ = lean_nat_add(v___x_3304_, v_size_3246_);
lean_dec(v_size_3246_);
v___x_3306_ = lean_nat_add(v___x_3304_, v_size_3262_);
lean_dec(v___x_3304_);
lean_inc_ref(v_l_3097_);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 4, v_l_3249_);
lean_ctor_set(v___x_3260_, 3, v_l_3097_);
lean_ctor_set(v___x_3260_, 2, v_v_3096_);
lean_ctor_set(v___x_3260_, 1, v_k_3095_);
lean_ctor_set(v___x_3260_, 0, v___x_3306_);
v___x_3308_ = v___x_3260_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3306_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3321_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3321_, 3, v_l_3097_);
lean_ctor_set(v_reuseFailAlloc_3321_, 4, v_l_3249_);
v___x_3308_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
v_isSharedCheck_3315_ = !lean_is_exclusive(v_l_3097_);
if (v_isSharedCheck_3315_ == 0)
{
lean_object* v_unused_3316_; lean_object* v_unused_3317_; lean_object* v_unused_3318_; lean_object* v_unused_3319_; lean_object* v_unused_3320_; 
v_unused_3316_ = lean_ctor_get(v_l_3097_, 4);
lean_dec(v_unused_3316_);
v_unused_3317_ = lean_ctor_get(v_l_3097_, 3);
lean_dec(v_unused_3317_);
v_unused_3318_ = lean_ctor_get(v_l_3097_, 2);
lean_dec(v_unused_3318_);
v_unused_3319_ = lean_ctor_get(v_l_3097_, 1);
lean_dec(v_unused_3319_);
v_unused_3320_ = lean_ctor_get(v_l_3097_, 0);
lean_dec(v_unused_3320_);
v___x_3310_ = v_l_3097_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_dec(v_l_3097_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
lean_ctor_set(v___x_3310_, 4, v_r_3250_);
lean_ctor_set(v___x_3310_, 3, v___x_3308_);
lean_ctor_set(v___x_3310_, 2, v_v_3248_);
lean_ctor_set(v___x_3310_, 1, v_k_3247_);
lean_ctor_set(v___x_3310_, 0, v___x_3305_);
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3305_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_k_3247_);
lean_ctor_set(v_reuseFailAlloc_3314_, 2, v_v_3248_);
lean_ctor_set(v_reuseFailAlloc_3314_, 3, v___x_3308_);
lean_ctor_set(v_reuseFailAlloc_3314_, 4, v_r_3250_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3328_; 
v_l_3328_ = lean_ctor_get(v_impl_3243_, 3);
lean_inc(v_l_3328_);
if (lean_obj_tag(v_l_3328_) == 0)
{
lean_object* v_r_3329_; lean_object* v_k_3330_; lean_object* v_v_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3354_; 
v_r_3329_ = lean_ctor_get(v_impl_3243_, 4);
v_k_3330_ = lean_ctor_get(v_impl_3243_, 1);
v_v_3331_ = lean_ctor_get(v_impl_3243_, 2);
v_isSharedCheck_3354_ = !lean_is_exclusive(v_impl_3243_);
if (v_isSharedCheck_3354_ == 0)
{
lean_object* v_unused_3355_; lean_object* v_unused_3356_; 
v_unused_3355_ = lean_ctor_get(v_impl_3243_, 3);
lean_dec(v_unused_3355_);
v_unused_3356_ = lean_ctor_get(v_impl_3243_, 0);
lean_dec(v_unused_3356_);
v___x_3333_ = v_impl_3243_;
v_isShared_3334_ = v_isSharedCheck_3354_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_r_3329_);
lean_inc(v_v_3331_);
lean_inc(v_k_3330_);
lean_dec(v_impl_3243_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3354_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v_k_3335_; lean_object* v_v_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3350_; 
v_k_3335_ = lean_ctor_get(v_l_3328_, 1);
v_v_3336_ = lean_ctor_get(v_l_3328_, 2);
v_isSharedCheck_3350_ = !lean_is_exclusive(v_l_3328_);
if (v_isSharedCheck_3350_ == 0)
{
lean_object* v_unused_3351_; lean_object* v_unused_3352_; lean_object* v_unused_3353_; 
v_unused_3351_ = lean_ctor_get(v_l_3328_, 4);
lean_dec(v_unused_3351_);
v_unused_3352_ = lean_ctor_get(v_l_3328_, 3);
lean_dec(v_unused_3352_);
v_unused_3353_ = lean_ctor_get(v_l_3328_, 0);
lean_dec(v_unused_3353_);
v___x_3338_ = v_l_3328_;
v_isShared_3339_ = v_isSharedCheck_3350_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_v_3336_);
lean_inc(v_k_3335_);
lean_dec(v_l_3328_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3350_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3340_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3329_, 2);
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 4, v_r_3329_);
lean_ctor_set(v___x_3338_, 3, v_r_3329_);
lean_ctor_set(v___x_3338_, 2, v_v_3096_);
lean_ctor_set(v___x_3338_, 1, v_k_3095_);
lean_ctor_set(v___x_3338_, 0, v___x_3244_);
v___x_3342_ = v___x_3338_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3349_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3349_, 3, v_r_3329_);
lean_ctor_set(v_reuseFailAlloc_3349_, 4, v_r_3329_);
v___x_3342_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3344_; 
lean_inc(v_r_3329_);
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 3, v_r_3329_);
lean_ctor_set(v___x_3333_, 0, v___x_3244_);
v___x_3344_ = v___x_3333_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_k_3330_);
lean_ctor_set(v_reuseFailAlloc_3348_, 2, v_v_3331_);
lean_ctor_set(v_reuseFailAlloc_3348_, 3, v_r_3329_);
lean_ctor_set(v_reuseFailAlloc_3348_, 4, v_r_3329_);
v___x_3344_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
lean_object* v___x_3346_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v___x_3344_);
lean_ctor_set(v___x_3100_, 3, v___x_3342_);
lean_ctor_set(v___x_3100_, 2, v_v_3336_);
lean_ctor_set(v___x_3100_, 1, v_k_3335_);
lean_ctor_set(v___x_3100_, 0, v___x_3340_);
v___x_3346_ = v___x_3100_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3340_);
lean_ctor_set(v_reuseFailAlloc_3347_, 1, v_k_3335_);
lean_ctor_set(v_reuseFailAlloc_3347_, 2, v_v_3336_);
lean_ctor_set(v_reuseFailAlloc_3347_, 3, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3347_, 4, v___x_3344_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
}
}
else
{
lean_object* v_r_3357_; 
v_r_3357_ = lean_ctor_get(v_impl_3243_, 4);
lean_inc(v_r_3357_);
if (lean_obj_tag(v_r_3357_) == 0)
{
lean_object* v_k_3358_; lean_object* v_v_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3370_; 
v_k_3358_ = lean_ctor_get(v_impl_3243_, 1);
v_v_3359_ = lean_ctor_get(v_impl_3243_, 2);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_impl_3243_);
if (v_isSharedCheck_3370_ == 0)
{
lean_object* v_unused_3371_; lean_object* v_unused_3372_; lean_object* v_unused_3373_; 
v_unused_3371_ = lean_ctor_get(v_impl_3243_, 4);
lean_dec(v_unused_3371_);
v_unused_3372_ = lean_ctor_get(v_impl_3243_, 3);
lean_dec(v_unused_3372_);
v_unused_3373_ = lean_ctor_get(v_impl_3243_, 0);
lean_dec(v_unused_3373_);
v___x_3361_ = v_impl_3243_;
v_isShared_3362_ = v_isSharedCheck_3370_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_v_3359_);
lean_inc(v_k_3358_);
lean_dec(v_impl_3243_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3370_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3363_ = lean_unsigned_to_nat(3u);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 4, v_l_3328_);
lean_ctor_set(v___x_3361_, 2, v_v_3096_);
lean_ctor_set(v___x_3361_, 1, v_k_3095_);
lean_ctor_set(v___x_3361_, 0, v___x_3244_);
v___x_3365_ = v___x_3361_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3369_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3369_, 3, v_l_3328_);
lean_ctor_set(v_reuseFailAlloc_3369_, 4, v_l_3328_);
v___x_3365_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3367_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v_r_3357_);
lean_ctor_set(v___x_3100_, 3, v___x_3365_);
lean_ctor_set(v___x_3100_, 2, v_v_3359_);
lean_ctor_set(v___x_3100_, 1, v_k_3358_);
lean_ctor_set(v___x_3100_, 0, v___x_3363_);
v___x_3367_ = v___x_3100_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3368_, 1, v_k_3358_);
lean_ctor_set(v_reuseFailAlloc_3368_, 2, v_v_3359_);
lean_ctor_set(v_reuseFailAlloc_3368_, 3, v___x_3365_);
lean_ctor_set(v_reuseFailAlloc_3368_, 4, v_r_3357_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
else
{
lean_object* v___x_3374_; lean_object* v___x_3376_; 
v___x_3374_ = lean_unsigned_to_nat(2u);
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 4, v_impl_3243_);
lean_ctor_set(v___x_3100_, 3, v_r_3357_);
lean_ctor_set(v___x_3100_, 0, v___x_3374_);
v___x_3376_ = v___x_3100_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3374_);
lean_ctor_set(v_reuseFailAlloc_3377_, 1, v_k_3095_);
lean_ctor_set(v_reuseFailAlloc_3377_, 2, v_v_3096_);
lean_ctor_set(v_reuseFailAlloc_3377_, 3, v_r_3357_);
lean_ctor_set(v_reuseFailAlloc_3377_, 4, v_impl_3243_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
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
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = lean_unsigned_to_nat(1u);
v___x_3380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
lean_ctor_set(v___x_3380_, 1, v_k_3091_);
lean_ctor_set(v___x_3380_, 2, v_v_3092_);
lean_ctor_set(v___x_3380_, 3, v_t_3093_);
lean_ctor_set(v___x_3380_, 4, v_t_3093_);
return v___x_3380_;
}
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3381_ = lean_box(1);
v___x_3382_ = l_Lake_Package_depsFacetConfig;
v___x_3383_ = l_Lake_Package_depsFacet;
v___x_3384_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3383_, v___x_3382_, v___x_3381_);
return v___x_3384_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3385_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__0, &l_Lake_Package_initFacetConfigs___closed__0_once, _init_l_Lake_Package_initFacetConfigs___closed__0);
v___x_3386_ = l_Lake_Package_transDepsFacetConfig;
v___x_3387_ = l_Lake_Package_transDepsFacet;
v___x_3388_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3387_, v___x_3386_, v___x_3385_);
return v___x_3388_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3389_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__1, &l_Lake_Package_initFacetConfigs___closed__1_once, _init_l_Lake_Package_initFacetConfigs___closed__1);
v___x_3390_ = l_Lake_Package_extraDepFacetConfig;
v___x_3391_ = l_Lake_Package_extraDepFacet;
v___x_3392_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3391_, v___x_3390_, v___x_3389_);
return v___x_3392_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3393_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__2, &l_Lake_Package_initFacetConfigs___closed__2_once, _init_l_Lake_Package_initFacetConfigs___closed__2);
v___x_3394_ = l_Lake_Package_optBuildCacheFacetConfig;
v___x_3395_ = l_Lake_Package_optBuildCacheFacet;
v___x_3396_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3395_, v___x_3394_, v___x_3393_);
return v___x_3396_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3397_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__3, &l_Lake_Package_initFacetConfigs___closed__3_once, _init_l_Lake_Package_initFacetConfigs___closed__3);
v___x_3398_ = l_Lake_Package_buildCacheFacetConfig;
v___x_3399_ = l_Lake_Package_buildCacheFacet;
v___x_3400_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3399_, v___x_3398_, v___x_3397_);
return v___x_3400_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3401_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__4, &l_Lake_Package_initFacetConfigs___closed__4_once, _init_l_Lake_Package_initFacetConfigs___closed__4);
v___x_3402_ = l_Lake_Package_optBarrelFacetConfig;
v___x_3403_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3404_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3403_, v___x_3402_, v___x_3401_);
return v___x_3404_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3405_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__5, &l_Lake_Package_initFacetConfigs___closed__5_once, _init_l_Lake_Package_initFacetConfigs___closed__5);
v___x_3406_ = l_Lake_Package_barrelFacetConfig;
v___x_3407_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3408_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3407_, v___x_3406_, v___x_3405_);
return v___x_3408_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3409_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__6, &l_Lake_Package_initFacetConfigs___closed__6_once, _init_l_Lake_Package_initFacetConfigs___closed__6);
v___x_3410_ = l_Lake_Package_optGitHubReleaseFacetConfig;
v___x_3411_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3412_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3411_, v___x_3410_, v___x_3409_);
return v___x_3412_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3413_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__7, &l_Lake_Package_initFacetConfigs___closed__7_once, _init_l_Lake_Package_initFacetConfigs___closed__7);
v___x_3414_ = l_Lake_Package_gitHubReleaseFacetConfig;
v___x_3415_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3416_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3415_, v___x_3414_, v___x_3413_);
return v___x_3416_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs(void){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__8, &l_Lake_Package_initFacetConfigs___closed__8_once, _init_l_Lake_Package_initFacetConfigs___closed__8);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3418_, lean_object* v_k_3419_, lean_object* v_v_3420_, lean_object* v_t_3421_, lean_object* v_hl_3422_){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3419_, v_v_3420_, v_t_3421_);
return v___x_3423_;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs(void){
_start:
{
lean_object* v___x_3424_; 
v___x_3424_ = l_Lake_Package_initFacetConfigs;
return v___x_3424_;
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
