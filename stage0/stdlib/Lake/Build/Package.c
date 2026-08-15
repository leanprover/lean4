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
uint8_t l_Lake_instDecidableEqVerbosity(uint8_t, uint8_t);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_box(0);
v___x_130_ = lean_unsigned_to_nat(16u);
v___x_131_ = lean_mk_array(v___x_130_, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0);
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2));
v___x_138_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1);
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2(void){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3);
return v___x_140_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(lean_object* v_a_141_, lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
uint8_t v___x_143_; 
v___x_143_ = 0;
return v___x_143_;
}
else
{
lean_object* v_key_144_; lean_object* v_tail_145_; lean_object* v_wsIdx_146_; lean_object* v_wsIdx_147_; uint8_t v___x_148_; 
v_key_144_ = lean_ctor_get(v_x_142_, 0);
v_tail_145_ = lean_ctor_get(v_x_142_, 2);
v_wsIdx_146_ = lean_ctor_get(v_key_144_, 0);
v_wsIdx_147_ = lean_ctor_get(v_a_141_, 0);
v___x_148_ = lean_nat_dec_eq(v_wsIdx_146_, v_wsIdx_147_);
if (v___x_148_ == 0)
{
v_x_142_ = v_tail_145_;
goto _start;
}
else
{
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_a_150_, lean_object* v_x_151_){
_start:
{
uint8_t v_res_152_; lean_object* v_r_153_; 
v_res_152_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_150_, v_x_151_);
lean_dec(v_x_151_);
lean_dec_ref(v_a_150_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(lean_object* v_m_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_buckets_156_; lean_object* v_keyName_157_; lean_object* v___x_158_; uint64_t v___y_160_; 
v_buckets_156_ = lean_ctor_get(v_m_154_, 1);
v_keyName_157_ = lean_ctor_get(v_a_155_, 2);
v___x_158_ = lean_array_get_size(v_buckets_156_);
if (lean_obj_tag(v_keyName_157_) == 0)
{
uint64_t v___x_174_; 
v___x_174_ = 1723ULL;
v___y_160_ = v___x_174_;
goto v___jp_159_;
}
else
{
uint64_t v_hash_175_; 
v_hash_175_ = lean_ctor_get_uint64(v_keyName_157_, sizeof(void*)*2);
v___y_160_ = v_hash_175_;
goto v___jp_159_;
}
v___jp_159_:
{
uint64_t v___x_161_; uint64_t v___x_162_; uint64_t v_fold_163_; uint64_t v___x_164_; uint64_t v___x_165_; uint64_t v___x_166_; size_t v___x_167_; size_t v___x_168_; size_t v___x_169_; size_t v___x_170_; size_t v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_161_ = 32ULL;
v___x_162_ = lean_uint64_shift_right(v___y_160_, v___x_161_);
v_fold_163_ = lean_uint64_xor(v___y_160_, v___x_162_);
v___x_164_ = 16ULL;
v___x_165_ = lean_uint64_shift_right(v_fold_163_, v___x_164_);
v___x_166_ = lean_uint64_xor(v_fold_163_, v___x_165_);
v___x_167_ = lean_uint64_to_usize(v___x_166_);
v___x_168_ = lean_usize_of_nat(v___x_158_);
v___x_169_ = ((size_t)1ULL);
v___x_170_ = lean_usize_sub(v___x_168_, v___x_169_);
v___x_171_ = lean_usize_land(v___x_167_, v___x_170_);
v___x_172_ = lean_array_uget_borrowed(v_buckets_156_, v___x_171_);
v___x_173_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_155_, v___x_172_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(lean_object* v_m_176_, lean_object* v_a_177_){
_start:
{
uint8_t v_res_178_; lean_object* v_r_179_; 
v_res_178_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_176_, v_a_177_);
lean_dec_ref(v_a_177_);
lean_dec_ref(v_m_176_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
return v_x_180_;
}
else
{
lean_object* v_key_182_; lean_object* v_value_183_; lean_object* v_tail_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_211_; 
v_key_182_ = lean_ctor_get(v_x_181_, 0);
v_value_183_ = lean_ctor_get(v_x_181_, 1);
v_tail_184_ = lean_ctor_get(v_x_181_, 2);
v_isSharedCheck_211_ = !lean_is_exclusive(v_x_181_);
if (v_isSharedCheck_211_ == 0)
{
v___x_186_ = v_x_181_;
v_isShared_187_ = v_isSharedCheck_211_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_tail_184_);
lean_inc(v_value_183_);
lean_inc(v_key_182_);
lean_dec(v_x_181_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_211_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v_keyName_188_; lean_object* v___x_189_; uint64_t v___y_191_; 
v_keyName_188_ = lean_ctor_get(v_key_182_, 2);
v___x_189_ = lean_array_get_size(v_x_180_);
if (lean_obj_tag(v_keyName_188_) == 0)
{
uint64_t v___x_209_; 
v___x_209_ = 1723ULL;
v___y_191_ = v___x_209_;
goto v___jp_190_;
}
else
{
uint64_t v_hash_210_; 
v_hash_210_ = lean_ctor_get_uint64(v_keyName_188_, sizeof(void*)*2);
v___y_191_ = v_hash_210_;
goto v___jp_190_;
}
v___jp_190_:
{
uint64_t v___x_192_; uint64_t v___x_193_; uint64_t v_fold_194_; uint64_t v___x_195_; uint64_t v___x_196_; uint64_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; size_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_192_ = 32ULL;
v___x_193_ = lean_uint64_shift_right(v___y_191_, v___x_192_);
v_fold_194_ = lean_uint64_xor(v___y_191_, v___x_193_);
v___x_195_ = 16ULL;
v___x_196_ = lean_uint64_shift_right(v_fold_194_, v___x_195_);
v___x_197_ = lean_uint64_xor(v_fold_194_, v___x_196_);
v___x_198_ = lean_uint64_to_usize(v___x_197_);
v___x_199_ = lean_usize_of_nat(v___x_189_);
v___x_200_ = ((size_t)1ULL);
v___x_201_ = lean_usize_sub(v___x_199_, v___x_200_);
v___x_202_ = lean_usize_land(v___x_198_, v___x_201_);
v___x_203_ = lean_array_uget_borrowed(v_x_180_, v___x_202_);
lean_inc(v___x_203_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 2, v___x_203_);
v___x_205_ = v___x_186_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_key_182_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_value_183_);
lean_ctor_set(v_reuseFailAlloc_208_, 2, v___x_203_);
v___x_205_ = v_reuseFailAlloc_208_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; 
v___x_206_ = lean_array_uset(v_x_180_, v___x_202_, v___x_205_);
v_x_180_ = v___x_206_;
v_x_181_ = v_tail_184_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_i_212_, lean_object* v_source_213_, lean_object* v_target_214_){
_start:
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_array_get_size(v_source_213_);
v___x_216_ = lean_nat_dec_lt(v_i_212_, v___x_215_);
if (v___x_216_ == 0)
{
lean_dec_ref(v_source_213_);
lean_dec(v_i_212_);
return v_target_214_;
}
else
{
lean_object* v_es_217_; lean_object* v___x_218_; lean_object* v_source_219_; lean_object* v_target_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_es_217_ = lean_array_fget(v_source_213_, v_i_212_);
v___x_218_ = lean_box(0);
v_source_219_ = lean_array_fset(v_source_213_, v_i_212_, v___x_218_);
v_target_220_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(v_target_214_, v_es_217_);
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_add(v_i_212_, v___x_221_);
lean_dec(v_i_212_);
v_i_212_ = v___x_222_;
v_source_213_ = v_source_219_;
v_target_214_ = v_target_220_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(lean_object* v_data_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v_nbuckets_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_225_ = lean_array_get_size(v_data_224_);
v___x_226_ = lean_unsigned_to_nat(2u);
v_nbuckets_227_ = lean_nat_mul(v___x_225_, v___x_226_);
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_box(0);
v___x_230_ = lean_mk_array(v_nbuckets_227_, v___x_229_);
v___x_231_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v___x_228_, v_data_224_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(lean_object* v_m_232_, lean_object* v_a_233_, lean_object* v_b_234_){
_start:
{
lean_object* v_size_235_; lean_object* v_buckets_236_; lean_object* v_keyName_237_; lean_object* v___x_238_; uint64_t v___y_240_; 
v_size_235_ = lean_ctor_get(v_m_232_, 0);
v_buckets_236_ = lean_ctor_get(v_m_232_, 1);
v_keyName_237_ = lean_ctor_get(v_a_233_, 2);
v___x_238_ = lean_array_get_size(v_buckets_236_);
if (lean_obj_tag(v_keyName_237_) == 0)
{
uint64_t v___x_277_; 
v___x_277_ = 1723ULL;
v___y_240_ = v___x_277_;
goto v___jp_239_;
}
else
{
uint64_t v_hash_278_; 
v_hash_278_ = lean_ctor_get_uint64(v_keyName_237_, sizeof(void*)*2);
v___y_240_ = v_hash_278_;
goto v___jp_239_;
}
v___jp_239_:
{
uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v_fold_243_; uint64_t v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; lean_object* v_bkt_252_; uint8_t v___x_253_; 
v___x_241_ = 32ULL;
v___x_242_ = lean_uint64_shift_right(v___y_240_, v___x_241_);
v_fold_243_ = lean_uint64_xor(v___y_240_, v___x_242_);
v___x_244_ = 16ULL;
v___x_245_ = lean_uint64_shift_right(v_fold_243_, v___x_244_);
v___x_246_ = lean_uint64_xor(v_fold_243_, v___x_245_);
v___x_247_ = lean_uint64_to_usize(v___x_246_);
v___x_248_ = lean_usize_of_nat(v___x_238_);
v___x_249_ = ((size_t)1ULL);
v___x_250_ = lean_usize_sub(v___x_248_, v___x_249_);
v___x_251_ = lean_usize_land(v___x_247_, v___x_250_);
v_bkt_252_ = lean_array_uget_borrowed(v_buckets_236_, v___x_251_);
v___x_253_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_233_, v_bkt_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_274_; 
lean_inc_ref(v_buckets_236_);
lean_inc(v_size_235_);
v_isSharedCheck_274_ = !lean_is_exclusive(v_m_232_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; lean_object* v_unused_276_; 
v_unused_275_ = lean_ctor_get(v_m_232_, 1);
lean_dec(v_unused_275_);
v_unused_276_ = lean_ctor_get(v_m_232_, 0);
lean_dec(v_unused_276_);
v___x_255_ = v_m_232_;
v_isShared_256_ = v_isSharedCheck_274_;
goto v_resetjp_254_;
}
else
{
lean_dec(v_m_232_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_274_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v_size_x27_258_; lean_object* v___x_259_; lean_object* v_buckets_x27_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_257_ = lean_unsigned_to_nat(1u);
v_size_x27_258_ = lean_nat_add(v_size_235_, v___x_257_);
lean_dec(v_size_235_);
lean_inc(v_bkt_252_);
v___x_259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_259_, 0, v_a_233_);
lean_ctor_set(v___x_259_, 1, v_b_234_);
lean_ctor_set(v___x_259_, 2, v_bkt_252_);
v_buckets_x27_260_ = lean_array_uset(v_buckets_236_, v___x_251_, v___x_259_);
v___x_261_ = lean_unsigned_to_nat(4u);
v___x_262_ = lean_nat_mul(v_size_x27_258_, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(3u);
v___x_264_ = lean_nat_div(v___x_262_, v___x_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_array_get_size(v_buckets_x27_260_);
v___x_266_ = lean_nat_dec_le(v___x_264_, v___x_265_);
lean_dec(v___x_264_);
if (v___x_266_ == 0)
{
lean_object* v_val_267_; lean_object* v___x_269_; 
v_val_267_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_buckets_x27_260_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v_val_267_);
lean_ctor_set(v___x_255_, 0, v_size_x27_258_);
v___x_269_ = v___x_255_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_size_x27_258_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_val_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
else
{
lean_object* v___x_272_; 
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v_buckets_x27_260_);
lean_ctor_set(v___x_255_, 0, v_size_x27_258_);
v___x_272_ = v___x_255_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_size_x27_258_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_buckets_x27_260_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
else
{
lean_dec(v_b_234_);
lean_dec_ref(v_a_233_);
return v_m_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(lean_object* v_self_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_toHashSet_281_; lean_object* v_toArray_282_; uint8_t v___x_283_; 
v_toHashSet_281_ = lean_ctor_get(v_self_279_, 0);
v_toArray_282_ = lean_ctor_get(v_self_279_, 1);
v___x_283_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_toHashSet_281_, v_a_280_);
if (v___x_283_ == 0)
{
lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_293_; 
lean_inc_ref(v_toArray_282_);
lean_inc_ref(v_toHashSet_281_);
v_isSharedCheck_293_ = !lean_is_exclusive(v_self_279_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; lean_object* v_unused_295_; 
v_unused_294_ = lean_ctor_get(v_self_279_, 1);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_self_279_, 0);
lean_dec(v_unused_295_);
v___x_285_ = v_self_279_;
v_isShared_286_ = v_isSharedCheck_293_;
goto v_resetjp_284_;
}
else
{
lean_dec(v_self_279_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_293_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_287_ = lean_box(0);
lean_inc_ref(v_a_280_);
v___x_288_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_toHashSet_281_, v_a_280_, v___x_287_);
v___x_289_ = lean_array_push(v_toArray_282_, v_a_280_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v___x_289_);
lean_ctor_set(v___x_285_, 0, v___x_288_);
v___x_291_ = v___x_285_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
lean_dec_ref(v_a_280_);
return v_self_279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(lean_object* v_as_296_, size_t v_i_297_, size_t v_stop_298_, lean_object* v_b_299_){
_start:
{
uint8_t v___x_300_; 
v___x_300_ = lean_usize_dec_eq(v_i_297_, v_stop_298_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; size_t v___x_303_; size_t v___x_304_; 
v___x_301_ = lean_array_uget_borrowed(v_as_296_, v_i_297_);
lean_inc(v___x_301_);
v___x_302_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v_b_299_, v___x_301_);
v___x_303_ = ((size_t)1ULL);
v___x_304_ = lean_usize_add(v_i_297_, v___x_303_);
v_i_297_ = v___x_304_;
v_b_299_ = v___x_302_;
goto _start;
}
else
{
return v_b_299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1___boxed(lean_object* v_as_306_, lean_object* v_i_307_, lean_object* v_stop_308_, lean_object* v_b_309_){
_start:
{
size_t v_i_boxed_310_; size_t v_stop_boxed_311_; lean_object* v_res_312_; 
v_i_boxed_310_ = lean_unbox_usize(v_i_307_);
lean_dec(v_i_307_);
v_stop_boxed_311_ = lean_unbox_usize(v_stop_308_);
lean_dec(v_stop_308_);
v_res_312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_as_306_, v_i_boxed_310_, v_stop_boxed_311_, v_b_309_);
lean_dec_ref(v_as_306_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(lean_object* v_as_313_, size_t v_i_314_, size_t v_stop_315_, lean_object* v_b_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
uint8_t v___x_324_; 
v___x_324_ = lean_usize_dec_eq(v_i_314_, v_stop_315_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v_keyName_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_325_ = lean_array_uget_borrowed(v_as_313_, v_i_314_);
v_keyName_326_ = lean_ctor_get(v___x_325_, 2);
v___x_327_ = l_Lake_Package_transDepsFacet;
lean_inc(v_keyName_326_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v_keyName_326_);
v___x_329_ = l_Lake_Package_keyword;
lean_inc(v___x_325_);
v___x_330_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
lean_ctor_set(v___x_330_, 2, v___x_325_);
lean_ctor_set(v___x_330_, 3, v___x_327_);
lean_inc_ref(v___y_317_);
lean_inc_ref(v___y_321_);
lean_inc(v___y_320_);
lean_inc(v___y_319_);
lean_inc(v___y_318_);
v___x_331_ = lean_apply_7(v___y_317_, v___x_330_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, lean_box(0));
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v_a_333_; lean_object* v___x_334_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
v_a_333_ = lean_ctor_get(v___x_331_, 1);
lean_inc(v_a_333_);
lean_dec_ref_known(v___x_331_, 2);
v___x_334_ = l_Lake_Job_await___redArg(v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v_a_336_; lean_object* v___y_338_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
v_a_336_ = lean_ctor_get(v___x_334_, 1);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_334_, 2);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_array_get_size(v_a_335_);
v___x_345_ = lean_nat_dec_lt(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
lean_dec(v_a_335_);
v___y_338_ = v_b_316_;
goto v___jp_337_;
}
else
{
uint8_t v___x_346_; 
v___x_346_ = lean_nat_dec_le(v___x_344_, v___x_344_);
if (v___x_346_ == 0)
{
if (v___x_345_ == 0)
{
lean_dec(v_a_335_);
v___y_338_ = v_b_316_;
goto v___jp_337_;
}
else
{
size_t v___x_347_; size_t v___x_348_; lean_object* v___x_349_; 
v___x_347_ = ((size_t)0ULL);
v___x_348_ = lean_usize_of_nat(v___x_344_);
v___x_349_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_335_, v___x_347_, v___x_348_, v_b_316_);
lean_dec(v_a_335_);
v___y_338_ = v___x_349_;
goto v___jp_337_;
}
}
else
{
size_t v___x_350_; size_t v___x_351_; lean_object* v___x_352_; 
v___x_350_ = ((size_t)0ULL);
v___x_351_ = lean_usize_of_nat(v___x_344_);
v___x_352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_335_, v___x_350_, v___x_351_, v_b_316_);
lean_dec(v_a_335_);
v___y_338_ = v___x_352_;
goto v___jp_337_;
}
}
v___jp_337_:
{
lean_object* v___x_339_; size_t v___x_340_; size_t v___x_341_; 
lean_inc(v___x_325_);
v___x_339_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v___y_338_, v___x_325_);
v___x_340_ = ((size_t)1ULL);
v___x_341_ = lean_usize_add(v_i_314_, v___x_340_);
v_i_314_ = v___x_341_;
v_b_316_ = v___x_339_;
v___y_322_ = v_a_336_;
goto _start;
}
}
else
{
lean_object* v_a_353_; lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec_ref(v___y_317_);
lean_dec_ref(v_b_316_);
v_a_353_ = lean_ctor_get(v___x_334_, 0);
v_a_354_ = lean_ctor_get(v___x_334_, 1);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_334_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_inc(v_a_353_);
lean_dec(v___x_334_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_353_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
else
{
lean_object* v_a_362_; lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec_ref(v___y_317_);
lean_dec_ref(v_b_316_);
v_a_362_ = lean_ctor_get(v___x_331_, 0);
v_a_363_ = lean_ctor_get(v___x_331_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_331_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_inc(v_a_362_);
lean_dec(v___x_331_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_362_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
lean_object* v___x_371_; 
lean_dec_ref(v___y_317_);
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v_b_316_);
lean_ctor_set(v___x_371_, 1, v___y_322_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3___boxed(lean_object* v_as_372_, lean_object* v_i_373_, lean_object* v_stop_374_, lean_object* v_b_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
size_t v_i_boxed_383_; size_t v_stop_boxed_384_; lean_object* v_res_385_; 
v_i_boxed_383_ = lean_unbox_usize(v_i_373_);
lean_dec(v_i_373_);
v_stop_boxed_384_ = lean_unbox_usize(v_stop_374_);
lean_dec(v_stop_374_);
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_as_372_, v_i_boxed_383_, v_stop_boxed_384_, v_b_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v_as_372_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(lean_object* v___x_386_, lean_object* v___x_387_, lean_object* v___x_388_, lean_object* v___x_389_, lean_object* v_depPkgs_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_a_399_; lean_object* v_a_400_; lean_object* v___y_420_; uint8_t v___x_432_; 
v___x_432_ = lean_nat_dec_lt(v___x_386_, v___x_388_);
if (v___x_432_ == 0)
{
lean_dec_ref(v___y_391_);
v_a_399_ = v___x_389_;
v_a_400_ = v___y_396_;
goto v___jp_398_;
}
else
{
uint8_t v___x_433_; 
v___x_433_ = lean_nat_dec_le(v___x_388_, v___x_388_);
if (v___x_433_ == 0)
{
if (v___x_432_ == 0)
{
lean_dec_ref(v___y_391_);
v_a_399_ = v___x_389_;
v_a_400_ = v___y_396_;
goto v___jp_398_;
}
else
{
size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
v___x_434_ = ((size_t)0ULL);
v___x_435_ = lean_usize_of_nat(v___x_388_);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_390_, v___x_434_, v___x_435_, v___x_389_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
v___y_420_ = v___x_436_;
goto v___jp_419_;
}
}
else
{
size_t v___x_437_; size_t v___x_438_; lean_object* v___x_439_; 
v___x_437_ = ((size_t)0ULL);
v___x_438_ = lean_usize_of_nat(v___x_388_);
v___x_439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_390_, v___x_437_, v___x_438_, v___x_389_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
v___y_420_ = v___x_439_;
goto v___jp_419_;
}
}
v___jp_398_:
{
lean_object* v_toArray_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_417_; 
v_toArray_401_ = lean_ctor_get(v_a_399_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v_a_399_);
if (v_isSharedCheck_417_ == 0)
{
lean_object* v_unused_418_; 
v_unused_418_ = lean_ctor_get(v_a_399_, 0);
lean_dec(v_unused_418_);
v___x_403_ = v_a_399_;
v_isShared_404_ = v_isSharedCheck_417_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_toArray_401_);
lean_dec(v_a_399_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_417_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_405_ = lean_mk_empty_array_with_capacity(v___x_386_);
v___x_406_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_407_ = 0;
v___x_408_ = 0;
v___x_409_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_410_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_410_, 0, v___x_405_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
lean_ctor_set(v___x_410_, 2, v___x_386_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*3, v___x_407_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*3 + 1, v___x_408_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 1, v___x_410_);
lean_ctor_set(v___x_403_, 0, v_toArray_401_);
v___x_412_ = v___x_403_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_toArray_401_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v___x_410_);
v___x_412_ = v_reuseFailAlloc_416_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = lean_task_pure(v___x_412_);
v___x_414_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_387_);
lean_ctor_set(v___x_414_, 2, v___x_406_);
lean_ctor_set_uint8(v___x_414_, sizeof(void*)*3, v___x_408_);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v_a_400_);
return v___x_415_;
}
}
}
v___jp_419_:
{
if (lean_obj_tag(v___y_420_) == 0)
{
lean_object* v_a_421_; lean_object* v_a_422_; 
v_a_421_ = lean_ctor_get(v___y_420_, 0);
lean_inc(v_a_421_);
v_a_422_ = lean_ctor_get(v___y_420_, 1);
lean_inc(v_a_422_);
lean_dec_ref_known(v___y_420_, 2);
v_a_399_ = v_a_421_;
v_a_400_ = v_a_422_;
goto v___jp_398_;
}
else
{
lean_object* v_a_423_; lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec(v___x_387_);
lean_dec(v___x_386_);
v_a_423_ = lean_ctor_get(v___y_420_, 0);
v_a_424_ = lean_ctor_get(v___y_420_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v___y_420_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___y_420_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_inc(v_a_423_);
lean_dec(v___y_420_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed(lean_object* v___x_440_, lean_object* v___x_441_, lean_object* v___x_442_, lean_object* v___x_443_, lean_object* v_depPkgs_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(v___x_440_, v___x_441_, v___x_442_, v___x_443_, v_depPkgs_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v_depPkgs_444_);
lean_dec(v___x_442_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(lean_object* v_self_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_depPkgs_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___f_466_; lean_object* v___x_467_; 
v_depPkgs_461_ = lean_ctor_get(v_self_453_, 14);
lean_inc_ref(v_depPkgs_461_);
lean_dec_ref(v_self_453_);
v___x_462_ = lean_box(0);
v___x_463_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2;
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_array_get_size(v_depPkgs_461_);
v___f_466_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed), 12, 5);
lean_closure_set(v___f_466_, 0, v___x_464_);
lean_closure_set(v___f_466_, 1, v___x_462_);
lean_closure_set(v___f_466_, 2, v___x_465_);
lean_closure_set(v___f_466_, 3, v___x_463_);
lean_closure_set(v___f_466_, 4, v_depPkgs_461_);
v___x_467_ = l_Lake_ensureJob___redArg(v___x_462_, v___f_466_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___boxed(lean_object* v_self_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(v_self_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec(v_a_471_);
lean_dec(v_a_470_);
return v_res_476_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object* v_00_u03b2_477_, lean_object* v_m_478_, lean_object* v_a_479_){
_start:
{
uint8_t v___x_480_; 
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_478_, v_a_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_481_, lean_object* v_m_482_, lean_object* v_a_483_){
_start:
{
uint8_t v_res_484_; lean_object* v_r_485_; 
v_res_484_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(v_00_u03b2_481_, v_m_482_, v_a_483_);
lean_dec_ref(v_a_483_);
lean_dec_ref(v_m_482_);
v_r_485_ = lean_box(v_res_484_);
return v_r_485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1(lean_object* v_00_u03b2_486_, lean_object* v_m_487_, lean_object* v_a_488_, lean_object* v_b_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_m_487_, v_a_488_, v_b_489_);
return v___x_490_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_491_, lean_object* v_a_492_, lean_object* v_x_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_492_, v_x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_495_, lean_object* v_a_496_, lean_object* v_x_497_){
_start:
{
uint8_t v_res_498_; lean_object* v_r_499_; 
v_res_498_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(v_00_u03b2_495_, v_a_496_, v_x_497_);
lean_dec(v_x_497_);
lean_dec_ref(v_a_496_);
v_r_499_ = lean_box(v_res_498_);
return v_r_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_500_, lean_object* v_data_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_data_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_503_, lean_object* v_i_504_, lean_object* v_source_505_, lean_object* v_target_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v_i_504_, v_source_505_, v_target_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_508_, lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(v_x_509_, v_x_510_);
return v___x_511_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_513_; lean_object* v___f_514_; uint8_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_513_ = 1;
v___f_514_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__0));
v___x_515_ = 0;
v___x_516_ = lean_box(0);
v___x_517_ = ((lean_object*)(l_Lake_Package_transDepsFacetConfig___closed__0));
v___x_518_ = l_Lake_Package_keyword;
v___x_519_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v___x_517_);
lean_ctor_set(v___x_519_, 2, v___x_516_);
lean_ctor_set(v___x_519_, 3, v___f_514_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*4, v___x_515_);
lean_ctor_set_uint8(v___x_519_, sizeof(void*)*4 + 1, v___x_513_);
return v___x_519_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig(void){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lean_obj_once(&l_Lake_Package_transDepsFacetConfig___closed__1, &l_Lake_Package_transDepsFacetConfig___closed__1_once, _init_l_Lake_Package_transDepsFacetConfig___closed__1);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object* v_self_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_config_529_; uint8_t v_preferReleaseBuild_530_; 
v_config_529_ = lean_ctor_get(v_self_521_, 6);
v_preferReleaseBuild_530_ = lean_ctor_get_uint8(v_config_529_, sizeof(void*)*27 + 2);
if (v_preferReleaseBuild_530_ == 0)
{
lean_object* v_keyName_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_keyName_531_ = lean_ctor_get(v_self_521_, 2);
v___x_532_ = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(v_keyName_531_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v_keyName_531_);
v___x_534_ = l_Lake_Package_keyword;
v___x_535_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
lean_ctor_set(v___x_535_, 2, v_self_521_);
lean_ctor_set(v___x_535_, 3, v___x_532_);
lean_inc_ref(v_a_526_);
lean_inc(v_a_525_);
lean_inc(v_a_524_);
lean_inc(v_a_523_);
v___x_536_ = lean_apply_7(v_a_522_, v___x_535_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, lean_box(0));
return v___x_536_;
}
else
{
lean_object* v_keyName_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_keyName_537_ = lean_ctor_get(v_self_521_, 2);
v___x_538_ = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(v_keyName_537_);
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v_keyName_537_);
v___x_540_ = l_Lake_Package_keyword;
v___x_541_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
lean_ctor_set(v___x_541_, 2, v_self_521_);
lean_ctor_set(v___x_541_, 3, v___x_538_);
lean_inc_ref(v_a_526_);
lean_inc(v_a_525_);
lean_inc(v_a_524_);
lean_inc(v_a_523_);
v___x_542_ = lean_apply_7(v_a_522_, v___x_541_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, lean_box(0));
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___boxed(lean_object* v_self_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(v_self_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec(v_a_546_);
lean_dec(v_a_545_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t v_fmt_554_, uint8_t v_a_555_){
_start:
{
if (v_fmt_554_ == 0)
{
if (v_a_555_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0));
return v___x_556_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1));
return v___x_557_;
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_558_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_558_, 0, v_a_555_);
v___x_559_ = l_Lean_Json_compress(v___x_558_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object* v_fmt_560_, lean_object* v_a_561_){
_start:
{
uint8_t v_fmt_boxed_562_; uint8_t v_a_boxed_563_; lean_object* v_res_564_; 
v_fmt_boxed_562_ = lean_unbox(v_fmt_560_);
v_a_boxed_563_ = lean_unbox(v_a_561_);
v_res_564_ = l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(v_fmt_boxed_562_, v_a_boxed_563_);
return v_res_564_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_567_; uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___f_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___f_567_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_568_ = 1;
v___x_569_ = l_Lake_instDataKindBool;
v___f_570_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__0));
v___x_571_ = l_Lake_Package_keyword;
v___x_572_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v___f_570_);
lean_ctor_set(v___x_572_, 2, v___x_569_);
lean_ctor_set(v___x_572_, 3, v___f_567_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*4, v___x_568_);
lean_ctor_set_uint8(v___x_572_, sizeof(void*)*4 + 1, v___x_568_);
return v___x_572_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig(void){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = lean_obj_once(&l_Lake_Package_optBuildCacheFacetConfig___closed__2, &l_Lake_Package_optBuildCacheFacetConfig___closed__2_once, _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(lean_object* v_self_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___y_585_; uint8_t v___y_586_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_609_; lean_object* v___y_610_; uint8_t v___y_611_; lean_object* v___y_612_; uint8_t v___y_613_; lean_object* v_toContext_617_; lean_object* v_lakeEnv_618_; uint8_t v_noCache_619_; lean_object* v_toolchain_620_; uint8_t v_a_622_; lean_object* v_a_623_; 
v_toContext_617_ = lean_ctor_get(v_a_581_, 1);
v_lakeEnv_618_ = lean_ctor_get(v_toContext_617_, 0);
v_noCache_619_ = lean_ctor_get_uint8(v_lakeEnv_618_, sizeof(void*)*20);
v_toolchain_620_ = lean_ctor_get(v_lakeEnv_618_, 19);
if (v_noCache_619_ == 0)
{
uint8_t v___x_638_; 
v___x_638_ = 1;
v_a_622_ = v___x_638_;
v_a_623_ = v_a_582_;
goto v___jp_621_;
}
else
{
uint8_t v___x_639_; 
v___x_639_ = 0;
v_a_622_ = v___x_639_;
v_a_623_ = v_a_582_;
goto v___jp_621_;
}
v___jp_584_:
{
uint8_t v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_587_ = 1;
v___x_588_ = lean_box(0);
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_591_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_592_ = 0;
v___x_593_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_594_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_594_, 0, v___x_590_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
lean_ctor_set(v___x_594_, 2, v___x_589_);
lean_ctor_set_uint8(v___x_594_, sizeof(void*)*3, v___x_592_);
lean_ctor_set_uint8(v___x_594_, sizeof(void*)*3 + 1, v___y_586_);
v___x_595_ = lean_box(v___x_587_);
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v___x_594_);
v___x_597_ = lean_task_pure(v___x_596_);
v___x_598_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___x_588_);
lean_ctor_set(v___x_598_, 2, v___x_591_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*3, v___y_586_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
lean_ctor_set(v___x_599_, 1, v___y_585_);
return v___x_599_;
}
v___jp_600_:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_603_ = l_Lake_Package_optBuildCacheFacet;
v___x_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_604_, 0, v___y_602_);
v___x_605_ = l_Lake_Package_keyword;
v___x_606_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
lean_ctor_set(v___x_606_, 2, v_self_576_);
lean_ctor_set(v___x_606_, 3, v___x_603_);
lean_inc_ref(v_a_581_);
lean_inc(v_a_580_);
lean_inc(v_a_579_);
lean_inc(v_a_578_);
v___x_607_ = lean_apply_7(v_a_577_, v___x_606_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v___y_601_, lean_box(0));
return v___x_607_;
}
v___jp_608_:
{
if (v___y_613_ == 0)
{
lean_dec(v___y_612_);
lean_dec_ref(v_a_577_);
lean_dec_ref(v_self_576_);
v___y_585_ = v___y_610_;
v___y_586_ = v___y_613_;
goto v___jp_584_;
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_614_ = lean_string_utf8_byte_size(v___y_609_);
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_nat_dec_eq(v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
v___y_601_ = v___y_610_;
v___y_602_ = v___y_612_;
goto v___jp_600_;
}
else
{
lean_dec(v___y_612_);
lean_dec_ref(v_a_577_);
lean_dec_ref(v_self_576_);
v___y_585_ = v___y_610_;
v___y_586_ = v___y_611_;
goto v___jp_584_;
}
}
}
v___jp_621_:
{
lean_object* v_config_624_; lean_object* v_keyName_625_; lean_object* v_dir_626_; lean_object* v_scope_627_; lean_object* v_buildDir_628_; uint8_t v_preferReleaseBuild_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_config_624_ = lean_ctor_get(v_self_576_, 6);
v_keyName_625_ = lean_ctor_get(v_self_576_, 2);
v_dir_626_ = lean_ctor_get(v_self_576_, 4);
v_scope_627_ = lean_ctor_get(v_self_576_, 10);
v_buildDir_628_ = lean_ctor_get(v_config_624_, 5);
v_preferReleaseBuild_629_ = lean_ctor_get_uint8(v_config_624_, sizeof(void*)*27 + 2);
lean_inc_ref(v_buildDir_628_);
v___x_630_ = l_System_FilePath_normalize(v_buildDir_628_);
lean_inc_ref(v_dir_626_);
v___x_631_ = l_Lake_joinRelative(v_dir_626_, v___x_630_);
v___x_632_ = l_System_FilePath_pathExists(v___x_631_);
lean_dec_ref(v___x_631_);
if (v_a_622_ == 0)
{
lean_dec_ref(v_a_577_);
lean_dec_ref(v_self_576_);
v___y_585_ = v_a_623_;
v___y_586_ = v_a_622_;
goto v___jp_584_;
}
else
{
if (v___x_632_ == 0)
{
if (v_preferReleaseBuild_629_ == 0)
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0));
v___x_634_ = lean_string_dec_eq(v_scope_627_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1));
v___x_636_ = lean_string_dec_eq(v_scope_627_, v___x_635_);
lean_inc(v_keyName_625_);
v___y_609_ = v_toolchain_620_;
v___y_610_ = v_a_623_;
v___y_611_ = v_preferReleaseBuild_629_;
v___y_612_ = v_keyName_625_;
v___y_613_ = v___x_636_;
goto v___jp_608_;
}
else
{
lean_inc(v_keyName_625_);
v___y_609_ = v_toolchain_620_;
v___y_610_ = v_a_623_;
v___y_611_ = v_preferReleaseBuild_629_;
v___y_612_ = v_keyName_625_;
v___y_613_ = v___x_634_;
goto v___jp_608_;
}
}
else
{
lean_inc(v_keyName_625_);
v___y_601_ = v_a_623_;
v___y_602_ = v_keyName_625_;
goto v___jp_600_;
}
}
else
{
uint8_t v___x_637_; 
lean_dec_ref(v_a_577_);
lean_dec_ref(v_self_576_);
v___x_637_ = 0;
v___y_585_ = v_a_623_;
v___y_586_ = v___x_637_;
goto v___jp_584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___boxed(lean_object* v_self_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec(v_a_643_);
lean_dec(v_a_642_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object* v_self_653_, lean_object* v_facet_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_toBuildConfig_658_; uint8_t v_verbosity_659_; uint8_t v___x_660_; uint8_t v___x_661_; 
v_toBuildConfig_658_ = lean_ctor_get(v_a_655_, 0);
v_verbosity_659_ = lean_ctor_get_uint8(v_toBuildConfig_658_, sizeof(void*)*4 + 3);
v___x_660_ = 2;
v___x_661_ = l_Lake_instDecidableEqVerbosity(v_verbosity_659_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; 
lean_dec(v_facet_654_);
lean_dec_ref(v_self_653_);
v___x_662_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v_a_656_);
return v___x_663_;
}
else
{
lean_object* v_baseName_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_baseName_664_ = lean_ctor_get(v_self_653_, 1);
lean_inc(v_baseName_664_);
lean_dec_ref(v_self_653_);
v___x_665_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_666_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_664_, v___x_661_);
v___x_667_ = lean_string_append(v___x_665_, v___x_666_);
lean_dec_ref(v___x_666_);
v___x_668_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_669_ = lean_string_append(v___x_667_, v___x_668_);
v___x_670_ = l_Lake_Name_eraseHead(v_facet_654_);
v___x_671_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_670_, v___x_661_);
v___x_672_ = lean_string_append(v___x_669_, v___x_671_);
lean_dec_ref(v___x_671_);
v___x_673_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_674_ = lean_string_append(v___x_672_, v___x_673_);
v___x_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v_a_656_);
return v___x_675_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* v_self_676_, lean_object* v_facet_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(v_self_676_, v_facet_677_, v_a_678_, v_a_679_);
lean_dec_ref(v_a_678_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* v_self_682_, lean_object* v_facet_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_toBuildConfig_691_; uint8_t v_verbosity_692_; uint8_t v___x_693_; uint8_t v___x_694_; 
v_toBuildConfig_691_ = lean_ctor_get(v_a_688_, 0);
v_verbosity_692_ = lean_ctor_get_uint8(v_toBuildConfig_691_, sizeof(void*)*4 + 3);
v___x_693_ = 2;
v___x_694_ = l_Lake_instDecidableEqVerbosity(v_verbosity_692_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec(v_facet_683_);
lean_dec_ref(v_self_682_);
v___x_695_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v_a_689_);
return v___x_696_;
}
else
{
lean_object* v_baseName_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_baseName_697_ = lean_ctor_get(v_self_682_, 1);
lean_inc(v_baseName_697_);
lean_dec_ref(v_self_682_);
v___x_698_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_699_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_697_, v___x_694_);
v___x_700_ = lean_string_append(v___x_698_, v___x_699_);
lean_dec_ref(v___x_699_);
v___x_701_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_702_ = lean_string_append(v___x_700_, v___x_701_);
v___x_703_ = l_Lake_Name_eraseHead(v_facet_683_);
v___x_704_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_703_, v___x_694_);
v___x_705_ = lean_string_append(v___x_702_, v___x_704_);
lean_dec_ref(v___x_704_);
v___x_706_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_707_ = lean_string_append(v___x_705_, v___x_706_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v_a_689_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* v_self_709_, lean_object* v_facet_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(v_self_709_, v_facet_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
return v_res_718_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_722_ = l_Lake_Name_eraseHead(v___x_721_);
return v___x_722_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_724_ = l_Lake_Name_eraseHead(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(lean_object* v_self_725_, uint8_t v_success_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_a_735_; lean_object* v_a_736_; lean_object* v_a_757_; lean_object* v_a_758_; 
if (v_success_726_ == 0)
{
lean_object* v_config_778_; uint8_t v_preferReleaseBuild_779_; 
v_config_778_ = lean_ctor_get(v_self_725_, 6);
v_preferReleaseBuild_779_ = lean_ctor_get_uint8(v_config_778_, sizeof(void*)*27 + 2);
if (v_preferReleaseBuild_779_ == 0)
{
lean_object* v_toBuildConfig_780_; lean_object* v_baseName_781_; uint8_t v_verbosity_782_; uint8_t v___x_783_; uint8_t v___x_784_; 
v_toBuildConfig_780_ = lean_ctor_get(v___y_731_, 0);
v_baseName_781_ = lean_ctor_get(v_self_725_, 1);
lean_inc(v_baseName_781_);
lean_dec_ref(v_self_725_);
v_verbosity_782_ = lean_ctor_get_uint8(v_toBuildConfig_780_, sizeof(void*)*4 + 3);
v___x_783_ = 2;
v___x_784_ = l_Lake_instDecidableEqVerbosity(v_verbosity_782_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec(v_baseName_781_);
v___x_785_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_735_ = v___x_785_;
v_a_736_ = v___y_732_;
goto v___jp_734_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_786_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_787_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_781_, v___x_784_);
v___x_788_ = lean_string_append(v___x_786_, v___x_787_);
lean_dec_ref(v___x_787_);
v___x_789_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_790_ = lean_string_append(v___x_788_, v___x_789_);
v___x_791_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2);
v___x_792_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_791_, v___x_784_);
v___x_793_ = lean_string_append(v___x_790_, v___x_792_);
lean_dec_ref(v___x_792_);
v___x_794_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_795_ = lean_string_append(v___x_793_, v___x_794_);
v_a_735_ = v___x_795_;
v_a_736_ = v___y_732_;
goto v___jp_734_;
}
}
else
{
lean_object* v_toBuildConfig_796_; lean_object* v_baseName_797_; uint8_t v_verbosity_798_; uint8_t v___x_799_; uint8_t v___x_800_; 
v_toBuildConfig_796_ = lean_ctor_get(v___y_731_, 0);
v_baseName_797_ = lean_ctor_get(v_self_725_, 1);
lean_inc(v_baseName_797_);
lean_dec_ref(v_self_725_);
v_verbosity_798_ = lean_ctor_get_uint8(v_toBuildConfig_796_, sizeof(void*)*4 + 3);
v___x_799_ = 2;
v___x_800_ = l_Lake_instDecidableEqVerbosity(v_verbosity_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; 
lean_dec(v_baseName_797_);
v___x_801_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_757_ = v___x_801_;
v_a_758_ = v___y_732_;
goto v___jp_756_;
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_802_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_803_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_797_, v___x_800_);
v___x_804_ = lean_string_append(v___x_802_, v___x_803_);
lean_dec_ref(v___x_803_);
v___x_805_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_806_ = lean_string_append(v___x_804_, v___x_805_);
v___x_807_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
v___x_808_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_807_, v___x_800_);
v___x_809_ = lean_string_append(v___x_806_, v___x_808_);
lean_dec_ref(v___x_808_);
v___x_810_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_811_ = lean_string_append(v___x_809_, v___x_810_);
v_a_757_ = v___x_811_;
v_a_758_ = v___y_732_;
goto v___jp_756_;
}
}
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; 
lean_dec_ref(v_self_725_);
v___x_812_ = lean_box(0);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v___y_732_);
return v___x_813_;
}
v___jp_734_:
{
lean_object* v_log_737_; uint8_t v_action_738_; uint8_t v_wantsRebuild_739_; lean_object* v_trace_740_; lean_object* v_buildTime_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_755_; 
v_log_737_ = lean_ctor_get(v_a_736_, 0);
v_action_738_ = lean_ctor_get_uint8(v_a_736_, sizeof(void*)*3);
v_wantsRebuild_739_ = lean_ctor_get_uint8(v_a_736_, sizeof(void*)*3 + 1);
v_trace_740_ = lean_ctor_get(v_a_736_, 1);
v_buildTime_741_ = lean_ctor_get(v_a_736_, 2);
v_isSharedCheck_755_ = !lean_is_exclusive(v_a_736_);
if (v_isSharedCheck_755_ == 0)
{
v___x_743_ = v_a_736_;
v_isShared_744_ = v_isSharedCheck_755_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_buildTime_741_);
lean_inc(v_trace_740_);
lean_inc(v_log_737_);
lean_dec(v_a_736_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_755_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_745_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0));
v___x_746_ = lean_string_append(v___x_745_, v_a_735_);
lean_dec_ref(v_a_735_);
v___x_747_ = 0;
v___x_748_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set_uint8(v___x_748_, sizeof(void*)*1, v___x_747_);
v___x_749_ = lean_box(0);
v___x_750_ = lean_array_push(v_log_737_, v___x_748_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_750_);
v___x_752_ = v___x_743_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_trace_740_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_buildTime_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*3, v_action_738_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*3 + 1, v_wantsRebuild_739_);
v___x_752_ = v_reuseFailAlloc_754_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; 
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_749_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
return v___x_753_;
}
}
}
v___jp_756_:
{
lean_object* v_log_759_; uint8_t v_action_760_; uint8_t v_wantsRebuild_761_; lean_object* v_trace_762_; lean_object* v_buildTime_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_777_; 
v_log_759_ = lean_ctor_get(v_a_758_, 0);
v_action_760_ = lean_ctor_get_uint8(v_a_758_, sizeof(void*)*3);
v_wantsRebuild_761_ = lean_ctor_get_uint8(v_a_758_, sizeof(void*)*3 + 1);
v_trace_762_ = lean_ctor_get(v_a_758_, 1);
v_buildTime_763_ = lean_ctor_get(v_a_758_, 2);
v_isSharedCheck_777_ = !lean_is_exclusive(v_a_758_);
if (v_isSharedCheck_777_ == 0)
{
v___x_765_ = v_a_758_;
v_isShared_766_ = v_isSharedCheck_777_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_buildTime_763_);
lean_inc(v_trace_762_);
lean_inc(v_log_759_);
lean_dec(v_a_758_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_777_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_767_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1));
v___x_768_ = lean_string_append(v___x_767_, v_a_757_);
lean_dec_ref(v_a_757_);
v___x_769_ = 2;
v___x_770_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set_uint8(v___x_770_, sizeof(void*)*1, v___x_769_);
v___x_771_ = lean_box(0);
v___x_772_ = lean_array_push(v_log_759_, v___x_770_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_772_);
v___x_774_ = v___x_765_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_trace_762_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_buildTime_763_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, sizeof(void*)*3, v_action_760_);
lean_ctor_set_uint8(v_reuseFailAlloc_776_, sizeof(void*)*3 + 1, v_wantsRebuild_761_);
v___x_774_ = v_reuseFailAlloc_776_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_775_; 
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_771_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
return v___x_775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* v_self_814_, lean_object* v_success_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
uint8_t v_success_boxed_823_; lean_object* v_res_824_; 
v_success_boxed_823_ = lean_unbox(v_success_815_);
v_res_824_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(v_self_814_, v_success_boxed_823_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* v_self_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_833_; 
lean_inc_ref(v_a_826_);
lean_inc_ref(v_self_825_);
v___x_833_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_848_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_a_835_ = lean_ctor_get(v___x_833_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_848_ == 0)
{
v___x_837_ = v___x_833_;
v_isShared_838_ = v_isSharedCheck_848_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_848_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___f_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___f_839_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(v___f_839_, 0, v_self_825_);
v___x_840_ = l_Lake_instDataKindUnit;
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_842_ = 0;
v___x_843_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_844_ = l_Lake_Job_mapM___redArg(v___x_840_, v_a_834_, v___f_839_, v___x_841_, v___x_842_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v___x_843_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_844_);
v___x_846_ = v___x_837_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_a_835_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
else
{
lean_object* v_a_849_; lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec_ref(v_a_826_);
lean_dec_ref(v_self_825_);
v_a_849_ = lean_ctor_get(v___x_833_, 0);
v_a_850_ = lean_ctor_get(v___x_833_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_833_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_inc(v_a_849_);
lean_dec(v___x_833_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_849_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(lean_object* v_self_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
lean_dec_ref(v_a_863_);
lean_dec(v_a_862_);
lean_dec(v_a_861_);
lean_dec(v_a_860_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* v_self_867_, lean_object* v_as_868_, size_t v_sz_869_, size_t v_i_870_, lean_object* v_b_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = lean_usize_dec_lt(v_i_870_, v_sz_869_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; 
lean_dec_ref(v___y_872_);
lean_dec_ref(v_self_867_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_b_871_);
lean_ctor_set(v___x_880_, 1, v___y_877_);
return v___x_880_;
}
else
{
lean_object* v_a_881_; lean_object* v___x_882_; 
v_a_881_ = lean_array_uget_borrowed(v_as_868_, v_i_870_);
lean_inc_ref(v___y_872_);
lean_inc(v_a_881_);
lean_inc_ref(v_self_867_);
v___x_882_ = l_Lake_Package_fetchTargetJob(v_self_867_, v_a_881_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v_a_884_; lean_object* v___x_885_; size_t v___x_886_; size_t v___x_887_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
v_a_884_ = lean_ctor_get(v___x_882_, 1);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_882_, 2);
v___x_885_ = l_Lake_Job_mix___redArg(v_b_871_, v_a_883_);
v___x_886_ = ((size_t)1ULL);
v___x_887_ = lean_usize_add(v_i_870_, v___x_886_);
v_i_870_ = v___x_887_;
v_b_871_ = v___x_885_;
v___y_877_ = v_a_884_;
goto _start;
}
else
{
lean_object* v_a_889_; lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v___y_872_);
lean_dec_ref(v_b_871_);
lean_dec_ref(v_self_867_);
v_a_889_ = lean_ctor_get(v___x_882_, 0);
v_a_890_ = lean_ctor_get(v___x_882_, 1);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_882_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_inc(v_a_889_);
lean_dec(v___x_882_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_889_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* v_self_898_, lean_object* v_as_899_, lean_object* v_sz_900_, lean_object* v_i_901_, lean_object* v_b_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
size_t v_sz_boxed_910_; size_t v_i_boxed_911_; lean_object* v_res_912_; 
v_sz_boxed_910_ = lean_unbox_usize(v_sz_900_);
lean_dec(v_sz_900_);
v_i_boxed_911_ = lean_unbox_usize(v_i_901_);
lean_dec(v_i_901_);
v_res_912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_898_, v_as_899_, v_sz_boxed_910_, v_i_boxed_911_, v_b_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v_as_899_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object* v_config_913_, lean_object* v_self_914_, lean_object* v_____r_915_, lean_object* v_job_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_extraDepTargets_924_; size_t v_sz_925_; size_t v___x_926_; lean_object* v___x_927_; 
v_extraDepTargets_924_ = lean_ctor_get(v_config_913_, 2);
v_sz_925_ = lean_array_size(v_extraDepTargets_924_);
v___x_926_ = ((size_t)0ULL);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_914_, v_extraDepTargets_924_, v_sz_925_, v___x_926_, v_job_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object* v_config_928_, lean_object* v_self_929_, lean_object* v_____r_930_, lean_object* v_job_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(v_config_928_, v_self_929_, v_____r_930_, v_job_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v_config_928_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(uint8_t v___x_940_, lean_object* v_self_941_, lean_object* v_job_942_, lean_object* v___f_943_, lean_object* v___x_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
if (v___x_940_ == 0)
{
lean_object* v___x_952_; 
lean_inc_ref(v___y_945_);
v___x_952_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_941_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
v_a_954_ = lean_ctor_get(v___x_952_, 1);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_952_, 2);
v___x_955_ = l_Lake_Job_add___redArg(v_job_942_, v_a_953_);
lean_inc_ref(v___y_949_);
lean_inc(v___y_948_);
lean_inc(v___y_947_);
lean_inc(v___y_946_);
v___x_956_ = lean_apply_9(v___f_943_, v___x_944_, v___x_955_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v_a_954_, lean_box(0));
return v___x_956_;
}
else
{
lean_dec_ref(v___y_945_);
lean_dec_ref(v___f_943_);
lean_dec_ref(v_job_942_);
return v___x_952_;
}
}
else
{
lean_object* v___x_957_; 
lean_dec_ref(v_self_941_);
lean_inc_ref(v___y_949_);
lean_inc(v___y_948_);
lean_inc(v___y_947_);
lean_inc(v___y_946_);
v___x_957_ = lean_apply_9(v___f_943_, v___x_944_, v_job_942_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, lean_box(0));
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* v___x_958_, lean_object* v_self_959_, lean_object* v_job_960_, lean_object* v___f_961_, lean_object* v___x_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
uint8_t v___x_4162__boxed_970_; lean_object* v_res_971_; 
v___x_4162__boxed_970_ = lean_unbox(v___x_958_);
v_res_971_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(v___x_4162__boxed_970_, v_self_959_, v_job_960_, v___f_961_, v___x_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v___y_965_);
lean_dec(v___y_964_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object* v_self_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_wsIdx_982_; lean_object* v_baseName_983_; lean_object* v_config_984_; lean_object* v___f_985_; lean_object* v___x_986_; uint8_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v_job_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___y_1007_; lean_object* v___x_1008_; 
v_wsIdx_982_ = lean_ctor_get(v_self_974_, 0);
v_baseName_983_ = lean_ctor_get(v_self_974_, 1);
v_config_984_ = lean_ctor_get(v_self_974_, 6);
lean_inc_ref(v_self_974_);
lean_inc_ref(v_config_984_);
v___f_985_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed), 11, 2);
lean_closure_set(v___f_985_, 0, v_config_984_);
lean_closure_set(v___f_985_, 1, v_self_974_);
v___x_986_ = l_Lake_instDataKindUnit;
v___x_987_ = 1;
lean_inc(v_baseName_983_);
v___x_988_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_983_, v___x_987_);
v___x_989_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0));
v___x_990_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1));
v___x_991_ = lean_string_append(v___x_990_, v___x_988_);
v___x_992_ = lean_string_append(v___x_991_, v___x_989_);
v___x_993_ = lean_box(0);
v___x_994_ = lean_box(0);
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_997_ = 0;
v___x_998_ = 0;
v___x_999_ = l_Lake_BuildTrace_nil(v___x_992_);
v___x_1000_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1000_, 0, v___x_996_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
lean_ctor_set(v___x_1000_, 2, v___x_995_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*3, v___x_997_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*3 + 1, v___x_998_);
v___x_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_993_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_task_pure(v___x_1001_);
v___x_1003_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_job_1004_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_1004_, 0, v___x_1002_);
lean_ctor_set(v_job_1004_, 1, v___x_994_);
lean_ctor_set(v_job_1004_, 2, v___x_1003_);
lean_ctor_set_uint8(v_job_1004_, sizeof(void*)*3, v___x_998_);
v___x_1005_ = lean_nat_dec_eq(v_wsIdx_982_, v___x_995_);
v___x_1006_ = lean_box(v___x_1005_);
v___y_1007_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 12, 5);
lean_closure_set(v___y_1007_, 0, v___x_1006_);
lean_closure_set(v___y_1007_, 1, v_self_974_);
lean_closure_set(v___y_1007_, 2, v_job_1004_);
lean_closure_set(v___y_1007_, 3, v___f_985_);
lean_closure_set(v___y_1007_, 4, v___x_993_);
v___x_1008_ = l_Lake_ensureJob___redArg(v___x_986_, v___y_1007_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1034_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_a_1010_ = lean_ctor_get(v___x_1008_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1012_ = v___x_1008_;
v_isShared_1013_ = v_isSharedCheck_1034_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1034_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v_task_1014_; lean_object* v_kind_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1032_; 
v_task_1014_ = lean_ctor_get(v_a_1009_, 0);
v_kind_1015_ = lean_ctor_get(v_a_1009_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_a_1009_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v_a_1009_, 2);
lean_dec(v_unused_1033_);
v___x_1017_ = v_a_1009_;
v_isShared_1018_ = v_isSharedCheck_1032_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_kind_1015_);
lean_inc(v_task_1014_);
lean_dec(v_a_1009_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1032_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v_registeredJobs_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v_job_1023_; 
v_registeredJobs_1019_ = lean_ctor_get(v_a_979_, 3);
v___x_1020_ = lean_st_ref_take(v_registeredJobs_1019_);
v___x_1021_ = lean_string_append(v___x_988_, v___x_989_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 2, v___x_1021_);
v_job_1023_ = v___x_1017_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_task_1014_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_kind_1015_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v___x_1021_);
v_job_1023_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
lean_ctor_set_uint8(v_job_1023_, sizeof(void*)*3, v___x_998_);
lean_inc_ref(v_job_1023_);
v___x_1024_ = l_Lake_Job_toOpaque___redArg(v_job_1023_);
v___x_1025_ = lean_array_push(v___x_1020_, v___x_1024_);
v___x_1026_ = lean_st_ref_set(v_registeredJobs_1019_, v___x_1025_);
v___x_1027_ = l_Lake_Job_renew___redArg(v_job_1023_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1027_);
v___x_1029_ = v___x_1012_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_a_1010_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_988_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(lean_object* v_self_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(v_self_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec(v_a_1037_);
return v_res_1043_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = lean_box(0);
v___x_1045_ = l_Lean_Json_compress(v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t v_fmt_1046_){
_start:
{
if (v_fmt_1046_ == 0)
{
lean_object* v___x_1047_; 
v___x_1047_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
return v___x_1047_;
}
else
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_1049_){
_start:
{
uint8_t v_fmt_boxed_1050_; lean_object* v_res_1051_; 
v_fmt_boxed_1050_ = lean_unbox(v_fmt_1049_);
v_res_1051_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_boxed_1050_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(uint8_t v_fmt_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object* v_fmt_1055_, lean_object* v_a_1056_){
_start:
{
uint8_t v_fmt_boxed_1057_; lean_object* v_res_1058_; 
v_fmt_boxed_1057_ = lean_unbox(v_fmt_1055_);
v_res_1058_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(v_fmt_boxed_1057_, v_a_1056_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v___y_1059_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
uint8_t v___y_67__boxed_1064_; lean_object* v_res_1065_; 
v___y_67__boxed_1064_ = lean_unbox(v___y_1062_);
v_res_1065_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_67__boxed_1064_, v___y_1063_);
return v_res_1065_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1068_; uint8_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___f_1068_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_1069_ = 1;
v___x_1070_ = l_Lake_instDataKindUnit;
v___x_1071_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__1));
v___x_1072_ = l_Lake_Package_keyword;
v___x_1073_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v___x_1071_);
lean_ctor_set(v___x_1073_, 2, v___x_1070_);
lean_ctor_set(v___x_1073_, 3, v___f_1068_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*4, v___x_1069_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*4 + 1, v___x_1069_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_obj_once(&l_Lake_Package_extraDepFacetConfig___closed__2, &l_Lake_Package_extraDepFacetConfig___closed__2_once, _init_l_Lake_Package_extraDepFacetConfig___closed__2);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object* v_self_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_origName_1094_; lean_object* v_dir_1095_; lean_object* v_scope_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_origName_1094_ = lean_ctor_get(v_self_1090_, 3);
lean_inc(v_origName_1094_);
v_dir_1095_ = lean_ctor_get(v_self_1090_, 4);
lean_inc_ref(v_dir_1095_);
v_scope_1096_ = lean_ctor_get(v_self_1090_, 10);
lean_inc_ref(v_scope_1096_);
lean_dec_ref(v_self_1090_);
v___x_1097_ = lean_string_utf8_byte_size(v_scope_1096_);
v___x_1098_ = lean_unsigned_to_nat(0u);
v___x_1099_ = lean_nat_dec_eq(v___x_1097_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
v___x_1101_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1100_, v_dir_1095_);
if (lean_obj_tag(v___x_1101_) == 1)
{
lean_object* v_toContext_1102_; lean_object* v_lakeEnv_1103_; lean_object* v_log_1104_; uint8_t v_action_1105_; uint8_t v_wantsRebuild_1106_; lean_object* v_trace_1107_; lean_object* v_buildTime_1108_; lean_object* v_val_1109_; lean_object* v_toolchain_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v_toContext_1102_ = lean_ctor_get(v_a_1091_, 1);
v_lakeEnv_1103_ = lean_ctor_get(v_toContext_1102_, 0);
v_log_1104_ = lean_ctor_get(v_a_1092_, 0);
v_action_1105_ = lean_ctor_get_uint8(v_a_1092_, sizeof(void*)*3);
v_wantsRebuild_1106_ = lean_ctor_get_uint8(v_a_1092_, sizeof(void*)*3 + 1);
v_trace_1107_ = lean_ctor_get(v_a_1092_, 1);
v_buildTime_1108_ = lean_ctor_get(v_a_1092_, 2);
v_val_1109_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_val_1109_);
lean_dec_ref_known(v___x_1101_, 1);
v_toolchain_1110_ = lean_ctor_get(v_lakeEnv_1103_, 19);
v___x_1111_ = lean_string_utf8_byte_size(v_toolchain_1110_);
v___x_1112_ = lean_nat_dec_eq(v___x_1111_, v___x_1098_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1113_ = l_Lean_Name_toString(v_origName_1094_, v___x_1099_);
lean_inc_ref(v_lakeEnv_1103_);
v___x_1114_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_1103_, v_scope_1096_, v___x_1113_);
v___x_1115_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1));
v___x_1116_ = lean_string_append(v___x_1114_, v___x_1115_);
v___x_1117_ = lean_string_append(v___x_1116_, v_val_1109_);
lean_dec(v_val_1109_);
v___x_1118_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2));
v___x_1119_ = lean_string_append(v___x_1117_, v___x_1118_);
v___x_1120_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc_ref(v_toolchain_1110_);
v___x_1121_ = l_Lake_uriEncode(v_toolchain_1110_, v___x_1120_);
v___x_1122_ = lean_string_append(v___x_1119_, v___x_1121_);
lean_dec_ref(v___x_1121_);
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
lean_ctor_set(v___x_1123_, 1, v_a_1092_);
return v___x_1123_;
}
else
{
lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1134_; 
lean_inc(v_buildTime_1108_);
lean_inc_ref(v_trace_1107_);
lean_inc_ref(v_log_1104_);
lean_dec(v_val_1109_);
lean_dec_ref(v_scope_1096_);
lean_dec(v_origName_1094_);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_a_1092_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; lean_object* v_unused_1136_; lean_object* v_unused_1137_; 
v_unused_1135_ = lean_ctor_get(v_a_1092_, 2);
lean_dec(v_unused_1135_);
v_unused_1136_ = lean_ctor_get(v_a_1092_, 1);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v_a_1092_, 0);
lean_dec(v_unused_1137_);
v___x_1125_ = v_a_1092_;
v_isShared_1126_ = v_isSharedCheck_1134_;
goto v_resetjp_1124_;
}
else
{
lean_dec(v_a_1092_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1134_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1127_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4));
v___x_1128_ = lean_array_get_size(v_log_1104_);
v___x_1129_ = lean_array_push(v_log_1104_, v___x_1127_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1129_);
v___x_1131_ = v___x_1125_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_trace_1107_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_buildTime_1108_);
lean_ctor_set_uint8(v_reuseFailAlloc_1133_, sizeof(void*)*3, v_action_1105_);
lean_ctor_set_uint8(v_reuseFailAlloc_1133_, sizeof(void*)*3 + 1, v_wantsRebuild_1106_);
v___x_1131_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1128_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
return v___x_1132_;
}
}
}
}
else
{
lean_object* v_log_1138_; uint8_t v_action_1139_; uint8_t v_wantsRebuild_1140_; lean_object* v_trace_1141_; lean_object* v_buildTime_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v___x_1101_);
lean_dec_ref(v_scope_1096_);
lean_dec(v_origName_1094_);
v_log_1138_ = lean_ctor_get(v_a_1092_, 0);
v_action_1139_ = lean_ctor_get_uint8(v_a_1092_, sizeof(void*)*3);
v_wantsRebuild_1140_ = lean_ctor_get_uint8(v_a_1092_, sizeof(void*)*3 + 1);
v_trace_1141_ = lean_ctor_get(v_a_1092_, 1);
v_buildTime_1142_ = lean_ctor_get(v_a_1092_, 2);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_a_1092_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1144_ = v_a_1092_;
v_isShared_1145_ = v_isSharedCheck_1153_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_buildTime_1142_);
lean_inc(v_trace_1141_);
lean_inc(v_log_1138_);
lean_dec(v_a_1092_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1153_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1146_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6));
v___x_1147_ = lean_array_get_size(v_log_1138_);
v___x_1148_ = lean_array_push(v_log_1138_, v___x_1146_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1148_);
v___x_1150_ = v___x_1144_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_trace_1141_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_buildTime_1142_);
lean_ctor_set_uint8(v_reuseFailAlloc_1152_, sizeof(void*)*3, v_action_1139_);
lean_ctor_set_uint8(v_reuseFailAlloc_1152_, sizeof(void*)*3 + 1, v_wantsRebuild_1140_);
v___x_1150_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1147_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
return v___x_1151_;
}
}
}
}
else
{
lean_object* v_log_1154_; uint8_t v_action_1155_; uint8_t v_wantsRebuild_1156_; lean_object* v_trace_1157_; lean_object* v_buildTime_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1169_; 
lean_dec_ref(v_scope_1096_);
lean_dec_ref(v_dir_1095_);
lean_dec(v_origName_1094_);
v_log_1154_ = lean_ctor_get(v_a_1092_, 0);
v_action_1155_ = lean_ctor_get_uint8(v_a_1092_, sizeof(void*)*3);
v_wantsRebuild_1156_ = lean_ctor_get_uint8(v_a_1092_, sizeof(void*)*3 + 1);
v_trace_1157_ = lean_ctor_get(v_a_1092_, 1);
v_buildTime_1158_ = lean_ctor_get(v_a_1092_, 2);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_a_1092_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1160_ = v_a_1092_;
v_isShared_1161_ = v_isSharedCheck_1169_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_buildTime_1158_);
lean_inc(v_trace_1157_);
lean_inc(v_log_1154_);
lean_dec(v_a_1092_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1169_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1162_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8));
v___x_1163_ = lean_array_get_size(v_log_1154_);
v___x_1164_ = lean_array_push(v_log_1154_, v___x_1162_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1164_);
v___x_1166_ = v___x_1160_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_trace_1157_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_buildTime_1158_);
lean_ctor_set_uint8(v_reuseFailAlloc_1168_, sizeof(void*)*3, v_action_1155_);
lean_ctor_set_uint8(v_reuseFailAlloc_1168_, sizeof(void*)*3 + 1, v_wantsRebuild_1156_);
v___x_1166_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1163_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
return v___x_1167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___boxed(lean_object* v_self_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1170_, v_a_1171_, v_a_1172_);
lean_dec_ref(v_a_1171_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object* v_self_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1175_, v_a_1180_, v_a_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object* v_self_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(v_self_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object* v_self_1202_, lean_object* v_a_1203_){
_start:
{
lean_object* v_rev_1206_; lean_object* v_log_1207_; uint8_t v_action_1208_; uint8_t v_wantsRebuild_1209_; lean_object* v_trace_1210_; lean_object* v_buildTime_1211_; lean_object* v_dir_1220_; lean_object* v_config_1221_; lean_object* v_remoteUrl_1222_; lean_object* v_buildArchive_1223_; uint8_t v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; uint8_t v___y_1229_; lean_object* v_val_1230_; lean_object* v___y_1250_; lean_object* v_releaseRepo_1281_; 
v_dir_1220_ = lean_ctor_get(v_self_1202_, 4);
lean_inc_ref(v_dir_1220_);
v_config_1221_ = lean_ctor_get(v_self_1202_, 6);
lean_inc_ref(v_config_1221_);
v_remoteUrl_1222_ = lean_ctor_get(v_self_1202_, 11);
lean_inc_ref(v_remoteUrl_1222_);
v_buildArchive_1223_ = lean_ctor_get(v_self_1202_, 21);
lean_inc_ref(v_buildArchive_1223_);
lean_dec_ref(v_self_1202_);
v_releaseRepo_1281_ = lean_ctor_get(v_config_1221_, 10);
lean_inc(v_releaseRepo_1281_);
lean_dec_ref(v_config_1221_);
if (lean_obj_tag(v_releaseRepo_1281_) == 0)
{
lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1282_ = lean_string_utf8_byte_size(v_remoteUrl_1222_);
v___x_1283_ = lean_unsigned_to_nat(0u);
v___x_1284_ = lean_nat_dec_eq(v___x_1282_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_remoteUrl_1222_);
v___y_1250_ = v___x_1285_;
goto v___jp_1249_;
}
else
{
lean_dec_ref(v_remoteUrl_1222_);
v___y_1250_ = v_releaseRepo_1281_;
goto v___jp_1249_;
}
}
else
{
lean_dec_ref(v_remoteUrl_1222_);
v___y_1250_ = v_releaseRepo_1281_;
goto v___jp_1249_;
}
v___jp_1205_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1212_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0));
v___x_1213_ = lean_string_append(v___x_1212_, v_rev_1206_);
lean_dec_ref(v_rev_1206_);
v___x_1214_ = 3;
v___x_1215_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set_uint8(v___x_1215_, sizeof(void*)*1, v___x_1214_);
v___x_1216_ = lean_array_get_size(v_log_1207_);
v___x_1217_ = lean_array_push(v_log_1207_, v___x_1215_);
v___x_1218_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v_trace_1210_);
lean_ctor_set(v___x_1218_, 2, v_buildTime_1211_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*3, v_action_1208_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*3 + 1, v_wantsRebuild_1209_);
v___x_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1216_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
return v___x_1219_;
}
v___jp_1224_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
lean_inc_ref(v_dir_1220_);
v___x_1232_ = l_Lake_GitRepo_findTag_x3f(v___x_1231_, v_dir_1220_);
if (lean_obj_tag(v___x_1232_) == 1)
{
lean_object* v_val_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec_ref(v_dir_1220_);
v_val_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_val_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v___x_1234_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1234_, 0, v___y_1226_);
lean_ctor_set(v___x_1234_, 1, v___y_1228_);
lean_ctor_set(v___x_1234_, 2, v___y_1227_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*3, v___y_1225_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*3 + 1, v___y_1229_);
v___x_1235_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1));
v___x_1236_ = lean_string_append(v_val_1230_, v___x_1235_);
v___x_1237_ = lean_string_append(v___x_1236_, v_val_1233_);
lean_dec(v_val_1233_);
v___x_1238_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2));
v___x_1239_ = lean_string_append(v___x_1237_, v___x_1238_);
v___x_1240_ = lean_string_append(v___x_1239_, v_buildArchive_1223_);
lean_dec_ref(v_buildArchive_1223_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v___x_1234_);
return v___x_1241_;
}
else
{
lean_object* v___x_1242_; 
lean_dec(v___x_1232_);
lean_dec_ref(v_val_1230_);
lean_dec_ref(v_buildArchive_1223_);
v___x_1242_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1231_, v_dir_1220_);
if (lean_obj_tag(v___x_1242_) == 1)
{
lean_object* v_val_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_val_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_val_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v___x_1244_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3));
v___x_1245_ = lean_string_append(v___x_1244_, v_val_1243_);
lean_dec(v_val_1243_);
v___x_1246_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4));
v___x_1247_ = lean_string_append(v___x_1245_, v___x_1246_);
v_rev_1206_ = v___x_1247_;
v_log_1207_ = v___y_1226_;
v_action_1208_ = v___y_1225_;
v_wantsRebuild_1209_ = v___y_1229_;
v_trace_1210_ = v___y_1228_;
v_buildTime_1211_ = v___y_1227_;
goto v___jp_1205_;
}
else
{
lean_object* v___x_1248_; 
lean_dec(v___x_1242_);
v___x_1248_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_rev_1206_ = v___x_1248_;
v_log_1207_ = v___y_1226_;
v_action_1208_ = v___y_1225_;
v_wantsRebuild_1209_ = v___y_1229_;
v_trace_1210_ = v___y_1228_;
v_buildTime_1211_ = v___y_1227_;
goto v___jp_1205_;
}
}
}
v___jp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_dir_1220_);
v___x_1252_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v___x_1251_, v_dir_1220_);
if (lean_obj_tag(v___y_1250_) == 0)
{
if (lean_obj_tag(v___x_1252_) == 1)
{
lean_object* v_log_1253_; uint8_t v_action_1254_; uint8_t v_wantsRebuild_1255_; lean_object* v_trace_1256_; lean_object* v_buildTime_1257_; lean_object* v_val_1258_; 
v_log_1253_ = lean_ctor_get(v_a_1203_, 0);
lean_inc_ref(v_log_1253_);
v_action_1254_ = lean_ctor_get_uint8(v_a_1203_, sizeof(void*)*3);
v_wantsRebuild_1255_ = lean_ctor_get_uint8(v_a_1203_, sizeof(void*)*3 + 1);
v_trace_1256_ = lean_ctor_get(v_a_1203_, 1);
lean_inc_ref(v_trace_1256_);
v_buildTime_1257_ = lean_ctor_get(v_a_1203_, 2);
lean_inc(v_buildTime_1257_);
lean_dec_ref(v_a_1203_);
v_val_1258_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v___x_1252_, 1);
v___y_1225_ = v_action_1254_;
v___y_1226_ = v_log_1253_;
v___y_1227_ = v_buildTime_1257_;
v___y_1228_ = v_trace_1256_;
v___y_1229_ = v_wantsRebuild_1255_;
v_val_1230_ = v_val_1258_;
goto v___jp_1224_;
}
else
{
lean_object* v_log_1259_; uint8_t v_action_1260_; uint8_t v_wantsRebuild_1261_; lean_object* v_trace_1262_; lean_object* v_buildTime_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v___x_1252_);
lean_dec_ref(v_buildArchive_1223_);
lean_dec_ref(v_dir_1220_);
v_log_1259_ = lean_ctor_get(v_a_1203_, 0);
v_action_1260_ = lean_ctor_get_uint8(v_a_1203_, sizeof(void*)*3);
v_wantsRebuild_1261_ = lean_ctor_get_uint8(v_a_1203_, sizeof(void*)*3 + 1);
v_trace_1262_ = lean_ctor_get(v_a_1203_, 1);
v_buildTime_1263_ = lean_ctor_get(v_a_1203_, 2);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_a_1203_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1265_ = v_a_1203_;
v_isShared_1266_ = v_isSharedCheck_1274_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_buildTime_1263_);
lean_inc(v_trace_1262_);
lean_inc(v_log_1259_);
lean_dec(v_a_1203_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1274_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1271_; 
v___x_1267_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6));
v___x_1268_ = lean_array_get_size(v_log_1259_);
v___x_1269_ = lean_array_push(v_log_1259_, v___x_1267_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1269_);
v___x_1271_ = v___x_1265_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_trace_1262_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_buildTime_1263_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*3, v_action_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*3 + 1, v_wantsRebuild_1261_);
v___x_1271_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1268_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
return v___x_1272_;
}
}
}
}
else
{
lean_object* v_log_1275_; uint8_t v_action_1276_; uint8_t v_wantsRebuild_1277_; lean_object* v_trace_1278_; lean_object* v_buildTime_1279_; lean_object* v_val_1280_; 
lean_dec(v___x_1252_);
v_log_1275_ = lean_ctor_get(v_a_1203_, 0);
lean_inc_ref(v_log_1275_);
v_action_1276_ = lean_ctor_get_uint8(v_a_1203_, sizeof(void*)*3);
v_wantsRebuild_1277_ = lean_ctor_get_uint8(v_a_1203_, sizeof(void*)*3 + 1);
v_trace_1278_ = lean_ctor_get(v_a_1203_, 1);
lean_inc_ref(v_trace_1278_);
v_buildTime_1279_ = lean_ctor_get(v_a_1203_, 2);
lean_inc(v_buildTime_1279_);
lean_dec_ref(v_a_1203_);
v_val_1280_ = lean_ctor_get(v___y_1250_, 0);
lean_inc(v_val_1280_);
lean_dec_ref_known(v___y_1250_, 1);
v___y_1225_ = v_action_1276_;
v___y_1226_ = v_log_1275_;
v___y_1227_ = v_buildTime_1279_;
v___y_1228_ = v_trace_1278_;
v___y_1229_ = v_wantsRebuild_1277_;
v_val_1230_ = v_val_1280_;
goto v___jp_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(lean_object* v_self_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1286_, v_a_1287_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object* v_self_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1290_, v_a_1296_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object* v_self_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(v_self_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(lean_object* v_val_1308_, lean_object* v_a_x3f_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; lean_object* v_log_1313_; uint8_t v_action_1314_; uint8_t v_wantsRebuild_1315_; lean_object* v_trace_1316_; lean_object* v_buildTime_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1328_; 
v___x_1312_ = lean_io_mono_ms_now();
v_log_1313_ = lean_ctor_get(v___y_1310_, 0);
v_action_1314_ = lean_ctor_get_uint8(v___y_1310_, sizeof(void*)*3);
v_wantsRebuild_1315_ = lean_ctor_get_uint8(v___y_1310_, sizeof(void*)*3 + 1);
v_trace_1316_ = lean_ctor_get(v___y_1310_, 1);
v_buildTime_1317_ = lean_ctor_get(v___y_1310_, 2);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___y_1310_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1319_ = v___y_1310_;
v_isShared_1320_ = v_isSharedCheck_1328_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_buildTime_1317_);
lean_inc(v_trace_1316_);
lean_inc(v_log_1313_);
lean_dec(v___y_1310_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1328_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1321_ = lean_nat_sub(v___x_1312_, v_val_1308_);
lean_dec(v___x_1312_);
v___x_1322_ = lean_box(0);
v___x_1323_ = lean_nat_add(v_buildTime_1317_, v___x_1321_);
lean_dec(v___x_1321_);
lean_dec(v_buildTime_1317_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 2, v___x_1323_);
v___x_1325_ = v___x_1319_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_log_1313_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_trace_1316_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v___x_1323_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, sizeof(void*)*3, v_action_1314_);
lean_ctor_set_uint8(v_reuseFailAlloc_1327_, sizeof(void*)*3 + 1, v_wantsRebuild_1315_);
v___x_1325_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1326_; 
v___x_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1322_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0___boxed(lean_object* v_val_1329_, lean_object* v_a_x3f_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v_val_1329_, v_a_x3f_1330_, v___y_1331_);
lean_dec(v_a_x3f_1330_);
lean_dec(v_val_1329_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(lean_object* v_url_1339_, lean_object* v_archiveFile_1340_, lean_object* v_headers_1341_, lean_object* v_depTrace_1342_, lean_object* v_traceFile_1343_, uint8_t v_action_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_a_1349_; lean_object* v_a_1350_; lean_object* v_log_1353_; uint8_t v_action_1354_; uint8_t v_wantsRebuild_1355_; lean_object* v_trace_1356_; lean_object* v_buildTime_1357_; lean_object* v_toBuildConfig_1363_; lean_object* v_log_1364_; uint8_t v_action_1365_; uint8_t v_wantsRebuild_1366_; lean_object* v_trace_1367_; lean_object* v_buildTime_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1458_; 
v_toBuildConfig_1363_ = lean_ctor_get(v_a_1345_, 0);
v_log_1364_ = lean_ctor_get(v_a_1346_, 0);
v_action_1365_ = lean_ctor_get_uint8(v_a_1346_, sizeof(void*)*3);
v_wantsRebuild_1366_ = lean_ctor_get_uint8(v_a_1346_, sizeof(void*)*3 + 1);
v_trace_1367_ = lean_ctor_get(v_a_1346_, 1);
v_buildTime_1368_ = lean_ctor_get(v_a_1346_, 2);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_a_1346_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1370_ = v_a_1346_;
v_isShared_1371_ = v_isSharedCheck_1458_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_buildTime_1368_);
lean_inc(v_trace_1367_);
lean_inc(v_log_1364_);
lean_dec(v_a_1346_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1458_;
goto v_resetjp_1369_;
}
v___jp_1348_:
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1351_, 0, v_a_1349_);
lean_ctor_set(v___x_1351_, 1, v_a_1350_);
return v___x_1351_;
}
v___jp_1352_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1358_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1));
v___x_1359_ = lean_array_get_size(v_log_1353_);
v___x_1360_ = lean_array_push(v_log_1353_, v___x_1358_);
v___x_1361_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
lean_ctor_set(v___x_1361_, 1, v_trace_1356_);
lean_ctor_set(v___x_1361_, 2, v_buildTime_1357_);
lean_ctor_set_uint8(v___x_1361_, sizeof(void*)*3, v_action_1354_);
lean_ctor_set_uint8(v___x_1361_, sizeof(void*)*3 + 1, v_wantsRebuild_1355_);
v___x_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1359_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
return v___x_1362_;
}
v_resetjp_1369_:
{
uint8_t v_noBuild_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_noBuild_1372_ = lean_ctor_get_uint8(v_toBuildConfig_1363_, sizeof(void*)*4 + 2);
v___x_1373_ = l_Lake_JobAction_merge(v_action_1365_, v_action_1344_);
v___x_1374_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2));
lean_inc_ref(v_traceFile_1343_);
v___x_1375_ = l_System_FilePath_addExtension(v_traceFile_1343_, v___x_1374_);
if (v_noBuild_1372_ == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_a_1379_; lean_object* v_a_1380_; 
v___x_1376_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1364_);
v___x_1377_ = l_Lake_download(v_url_1339_, v_archiveFile_1340_, v_headers_1341_, v_log_1364_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1384_; lean_object* v_a_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_a_1384_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1384_);
v_a_1385_ = lean_ctor_get(v___x_1377_, 1);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1377_, 2);
v___x_1386_ = lean_array_get_size(v_log_1364_);
lean_dec_ref(v_log_1364_);
v___x_1387_ = lean_array_get_size(v_a_1385_);
v___x_1388_ = l_Array_extract___redArg(v_a_1385_, v___x_1386_, v___x_1387_);
v___x_1389_ = lean_box(0);
v___x_1390_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1342_, v___x_1389_, v___x_1388_);
v___x_1391_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1343_, v___x_1390_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1428_; 
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; 
v_unused_1429_ = lean_ctor_get(v___x_1391_, 0);
lean_dec(v_unused_1429_);
v___x_1393_ = v___x_1391_;
v_isShared_1394_ = v_isSharedCheck_1428_;
goto v_resetjp_1392_;
}
else
{
lean_dec(v___x_1391_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1428_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lake_removeFileIfExists(v___x_1375_);
lean_dec_ref(v___x_1375_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1418_; 
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1418_ == 0)
{
lean_object* v_unused_1419_; 
v_unused_1419_ = lean_ctor_get(v___x_1395_, 0);
lean_dec(v_unused_1419_);
v___x_1397_ = v___x_1395_;
v_isShared_1398_ = v_isSharedCheck_1418_;
goto v_resetjp_1396_;
}
else
{
lean_dec(v___x_1395_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1418_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v_a_1385_);
v___x_1400_ = v___x_1370_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1385_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_trace_1367_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_buildTime_1368_);
lean_ctor_set_uint8(v_reuseFailAlloc_1417_, sizeof(void*)*3 + 1, v_wantsRebuild_1366_);
v___x_1400_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1402_; 
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*3, v___x_1373_);
lean_inc(v_a_1384_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 0, v_a_1384_);
v___x_1402_ = v___x_1397_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1384_);
v___x_1402_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1404_; 
if (v_isShared_1394_ == 0)
{
lean_ctor_set_tag(v___x_1393_, 1);
lean_ctor_set(v___x_1393_, 0, v___x_1402_);
v___x_1404_ = v___x_1393_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
v___x_1405_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1376_, v___x_1404_, v___x_1400_);
lean_dec_ref(v___x_1404_);
lean_dec(v___x_1376_);
v_a_1406_ = lean_ctor_get(v___x_1405_, 1);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v___x_1405_, 0);
lean_dec(v_unused_1414_);
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v_a_1384_);
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1384_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
lean_del_object(v___x_1393_);
lean_dec(v_a_1384_);
v_a_1420_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1421_ = lean_io_error_to_string(v_a_1420_);
v___x_1422_ = 3;
v___x_1423_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
lean_ctor_set_uint8(v___x_1423_, sizeof(void*)*1, v___x_1422_);
v___x_1424_ = lean_array_push(v_a_1385_, v___x_1423_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1424_);
v___x_1426_ = v___x_1370_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_trace_1367_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_buildTime_1368_);
lean_ctor_set_uint8(v_reuseFailAlloc_1427_, sizeof(void*)*3 + 1, v_wantsRebuild_1366_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_ctor_set_uint8(v___x_1426_, sizeof(void*)*3, v___x_1373_);
v_a_1379_ = v___x_1387_;
v_a_1380_ = v___x_1426_;
goto v___jp_1378_;
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
lean_dec(v_a_1384_);
lean_dec_ref(v___x_1375_);
v_a_1430_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1431_ = lean_io_error_to_string(v_a_1430_);
v___x_1432_ = 3;
v___x_1433_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set_uint8(v___x_1433_, sizeof(void*)*1, v___x_1432_);
v___x_1434_ = lean_array_push(v_a_1385_, v___x_1433_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1434_);
v___x_1436_ = v___x_1370_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_trace_1367_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_buildTime_1368_);
lean_ctor_set_uint8(v_reuseFailAlloc_1437_, sizeof(void*)*3 + 1, v_wantsRebuild_1366_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_ctor_set_uint8(v___x_1436_, sizeof(void*)*3, v___x_1373_);
v_a_1379_ = v___x_1387_;
v_a_1380_ = v___x_1436_;
goto v___jp_1378_;
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v_a_1439_; lean_object* v___x_1441_; 
lean_dec_ref(v___x_1375_);
lean_dec_ref(v_log_1364_);
lean_dec_ref(v_traceFile_1343_);
v_a_1438_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1438_);
v_a_1439_ = lean_ctor_get(v___x_1377_, 1);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1377_, 2);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v_a_1439_);
v___x_1441_ = v___x_1370_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1439_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_trace_1367_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_buildTime_1368_);
lean_ctor_set_uint8(v_reuseFailAlloc_1442_, sizeof(void*)*3 + 1, v_wantsRebuild_1366_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*3, v___x_1373_);
v_a_1379_ = v_a_1438_;
v_a_1380_ = v___x_1441_;
goto v___jp_1378_;
}
}
v___jp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v_a_1383_; 
v___x_1381_ = lean_box(0);
v___x_1382_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1376_, v___x_1381_, v_a_1380_);
lean_dec(v___x_1376_);
v_a_1383_ = lean_ctor_get(v___x_1382_, 1);
lean_inc(v_a_1383_);
lean_dec_ref(v___x_1382_);
v_a_1349_ = v_a_1379_;
v_a_1350_ = v_a_1383_;
goto v___jp_1348_;
}
}
else
{
uint8_t v___x_1443_; 
lean_dec_ref(v_archiveFile_1340_);
lean_dec_ref(v_url_1339_);
v___x_1443_ = l_System_FilePath_pathExists(v_traceFile_1343_);
lean_dec_ref(v_traceFile_1343_);
if (v___x_1443_ == 0)
{
lean_dec_ref(v___x_1375_);
lean_del_object(v___x_1370_);
v_log_1353_ = v_log_1364_;
v_action_1354_ = v___x_1373_;
v_wantsRebuild_1355_ = v_noBuild_1372_;
v_trace_1356_ = v_trace_1367_;
v_buildTime_1357_ = v_buildTime_1368_;
goto v___jp_1352_;
}
else
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1444_ = lean_box(0);
v___x_1445_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1446_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1342_, v___x_1444_, v___x_1445_);
v___x_1447_ = l_Lake_BuildMetadata_writeFile(v___x_1375_, v___x_1446_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_dec_ref_known(v___x_1447_, 1);
lean_del_object(v___x_1370_);
v_log_1353_ = v_log_1364_;
v_action_1354_ = v___x_1373_;
v_wantsRebuild_1355_ = v_noBuild_1372_;
v_trace_1356_ = v_trace_1367_;
v_buildTime_1357_ = v_buildTime_1368_;
goto v___jp_1352_;
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
v___x_1449_ = lean_io_error_to_string(v_a_1448_);
v___x_1450_ = 3;
v___x_1451_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set_uint8(v___x_1451_, sizeof(void*)*1, v___x_1450_);
v___x_1452_ = lean_array_get_size(v_log_1364_);
v___x_1453_ = lean_array_push(v_log_1364_, v___x_1451_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1453_);
v___x_1455_ = v___x_1370_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_trace_1367_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_buildTime_1368_);
v___x_1455_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; 
lean_ctor_set_uint8(v___x_1455_, sizeof(void*)*3, v___x_1373_);
lean_ctor_set_uint8(v___x_1455_, sizeof(void*)*3 + 1, v_noBuild_1372_);
v___x_1456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1452_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
return v___x_1456_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___boxed(lean_object* v_url_1459_, lean_object* v_archiveFile_1460_, lean_object* v_headers_1461_, lean_object* v_depTrace_1462_, lean_object* v_traceFile_1463_, lean_object* v_action_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
uint8_t v_action_boxed_1468_; lean_object* v_res_1469_; 
v_action_boxed_1468_ = lean_unbox(v_action_1464_);
v_res_1469_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1459_, v_archiveFile_1460_, v_headers_1461_, v_depTrace_1462_, v_traceFile_1463_, v_action_boxed_1468_, v_a_1465_, v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec_ref(v_depTrace_1462_);
lean_dec_ref(v_headers_1461_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(lean_object* v_url_1470_, lean_object* v_archiveFile_1471_, lean_object* v_headers_1472_, lean_object* v_a_1473_, lean_object* v_depTrace_1474_, lean_object* v_traceFile_1475_, uint8_t v_action_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1470_, v_archiveFile_1471_, v_headers_1472_, v_depTrace_1474_, v_traceFile_1475_, v_action_1476_, v_a_1480_, v_a_1481_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___boxed(lean_object* v_url_1484_, lean_object* v_archiveFile_1485_, lean_object* v_headers_1486_, lean_object* v_a_1487_, lean_object* v_depTrace_1488_, lean_object* v_traceFile_1489_, lean_object* v_action_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_){
_start:
{
uint8_t v_action_boxed_1497_; lean_object* v_res_1498_; 
v_action_boxed_1497_ = lean_unbox(v_action_1490_);
v_res_1498_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(v_url_1484_, v_archiveFile_1485_, v_headers_1486_, v_a_1487_, v_depTrace_1488_, v_traceFile_1489_, v_action_boxed_1497_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_depTrace_1488_);
lean_dec_ref(v_a_1487_);
lean_dec_ref(v_headers_1486_);
return v_res_1498_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
if (lean_obj_tag(v_x_1499_) == 0)
{
if (lean_obj_tag(v_x_1500_) == 0)
{
uint8_t v___x_1501_; 
v___x_1501_ = 1;
return v___x_1501_;
}
else
{
uint8_t v___x_1502_; 
v___x_1502_ = 0;
return v___x_1502_;
}
}
else
{
if (lean_obj_tag(v_x_1500_) == 0)
{
uint8_t v___x_1503_; 
v___x_1503_ = 0;
return v___x_1503_;
}
else
{
lean_object* v_val_1504_; lean_object* v_val_1505_; uint64_t v___x_1506_; uint64_t v___x_1507_; uint8_t v___x_1508_; 
v_val_1504_ = lean_ctor_get(v_x_1499_, 0);
v_val_1505_ = lean_ctor_get(v_x_1500_, 0);
v___x_1506_ = lean_unbox_uint64(v_val_1504_);
v___x_1507_ = lean_unbox_uint64(v_val_1505_);
v___x_1508_ = lean_uint64_dec_eq(v___x_1506_, v___x_1507_);
return v___x_1508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(lean_object* v_x_1509_, lean_object* v_x_1510_){
_start:
{
uint8_t v_res_1511_; lean_object* v_r_1512_; 
v_res_1511_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v_x_1509_, v_x_1510_);
lean_dec(v_x_1510_);
lean_dec(v_x_1509_);
v_r_1512_ = lean_box(v_res_1511_);
return v_r_1512_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object* v_info_1513_, lean_object* v_self_1514_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_io_metadata(v_info_1513_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v_modified_1518_; uint8_t v___x_1519_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v_modified_1518_ = lean_ctor_get(v_a_1517_, 1);
lean_inc_ref(v_modified_1518_);
lean_dec(v_a_1517_);
v___x_1519_ = l_IO_FS_instOrdSystemTime_ord(v_self_1514_, v_modified_1518_);
lean_dec_ref(v_modified_1518_);
if (v___x_1519_ == 0)
{
uint8_t v___x_1520_; 
v___x_1520_ = 1;
return v___x_1520_;
}
else
{
uint8_t v___x_1521_; 
v___x_1521_ = 0;
return v___x_1521_;
}
}
else
{
uint8_t v___x_1522_; 
lean_dec_ref_known(v___x_1516_, 1);
v___x_1522_ = 0;
return v___x_1522_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object* v_info_1523_, lean_object* v_self_1524_, lean_object* v_a_1525_){
_start:
{
uint8_t v_res_1526_; lean_object* v_r_1527_; 
v_res_1526_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1523_, v_self_1524_);
lean_dec_ref(v_self_1524_);
lean_dec_ref(v_info_1523_);
v_r_1527_ = lean_box(v_res_1526_);
return v_r_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(lean_object* v_info_1528_, lean_object* v_depTrace_1529_, lean_object* v_depHash_1530_, lean_object* v_oldTrace_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
uint64_t v_hash_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_hash_1535_ = lean_ctor_get_uint64(v_depTrace_1529_, sizeof(void*)*3);
v___x_1536_ = lean_box_uint64(v_hash_1535_);
v___x_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
v___x_1538_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v___x_1537_, v_depHash_1530_);
lean_dec_ref_known(v___x_1537_, 1);
if (v___x_1538_ == 0)
{
lean_object* v_toBuildConfig_1539_; uint8_t v_oldMode_1540_; 
v_toBuildConfig_1539_ = lean_ctor_get(v_a_1532_, 0);
v_oldMode_1540_ = lean_ctor_get_uint8(v_toBuildConfig_1539_, sizeof(void*)*4);
if (v_oldMode_1540_ == 0)
{
uint8_t v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1541_ = 0;
v___x_1542_ = lean_box(v___x_1541_);
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v_a_1533_);
return v___x_1543_;
}
else
{
uint8_t v___x_1544_; 
v___x_1544_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1528_, v_oldTrace_1531_);
if (v___x_1544_ == 0)
{
uint8_t v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = 0;
v___x_1546_ = lean_box(v___x_1545_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v_a_1533_);
return v___x_1547_;
}
else
{
uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = 1;
v___x_1549_ = lean_box(v___x_1548_);
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v_a_1533_);
return v___x_1550_;
}
}
}
else
{
uint8_t v___x_1551_; 
v___x_1551_ = l_System_FilePath_pathExists(v_info_1528_);
if (v___x_1551_ == 0)
{
uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = 0;
v___x_1553_ = lean_box(v___x_1552_);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v_a_1533_);
return v___x_1554_;
}
else
{
uint8_t v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = 2;
v___x_1556_ = lean_box(v___x_1555_);
v___x_1557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v_a_1533_);
return v___x_1557_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(lean_object* v_info_1558_, lean_object* v_depTrace_1559_, lean_object* v_depHash_1560_, lean_object* v_oldTrace_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1558_, v_depTrace_1559_, v_depHash_1560_, v_oldTrace_1561_, v_a_1562_, v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec_ref(v_oldTrace_1561_);
lean_dec(v_depHash_1560_);
lean_dec_ref(v_depTrace_1559_);
lean_dec_ref(v_info_1558_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(lean_object* v_a_1566_, lean_object* v_info_1567_, lean_object* v_depTrace_1568_, lean_object* v_savedTrace_1569_, lean_object* v_oldTrace_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
if (lean_obj_tag(v_savedTrace_1569_) == 2)
{
lean_object* v_data_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1627_; 
v_data_1577_ = lean_ctor_get(v_savedTrace_1569_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_savedTrace_1569_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1579_ = v_savedTrace_1569_;
v_isShared_1580_ = v_isSharedCheck_1627_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_data_1577_);
lean_dec(v_savedTrace_1569_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1627_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
uint64_t v_depHash_1581_; lean_object* v_log_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v_depHash_1581_ = lean_ctor_get_uint64(v_data_1577_, sizeof(void*)*3);
v_log_1582_ = lean_ctor_get(v_data_1577_, 2);
lean_inc_ref(v_log_1582_);
lean_dec_ref(v_data_1577_);
v___x_1583_ = lean_box_uint64(v_depHash_1581_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 1);
lean_ctor_set(v___x_1579_, 0, v___x_1583_);
v___x_1585_ = v___x_1579_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; lean_object* v_a_1587_; lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1625_; 
v___x_1586_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1567_, v_depTrace_1568_, v___x_1585_, v_oldTrace_1570_, v_a_1574_, v_a_1575_);
lean_dec_ref(v___x_1585_);
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
v_a_1588_ = lean_ctor_get(v___x_1586_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1590_ = v___x_1586_;
v_isShared_1591_ = v_isSharedCheck_1625_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_inc(v_a_1587_);
lean_dec(v___x_1586_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1625_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___y_1593_; uint8_t v___x_1597_; uint8_t v___x_1598_; uint8_t v___x_1599_; 
v___x_1597_ = 0;
v___x_1598_ = lean_unbox(v_a_1587_);
v___x_1599_ = l_Lake_instDecidableEqOutputStatus(v___x_1598_, v___x_1597_);
if (v___x_1599_ == 0)
{
lean_object* v_log_1600_; uint8_t v_action_1601_; uint8_t v_wantsRebuild_1602_; lean_object* v_trace_1603_; lean_object* v_buildTime_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1624_; 
v_log_1600_ = lean_ctor_get(v_a_1588_, 0);
v_action_1601_ = lean_ctor_get_uint8(v_a_1588_, sizeof(void*)*3);
v_wantsRebuild_1602_ = lean_ctor_get_uint8(v_a_1588_, sizeof(void*)*3 + 1);
v_trace_1603_ = lean_ctor_get(v_a_1588_, 1);
v_buildTime_1604_ = lean_ctor_get(v_a_1588_, 2);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_a_1588_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1606_ = v_a_1588_;
v_isShared_1607_ = v_isSharedCheck_1624_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_buildTime_1604_);
lean_inc(v_trace_1603_);
lean_inc(v_log_1600_);
lean_dec(v_a_1588_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1624_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
uint8_t v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1611_; 
v___x_1608_ = 2;
v___x_1609_ = l_Lake_JobAction_merge(v_action_1601_, v___x_1608_);
if (v_isShared_1607_ == 0)
{
v___x_1611_ = v___x_1606_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_log_1600_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_trace_1603_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_buildTime_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1623_, sizeof(void*)*3 + 1, v_wantsRebuild_1602_);
v___x_1611_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; 
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3, v___x_1609_);
v___x_1612_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1582_, v_a_1566_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v___x_1611_);
lean_dec_ref(v_log_1582_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 1);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1612_, 2);
v___y_1593_ = v_a_1613_;
goto v___jp_1592_;
}
else
{
lean_object* v_a_1614_; lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_del_object(v___x_1590_);
lean_dec(v_a_1587_);
v_a_1614_ = lean_ctor_get(v___x_1612_, 0);
v_a_1615_ = lean_ctor_get(v___x_1612_, 1);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1612_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_inc(v_a_1614_);
lean_dec(v___x_1612_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1614_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_1582_);
v___y_1593_ = v_a_1588_;
goto v___jp_1592_;
}
v___jp_1592_:
{
lean_object* v___x_1595_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 1, v___y_1593_);
v___x_1595_ = v___x_1590_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1587_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v___y_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_1628_; uint8_t v_oldMode_1629_; 
lean_dec(v_savedTrace_1569_);
v_toBuildConfig_1628_ = lean_ctor_get(v_a_1574_, 0);
v_oldMode_1629_ = lean_ctor_get_uint8(v_toBuildConfig_1628_, sizeof(void*)*4);
if (v_oldMode_1629_ == 0)
{
uint8_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = 0;
v___x_1631_ = lean_box(v___x_1630_);
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v_a_1575_);
return v___x_1632_;
}
else
{
uint8_t v___x_1633_; 
v___x_1633_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1567_, v_oldTrace_1570_);
if (v___x_1633_ == 0)
{
uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = 0;
v___x_1635_ = lean_box(v___x_1634_);
v___x_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v_a_1575_);
return v___x_1636_;
}
else
{
uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = 1;
v___x_1638_ = lean_box(v___x_1637_);
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v_a_1575_);
return v___x_1639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object* v_a_1640_, lean_object* v_info_1641_, lean_object* v_depTrace_1642_, lean_object* v_savedTrace_1643_, lean_object* v_oldTrace_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_1640_, v_info_1641_, v_depTrace_1642_, v_savedTrace_1643_, v_oldTrace_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_oldTrace_1644_);
lean_dec_ref(v_depTrace_1642_);
lean_dec_ref(v_info_1641_);
lean_dec_ref(v_a_1640_);
return v_res_1651_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = lean_unsigned_to_nat(0u);
v___x_1657_ = lean_nat_to_int(v___x_1656_);
return v___x_1657_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4(void){
_start:
{
uint32_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = 0;
v___x_1659_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3);
v___x_1660_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
lean_ctor_set_uint32(v___x_1660_, sizeof(void*)*1, v___x_1658_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(lean_object* v_self_1661_, lean_object* v_url_1662_, lean_object* v_archiveFile_1663_, lean_object* v_headers_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_a_1673_; lean_object* v_a_1674_; lean_object* v___y_1677_; uint8_t v___y_1678_; uint8_t v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; uint8_t v_a_1708_; lean_object* v_a_1709_; lean_object* v_log_1728_; uint8_t v_action_1729_; uint8_t v_wantsRebuild_1730_; lean_object* v_trace_1731_; lean_object* v_buildTime_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1771_; 
v_log_1728_ = lean_ctor_get(v_a_1670_, 0);
v_action_1729_ = lean_ctor_get_uint8(v_a_1670_, sizeof(void*)*3);
v_wantsRebuild_1730_ = lean_ctor_get_uint8(v_a_1670_, sizeof(void*)*3 + 1);
v_trace_1731_ = lean_ctor_get(v_a_1670_, 1);
v_buildTime_1732_ = lean_ctor_get(v_a_1670_, 2);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_a_1670_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1734_ = v_a_1670_;
v_isShared_1735_ = v_isSharedCheck_1771_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_buildTime_1732_);
lean_inc(v_trace_1731_);
lean_inc(v_log_1728_);
lean_dec(v_a_1670_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1771_;
goto v_resetjp_1733_;
}
v___jp_1672_:
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_a_1673_);
lean_ctor_set(v___x_1675_, 1, v_a_1674_);
return v___x_1675_;
}
v___jp_1676_:
{
uint8_t v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; uint8_t v___x_1686_; 
v___x_1683_ = 1;
v___x_1684_ = l_Lake_untar(v_archiveFile_1663_, v___y_1677_, v___x_1683_, v___y_1681_);
v___x_1685_ = 3;
v___x_1686_ = l_Lake_JobAction_merge(v___y_1679_, v___x_1685_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1687_; lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1696_; 
v_a_1687_ = lean_ctor_get(v___x_1684_, 0);
v_a_1688_ = lean_ctor_get(v___x_1684_, 1);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1690_ = v___x_1684_;
v_isShared_1691_ = v_isSharedCheck_1696_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_inc(v_a_1687_);
lean_dec(v___x_1684_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1696_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1692_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1692_, 0, v_a_1688_);
lean_ctor_set(v___x_1692_, 1, v___y_1682_);
lean_ctor_set(v___x_1692_, 2, v___y_1680_);
lean_ctor_set_uint8(v___x_1692_, sizeof(void*)*3, v___x_1686_);
lean_ctor_set_uint8(v___x_1692_, sizeof(void*)*3 + 1, v___y_1678_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 1, v___x_1692_);
v___x_1694_ = v___x_1690_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1687_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1706_; 
v_a_1697_ = lean_ctor_get(v___x_1684_, 0);
v_a_1698_ = lean_ctor_get(v___x_1684_, 1);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1700_ = v___x_1684_;
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_inc(v_a_1697_);
lean_dec(v___x_1684_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1702_, 0, v_a_1698_);
lean_ctor_set(v___x_1702_, 1, v___y_1682_);
lean_ctor_set(v___x_1702_, 2, v___y_1680_);
lean_ctor_set_uint8(v___x_1702_, sizeof(void*)*3, v___x_1686_);
lean_ctor_set_uint8(v___x_1702_, sizeof(void*)*3 + 1, v___y_1678_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1697_);
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
v___jp_1707_:
{
lean_object* v_config_1710_; lean_object* v_dir_1711_; lean_object* v_buildDir_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v_config_1710_ = lean_ctor_get(v_self_1661_, 6);
lean_inc_ref(v_config_1710_);
v_dir_1711_ = lean_ctor_get(v_self_1661_, 4);
lean_inc_ref(v_dir_1711_);
lean_dec_ref(v_self_1661_);
v_buildDir_1712_ = lean_ctor_get(v_config_1710_, 5);
lean_inc_ref(v_buildDir_1712_);
lean_dec_ref(v_config_1710_);
v___x_1713_ = l_System_FilePath_normalize(v_buildDir_1712_);
v___x_1714_ = l_Lake_joinRelative(v_dir_1711_, v___x_1713_);
v___x_1715_ = l_System_FilePath_pathExists(v___x_1714_);
if (v_a_1708_ == 0)
{
lean_object* v_log_1716_; uint8_t v_action_1717_; uint8_t v_wantsRebuild_1718_; lean_object* v_trace_1719_; lean_object* v_buildTime_1720_; 
v_log_1716_ = lean_ctor_get(v_a_1709_, 0);
lean_inc_ref(v_log_1716_);
v_action_1717_ = lean_ctor_get_uint8(v_a_1709_, sizeof(void*)*3);
v_wantsRebuild_1718_ = lean_ctor_get_uint8(v_a_1709_, sizeof(void*)*3 + 1);
v_trace_1719_ = lean_ctor_get(v_a_1709_, 1);
lean_inc_ref(v_trace_1719_);
v_buildTime_1720_ = lean_ctor_get(v_a_1709_, 2);
lean_inc(v_buildTime_1720_);
lean_dec_ref(v_a_1709_);
v___y_1677_ = v___x_1714_;
v___y_1678_ = v_wantsRebuild_1718_;
v___y_1679_ = v_action_1717_;
v___y_1680_ = v_buildTime_1720_;
v___y_1681_ = v_log_1716_;
v___y_1682_ = v_trace_1719_;
goto v___jp_1676_;
}
else
{
if (v___x_1715_ == 0)
{
lean_object* v_log_1721_; uint8_t v_action_1722_; uint8_t v_wantsRebuild_1723_; lean_object* v_trace_1724_; lean_object* v_buildTime_1725_; 
v_log_1721_ = lean_ctor_get(v_a_1709_, 0);
lean_inc_ref(v_log_1721_);
v_action_1722_ = lean_ctor_get_uint8(v_a_1709_, sizeof(void*)*3);
v_wantsRebuild_1723_ = lean_ctor_get_uint8(v_a_1709_, sizeof(void*)*3 + 1);
v_trace_1724_ = lean_ctor_get(v_a_1709_, 1);
lean_inc_ref(v_trace_1724_);
v_buildTime_1725_ = lean_ctor_get(v_a_1709_, 2);
lean_inc(v_buildTime_1725_);
lean_dec_ref(v_a_1709_);
v___y_1677_ = v___x_1714_;
v___y_1678_ = v_wantsRebuild_1723_;
v___y_1679_ = v_action_1722_;
v___y_1680_ = v_buildTime_1725_;
v___y_1681_ = v_log_1721_;
v___y_1682_ = v_trace_1724_;
goto v___jp_1676_;
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec_ref(v___x_1714_);
lean_dec_ref(v_archiveFile_1663_);
v___x_1726_ = lean_box(0);
v___x_1727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
lean_ctor_set(v___x_1727_, 1, v_a_1709_);
return v___x_1727_;
}
}
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v_traceFile_1737_; lean_object* v___x_1738_; 
v___x_1736_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0));
lean_inc_ref(v_archiveFile_1663_);
v_traceFile_1737_ = l_System_FilePath_addExtension(v_archiveFile_1663_, v___x_1736_);
lean_inc_ref(v_traceFile_1737_);
v___x_1738_ = l_Lake_readTraceFile(v_traceFile_1737_, v_log_1728_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v_a_1740_; lean_object* v___x_1741_; uint64_t v___x_1742_; uint64_t v___x_1743_; uint64_t v_depTrace_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
v_a_1740_ = lean_ctor_get(v___x_1738_, 1);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1738_, 2);
v___x_1741_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1));
v___x_1742_ = l_Lake_Hash_nil;
v___x_1743_ = lean_string_hash(v_url_1662_);
v_depTrace_1744_ = lean_uint64_mix_hash(v___x_1742_, v___x_1743_);
v___x_1745_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2));
v___x_1746_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
v___x_1747_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1747_, 0, v___x_1745_);
lean_ctor_set(v___x_1747_, 1, v___x_1741_);
lean_ctor_set(v___x_1747_, 2, v___x_1746_);
lean_ctor_set_uint64(v___x_1747_, sizeof(void*)*3, v_depTrace_1744_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v_a_1740_);
v___x_1749_ = v___x_1734_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1740_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_trace_1731_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v_buildTime_1732_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, sizeof(void*)*3, v_action_1729_);
lean_ctor_set_uint8(v_reuseFailAlloc_1765_, sizeof(void*)*3 + 1, v_wantsRebuild_1730_);
v___x_1749_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_1665_, v_archiveFile_1663_, v___x_1747_, v_a_1739_, v___x_1746_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v___x_1749_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v_a_1752_; uint8_t v___x_1753_; uint8_t v___x_1754_; uint8_t v___x_1755_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
v_a_1752_ = lean_ctor_get(v___x_1750_, 1);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1750_, 2);
v___x_1753_ = 0;
v___x_1754_ = lean_unbox(v_a_1751_);
lean_dec(v_a_1751_);
v___x_1755_ = l_Lake_instDecidableEqOutputStatus(v___x_1754_, v___x_1753_);
if (v___x_1755_ == 0)
{
uint8_t v___x_1756_; 
lean_dec_ref_known(v___x_1747_, 3);
lean_dec_ref(v_traceFile_1737_);
lean_dec_ref(v_url_1662_);
v___x_1756_ = 1;
v_a_1708_ = v___x_1756_;
v_a_1709_ = v_a_1752_;
goto v___jp_1707_;
}
else
{
uint8_t v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = 4;
lean_inc_ref(v_archiveFile_1663_);
v___x_1758_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1662_, v_archiveFile_1663_, v_headers_1664_, v___x_1747_, v_traceFile_1737_, v___x_1757_, v_a_1669_, v_a_1752_);
lean_dec_ref_known(v___x_1747_, 3);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; uint8_t v___x_1760_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 1);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 2);
v___x_1760_ = 0;
v_a_1708_ = v___x_1760_;
v_a_1709_ = v_a_1759_;
goto v___jp_1707_;
}
else
{
lean_object* v_a_1761_; lean_object* v_a_1762_; 
lean_dec_ref(v_archiveFile_1663_);
lean_dec_ref(v_self_1661_);
v_a_1761_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1761_);
v_a_1762_ = lean_ctor_get(v___x_1758_, 1);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1758_, 2);
v_a_1673_ = v_a_1761_;
v_a_1674_ = v_a_1762_;
goto v___jp_1672_;
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v_a_1764_; 
lean_dec_ref_known(v___x_1747_, 3);
lean_dec_ref(v_traceFile_1737_);
lean_dec_ref(v_archiveFile_1663_);
lean_dec_ref(v_url_1662_);
lean_dec_ref(v_self_1661_);
v_a_1763_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1763_);
v_a_1764_ = lean_ctor_get(v___x_1750_, 1);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1750_, 2);
v_a_1673_ = v_a_1763_;
v_a_1674_ = v_a_1764_;
goto v___jp_1672_;
}
}
}
else
{
lean_object* v_a_1766_; lean_object* v_a_1767_; lean_object* v___x_1769_; 
lean_dec_ref(v_traceFile_1737_);
lean_dec_ref(v_archiveFile_1663_);
lean_dec_ref(v_url_1662_);
lean_dec_ref(v_self_1661_);
v_a_1766_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1766_);
v_a_1767_ = lean_ctor_get(v___x_1738_, 1);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1738_, 2);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v_a_1767_);
v___x_1769_ = v___x_1734_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1767_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_trace_1731_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_buildTime_1732_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*3, v_action_1729_);
lean_ctor_set_uint8(v_reuseFailAlloc_1770_, sizeof(void*)*3 + 1, v_wantsRebuild_1730_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
v_a_1673_ = v_a_1766_;
v_a_1674_ = v___x_1769_;
goto v___jp_1672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object* v_self_1772_, lean_object* v_url_1773_, lean_object* v_archiveFile_1774_, lean_object* v_headers_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_self_1772_, v_url_1773_, v_archiveFile_1774_, v_headers_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
lean_dec_ref(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec_ref(v_headers_1775_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object* v_a_1784_, lean_object* v_info_1785_, lean_object* v_depTrace_1786_, lean_object* v_depHash_1787_, lean_object* v_oldTrace_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1785_, v_depTrace_1786_, v_depHash_1787_, v_oldTrace_1788_, v_a_1792_, v_a_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object* v_a_1796_, lean_object* v_info_1797_, lean_object* v_depTrace_1798_, lean_object* v_depHash_1799_, lean_object* v_oldTrace_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_1796_, v_info_1797_, v_depTrace_1798_, v_depHash_1799_, v_oldTrace_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
lean_dec_ref(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_oldTrace_1800_);
lean_dec(v_depHash_1799_);
lean_dec_ref(v_depTrace_1798_);
lean_dec_ref(v_info_1797_);
lean_dec_ref(v_a_1796_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_getUrl_1808_, lean_object* v_pkg_1809_, lean_object* v_archiveFile_1810_, lean_object* v_headers_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
uint8_t v_r_1820_; lean_object* v___y_1821_; lean_object* v_a_1825_; lean_object* v___x_1841_; 
lean_inc_ref(v___y_1816_);
lean_inc(v___y_1815_);
lean_inc(v___y_1814_);
lean_inc(v___y_1813_);
lean_inc_ref(v___y_1812_);
lean_inc_ref(v_pkg_1809_);
v___x_1841_ = lean_apply_8(v_getUrl_1808_, v_pkg_1809_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, lean_box(0));
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v_a_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
v_a_1843_ = lean_ctor_get(v___x_1841_, 1);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1841_, 2);
lean_inc_ref(v_pkg_1809_);
v___x_1844_ = lean_apply_1(v_archiveFile_1810_, v_pkg_1809_);
v___x_1845_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_1809_, v_a_1842_, v___x_1844_, v_headers_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v_a_1843_);
lean_dec_ref(v___y_1812_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; uint8_t v___x_1847_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 1);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 2);
v___x_1847_ = 1;
v_r_1820_ = v___x_1847_;
v___y_1821_ = v_a_1846_;
goto v___jp_1819_;
}
else
{
lean_object* v_a_1848_; 
v_a_1848_ = lean_ctor_get(v___x_1845_, 1);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1845_, 2);
v_a_1825_ = v_a_1848_;
goto v___jp_1824_;
}
}
else
{
lean_object* v_a_1849_; 
lean_dec_ref(v___y_1812_);
lean_dec_ref(v_archiveFile_1810_);
lean_dec_ref(v_pkg_1809_);
v_a_1849_ = lean_ctor_get(v___x_1841_, 1);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1841_, 2);
v_a_1825_ = v_a_1849_;
goto v___jp_1824_;
}
v___jp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_box(v_r_1820_);
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v___y_1821_);
return v___x_1823_;
}
v___jp_1824_:
{
lean_object* v_log_1826_; uint8_t v_action_1827_; uint8_t v_wantsRebuild_1828_; lean_object* v_trace_1829_; lean_object* v_buildTime_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1840_; 
v_log_1826_ = lean_ctor_get(v_a_1825_, 0);
v_action_1827_ = lean_ctor_get_uint8(v_a_1825_, sizeof(void*)*3);
v_wantsRebuild_1828_ = lean_ctor_get_uint8(v_a_1825_, sizeof(void*)*3 + 1);
v_trace_1829_ = lean_ctor_get(v_a_1825_, 1);
v_buildTime_1830_ = lean_ctor_get(v_a_1825_, 2);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_a_1825_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1832_ = v_a_1825_;
v_isShared_1833_ = v_isSharedCheck_1840_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_buildTime_1830_);
lean_inc(v_trace_1829_);
lean_inc(v_log_1826_);
lean_dec(v_a_1825_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1840_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
uint8_t v___x_1834_; uint8_t v___x_1835_; lean_object* v___x_1837_; 
v___x_1834_ = 4;
v___x_1835_ = l_Lake_JobAction_merge(v_action_1827_, v___x_1834_);
if (v_isShared_1833_ == 0)
{
v___x_1837_ = v___x_1832_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_log_1826_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_trace_1829_);
lean_ctor_set(v_reuseFailAlloc_1839_, 2, v_buildTime_1830_);
lean_ctor_set_uint8(v_reuseFailAlloc_1839_, sizeof(void*)*3 + 1, v_wantsRebuild_1828_);
v___x_1837_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
uint8_t v___x_1838_; 
lean_ctor_set_uint8(v___x_1837_, sizeof(void*)*3, v___x_1835_);
v___x_1838_ = 0;
v_r_1820_ = v___x_1838_;
v___y_1821_ = v___x_1837_;
goto v___jp_1819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_getUrl_1850_, lean_object* v_pkg_1851_, lean_object* v_archiveFile_1852_, lean_object* v_headers_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(v_getUrl_1850_, v_pkg_1851_, v_archiveFile_1852_, v_headers_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v_headers_1853_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* v_getUrl_1862_, lean_object* v_archiveFile_1863_, lean_object* v_headers_1864_, lean_object* v___x_1865_, lean_object* v_facet_1866_, lean_object* v_pkg_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___f_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
lean_inc_ref(v_pkg_1867_);
v___f_1875_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1875_, 0, v_getUrl_1862_);
lean_closure_set(v___f_1875_, 1, v_pkg_1867_);
lean_closure_set(v___f_1875_, 2, v_archiveFile_1863_);
lean_closure_set(v___f_1875_, 3, v_headers_1864_);
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_1865_);
v___x_1878_ = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(v___x_1878_, 0, lean_box(0));
lean_closure_set(v___x_1878_, 1, v___x_1865_);
lean_closure_set(v___x_1878_, 2, v___f_1875_);
lean_closure_set(v___x_1878_, 3, v___x_1876_);
lean_closure_set(v___x_1878_, 4, v___x_1877_);
v___x_1879_ = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM___boxed), 9, 2);
lean_closure_set(v___x_1879_, 0, lean_box(0));
lean_closure_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM___boxed), 9, 2);
lean_closure_set(v___x_1880_, 0, lean_box(0));
lean_closure_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = l_Lake_ensureJob___redArg(v___x_1865_, v___x_1880_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1914_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_a_1883_ = lean_ctor_get(v___x_1881_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1885_ = v___x_1881_;
v_isShared_1886_ = v_isSharedCheck_1914_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1914_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_task_1887_; lean_object* v_kind_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1912_; 
v_task_1887_ = lean_ctor_get(v_a_1882_, 0);
v_kind_1888_ = lean_ctor_get(v_a_1882_, 1);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_a_1882_);
if (v_isSharedCheck_1912_ == 0)
{
lean_object* v_unused_1913_; 
v_unused_1913_ = lean_ctor_get(v_a_1882_, 2);
lean_dec(v_unused_1913_);
v___x_1890_ = v_a_1882_;
v_isShared_1891_ = v_isSharedCheck_1912_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_kind_1888_);
lean_inc(v_task_1887_);
lean_dec(v_a_1882_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1912_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v_registeredJobs_1892_; lean_object* v___x_1893_; lean_object* v_baseName_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v_job_1903_; 
v_registeredJobs_1892_ = lean_ctor_get(v___y_1872_, 3);
v___x_1893_ = lean_st_ref_take(v_registeredJobs_1892_);
v_baseName_1894_ = lean_ctor_get(v_pkg_1867_, 1);
lean_inc(v_baseName_1894_);
lean_dec_ref(v_pkg_1867_);
v___x_1895_ = 1;
v___x_1896_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1894_, v___x_1895_);
v___x_1897_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1898_ = lean_string_append(v___x_1896_, v___x_1897_);
v___x_1899_ = l_Lake_Name_eraseHead(v_facet_1866_);
v___x_1900_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1899_, v___x_1895_);
v___x_1901_ = lean_string_append(v___x_1898_, v___x_1900_);
lean_dec_ref(v___x_1900_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 2, v___x_1901_);
v_job_1903_ = v___x_1890_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_task_1887_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v_kind_1888_);
lean_ctor_set(v_reuseFailAlloc_1911_, 2, v___x_1901_);
v_job_1903_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
lean_ctor_set_uint8(v_job_1903_, sizeof(void*)*3, v___x_1895_);
lean_inc_ref(v_job_1903_);
v___x_1904_ = l_Lake_Job_toOpaque___redArg(v_job_1903_);
v___x_1905_ = lean_array_push(v___x_1893_, v___x_1904_);
v___x_1906_ = lean_st_ref_set(v_registeredJobs_1892_, v___x_1905_);
v___x_1907_ = l_Lake_Job_renew___redArg(v_job_1903_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1907_);
v___x_1909_ = v___x_1885_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_a_1883_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_1867_);
lean_dec(v_facet_1866_);
return v___x_1881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v_getUrl_1915_, lean_object* v_archiveFile_1916_, lean_object* v_headers_1917_, lean_object* v___x_1918_, lean_object* v_facet_1919_, lean_object* v_pkg_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_1915_, v_archiveFile_1916_, v_headers_1917_, v___x_1918_, v_facet_1919_, v_pkg_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec(v___y_1922_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object* v_facet_1936_, lean_object* v_archiveFile_1937_, lean_object* v_getUrl_1938_, lean_object* v_headers_1939_){
_start:
{
lean_object* v___x_1940_; lean_object* v___f_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1940_ = l_Lake_instDataKindBool;
v___f_1941_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_1941_, 0, v_getUrl_1938_);
lean_closure_set(v___f_1941_, 1, v_archiveFile_1937_);
lean_closure_set(v___f_1941_, 2, v_headers_1939_);
lean_closure_set(v___f_1941_, 3, v___x_1940_);
lean_closure_set(v___f_1941_, 4, v_facet_1936_);
v___x_1942_ = l_Lake_Package_keyword;
v___x_1943_ = 1;
v___x_1944_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_1945_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1945_, 0, v___x_1942_);
lean_ctor_set(v___x_1945_, 1, v___f_1941_);
lean_ctor_set(v___x_1945_, 2, v___x_1940_);
lean_ctor_set(v___x_1945_, 3, v___x_1944_);
lean_ctor_set_uint8(v___x_1945_, sizeof(void*)*4, v___x_1943_);
lean_ctor_set_uint8(v___x_1945_, sizeof(void*)*4 + 1, v___x_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* v_facet_1946_, lean_object* v_archiveFile_1947_, lean_object* v_getUrl_1948_, lean_object* v_headers_1949_, lean_object* v_inst_1950_){
_start:
{
lean_object* v___x_1951_; lean_object* v___f_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1951_ = l_Lake_instDataKindBool;
v___f_1952_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_1952_, 0, v_getUrl_1948_);
lean_closure_set(v___f_1952_, 1, v_archiveFile_1947_);
lean_closure_set(v___f_1952_, 2, v_headers_1949_);
lean_closure_set(v___f_1952_, 3, v___x_1951_);
lean_closure_set(v___f_1952_, 4, v_facet_1946_);
v___x_1953_ = l_Lake_Package_keyword;
v___x_1954_ = 1;
v___x_1955_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_1956_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1956_, 0, v___x_1953_);
lean_ctor_set(v___x_1956_, 1, v___f_1952_);
lean_ctor_set(v___x_1956_, 2, v___x_1951_);
lean_ctor_set(v___x_1956_, 3, v___x_1955_);
lean_ctor_set_uint8(v___x_1956_, sizeof(void*)*4, v___x_1954_);
lean_ctor_set_uint8(v___x_1956_, sizeof(void*)*4 + 1, v___x_1954_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_what_1958_, lean_object* v_baseName_1959_, lean_object* v_optFacet_1960_, uint8_t v_success_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_a_1970_; lean_object* v_a_1971_; 
if (v_success_1961_ == 0)
{
lean_object* v_toBuildConfig_1992_; uint8_t v_verbosity_1993_; uint8_t v___x_1994_; uint8_t v___x_1995_; 
v_toBuildConfig_1992_ = lean_ctor_get(v___y_1966_, 0);
v_verbosity_1993_ = lean_ctor_get_uint8(v_toBuildConfig_1992_, sizeof(void*)*4 + 3);
v___x_1994_ = 2;
v___x_1995_ = l_Lake_instDecidableEqVerbosity(v_verbosity_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
lean_dec(v_optFacet_1960_);
lean_dec(v_baseName_1959_);
v___x_1996_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_1970_ = v___x_1996_;
v_a_1971_ = v___y_1967_;
goto v___jp_1969_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_1997_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1998_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1959_, v___x_1995_);
v___x_1999_ = lean_string_append(v___x_1997_, v___x_1998_);
lean_dec_ref(v___x_1998_);
v___x_2000_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2001_ = lean_string_append(v___x_1999_, v___x_2000_);
v___x_2002_ = l_Lake_Name_eraseHead(v_optFacet_1960_);
v___x_2003_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2002_, v___x_1995_);
v___x_2004_ = lean_string_append(v___x_2001_, v___x_2003_);
lean_dec_ref(v___x_2003_);
v___x_2005_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2006_ = lean_string_append(v___x_2004_, v___x_2005_);
v_a_1970_ = v___x_2006_;
v_a_1971_ = v___y_1967_;
goto v___jp_1969_;
}
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec(v_optFacet_1960_);
lean_dec(v_baseName_1959_);
v___x_2007_ = lean_box(0);
v___x_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
lean_ctor_set(v___x_2008_, 1, v___y_1967_);
return v___x_2008_;
}
v___jp_1969_:
{
lean_object* v_log_1972_; uint8_t v_action_1973_; uint8_t v_wantsRebuild_1974_; lean_object* v_trace_1975_; lean_object* v_buildTime_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1991_; 
v_log_1972_ = lean_ctor_get(v_a_1971_, 0);
v_action_1973_ = lean_ctor_get_uint8(v_a_1971_, sizeof(void*)*3);
v_wantsRebuild_1974_ = lean_ctor_get_uint8(v_a_1971_, sizeof(void*)*3 + 1);
v_trace_1975_ = lean_ctor_get(v_a_1971_, 1);
v_buildTime_1976_ = lean_ctor_get(v_a_1971_, 2);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_a_1971_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1978_ = v_a_1971_;
v_isShared_1979_ = v_isSharedCheck_1991_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_buildTime_1976_);
lean_inc(v_trace_1975_);
lean_inc(v_log_1972_);
lean_dec(v_a_1971_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1991_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1980_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0));
v___x_1981_ = lean_string_append(v___x_1980_, v_what_1958_);
v___x_1982_ = lean_string_append(v___x_1981_, v_a_1970_);
lean_dec_ref(v_a_1970_);
v___x_1983_ = 3;
v___x_1984_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set_uint8(v___x_1984_, sizeof(void*)*1, v___x_1983_);
v___x_1985_ = lean_array_get_size(v_log_1972_);
v___x_1986_ = lean_array_push(v_log_1972_, v___x_1984_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1986_);
v___x_1988_ = v___x_1978_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_trace_1975_);
lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_buildTime_1976_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, sizeof(void*)*3, v_action_1973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1990_, sizeof(void*)*3 + 1, v_wantsRebuild_1974_);
v___x_1988_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; 
v___x_1989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1985_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
return v___x_1989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_what_2009_, lean_object* v_baseName_2010_, lean_object* v_optFacet_2011_, lean_object* v_success_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
uint8_t v_success_boxed_2020_; lean_object* v_res_2021_; 
v_success_boxed_2020_ = lean_unbox(v_success_2012_);
v_res_2021_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(v_what_2009_, v_baseName_2010_, v_optFacet_2011_, v_success_boxed_2020_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec_ref(v_what_2009_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object* v___x_2022_, lean_object* v___x_2023_, lean_object* v___f_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v___x_2032_; 
lean_inc_ref(v___y_2025_);
lean_inc_ref(v___y_2029_);
lean_inc(v___y_2028_);
lean_inc(v___y_2027_);
lean_inc(v___y_2026_);
v___x_2032_ = lean_apply_7(v___y_2025_, v___x_2022_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, lean_box(0));
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2045_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
v_a_2034_ = lean_ctor_get(v___x_2032_, 1);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2036_ = v___x_2032_;
v_isShared_2037_ = v_isSharedCheck_2045_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_inc(v_a_2033_);
lean_dec(v___x_2032_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2045_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; uint8_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2043_; 
v___x_2038_ = lean_unsigned_to_nat(0u);
v___x_2039_ = 0;
v___x_2040_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2041_ = l_Lake_Job_mapM___redArg(v___x_2023_, v_a_2033_, v___f_2024_, v___x_2038_, v___x_2039_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___x_2040_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2041_);
v___x_2043_ = v___x_2036_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_a_2034_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec_ref(v___y_2025_);
lean_dec_ref(v___f_2024_);
lean_dec(v___x_2023_);
v_a_2046_ = lean_ctor_get(v___x_2032_, 0);
v_a_2047_ = lean_ctor_get(v___x_2032_, 1);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2032_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_inc(v_a_2046_);
lean_dec(v___x_2032_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2046_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v___x_2055_, lean_object* v___x_2056_, lean_object* v___f_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(v___x_2055_, v___x_2056_, v___f_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec(v___y_2059_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object* v_what_2066_, lean_object* v_optFacet_2067_, lean_object* v___x_2068_, lean_object* v_facet_2069_, lean_object* v_pkg_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_baseName_2078_; lean_object* v_keyName_2079_; lean_object* v___f_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___f_2084_; lean_object* v___x_2085_; 
v_baseName_2078_ = lean_ctor_get(v_pkg_2070_, 1);
lean_inc_n(v_baseName_2078_, 2);
v_keyName_2079_ = lean_ctor_get(v_pkg_2070_, 2);
lean_inc(v_optFacet_2067_);
v___f_2080_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2080_, 0, v_what_2066_);
lean_closure_set(v___f_2080_, 1, v_baseName_2078_);
lean_closure_set(v___f_2080_, 2, v_optFacet_2067_);
lean_inc(v_keyName_2079_);
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_keyName_2079_);
v___x_2082_ = l_Lake_Package_keyword;
v___x_2083_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2081_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
lean_ctor_set(v___x_2083_, 2, v_pkg_2070_);
lean_ctor_set(v___x_2083_, 3, v_optFacet_2067_);
lean_inc(v___x_2068_);
v___f_2084_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2084_, 0, v___x_2083_);
lean_closure_set(v___f_2084_, 1, v___x_2068_);
lean_closure_set(v___f_2084_, 2, v___f_2080_);
v___x_2085_ = l_Lake_ensureJob___redArg(v___x_2068_, v___f_2084_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2118_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_a_2087_ = lean_ctor_get(v___x_2085_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2089_ = v___x_2085_;
v_isShared_2090_ = v_isSharedCheck_2118_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2118_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_task_2091_; lean_object* v_kind_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2116_; 
v_task_2091_ = lean_ctor_get(v_a_2086_, 0);
v_kind_2092_ = lean_ctor_get(v_a_2086_, 1);
v_isSharedCheck_2116_ = !lean_is_exclusive(v_a_2086_);
if (v_isSharedCheck_2116_ == 0)
{
lean_object* v_unused_2117_; 
v_unused_2117_ = lean_ctor_get(v_a_2086_, 2);
lean_dec(v_unused_2117_);
v___x_2094_ = v_a_2086_;
v_isShared_2095_ = v_isSharedCheck_2116_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_kind_2092_);
lean_inc(v_task_2091_);
lean_dec(v_a_2086_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2116_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_registeredJobs_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; lean_object* v_job_2107_; 
v_registeredJobs_2096_ = lean_ctor_get(v___y_2075_, 3);
v___x_2097_ = lean_st_ref_take(v_registeredJobs_2096_);
v___x_2098_ = 1;
v___x_2099_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2078_, v___x_2098_);
v___x_2100_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2101_ = lean_string_append(v___x_2099_, v___x_2100_);
v___x_2102_ = l_Lake_Name_eraseHead(v_facet_2069_);
v___x_2103_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2102_, v___x_2098_);
v___x_2104_ = lean_string_append(v___x_2101_, v___x_2103_);
lean_dec_ref(v___x_2103_);
v___x_2105_ = 0;
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 2, v___x_2104_);
v_job_2107_ = v___x_2094_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_task_2091_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_kind_2092_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v___x_2104_);
v_job_2107_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
lean_ctor_set_uint8(v_job_2107_, sizeof(void*)*3, v___x_2105_);
lean_inc_ref(v_job_2107_);
v___x_2108_ = l_Lake_Job_toOpaque___redArg(v_job_2107_);
v___x_2109_ = lean_array_push(v___x_2097_, v___x_2108_);
v___x_2110_ = lean_st_ref_set(v_registeredJobs_2096_, v___x_2109_);
v___x_2111_ = l_Lake_Job_renew___redArg(v_job_2107_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 0, v___x_2111_);
v___x_2113_ = v___x_2089_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_a_2087_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2078_);
lean_dec(v_facet_2069_);
return v___x_2085_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object* v_what_2119_, lean_object* v_optFacet_2120_, lean_object* v___x_2121_, lean_object* v_facet_2122_, lean_object* v_pkg_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(v_what_2119_, v_optFacet_2120_, v___x_2121_, v_facet_2122_, v_pkg_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec(v___y_2125_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object* v_facet_2139_, lean_object* v_optFacet_2140_, lean_object* v_what_2141_){
_start:
{
lean_object* v___x_2142_; lean_object* v___f_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2142_ = l_Lake_instDataKindUnit;
v___f_2143_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2143_, 0, v_what_2141_);
lean_closure_set(v___f_2143_, 1, v_optFacet_2140_);
lean_closure_set(v___f_2143_, 2, v___x_2142_);
lean_closure_set(v___f_2143_, 3, v_facet_2139_);
v___x_2144_ = l_Lake_Package_keyword;
v___x_2145_ = 1;
v___x_2146_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2147_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2147_, 0, v___x_2144_);
lean_ctor_set(v___x_2147_, 1, v___f_2143_);
lean_ctor_set(v___x_2147_, 2, v___x_2142_);
lean_ctor_set(v___x_2147_, 3, v___x_2146_);
lean_ctor_set_uint8(v___x_2147_, sizeof(void*)*4, v___x_2145_);
lean_ctor_set_uint8(v___x_2147_, sizeof(void*)*4 + 1, v___x_2145_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* v_facet_2148_, lean_object* v_optFacet_2149_, lean_object* v_what_2150_, lean_object* v_inst_2151_, lean_object* v_inst_2152_){
_start:
{
lean_object* v___x_2153_; lean_object* v___f_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2153_ = l_Lake_instDataKindUnit;
v___f_2154_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2154_, 0, v_what_2150_);
lean_closure_set(v___f_2154_, 1, v_optFacet_2149_);
lean_closure_set(v___f_2154_, 2, v___x_2153_);
lean_closure_set(v___f_2154_, 3, v_facet_2148_);
v___x_2155_ = l_Lake_Package_keyword;
v___x_2156_ = 1;
v___x_2157_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2158_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2158_, 0, v___x_2155_);
lean_ctor_set(v___x_2158_, 1, v___f_2154_);
lean_ctor_set(v___x_2158_, 2, v___x_2153_);
lean_ctor_set(v___x_2158_, 3, v___x_2157_);
lean_ctor_set_uint8(v___x_2158_, sizeof(void*)*4, v___x_2156_);
lean_ctor_set_uint8(v___x_2158_, sizeof(void*)*4 + 1, v___x_2156_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* v_baseName_2160_, lean_object* v___x_2161_, uint8_t v_success_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v_a_2171_; lean_object* v_a_2172_; 
if (v_success_2162_ == 0)
{
lean_object* v_toBuildConfig_2192_; uint8_t v_verbosity_2193_; uint8_t v___x_2194_; uint8_t v___x_2195_; 
v_toBuildConfig_2192_ = lean_ctor_get(v___y_2167_, 0);
v_verbosity_2193_ = lean_ctor_get_uint8(v_toBuildConfig_2192_, sizeof(void*)*4 + 3);
v___x_2194_ = 2;
v___x_2195_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2193_, v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; 
lean_dec(v___x_2161_);
lean_dec(v_baseName_2160_);
v___x_2196_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2171_ = v___x_2196_;
v_a_2172_ = v___y_2168_;
goto v___jp_2170_;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2197_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2198_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2160_, v___x_2195_);
v___x_2199_ = lean_string_append(v___x_2197_, v___x_2198_);
lean_dec_ref(v___x_2198_);
v___x_2200_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2201_ = lean_string_append(v___x_2199_, v___x_2200_);
v___x_2202_ = l_Lake_Name_eraseHead(v___x_2161_);
v___x_2203_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2202_, v___x_2195_);
v___x_2204_ = lean_string_append(v___x_2201_, v___x_2203_);
lean_dec_ref(v___x_2203_);
v___x_2205_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2206_ = lean_string_append(v___x_2204_, v___x_2205_);
v_a_2171_ = v___x_2206_;
v_a_2172_ = v___y_2168_;
goto v___jp_2170_;
}
}
else
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec(v___x_2161_);
lean_dec(v_baseName_2160_);
v___x_2207_ = lean_box(0);
v___x_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___y_2168_);
return v___x_2208_;
}
v___jp_2170_:
{
lean_object* v_log_2173_; uint8_t v_action_2174_; uint8_t v_wantsRebuild_2175_; lean_object* v_trace_2176_; lean_object* v_buildTime_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2191_; 
v_log_2173_ = lean_ctor_get(v_a_2172_, 0);
v_action_2174_ = lean_ctor_get_uint8(v_a_2172_, sizeof(void*)*3);
v_wantsRebuild_2175_ = lean_ctor_get_uint8(v_a_2172_, sizeof(void*)*3 + 1);
v_trace_2176_ = lean_ctor_get(v_a_2172_, 1);
v_buildTime_2177_ = lean_ctor_get(v_a_2172_, 2);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_a_2172_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2179_ = v_a_2172_;
v_isShared_2180_ = v_isSharedCheck_2191_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_buildTime_2177_);
lean_inc(v_trace_2176_);
lean_inc(v_log_2173_);
lean_dec(v_a_2172_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2191_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2188_; 
v___x_2181_ = ((lean_object*)(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0));
v___x_2182_ = lean_string_append(v___x_2181_, v_a_2171_);
lean_dec_ref(v_a_2171_);
v___x_2183_ = 3;
v___x_2184_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2184_, 0, v___x_2182_);
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*1, v___x_2183_);
v___x_2185_ = lean_array_get_size(v_log_2173_);
v___x_2186_ = lean_array_push(v_log_2173_, v___x_2184_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2186_);
v___x_2188_ = v___x_2179_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2186_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v_trace_2176_);
lean_ctor_set(v_reuseFailAlloc_2190_, 2, v_buildTime_2177_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*3, v_action_2174_);
lean_ctor_set_uint8(v_reuseFailAlloc_2190_, sizeof(void*)*3 + 1, v_wantsRebuild_2175_);
v___x_2188_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2185_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
return v___x_2189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object* v_baseName_2209_, lean_object* v___x_2210_, lean_object* v_success_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
uint8_t v_success_boxed_2219_; lean_object* v_res_2220_; 
v_success_boxed_2219_ = lean_unbox(v_success_2211_);
v_res_2220_ = l_Lake_Package_buildCacheFacetConfig___lam__1(v_baseName_2209_, v___x_2210_, v_success_boxed_2219_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* v___x_2221_, lean_object* v___x_2222_, lean_object* v___x_2223_, lean_object* v_pkg_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_baseName_2232_; lean_object* v_keyName_2233_; lean_object* v___f_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___f_2238_; lean_object* v___x_2239_; 
v_baseName_2232_ = lean_ctor_get(v_pkg_2224_, 1);
lean_inc_n(v_baseName_2232_, 2);
v_keyName_2233_ = lean_ctor_get(v_pkg_2224_, 2);
lean_inc(v___x_2221_);
v___f_2234_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2234_, 0, v_baseName_2232_);
lean_closure_set(v___f_2234_, 1, v___x_2221_);
lean_inc(v_keyName_2233_);
v___x_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2235_, 0, v_keyName_2233_);
v___x_2236_ = l_Lake_Package_keyword;
v___x_2237_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2235_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
lean_ctor_set(v___x_2237_, 2, v_pkg_2224_);
lean_ctor_set(v___x_2237_, 3, v___x_2221_);
lean_inc(v___x_2222_);
v___f_2238_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2238_, 0, v___x_2237_);
lean_closure_set(v___f_2238_, 1, v___x_2222_);
lean_closure_set(v___f_2238_, 2, v___f_2234_);
v___x_2239_ = l_Lake_ensureJob___redArg(v___x_2222_, v___f_2238_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2272_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_a_2241_ = lean_ctor_get(v___x_2239_, 1);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2243_ = v___x_2239_;
v_isShared_2244_ = v_isSharedCheck_2272_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2272_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v_task_2245_; lean_object* v_kind_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2270_; 
v_task_2245_ = lean_ctor_get(v_a_2240_, 0);
v_kind_2246_ = lean_ctor_get(v_a_2240_, 1);
v_isSharedCheck_2270_ = !lean_is_exclusive(v_a_2240_);
if (v_isSharedCheck_2270_ == 0)
{
lean_object* v_unused_2271_; 
v_unused_2271_ = lean_ctor_get(v_a_2240_, 2);
lean_dec(v_unused_2271_);
v___x_2248_ = v_a_2240_;
v_isShared_2249_ = v_isSharedCheck_2270_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_kind_2246_);
lean_inc(v_task_2245_);
lean_dec(v_a_2240_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2270_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v_registeredJobs_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; lean_object* v_job_2261_; 
v_registeredJobs_2250_ = lean_ctor_get(v___y_2229_, 3);
v___x_2251_ = lean_st_ref_take(v_registeredJobs_2250_);
v___x_2252_ = 1;
v___x_2253_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2232_, v___x_2252_);
v___x_2254_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2255_ = lean_string_append(v___x_2253_, v___x_2254_);
v___x_2256_ = l_Lake_Name_eraseHead(v___x_2223_);
v___x_2257_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2256_, v___x_2252_);
v___x_2258_ = lean_string_append(v___x_2255_, v___x_2257_);
lean_dec_ref(v___x_2257_);
v___x_2259_ = 0;
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 2, v___x_2258_);
v_job_2261_ = v___x_2248_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_task_2245_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_kind_2246_);
lean_ctor_set(v_reuseFailAlloc_2269_, 2, v___x_2258_);
v_job_2261_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2267_; 
lean_ctor_set_uint8(v_job_2261_, sizeof(void*)*3, v___x_2259_);
lean_inc_ref(v_job_2261_);
v___x_2262_ = l_Lake_Job_toOpaque___redArg(v_job_2261_);
v___x_2263_ = lean_array_push(v___x_2251_, v___x_2262_);
v___x_2264_ = lean_st_ref_set(v_registeredJobs_2250_, v___x_2263_);
v___x_2265_ = l_Lake_Job_renew___redArg(v_job_2261_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2265_);
v___x_2267_ = v___x_2243_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_a_2241_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2232_);
lean_dec(v___x_2223_);
return v___x_2239_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object* v___x_2273_, lean_object* v___x_2274_, lean_object* v___x_2275_, lean_object* v_pkg_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lake_Package_buildCacheFacetConfig___lam__2(v___x_2273_, v___x_2274_, v___x_2275_, v_pkg_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec(v___y_2278_);
return v_res_2284_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___f_2288_; 
v___x_2285_ = l_Lake_Package_buildCacheFacet;
v___x_2286_ = l_Lake_instDataKindUnit;
v___x_2287_ = l_Lake_Package_optBuildCacheFacet;
v___f_2288_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2288_, 0, v___x_2287_);
lean_closure_set(v___f_2288_, 1, v___x_2286_);
lean_closure_set(v___f_2288_, 2, v___x_2285_);
return v___f_2288_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___f_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___f_2289_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2290_ = 1;
v___x_2291_ = l_Lake_instDataKindUnit;
v___f_2292_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__0, &l_Lake_Package_buildCacheFacetConfig___closed__0_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__0);
v___x_2293_ = l_Lake_Package_keyword;
v___x_2294_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v___f_2292_);
lean_ctor_set(v___x_2294_, 2, v___x_2291_);
lean_ctor_set(v___x_2294_, 3, v___f_2289_);
lean_ctor_set_uint8(v___x_2294_, sizeof(void*)*4, v___x_2290_);
lean_ctor_set_uint8(v___x_2294_, sizeof(void*)*4 + 1, v___x_2290_);
return v___x_2294_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig(void){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__1, &l_Lake_Package_buildCacheFacetConfig___closed__1_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__1);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* v_pkg_2297_, lean_object* v___x_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
uint8_t v_r_2307_; lean_object* v___y_2308_; lean_object* v_a_2312_; lean_object* v___x_2328_; 
lean_inc_ref(v_pkg_2297_);
v___x_2328_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_pkg_2297_, v___y_2303_, v___y_2304_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v_a_2330_; lean_object* v_dir_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
v_a_2330_ = lean_ctor_get(v___x_2328_, 1);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2328_, 2);
v_dir_2331_ = lean_ctor_get(v_pkg_2297_, 4);
v___x_2332_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_2331_);
v___x_2333_ = l_Lake_joinRelative(v_dir_2331_, v___x_2332_);
v___x_2334_ = ((lean_object*)(l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0));
v___x_2335_ = l_Lake_joinRelative(v___x_2333_, v___x_2334_);
v___x_2336_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2297_, v_a_2329_, v___x_2335_, v___x_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v_a_2330_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; uint8_t v___x_2338_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 1);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 2);
v___x_2338_ = 1;
v_r_2307_ = v___x_2338_;
v___y_2308_ = v_a_2337_;
goto v___jp_2306_;
}
else
{
lean_object* v_a_2339_; 
v_a_2339_ = lean_ctor_get(v___x_2336_, 1);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2336_, 2);
v_a_2312_ = v_a_2339_;
goto v___jp_2311_;
}
}
else
{
lean_object* v_a_2340_; 
lean_dec_ref(v_pkg_2297_);
v_a_2340_ = lean_ctor_get(v___x_2328_, 1);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2328_, 2);
v_a_2312_ = v_a_2340_;
goto v___jp_2311_;
}
v___jp_2306_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_box(v_r_2307_);
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v___y_2308_);
return v___x_2310_;
}
v___jp_2311_:
{
lean_object* v_log_2313_; uint8_t v_action_2314_; uint8_t v_wantsRebuild_2315_; lean_object* v_trace_2316_; lean_object* v_buildTime_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2327_; 
v_log_2313_ = lean_ctor_get(v_a_2312_, 0);
v_action_2314_ = lean_ctor_get_uint8(v_a_2312_, sizeof(void*)*3);
v_wantsRebuild_2315_ = lean_ctor_get_uint8(v_a_2312_, sizeof(void*)*3 + 1);
v_trace_2316_ = lean_ctor_get(v_a_2312_, 1);
v_buildTime_2317_ = lean_ctor_get(v_a_2312_, 2);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_a_2312_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2319_ = v_a_2312_;
v_isShared_2320_ = v_isSharedCheck_2327_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_buildTime_2317_);
lean_inc(v_trace_2316_);
lean_inc(v_log_2313_);
lean_dec(v_a_2312_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2327_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
uint8_t v___x_2321_; uint8_t v___x_2322_; lean_object* v___x_2324_; 
v___x_2321_ = 4;
v___x_2322_ = l_Lake_JobAction_merge(v_action_2314_, v___x_2321_);
if (v_isShared_2320_ == 0)
{
v___x_2324_ = v___x_2319_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_log_2313_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_trace_2316_);
lean_ctor_set(v_reuseFailAlloc_2326_, 2, v_buildTime_2317_);
lean_ctor_set_uint8(v_reuseFailAlloc_2326_, sizeof(void*)*3 + 1, v_wantsRebuild_2315_);
v___x_2324_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
uint8_t v___x_2325_; 
lean_ctor_set_uint8(v___x_2324_, sizeof(void*)*3, v___x_2322_);
v___x_2325_ = 0;
v_r_2307_ = v___x_2325_;
v___y_2308_ = v___x_2324_;
goto v___jp_2306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* v_pkg_2341_, lean_object* v___x_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lake_Package_optBarrelFacetConfig___lam__0(v_pkg_2341_, v___x_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec_ref(v___x_2342_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* v___x_2351_, lean_object* v___f_2352_, lean_object* v___x_2353_, lean_object* v___x_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = l_Lake_Job_async___redArg(v___x_2351_, v___f_2352_, v___x_2353_, v___x_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
v___x_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
lean_ctor_set(v___x_2363_, 1, v___y_2360_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object* v___x_2364_, lean_object* v___f_2365_, lean_object* v___x_2366_, lean_object* v___x_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lake_Package_optBarrelFacetConfig___lam__1(v___x_2364_, v___f_2365_, v___x_2366_, v___x_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec_ref(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec(v___y_2369_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* v___x_2376_, lean_object* v___x_2377_, lean_object* v___x_2378_, lean_object* v_pkg_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v___f_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___f_2390_; lean_object* v___x_2391_; 
lean_inc_ref(v_pkg_2379_);
v___f_2387_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2387_, 0, v_pkg_2379_);
lean_closure_set(v___f_2387_, 1, v___x_2376_);
v___x_2388_ = lean_unsigned_to_nat(0u);
v___x_2389_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2377_);
v___f_2390_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2390_, 0, v___x_2377_);
lean_closure_set(v___f_2390_, 1, v___f_2387_);
lean_closure_set(v___f_2390_, 2, v___x_2388_);
lean_closure_set(v___f_2390_, 3, v___x_2389_);
v___x_2391_ = l_Lake_ensureJob___redArg(v___x_2377_, v___f_2390_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2424_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_a_2393_ = lean_ctor_get(v___x_2391_, 1);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2395_ = v___x_2391_;
v_isShared_2396_ = v_isSharedCheck_2424_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2424_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v_task_2397_; lean_object* v_kind_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2422_; 
v_task_2397_ = lean_ctor_get(v_a_2392_, 0);
v_kind_2398_ = lean_ctor_get(v_a_2392_, 1);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_a_2392_);
if (v_isSharedCheck_2422_ == 0)
{
lean_object* v_unused_2423_; 
v_unused_2423_ = lean_ctor_get(v_a_2392_, 2);
lean_dec(v_unused_2423_);
v___x_2400_ = v_a_2392_;
v_isShared_2401_ = v_isSharedCheck_2422_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_kind_2398_);
lean_inc(v_task_2397_);
lean_dec(v_a_2392_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2422_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v_registeredJobs_2402_; lean_object* v___x_2403_; lean_object* v_baseName_2404_; uint8_t v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v_job_2413_; 
v_registeredJobs_2402_ = lean_ctor_get(v___y_2384_, 3);
v___x_2403_ = lean_st_ref_take(v_registeredJobs_2402_);
v_baseName_2404_ = lean_ctor_get(v_pkg_2379_, 1);
lean_inc(v_baseName_2404_);
lean_dec_ref(v_pkg_2379_);
v___x_2405_ = 1;
v___x_2406_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2404_, v___x_2405_);
v___x_2407_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2408_ = lean_string_append(v___x_2406_, v___x_2407_);
v___x_2409_ = l_Lake_Name_eraseHead(v___x_2378_);
v___x_2410_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2409_, v___x_2405_);
v___x_2411_ = lean_string_append(v___x_2408_, v___x_2410_);
lean_dec_ref(v___x_2410_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 2, v___x_2411_);
v_job_2413_ = v___x_2400_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_task_2397_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_kind_2398_);
lean_ctor_set(v_reuseFailAlloc_2421_, 2, v___x_2411_);
v_job_2413_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
lean_ctor_set_uint8(v_job_2413_, sizeof(void*)*3, v___x_2405_);
lean_inc_ref(v_job_2413_);
v___x_2414_ = l_Lake_Job_toOpaque___redArg(v_job_2413_);
v___x_2415_ = lean_array_push(v___x_2403_, v___x_2414_);
v___x_2416_ = lean_st_ref_set(v_registeredJobs_2402_, v___x_2415_);
v___x_2417_ = l_Lake_Job_renew___redArg(v_job_2413_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2417_);
v___x_2419_ = v___x_2395_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_a_2393_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_2379_);
lean_dec(v___x_2378_);
return v___x_2391_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object* v___x_2425_, lean_object* v___x_2426_, lean_object* v___x_2427_, lean_object* v_pkg_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lake_Package_optBarrelFacetConfig___lam__2(v___x_2425_, v___x_2426_, v___x_2427_, v_pkg_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec(v___y_2430_);
return v_res_2436_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___f_2440_; 
v___x_2437_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_2438_ = l_Lake_instDataKindBool;
v___x_2439_ = l_Lake_Reservoir_lakeHeaders;
v___f_2440_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2440_, 0, v___x_2439_);
lean_closure_set(v___f_2440_, 1, v___x_2438_);
lean_closure_set(v___f_2440_, 2, v___x_2437_);
return v___f_2440_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2441_; uint8_t v___x_2442_; lean_object* v___x_2443_; lean_object* v___f_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___f_2441_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_2442_ = 1;
v___x_2443_ = l_Lake_instDataKindBool;
v___f_2444_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__0, &l_Lake_Package_optBarrelFacetConfig___closed__0_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__0);
v___x_2445_ = l_Lake_Package_keyword;
v___x_2446_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
lean_ctor_set(v___x_2446_, 1, v___f_2444_);
lean_ctor_set(v___x_2446_, 2, v___x_2443_);
lean_ctor_set(v___x_2446_, 3, v___f_2441_);
lean_ctor_set_uint8(v___x_2446_, sizeof(void*)*4, v___x_2442_);
lean_ctor_set_uint8(v___x_2446_, sizeof(void*)*4 + 1, v___x_2442_);
return v___x_2446_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig(void){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__1, &l_Lake_Package_optBarrelFacetConfig___closed__1_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__1);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* v_baseName_2449_, lean_object* v___x_2450_, uint8_t v_success_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_a_2460_; lean_object* v_a_2461_; 
if (v_success_2451_ == 0)
{
lean_object* v_toBuildConfig_2481_; uint8_t v_verbosity_2482_; uint8_t v___x_2483_; uint8_t v___x_2484_; 
v_toBuildConfig_2481_ = lean_ctor_get(v___y_2456_, 0);
v_verbosity_2482_ = lean_ctor_get_uint8(v_toBuildConfig_2481_, sizeof(void*)*4 + 3);
v___x_2483_ = 2;
v___x_2484_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2482_, v___x_2483_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; 
lean_dec(v___x_2450_);
lean_dec(v_baseName_2449_);
v___x_2485_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2460_ = v___x_2485_;
v_a_2461_ = v___y_2457_;
goto v___jp_2459_;
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2486_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2487_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2449_, v___x_2484_);
v___x_2488_ = lean_string_append(v___x_2486_, v___x_2487_);
lean_dec_ref(v___x_2487_);
v___x_2489_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2490_ = lean_string_append(v___x_2488_, v___x_2489_);
v___x_2491_ = l_Lake_Name_eraseHead(v___x_2450_);
v___x_2492_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2491_, v___x_2484_);
v___x_2493_ = lean_string_append(v___x_2490_, v___x_2492_);
lean_dec_ref(v___x_2492_);
v___x_2494_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2495_ = lean_string_append(v___x_2493_, v___x_2494_);
v_a_2460_ = v___x_2495_;
v_a_2461_ = v___y_2457_;
goto v___jp_2459_;
}
}
else
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
lean_dec(v___x_2450_);
lean_dec(v_baseName_2449_);
v___x_2496_ = lean_box(0);
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___y_2457_);
return v___x_2497_;
}
v___jp_2459_:
{
lean_object* v_log_2462_; uint8_t v_action_2463_; uint8_t v_wantsRebuild_2464_; lean_object* v_trace_2465_; lean_object* v_buildTime_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2480_; 
v_log_2462_ = lean_ctor_get(v_a_2461_, 0);
v_action_2463_ = lean_ctor_get_uint8(v_a_2461_, sizeof(void*)*3);
v_wantsRebuild_2464_ = lean_ctor_get_uint8(v_a_2461_, sizeof(void*)*3 + 1);
v_trace_2465_ = lean_ctor_get(v_a_2461_, 1);
v_buildTime_2466_ = lean_ctor_get(v_a_2461_, 2);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_a_2461_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2468_ = v_a_2461_;
v_isShared_2469_ = v_isSharedCheck_2480_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_buildTime_2466_);
lean_inc(v_trace_2465_);
lean_inc(v_log_2462_);
lean_dec(v_a_2461_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2480_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2470_ = ((lean_object*)(l_Lake_Package_barrelFacetConfig___lam__1___closed__0));
v___x_2471_ = lean_string_append(v___x_2470_, v_a_2460_);
lean_dec_ref(v_a_2460_);
v___x_2472_ = 3;
v___x_2473_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2473_, 0, v___x_2471_);
lean_ctor_set_uint8(v___x_2473_, sizeof(void*)*1, v___x_2472_);
v___x_2474_ = lean_array_get_size(v_log_2462_);
v___x_2475_ = lean_array_push(v_log_2462_, v___x_2473_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 0, v___x_2475_);
v___x_2477_ = v___x_2468_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_trace_2465_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v_buildTime_2466_);
lean_ctor_set_uint8(v_reuseFailAlloc_2479_, sizeof(void*)*3, v_action_2463_);
lean_ctor_set_uint8(v_reuseFailAlloc_2479_, sizeof(void*)*3 + 1, v_wantsRebuild_2464_);
v___x_2477_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2478_; 
v___x_2478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2474_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
return v___x_2478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object* v_baseName_2498_, lean_object* v___x_2499_, lean_object* v_success_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
uint8_t v_success_boxed_2508_; lean_object* v_res_2509_; 
v_success_boxed_2508_ = lean_unbox(v_success_2500_);
v_res_2509_ = l_Lake_Package_barrelFacetConfig___lam__1(v_baseName_2498_, v___x_2499_, v_success_boxed_2508_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* v___x_2510_, lean_object* v___x_2511_, lean_object* v___x_2512_, lean_object* v_pkg_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_baseName_2521_; lean_object* v_keyName_2522_; lean_object* v___f_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; 
v_baseName_2521_ = lean_ctor_get(v_pkg_2513_, 1);
lean_inc_n(v_baseName_2521_, 2);
v_keyName_2522_ = lean_ctor_get(v_pkg_2513_, 2);
lean_inc(v___x_2510_);
v___f_2523_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2523_, 0, v_baseName_2521_);
lean_closure_set(v___f_2523_, 1, v___x_2510_);
lean_inc(v_keyName_2522_);
v___x_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_keyName_2522_);
v___x_2525_ = l_Lake_Package_keyword;
v___x_2526_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2524_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
lean_ctor_set(v___x_2526_, 2, v_pkg_2513_);
lean_ctor_set(v___x_2526_, 3, v___x_2510_);
lean_inc(v___x_2511_);
v___f_2527_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2527_, 0, v___x_2526_);
lean_closure_set(v___f_2527_, 1, v___x_2511_);
lean_closure_set(v___f_2527_, 2, v___f_2523_);
v___x_2528_ = l_Lake_ensureJob___redArg(v___x_2511_, v___f_2527_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2561_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
v_a_2530_ = lean_ctor_get(v___x_2528_, 1);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2532_ = v___x_2528_;
v_isShared_2533_ = v_isSharedCheck_2561_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2561_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v_task_2534_; lean_object* v_kind_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2559_; 
v_task_2534_ = lean_ctor_get(v_a_2529_, 0);
v_kind_2535_ = lean_ctor_get(v_a_2529_, 1);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_a_2529_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v_a_2529_, 2);
lean_dec(v_unused_2560_);
v___x_2537_ = v_a_2529_;
v_isShared_2538_ = v_isSharedCheck_2559_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_kind_2535_);
lean_inc(v_task_2534_);
lean_dec(v_a_2529_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2559_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v_registeredJobs_2539_; lean_object* v___x_2540_; uint8_t v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; lean_object* v_job_2550_; 
v_registeredJobs_2539_ = lean_ctor_get(v___y_2518_, 3);
v___x_2540_ = lean_st_ref_take(v_registeredJobs_2539_);
v___x_2541_ = 1;
v___x_2542_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2521_, v___x_2541_);
v___x_2543_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2544_ = lean_string_append(v___x_2542_, v___x_2543_);
v___x_2545_ = l_Lake_Name_eraseHead(v___x_2512_);
v___x_2546_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2545_, v___x_2541_);
v___x_2547_ = lean_string_append(v___x_2544_, v___x_2546_);
lean_dec_ref(v___x_2546_);
v___x_2548_ = 0;
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 2, v___x_2547_);
v_job_2550_ = v___x_2537_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_task_2534_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_kind_2535_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v___x_2547_);
v_job_2550_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2556_; 
lean_ctor_set_uint8(v_job_2550_, sizeof(void*)*3, v___x_2548_);
lean_inc_ref(v_job_2550_);
v___x_2551_ = l_Lake_Job_toOpaque___redArg(v_job_2550_);
v___x_2552_ = lean_array_push(v___x_2540_, v___x_2551_);
v___x_2553_ = lean_st_ref_set(v_registeredJobs_2539_, v___x_2552_);
v___x_2554_ = l_Lake_Job_renew___redArg(v_job_2550_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v___x_2554_);
v___x_2556_ = v___x_2532_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2554_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_a_2530_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2521_);
lean_dec(v___x_2512_);
return v___x_2528_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object* v___x_2562_, lean_object* v___x_2563_, lean_object* v___x_2564_, lean_object* v_pkg_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lake_Package_barrelFacetConfig___lam__2(v___x_2562_, v___x_2563_, v___x_2564_, v_pkg_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec(v___y_2567_);
return v_res_2573_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___f_2577_; 
v___x_2574_ = l_Lake_Package_reservoirBarrelFacet;
v___x_2575_ = l_Lake_instDataKindUnit;
v___x_2576_ = l_Lake_Package_optReservoirBarrelFacet;
v___f_2577_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2577_, 0, v___x_2576_);
lean_closure_set(v___f_2577_, 1, v___x_2575_);
lean_closure_set(v___f_2577_, 2, v___x_2574_);
return v___f_2577_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2578_; uint8_t v___x_2579_; lean_object* v___x_2580_; lean_object* v___f_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___f_2578_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2579_ = 1;
v___x_2580_ = l_Lake_instDataKindUnit;
v___f_2581_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__0, &l_Lake_Package_barrelFacetConfig___closed__0_once, _init_l_Lake_Package_barrelFacetConfig___closed__0);
v___x_2582_ = l_Lake_Package_keyword;
v___x_2583_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2583_, 0, v___x_2582_);
lean_ctor_set(v___x_2583_, 1, v___f_2581_);
lean_ctor_set(v___x_2583_, 2, v___x_2580_);
lean_ctor_set(v___x_2583_, 3, v___f_2578_);
lean_ctor_set_uint8(v___x_2583_, sizeof(void*)*4, v___x_2579_);
lean_ctor_set_uint8(v___x_2583_, sizeof(void*)*4 + 1, v___x_2579_);
return v___x_2583_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig(void){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__1, &l_Lake_Package_barrelFacetConfig___closed__1_once, _init_l_Lake_Package_barrelFacetConfig___closed__1);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object* v_pkg_2585_, lean_object* v___x_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
uint8_t v_r_2595_; lean_object* v___y_2596_; lean_object* v_a_2600_; lean_object* v___x_2616_; 
lean_inc_ref(v_pkg_2585_);
v___x_2616_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_pkg_2585_, v___y_2592_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v_a_2618_; lean_object* v_dir_2619_; lean_object* v_buildArchive_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2617_);
v_a_2618_ = lean_ctor_get(v___x_2616_, 1);
lean_inc(v_a_2618_);
lean_dec_ref_known(v___x_2616_, 2);
v_dir_2619_ = lean_ctor_get(v_pkg_2585_, 4);
v_buildArchive_2620_ = lean_ctor_get(v_pkg_2585_, 21);
v___x_2621_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_2619_);
v___x_2622_ = l_Lake_joinRelative(v_dir_2619_, v___x_2621_);
lean_inc_ref(v_buildArchive_2620_);
v___x_2623_ = l_Lake_joinRelative(v___x_2622_, v_buildArchive_2620_);
v___x_2624_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2585_, v_a_2617_, v___x_2623_, v___x_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v_a_2618_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; uint8_t v___x_2626_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 1);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2624_, 2);
v___x_2626_ = 1;
v_r_2595_ = v___x_2626_;
v___y_2596_ = v_a_2625_;
goto v___jp_2594_;
}
else
{
lean_object* v_a_2627_; 
v_a_2627_ = lean_ctor_get(v___x_2624_, 1);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2624_, 2);
v_a_2600_ = v_a_2627_;
goto v___jp_2599_;
}
}
else
{
lean_object* v_a_2628_; 
lean_dec_ref(v_pkg_2585_);
v_a_2628_ = lean_ctor_get(v___x_2616_, 1);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2616_, 2);
v_a_2600_ = v_a_2628_;
goto v___jp_2599_;
}
v___jp_2594_:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2597_ = lean_box(v_r_2595_);
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
lean_ctor_set(v___x_2598_, 1, v___y_2596_);
return v___x_2598_;
}
v___jp_2599_:
{
lean_object* v_log_2601_; uint8_t v_action_2602_; uint8_t v_wantsRebuild_2603_; lean_object* v_trace_2604_; lean_object* v_buildTime_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2615_; 
v_log_2601_ = lean_ctor_get(v_a_2600_, 0);
v_action_2602_ = lean_ctor_get_uint8(v_a_2600_, sizeof(void*)*3);
v_wantsRebuild_2603_ = lean_ctor_get_uint8(v_a_2600_, sizeof(void*)*3 + 1);
v_trace_2604_ = lean_ctor_get(v_a_2600_, 1);
v_buildTime_2605_ = lean_ctor_get(v_a_2600_, 2);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_a_2600_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2607_ = v_a_2600_;
v_isShared_2608_ = v_isSharedCheck_2615_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_buildTime_2605_);
lean_inc(v_trace_2604_);
lean_inc(v_log_2601_);
lean_dec(v_a_2600_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2615_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
uint8_t v___x_2609_; uint8_t v___x_2610_; lean_object* v___x_2612_; 
v___x_2609_ = 4;
v___x_2610_ = l_Lake_JobAction_merge(v_action_2602_, v___x_2609_);
if (v_isShared_2608_ == 0)
{
v___x_2612_ = v___x_2607_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_log_2601_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_trace_2604_);
lean_ctor_set(v_reuseFailAlloc_2614_, 2, v_buildTime_2605_);
lean_ctor_set_uint8(v_reuseFailAlloc_2614_, sizeof(void*)*3 + 1, v_wantsRebuild_2603_);
v___x_2612_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
uint8_t v___x_2613_; 
lean_ctor_set_uint8(v___x_2612_, sizeof(void*)*3, v___x_2610_);
v___x_2613_ = 0;
v_r_2595_ = v___x_2613_;
v___y_2596_ = v___x_2612_;
goto v___jp_2594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object* v_pkg_2629_, lean_object* v___x_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(v_pkg_2629_, v___x_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec_ref(v___x_2630_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object* v___x_2639_, lean_object* v___x_2640_, lean_object* v___x_2641_, lean_object* v___x_2642_, lean_object* v_pkg_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___f_2651_; lean_object* v___x_2652_; lean_object* v___f_2653_; lean_object* v___x_2654_; 
lean_inc_ref(v_pkg_2643_);
v___f_2651_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2651_, 0, v_pkg_2643_);
lean_closure_set(v___f_2651_, 1, v___x_2639_);
v___x_2652_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2640_);
v___f_2653_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2653_, 0, v___x_2640_);
lean_closure_set(v___f_2653_, 1, v___f_2651_);
lean_closure_set(v___f_2653_, 2, v___x_2641_);
lean_closure_set(v___f_2653_, 3, v___x_2652_);
v___x_2654_ = l_Lake_ensureJob___redArg(v___x_2640_, v___f_2653_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
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
lean_object* v_registeredJobs_2665_; lean_object* v___x_2666_; lean_object* v_baseName_2667_; uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v_job_2676_; 
v_registeredJobs_2665_ = lean_ctor_get(v___y_2648_, 3);
v___x_2666_ = lean_st_ref_take(v_registeredJobs_2665_);
v_baseName_2667_ = lean_ctor_get(v_pkg_2643_, 1);
lean_inc(v_baseName_2667_);
lean_dec_ref(v_pkg_2643_);
v___x_2668_ = 1;
v___x_2669_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2667_, v___x_2668_);
v___x_2670_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2671_ = lean_string_append(v___x_2669_, v___x_2670_);
v___x_2672_ = l_Lake_Name_eraseHead(v___x_2642_);
v___x_2673_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2672_, v___x_2668_);
v___x_2674_ = lean_string_append(v___x_2671_, v___x_2673_);
lean_dec_ref(v___x_2673_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 2, v___x_2674_);
v_job_2676_ = v___x_2663_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_task_2660_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_kind_2661_);
lean_ctor_set(v_reuseFailAlloc_2684_, 2, v___x_2674_);
v_job_2676_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2682_; 
lean_ctor_set_uint8(v_job_2676_, sizeof(void*)*3, v___x_2668_);
lean_inc_ref(v_job_2676_);
v___x_2677_ = l_Lake_Job_toOpaque___redArg(v_job_2676_);
v___x_2678_ = lean_array_push(v___x_2666_, v___x_2677_);
v___x_2679_ = lean_st_ref_set(v_registeredJobs_2665_, v___x_2678_);
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
lean_dec_ref(v_pkg_2643_);
lean_dec(v___x_2642_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_2688_, lean_object* v___x_2689_, lean_object* v___x_2690_, lean_object* v___x_2691_, lean_object* v_pkg_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(v___x_2688_, v___x_2689_, v___x_2690_, v___x_2691_, v_pkg_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec(v___y_2694_);
return v_res_2700_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___f_2707_; 
v___x_2703_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_2704_ = lean_unsigned_to_nat(0u);
v___x_2705_ = l_Lake_instDataKindBool;
v___x_2706_ = ((lean_object*)(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0));
v___f_2707_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2707_, 0, v___x_2706_);
lean_closure_set(v___f_2707_, 1, v___x_2705_);
lean_closure_set(v___f_2707_, 2, v___x_2704_);
lean_closure_set(v___f_2707_, 3, v___x_2703_);
return v___f_2707_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2708_; uint8_t v___x_2709_; lean_object* v___x_2710_; lean_object* v___f_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___f_2708_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_2709_ = 1;
v___x_2710_ = l_Lake_instDataKindBool;
v___f_2711_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__1, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1);
v___x_2712_ = l_Lake_Package_keyword;
v___x_2713_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v___f_2711_);
lean_ctor_set(v___x_2713_, 2, v___x_2710_);
lean_ctor_set(v___x_2713_, 3, v___f_2708_);
lean_ctor_set_uint8(v___x_2713_, sizeof(void*)*4, v___x_2709_);
lean_ctor_set_uint8(v___x_2713_, sizeof(void*)*4 + 1, v___x_2709_);
return v___x_2713_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__2, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* v_baseName_2716_, lean_object* v___x_2717_, uint8_t v_success_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_a_2727_; lean_object* v_a_2728_; 
if (v_success_2718_ == 0)
{
lean_object* v_toBuildConfig_2748_; uint8_t v_verbosity_2749_; uint8_t v___x_2750_; uint8_t v___x_2751_; 
v_toBuildConfig_2748_ = lean_ctor_get(v___y_2723_, 0);
v_verbosity_2749_ = lean_ctor_get_uint8(v_toBuildConfig_2748_, sizeof(void*)*4 + 3);
v___x_2750_ = 2;
v___x_2751_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2749_, v___x_2750_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; 
lean_dec(v___x_2717_);
lean_dec(v_baseName_2716_);
v___x_2752_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2727_ = v___x_2752_;
v_a_2728_ = v___y_2724_;
goto v___jp_2726_;
}
else
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2753_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2754_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2716_, v___x_2751_);
v___x_2755_ = lean_string_append(v___x_2753_, v___x_2754_);
lean_dec_ref(v___x_2754_);
v___x_2756_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2757_ = lean_string_append(v___x_2755_, v___x_2756_);
v___x_2758_ = l_Lake_Name_eraseHead(v___x_2717_);
v___x_2759_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2758_, v___x_2751_);
v___x_2760_ = lean_string_append(v___x_2757_, v___x_2759_);
lean_dec_ref(v___x_2759_);
v___x_2761_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2762_ = lean_string_append(v___x_2760_, v___x_2761_);
v_a_2727_ = v___x_2762_;
v_a_2728_ = v___y_2724_;
goto v___jp_2726_;
}
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec(v___x_2717_);
lean_dec(v_baseName_2716_);
v___x_2763_ = lean_box(0);
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
lean_ctor_set(v___x_2764_, 1, v___y_2724_);
return v___x_2764_;
}
v___jp_2726_:
{
lean_object* v_log_2729_; uint8_t v_action_2730_; uint8_t v_wantsRebuild_2731_; lean_object* v_trace_2732_; lean_object* v_buildTime_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2747_; 
v_log_2729_ = lean_ctor_get(v_a_2728_, 0);
v_action_2730_ = lean_ctor_get_uint8(v_a_2728_, sizeof(void*)*3);
v_wantsRebuild_2731_ = lean_ctor_get_uint8(v_a_2728_, sizeof(void*)*3 + 1);
v_trace_2732_ = lean_ctor_get(v_a_2728_, 1);
v_buildTime_2733_ = lean_ctor_get(v_a_2728_, 2);
v_isSharedCheck_2747_ = !lean_is_exclusive(v_a_2728_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2735_ = v_a_2728_;
v_isShared_2736_ = v_isSharedCheck_2747_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_buildTime_2733_);
lean_inc(v_trace_2732_);
lean_inc(v_log_2729_);
lean_dec(v_a_2728_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2747_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2737_ = ((lean_object*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0));
v___x_2738_ = lean_string_append(v___x_2737_, v_a_2727_);
lean_dec_ref(v_a_2727_);
v___x_2739_ = 3;
v___x_2740_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set_uint8(v___x_2740_, sizeof(void*)*1, v___x_2739_);
v___x_2741_ = lean_array_get_size(v_log_2729_);
v___x_2742_ = lean_array_push(v_log_2729_, v___x_2740_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v___x_2742_);
v___x_2744_ = v___x_2735_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2742_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v_trace_2732_);
lean_ctor_set(v_reuseFailAlloc_2746_, 2, v_buildTime_2733_);
lean_ctor_set_uint8(v_reuseFailAlloc_2746_, sizeof(void*)*3, v_action_2730_);
lean_ctor_set_uint8(v_reuseFailAlloc_2746_, sizeof(void*)*3 + 1, v_wantsRebuild_2731_);
v___x_2744_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2741_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
return v___x_2745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object* v_baseName_2765_, lean_object* v___x_2766_, lean_object* v_success_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
uint8_t v_success_boxed_2775_; lean_object* v_res_2776_; 
v_success_boxed_2775_ = lean_unbox(v_success_2767_);
v_res_2776_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(v_baseName_2765_, v___x_2766_, v_success_boxed_2775_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* v___x_2777_, lean_object* v___x_2778_, lean_object* v___x_2779_, lean_object* v_pkg_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_baseName_2788_; lean_object* v_keyName_2789_; lean_object* v___f_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___f_2794_; lean_object* v___x_2795_; 
v_baseName_2788_ = lean_ctor_get(v_pkg_2780_, 1);
lean_inc_n(v_baseName_2788_, 2);
v_keyName_2789_ = lean_ctor_get(v_pkg_2780_, 2);
lean_inc(v___x_2777_);
v___f_2790_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2790_, 0, v_baseName_2788_);
lean_closure_set(v___f_2790_, 1, v___x_2777_);
lean_inc(v_keyName_2789_);
v___x_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_keyName_2789_);
v___x_2792_ = l_Lake_Package_keyword;
v___x_2793_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
lean_ctor_set(v___x_2793_, 2, v_pkg_2780_);
lean_ctor_set(v___x_2793_, 3, v___x_2777_);
lean_inc(v___x_2778_);
v___f_2794_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2794_, 0, v___x_2793_);
lean_closure_set(v___f_2794_, 1, v___x_2778_);
lean_closure_set(v___f_2794_, 2, v___f_2790_);
v___x_2795_ = l_Lake_ensureJob___redArg(v___x_2778_, v___f_2794_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2828_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_a_2797_ = lean_ctor_get(v___x_2795_, 1);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2799_ = v___x_2795_;
v_isShared_2800_ = v_isSharedCheck_2828_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2828_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v_task_2801_; lean_object* v_kind_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2826_; 
v_task_2801_ = lean_ctor_get(v_a_2796_, 0);
v_kind_2802_ = lean_ctor_get(v_a_2796_, 1);
v_isSharedCheck_2826_ = !lean_is_exclusive(v_a_2796_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v_a_2796_, 2);
lean_dec(v_unused_2827_);
v___x_2804_ = v_a_2796_;
v_isShared_2805_ = v_isSharedCheck_2826_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_kind_2802_);
lean_inc(v_task_2801_);
lean_dec(v_a_2796_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2826_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v_registeredJobs_2806_; lean_object* v___x_2807_; uint8_t v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; uint8_t v___x_2815_; lean_object* v_job_2817_; 
v_registeredJobs_2806_ = lean_ctor_get(v___y_2785_, 3);
v___x_2807_ = lean_st_ref_take(v_registeredJobs_2806_);
v___x_2808_ = 1;
v___x_2809_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2788_, v___x_2808_);
v___x_2810_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2811_ = lean_string_append(v___x_2809_, v___x_2810_);
v___x_2812_ = l_Lake_Name_eraseHead(v___x_2779_);
v___x_2813_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2812_, v___x_2808_);
v___x_2814_ = lean_string_append(v___x_2811_, v___x_2813_);
lean_dec_ref(v___x_2813_);
v___x_2815_ = 0;
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 2, v___x_2814_);
v_job_2817_ = v___x_2804_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_task_2801_);
lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_kind_2802_);
lean_ctor_set(v_reuseFailAlloc_2825_, 2, v___x_2814_);
v_job_2817_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2823_; 
lean_ctor_set_uint8(v_job_2817_, sizeof(void*)*3, v___x_2815_);
lean_inc_ref(v_job_2817_);
v___x_2818_ = l_Lake_Job_toOpaque___redArg(v_job_2817_);
v___x_2819_ = lean_array_push(v___x_2807_, v___x_2818_);
v___x_2820_ = lean_st_ref_set(v_registeredJobs_2806_, v___x_2819_);
v___x_2821_ = l_Lake_Job_renew___redArg(v_job_2817_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2821_);
v___x_2823_ = v___x_2799_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v_a_2797_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2788_);
lean_dec(v___x_2779_);
return v___x_2795_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_2829_, lean_object* v___x_2830_, lean_object* v___x_2831_, lean_object* v_pkg_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(v___x_2829_, v___x_2830_, v___x_2831_, v_pkg_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
return v_res_2840_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___f_2844_; 
v___x_2841_ = l_Lake_Package_gitHubReleaseFacet;
v___x_2842_ = l_Lake_instDataKindUnit;
v___x_2843_ = l_Lake_Package_optGitHubReleaseFacet;
v___f_2844_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2844_, 0, v___x_2843_);
lean_closure_set(v___f_2844_, 1, v___x_2842_);
lean_closure_set(v___f_2844_, 2, v___x_2841_);
return v___f_2844_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___f_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___f_2845_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2846_ = 1;
v___x_2847_ = l_Lake_instDataKindUnit;
v___f_2848_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__0, &l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0);
v___x_2849_ = l_Lake_Package_keyword;
v___x_2850_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
lean_ctor_set(v___x_2850_, 1, v___f_2848_);
lean_ctor_set(v___x_2850_, 2, v___x_2847_);
lean_ctor_set(v___x_2850_, 3, v___f_2845_);
lean_ctor_set_uint8(v___x_2850_, sizeof(void*)*4, v___x_2846_);
lean_ctor_set_uint8(v___x_2850_, sizeof(void*)*4 + 1, v___x_2846_);
return v___x_2850_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_2851_; 
v___x_2851_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__1, &l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* v_build_2852_, uint8_t v_x_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v_log_2861_; uint8_t v_action_2862_; uint8_t v_wantsRebuild_2863_; lean_object* v_buildTime_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2873_; 
v_log_2861_ = lean_ctor_get(v___y_2859_, 0);
v_action_2862_ = lean_ctor_get_uint8(v___y_2859_, sizeof(void*)*3);
v_wantsRebuild_2863_ = lean_ctor_get_uint8(v___y_2859_, sizeof(void*)*3 + 1);
v_buildTime_2864_ = lean_ctor_get(v___y_2859_, 2);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___y_2859_);
if (v_isSharedCheck_2873_ == 0)
{
lean_object* v_unused_2874_; 
v_unused_2874_ = lean_ctor_get(v___y_2859_, 1);
lean_dec(v_unused_2874_);
v___x_2866_ = v___y_2859_;
v_isShared_2867_ = v_isSharedCheck_2873_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_buildTime_2864_);
lean_inc(v_log_2861_);
lean_dec(v___y_2859_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2873_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2868_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 1, v___x_2868_);
v___x_2870_ = v___x_2866_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_log_2861_);
lean_ctor_set(v_reuseFailAlloc_2872_, 1, v___x_2868_);
lean_ctor_set(v_reuseFailAlloc_2872_, 2, v_buildTime_2864_);
lean_ctor_set_uint8(v_reuseFailAlloc_2872_, sizeof(void*)*3, v_action_2862_);
lean_ctor_set_uint8(v_reuseFailAlloc_2872_, sizeof(void*)*3 + 1, v_wantsRebuild_2863_);
v___x_2870_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; 
lean_inc_ref(v___y_2858_);
lean_inc(v___y_2857_);
lean_inc(v___y_2856_);
lean_inc(v___y_2855_);
v___x_2871_ = lean_apply_7(v_build_2852_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___x_2870_, lean_box(0));
return v___x_2871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* v_build_2875_, lean_object* v_x_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
uint8_t v_x_1923__boxed_2884_; lean_object* v_res_2885_; 
v_x_1923__boxed_2884_ = lean_unbox(v_x_2876_);
v_res_2885_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(v_build_2875_, v_x_1923__boxed_2884_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec(v___y_2878_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* v_self_2886_, lean_object* v_build_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v_wsIdx_2895_; lean_object* v___x_2896_; uint8_t v___x_2897_; 
v_wsIdx_2895_ = lean_ctor_get(v_self_2886_, 0);
v___x_2896_ = lean_unsigned_to_nat(0u);
v___x_2897_ = lean_nat_dec_eq(v_wsIdx_2895_, v___x_2896_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2898_; 
lean_inc_ref(v_a_2888_);
v___x_2898_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_2886_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2911_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
v_a_2900_ = lean_ctor_get(v___x_2898_, 1);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2902_ = v___x_2898_;
v_isShared_2903_ = v_isSharedCheck_2911_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_inc(v_a_2899_);
lean_dec(v___x_2898_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2911_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___f_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___f_2904_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2904_, 0, v_build_2887_);
v___x_2905_ = lean_box(0);
v___x_2906_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2907_ = l_Lake_Job_bindM___redArg(v___x_2905_, v_a_2899_, v___f_2904_, v___x_2896_, v___x_2897_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v___x_2906_);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v___x_2907_);
v___x_2909_ = v___x_2902_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_a_2900_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v_a_2888_);
lean_dec_ref(v_build_2887_);
v_a_2912_ = lean_ctor_get(v___x_2898_, 0);
v_a_2913_ = lean_ctor_get(v___x_2898_, 1);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2898_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_inc(v_a_2912_);
lean_dec(v___x_2898_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2912_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
uint8_t v___x_2921_; uint8_t v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
lean_dec_ref(v_self_2886_);
v___x_2921_ = 0;
v___x_2922_ = 0;
v___x_2923_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2924_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2924_, 0, v_a_2893_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
lean_ctor_set(v___x_2924_, 2, v___x_2896_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*3, v___x_2921_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*3 + 1, v___x_2922_);
lean_inc_ref(v_a_2892_);
lean_inc(v_a_2891_);
lean_inc(v_a_2890_);
lean_inc(v_a_2889_);
v___x_2925_ = lean_apply_7(v_build_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v___x_2924_, lean_box(0));
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2935_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 1);
v_a_2927_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2929_ = v___x_2925_;
v_isShared_2930_ = v_isSharedCheck_2935_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2926_);
lean_inc(v_a_2927_);
lean_dec(v___x_2925_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2935_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v_log_2931_; lean_object* v___x_2933_; 
v_log_2931_ = lean_ctor_get(v_a_2926_, 0);
lean_inc_ref(v_log_2931_);
lean_dec(v_a_2926_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v_log_2931_);
v___x_2933_ = v___x_2929_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2927_);
lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_log_2931_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
else
{
lean_object* v_a_2936_; lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2945_; 
v_a_2936_ = lean_ctor_get(v___x_2925_, 1);
v_a_2937_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2939_ = v___x_2925_;
v_isShared_2940_ = v_isSharedCheck_2945_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2936_);
lean_inc(v_a_2937_);
lean_dec(v___x_2925_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2945_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v_log_2941_; lean_object* v___x_2943_; 
v_log_2941_ = lean_ctor_get(v_a_2936_, 0);
lean_inc_ref(v_log_2941_);
lean_dec(v_a_2936_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 1, v_log_2941_);
v___x_2943_ = v___x_2939_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2937_);
lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_log_2941_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___boxed(lean_object* v_self_2946_, lean_object* v_build_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_2946_, v_build_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_);
lean_dec_ref(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec(v_a_2950_);
lean_dec(v_a_2949_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* v_00_u03b1_2956_, lean_object* v_self_2957_, lean_object* v_build_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v___x_2966_; 
v___x_2966_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_2957_, v_build_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_);
return v___x_2966_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___boxed(lean_object* v_00_u03b1_2967_, lean_object* v_self_2968_, lean_object* v_build_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Lake_Package_afterBuildCacheAsync(v_00_u03b1_2967_, v_self_2968_, v_build_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
lean_dec_ref(v_a_2974_);
lean_dec(v_a_2973_);
lean_dec(v_a_2972_);
lean_dec(v_a_2971_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* v_build_2978_, uint8_t v_x_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v_log_2987_; uint8_t v_action_2988_; uint8_t v_wantsRebuild_2989_; lean_object* v_buildTime_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2999_; 
v_log_2987_ = lean_ctor_get(v___y_2985_, 0);
v_action_2988_ = lean_ctor_get_uint8(v___y_2985_, sizeof(void*)*3);
v_wantsRebuild_2989_ = lean_ctor_get_uint8(v___y_2985_, sizeof(void*)*3 + 1);
v_buildTime_2990_ = lean_ctor_get(v___y_2985_, 2);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___y_2985_);
if (v_isSharedCheck_2999_ == 0)
{
lean_object* v_unused_3000_; 
v_unused_3000_ = lean_ctor_get(v___y_2985_, 1);
lean_dec(v_unused_3000_);
v___x_2992_ = v___y_2985_;
v_isShared_2993_ = v_isSharedCheck_2999_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_buildTime_2990_);
lean_inc(v_log_2987_);
lean_dec(v___y_2985_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2999_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; lean_object* v___x_2996_; 
v___x_2994_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v___x_2994_);
v___x_2996_ = v___x_2992_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_log_2987_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_2998_, 2, v_buildTime_2990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2998_, sizeof(void*)*3, v_action_2988_);
lean_ctor_set_uint8(v_reuseFailAlloc_2998_, sizeof(void*)*3 + 1, v_wantsRebuild_2989_);
v___x_2996_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2997_; 
lean_inc_ref(v___y_2984_);
lean_inc(v___y_2983_);
lean_inc(v___y_2982_);
lean_inc(v___y_2981_);
v___x_2997_ = lean_apply_7(v_build_2978_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___x_2996_, lean_box(0));
return v___x_2997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* v_build_3001_, lean_object* v_x_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
uint8_t v_x_1946__boxed_3010_; lean_object* v_res_3011_; 
v_x_1946__boxed_3010_ = lean_unbox(v_x_3002_);
v_res_3011_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(v_build_3001_, v_x_1946__boxed_3010_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec(v___y_3004_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* v_self_3012_, lean_object* v_build_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v_wsIdx_3021_; lean_object* v___x_3022_; uint8_t v___x_3023_; 
v_wsIdx_3021_ = lean_ctor_get(v_self_3012_, 0);
v___x_3022_ = lean_unsigned_to_nat(0u);
v___x_3023_ = lean_nat_dec_eq(v_wsIdx_3021_, v___x_3022_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; 
lean_inc_ref(v_a_3014_);
v___x_3024_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3012_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3037_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
v_a_3026_ = lean_ctor_get(v___x_3024_, 1);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3028_ = v___x_3024_;
v_isShared_3029_ = v_isSharedCheck_3037_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_inc(v_a_3025_);
lean_dec(v___x_3024_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3037_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___f_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
v___f_3030_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3030_, 0, v_build_3013_);
v___x_3031_ = lean_box(0);
v___x_3032_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3033_ = l_Lake_Job_mapM___redArg(v___x_3031_, v_a_3025_, v___f_3030_, v___x_3022_, v___x_3023_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v___x_3032_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 0, v___x_3033_);
v___x_3035_ = v___x_3028_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_a_3026_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec_ref(v_a_3014_);
lean_dec_ref(v_build_3013_);
v_a_3038_ = lean_ctor_get(v___x_3024_, 0);
v_a_3039_ = lean_ctor_get(v___x_3024_, 1);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3024_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_inc(v_a_3038_);
lean_dec(v___x_3024_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3038_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
else
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
lean_dec_ref(v_self_3012_);
v___x_3047_ = lean_box(0);
v___x_3048_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_3049_ = l_Lake_Job_async___redArg(v___x_3047_, v_build_3013_, v___x_3022_, v___x_3048_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
v___x_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
lean_ctor_set(v___x_3050_, 1, v_a_3019_);
return v___x_3050_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___boxed(lean_object* v_self_3051_, lean_object* v_build_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3051_, v_build_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_);
lean_dec_ref(v_a_3057_);
lean_dec(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec(v_a_3054_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* v_00_u03b1_3061_, lean_object* v_self_3062_, lean_object* v_build_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3062_, v_build_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___boxed(lean_object* v_00_u03b1_3072_, lean_object* v_self_3073_, lean_object* v_build_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Lake_Package_afterBuildCacheSync(v_00_u03b1_3072_, v_self_3073_, v_build_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_);
lean_dec_ref(v_a_3079_);
lean_dec(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec(v_a_3076_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(lean_object* v_k_3083_, lean_object* v_v_3084_, lean_object* v_t_3085_){
_start:
{
if (lean_obj_tag(v_t_3085_) == 0)
{
lean_object* v_size_3086_; lean_object* v_k_3087_; lean_object* v_v_3088_; lean_object* v_l_3089_; lean_object* v_r_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3370_; 
v_size_3086_ = lean_ctor_get(v_t_3085_, 0);
v_k_3087_ = lean_ctor_get(v_t_3085_, 1);
v_v_3088_ = lean_ctor_get(v_t_3085_, 2);
v_l_3089_ = lean_ctor_get(v_t_3085_, 3);
v_r_3090_ = lean_ctor_get(v_t_3085_, 4);
v_isSharedCheck_3370_ = !lean_is_exclusive(v_t_3085_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3092_ = v_t_3085_;
v_isShared_3093_ = v_isSharedCheck_3370_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_r_3090_);
lean_inc(v_l_3089_);
lean_inc(v_v_3088_);
lean_inc(v_k_3087_);
lean_inc(v_size_3086_);
lean_dec(v_t_3085_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3370_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
uint8_t v___x_3094_; 
v___x_3094_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3083_, v_k_3087_);
switch(v___x_3094_)
{
case 0:
{
lean_object* v_impl_3095_; lean_object* v___x_3096_; 
lean_dec(v_size_3086_);
v_impl_3095_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3083_, v_v_3084_, v_l_3089_);
v___x_3096_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3090_) == 0)
{
lean_object* v_size_3097_; lean_object* v_size_3098_; lean_object* v_k_3099_; lean_object* v_v_3100_; lean_object* v_l_3101_; lean_object* v_r_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; uint8_t v___x_3105_; 
v_size_3097_ = lean_ctor_get(v_r_3090_, 0);
v_size_3098_ = lean_ctor_get(v_impl_3095_, 0);
lean_inc(v_size_3098_);
v_k_3099_ = lean_ctor_get(v_impl_3095_, 1);
lean_inc(v_k_3099_);
v_v_3100_ = lean_ctor_get(v_impl_3095_, 2);
lean_inc(v_v_3100_);
v_l_3101_ = lean_ctor_get(v_impl_3095_, 3);
lean_inc(v_l_3101_);
v_r_3102_ = lean_ctor_get(v_impl_3095_, 4);
lean_inc(v_r_3102_);
v___x_3103_ = lean_unsigned_to_nat(3u);
v___x_3104_ = lean_nat_mul(v___x_3103_, v_size_3097_);
v___x_3105_ = lean_nat_dec_lt(v___x_3104_, v_size_3098_);
lean_dec(v___x_3104_);
if (v___x_3105_ == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3109_; 
lean_dec(v_r_3102_);
lean_dec(v_l_3101_);
lean_dec(v_v_3100_);
lean_dec(v_k_3099_);
v___x_3106_ = lean_nat_add(v___x_3096_, v_size_3098_);
lean_dec(v_size_3098_);
v___x_3107_ = lean_nat_add(v___x_3106_, v_size_3097_);
lean_dec(v___x_3106_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 3, v_impl_3095_);
lean_ctor_set(v___x_3092_, 0, v___x_3107_);
v___x_3109_ = v___x_3092_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_k_3087_);
lean_ctor_set(v_reuseFailAlloc_3110_, 2, v_v_3088_);
lean_ctor_set(v_reuseFailAlloc_3110_, 3, v_impl_3095_);
lean_ctor_set(v_reuseFailAlloc_3110_, 4, v_r_3090_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
else
{
lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3176_; 
v_isSharedCheck_3176_ = !lean_is_exclusive(v_impl_3095_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; lean_object* v_unused_3178_; lean_object* v_unused_3179_; lean_object* v_unused_3180_; lean_object* v_unused_3181_; 
v_unused_3177_ = lean_ctor_get(v_impl_3095_, 4);
lean_dec(v_unused_3177_);
v_unused_3178_ = lean_ctor_get(v_impl_3095_, 3);
lean_dec(v_unused_3178_);
v_unused_3179_ = lean_ctor_get(v_impl_3095_, 2);
lean_dec(v_unused_3179_);
v_unused_3180_ = lean_ctor_get(v_impl_3095_, 1);
lean_dec(v_unused_3180_);
v_unused_3181_ = lean_ctor_get(v_impl_3095_, 0);
lean_dec(v_unused_3181_);
v___x_3112_ = v_impl_3095_;
v_isShared_3113_ = v_isSharedCheck_3176_;
goto v_resetjp_3111_;
}
else
{
lean_dec(v_impl_3095_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3176_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v_size_3114_; lean_object* v_size_3115_; lean_object* v_k_3116_; lean_object* v_v_3117_; lean_object* v_l_3118_; lean_object* v_r_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; 
v_size_3114_ = lean_ctor_get(v_l_3101_, 0);
v_size_3115_ = lean_ctor_get(v_r_3102_, 0);
v_k_3116_ = lean_ctor_get(v_r_3102_, 1);
v_v_3117_ = lean_ctor_get(v_r_3102_, 2);
v_l_3118_ = lean_ctor_get(v_r_3102_, 3);
v_r_3119_ = lean_ctor_get(v_r_3102_, 4);
v___x_3120_ = lean_unsigned_to_nat(2u);
v___x_3121_ = lean_nat_mul(v___x_3120_, v_size_3114_);
v___x_3122_ = lean_nat_dec_lt(v_size_3115_, v___x_3121_);
lean_dec(v___x_3121_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3151_; 
lean_inc(v_r_3119_);
lean_inc(v_l_3118_);
lean_inc(v_v_3117_);
lean_inc(v_k_3116_);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_r_3102_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; lean_object* v_unused_3153_; lean_object* v_unused_3154_; lean_object* v_unused_3155_; lean_object* v_unused_3156_; 
v_unused_3152_ = lean_ctor_get(v_r_3102_, 4);
lean_dec(v_unused_3152_);
v_unused_3153_ = lean_ctor_get(v_r_3102_, 3);
lean_dec(v_unused_3153_);
v_unused_3154_ = lean_ctor_get(v_r_3102_, 2);
lean_dec(v_unused_3154_);
v_unused_3155_ = lean_ctor_get(v_r_3102_, 1);
lean_dec(v_unused_3155_);
v_unused_3156_ = lean_ctor_get(v_r_3102_, 0);
lean_dec(v_unused_3156_);
v___x_3124_ = v_r_3102_;
v_isShared_3125_ = v_isSharedCheck_3151_;
goto v_resetjp_3123_;
}
else
{
lean_dec(v_r_3102_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3151_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___x_3139_; lean_object* v___y_3141_; 
v___x_3126_ = lean_nat_add(v___x_3096_, v_size_3098_);
lean_dec(v_size_3098_);
v___x_3127_ = lean_nat_add(v___x_3126_, v_size_3097_);
lean_dec(v___x_3126_);
v___x_3139_ = lean_nat_add(v___x_3096_, v_size_3114_);
if (lean_obj_tag(v_l_3118_) == 0)
{
lean_object* v_size_3149_; 
v_size_3149_ = lean_ctor_get(v_l_3118_, 0);
lean_inc(v_size_3149_);
v___y_3141_ = v_size_3149_;
goto v___jp_3140_;
}
else
{
lean_object* v___x_3150_; 
v___x_3150_ = lean_unsigned_to_nat(0u);
v___y_3141_ = v___x_3150_;
goto v___jp_3140_;
}
v___jp_3128_:
{
lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3132_ = lean_nat_add(v___y_3130_, v___y_3131_);
lean_dec(v___y_3131_);
lean_dec(v___y_3130_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 4, v_r_3090_);
lean_ctor_set(v___x_3124_, 3, v_r_3119_);
lean_ctor_set(v___x_3124_, 2, v_v_3088_);
lean_ctor_set(v___x_3124_, 1, v_k_3087_);
lean_ctor_set(v___x_3124_, 0, v___x_3132_);
v___x_3134_ = v___x_3124_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3132_);
lean_ctor_set(v_reuseFailAlloc_3138_, 1, v_k_3087_);
lean_ctor_set(v_reuseFailAlloc_3138_, 2, v_v_3088_);
lean_ctor_set(v_reuseFailAlloc_3138_, 3, v_r_3119_);
lean_ctor_set(v_reuseFailAlloc_3138_, 4, v_r_3090_);
v___x_3134_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3136_; 
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 4, v___x_3134_);
lean_ctor_set(v___x_3112_, 3, v___y_3129_);
lean_ctor_set(v___x_3112_, 2, v_v_3117_);
lean_ctor_set(v___x_3112_, 1, v_k_3116_);
lean_ctor_set(v___x_3112_, 0, v___x_3127_);
v___x_3136_ = v___x_3112_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3127_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_k_3116_);
lean_ctor_set(v_reuseFailAlloc_3137_, 2, v_v_3117_);
lean_ctor_set(v_reuseFailAlloc_3137_, 3, v___y_3129_);
lean_ctor_set(v_reuseFailAlloc_3137_, 4, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
v___jp_3140_:
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3142_ = lean_nat_add(v___x_3139_, v___y_3141_);
lean_dec(v___y_3141_);
lean_dec(v___x_3139_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 4, v_l_3118_);
lean_ctor_set(v___x_3092_, 3, v_l_3101_);
lean_ctor_set(v___x_3092_, 2, v_v_3100_);
lean_ctor_set(v___x_3092_, 1, v_k_3099_);
lean_ctor_set(v___x_3092_, 0, v___x_3142_);
v___x_3144_ = v___x_3092_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_k_3099_);
lean_ctor_set(v_reuseFailAlloc_3148_, 2, v_v_3100_);
lean_ctor_set(v_reuseFailAlloc_3148_, 3, v_l_3101_);
lean_ctor_set(v_reuseFailAlloc_3148_, 4, v_l_3118_);
v___x_3144_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3145_; 
v___x_3145_ = lean_nat_add(v___x_3096_, v_size_3097_);
if (lean_obj_tag(v_r_3119_) == 0)
{
lean_object* v_size_3146_; 
v_size_3146_ = lean_ctor_get(v_r_3119_, 0);
lean_inc(v_size_3146_);
v___y_3129_ = v___x_3144_;
v___y_3130_ = v___x_3145_;
v___y_3131_ = v_size_3146_;
goto v___jp_3128_;
}
else
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_unsigned_to_nat(0u);
v___y_3129_ = v___x_3144_;
v___y_3130_ = v___x_3145_;
v___y_3131_ = v___x_3147_;
goto v___jp_3128_;
}
}
}
}
}
else
{
lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; 
lean_del_object(v___x_3092_);
v___x_3157_ = lean_nat_add(v___x_3096_, v_size_3098_);
lean_dec(v_size_3098_);
v___x_3158_ = lean_nat_add(v___x_3157_, v_size_3097_);
lean_dec(v___x_3157_);
v___x_3159_ = lean_nat_add(v___x_3096_, v_size_3097_);
v___x_3160_ = lean_nat_add(v___x_3159_, v_size_3115_);
lean_dec(v___x_3159_);
lean_inc_ref(v_r_3090_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 4, v_r_3090_);
lean_ctor_set(v___x_3112_, 3, v_r_3102_);
lean_ctor_set(v___x_3112_, 2, v_v_3088_);
lean_ctor_set(v___x_3112_, 1, v_k_3087_);
lean_ctor_set(v___x_3112_, 0, v___x_3160_);
v___x_3162_ = v___x_3112_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3160_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v_k_3087_);
lean_ctor_set(v_reuseFailAlloc_3175_, 2, v_v_3088_);
lean_ctor_set(v_reuseFailAlloc_3175_, 3, v_r_3102_);
lean_ctor_set(v_reuseFailAlloc_3175_, 4, v_r_3090_);
v___x_3162_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
v_isSharedCheck_3169_ = !lean_is_exclusive(v_r_3090_);
if (v_isSharedCheck_3169_ == 0)
{
lean_object* v_unused_3170_; lean_object* v_unused_3171_; lean_object* v_unused_3172_; lean_object* v_unused_3173_; lean_object* v_unused_3174_; 
v_unused_3170_ = lean_ctor_get(v_r_3090_, 4);
lean_dec(v_unused_3170_);
v_unused_3171_ = lean_ctor_get(v_r_3090_, 3);
lean_dec(v_unused_3171_);
v_unused_3172_ = lean_ctor_get(v_r_3090_, 2);
lean_dec(v_unused_3172_);
v_unused_3173_ = lean_ctor_get(v_r_3090_, 1);
lean_dec(v_unused_3173_);
v_unused_3174_ = lean_ctor_get(v_r_3090_, 0);
lean_dec(v_unused_3174_);
v___x_3164_ = v_r_3090_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_dec(v_r_3090_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 4, v___x_3162_);
lean_ctor_set(v___x_3164_, 3, v_l_3101_);
lean_ctor_set(v___x_3164_, 2, v_v_3100_);
lean_ctor_set(v___x_3164_, 1, v_k_3099_);
lean_ctor_set(v___x_3164_, 0, v___x_3158_);
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3158_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_k_3099_);
lean_ctor_set(v_reuseFailAlloc_3168_, 2, v_v_3100_);
lean_ctor_set(v_reuseFailAlloc_3168_, 3, v_l_3101_);
lean_ctor_set(v_reuseFailAlloc_3168_, 4, v___x_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3182_; 
v_l_3182_ = lean_ctor_get(v_impl_3095_, 3);
lean_inc(v_l_3182_);
if (lean_obj_tag(v_l_3182_) == 0)
{
lean_object* v_r_3183_; lean_object* v_k_3184_; lean_object* v_v_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3196_; 
v_r_3183_ = lean_ctor_get(v_impl_3095_, 4);
v_k_3184_ = lean_ctor_get(v_impl_3095_, 1);
v_v_3185_ = lean_ctor_get(v_impl_3095_, 2);
v_isSharedCheck_3196_ = !lean_is_exclusive(v_impl_3095_);
if (v_isSharedCheck_3196_ == 0)
{
lean_object* v_unused_3197_; lean_object* v_unused_3198_; 
v_unused_3197_ = lean_ctor_get(v_impl_3095_, 3);
lean_dec(v_unused_3197_);
v_unused_3198_ = lean_ctor_get(v_impl_3095_, 0);
lean_dec(v_unused_3198_);
v___x_3187_ = v_impl_3095_;
v_isShared_3188_ = v_isSharedCheck_3196_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_r_3183_);
lean_inc(v_v_3185_);
lean_inc(v_k_3184_);
lean_dec(v_impl_3095_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3196_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3189_; lean_object* v___x_3191_; 
v___x_3189_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3183_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 3, v_r_3183_);
lean_ctor_set(v___x_3187_, 2, v_v_3088_);
lean_ctor_set(v___x_3187_, 1, v_k_3087_);
lean_ctor_set(v___x_3187_, 0, v___x_3096_);
v___x_3191_ = v___x_3187_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v_k_3087_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v_v_3088_);
lean_ctor_set(v_reuseFailAlloc_3195_, 3, v_r_3183_);
lean_ctor_set(v_reuseFailAlloc_3195_, 4, v_r_3183_);
v___x_3191_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
lean_object* v___x_3193_; 
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 4, v___x_3191_);
lean_ctor_set(v___x_3092_, 3, v_l_3182_);
lean_ctor_set(v___x_3092_, 2, v_v_3185_);
lean_ctor_set(v___x_3092_, 1, v_k_3184_);
lean_ctor_set(v___x_3092_, 0, v___x_3189_);
v___x_3193_ = v___x_3092_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v_k_3184_);
lean_ctor_set(v_reuseFailAlloc_3194_, 2, v_v_3185_);
lean_ctor_set(v_reuseFailAlloc_3194_, 3, v_l_3182_);
lean_ctor_set(v_reuseFailAlloc_3194_, 4, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
else
{
lean_object* v_r_3199_; 
v_r_3199_ = lean_ctor_get(v_impl_3095_, 4);
lean_inc(v_r_3199_);
if (lean_obj_tag(v_r_3199_) == 0)
{
lean_object* v_k_3200_; lean_object* v_v_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3224_; 
v_k_3200_ = lean_ctor_get(v_impl_3095_, 1);
v_v_3201_ = lean_ctor_get(v_impl_3095_, 2);
v_isSharedCheck_3224_ = !lean_is_exclusive(v_impl_3095_);
if (v_isSharedCheck_3224_ == 0)
{
lean_object* v_unused_3225_; lean_object* v_unused_3226_; lean_object* v_unused_3227_; 
v_unused_3225_ = lean_ctor_get(v_impl_3095_, 4);
lean_dec(v_unused_3225_);
v_unused_3226_ = lean_ctor_get(v_impl_3095_, 3);
lean_dec(v_unused_3226_);
v_unused_3227_ = lean_ctor_get(v_impl_3095_, 0);
lean_dec(v_unused_3227_);
v___x_3203_ = v_impl_3095_;
v_isShared_3204_ = v_isSharedCheck_3224_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_v_3201_);
lean_inc(v_k_3200_);
lean_dec(v_impl_3095_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3224_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v_k_3205_; lean_object* v_v_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3220_; 
v_k_3205_ = lean_ctor_get(v_r_3199_, 1);
v_v_3206_ = lean_ctor_get(v_r_3199_, 2);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_r_3199_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; lean_object* v_unused_3222_; lean_object* v_unused_3223_; 
v_unused_3221_ = lean_ctor_get(v_r_3199_, 4);
lean_dec(v_unused_3221_);
v_unused_3222_ = lean_ctor_get(v_r_3199_, 3);
lean_dec(v_unused_3222_);
v_unused_3223_ = lean_ctor_get(v_r_3199_, 0);
lean_dec(v_unused_3223_);
v___x_3208_ = v_r_3199_;
v_isShared_3209_ = v_isSharedCheck_3220_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_v_3206_);
lean_inc(v_k_3205_);
lean_dec(v_r_3199_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3220_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v___x_3212_; 
v___x_3210_ = lean_unsigned_to_nat(3u);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 4, v_l_3182_);
lean_ctor_set(v___x_3208_, 3, v_l_3182_);
lean_ctor_set(v___x_3208_, 2, v_v_3201_);
lean_ctor_set(v___x_3208_, 1, v_k_3200_);
lean_ctor_set(v___x_3208_, 0, v___x_3096_);
v___x_3212_ = v___x_3208_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v_k_3200_);
lean_ctor_set(v_reuseFailAlloc_3219_, 2, v_v_3201_);
lean_ctor_set(v_reuseFailAlloc_3219_, 3, v_l_3182_);
lean_ctor_set(v_reuseFailAlloc_3219_, 4, v_l_3182_);
v___x_3212_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
lean_object* v___x_3214_; 
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 4, v_l_3182_);
lean_ctor_set(v___x_3203_, 2, v_v_3088_);
lean_ctor_set(v___x_3203_, 1, v_k_3087_);
lean_ctor_set(v___x_3203_, 0, v___x_3096_);
v___x_3214_ = v___x_3203_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_k_3087_);
lean_ctor_set(v_reuseFailAlloc_3218_, 2, v_v_3088_);
lean_ctor_set(v_reuseFailAlloc_3218_, 3, v_l_3182_);
lean_ctor_set(v_reuseFailAlloc_3218_, 4, v_l_3182_);
v___x_3214_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3216_; 
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 4, v___x_3214_);
lean_ctor_set(v___x_3092_, 3, v___x_3212_);
lean_ctor_set(v___x_3092_, 2, v_v_3206_);
lean_ctor_set(v___x_3092_, 1, v_k_3205_);
lean_ctor_set(v___x_3092_, 0, v___x_3210_);
v___x_3216_ = v___x_3092_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v___x_3210_);
lean_ctor_set(v_reuseFailAlloc_3217_, 1, v_k_3205_);
lean_ctor_set(v_reuseFailAlloc_3217_, 2, v_v_3206_);
lean_ctor_set(v_reuseFailAlloc_3217_, 3, v___x_3212_);
lean_ctor_set(v_reuseFailAlloc_3217_, 4, v___x_3214_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
}
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3228_ = lean_unsigned_to_nat(2u);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 4, v_r_3199_);
lean_ctor_set(v___x_3092_, 3, v_impl_3095_);
lean_ctor_set(v___x_3092_, 0, v___x_3228_);
v___x_3230_ = v___x_3092_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_k_3087_);
lean_ctor_set(v_reuseFailAlloc_3231_, 2, v_v_3088_);
lean_ctor_set(v_reuseFailAlloc_3231_, 3, v_impl_3095_);
lean_ctor_set(v_reuseFailAlloc_3231_, 4, v_r_3199_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3233_; 
lean_dec(v_v_3088_);
lean_dec(v_k_3087_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 2, v_v_3084_);
lean_ctor_set(v___x_3092_, 1, v_k_3083_);
v___x_3233_ = v___x_3092_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_size_3086_);
lean_ctor_set(v_reuseFailAlloc_3234_, 1, v_k_3083_);
lean_ctor_set(v_reuseFailAlloc_3234_, 2, v_v_3084_);
lean_ctor_set(v_reuseFailAlloc_3234_, 3, v_l_3089_);
lean_ctor_set(v_reuseFailAlloc_3234_, 4, v_r_3090_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
default: 
{
lean_object* v_impl_3235_; lean_object* v___x_3236_; 
lean_dec(v_size_3086_);
v_impl_3235_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3083_, v_v_3084_, v_r_3090_);
v___x_3236_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3089_) == 0)
{
lean_object* v_size_3237_; lean_object* v_size_3238_; lean_object* v_k_3239_; lean_object* v_v_3240_; lean_object* v_l_3241_; lean_object* v_r_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; uint8_t v___x_3245_; 
v_size_3237_ = lean_ctor_get(v_l_3089_, 0);
v_size_3238_ = lean_ctor_get(v_impl_3235_, 0);
lean_inc(v_size_3238_);
v_k_3239_ = lean_ctor_get(v_impl_3235_, 1);
lean_inc(v_k_3239_);
v_v_3240_ = lean_ctor_get(v_impl_3235_, 2);
lean_inc(v_v_3240_);
v_l_3241_ = lean_ctor_get(v_impl_3235_, 3);
lean_inc(v_l_3241_);
v_r_3242_ = lean_ctor_get(v_impl_3235_, 4);
lean_inc(v_r_3242_);
v___x_3243_ = lean_unsigned_to_nat(3u);
v___x_3244_ = lean_nat_mul(v___x_3243_, v_size_3237_);
v___x_3245_ = lean_nat_dec_lt(v___x_3244_, v_size_3238_);
lean_dec(v___x_3244_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3249_; 
lean_dec(v_r_3242_);
lean_dec(v_l_3241_);
lean_dec(v_v_3240_);
lean_dec(v_k_3239_);
v___x_3246_ = lean_nat_add(v___x_3236_, v_size_3237_);
v___x_3247_ = lean_nat_add(v___x_3246_, v_size_3238_);
lean_dec(v_size_3238_);
lean_dec(v___x_3246_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 4, v_impl_3235_);
lean_ctor_set(v___x_3092_, 0, v___x_3247_);
v___x_3249_ = v___x_3092_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3247_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v_k_3087_);
lean_ctor_set(v_reuseFailAlloc_3250_, 2, v_v_3088_);
lean_ctor_set(v_reuseFailAlloc_3250_, 3, v_l_3089_);
lean_ctor_set(v_reuseFailAlloc_3250_, 4, v_impl_3235_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
else
{
lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3314_; 
v_isSharedCheck_3314_ = !lean_is_exclusive(v_impl_3235_);
if (v_isSharedCheck_3314_ == 0)
{
lean_object* v_unused_3315_; lean_object* v_unused_3316_; lean_object* v_unused_3317_; lean_object* v_unused_3318_; lean_object* v_unused_3319_; 
v_unused_3315_ = lean_ctor_get(v_impl_3235_, 4);
lean_dec(v_unused_3315_);
v_unused_3316_ = lean_ctor_get(v_impl_3235_, 3);
lean_dec(v_unused_3316_);
v_unused_3317_ = lean_ctor_get(v_impl_3235_, 2);
lean_dec(v_unused_3317_);
v_unused_3318_ = lean_ctor_get(v_impl_3235_, 1);
lean_dec(v_unused_3318_);
v_unused_3319_ = lean_ctor_get(v_impl_3235_, 0);
lean_dec(v_unused_3319_);
v___x_3252_ = v_impl_3235_;
v_isShared_3253_ = v_isSharedCheck_3314_;
goto v_resetjp_3251_;
}
else
{
lean_dec(v_impl_3235_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3314_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v_size_3254_; lean_object* v_k_3255_; lean_object* v_v_3256_; lean_object* v_l_3257_; lean_object* v_r_3258_; lean_object* v_size_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; 
v_size_3254_ = lean_ctor_get(v_l_3241_, 0);
v_k_3255_ = lean_ctor_get(v_l_3241_, 1);
v_v_3256_ = lean_ctor_get(v_l_3241_, 2);
v_l_3257_ = lean_ctor_get(v_l_3241_, 3);
v_r_3258_ = lean_ctor_get(v_l_3241_, 4);
v_size_3259_ = lean_ctor_get(v_r_3242_, 0);
v___x_3260_ = lean_unsigned_to_nat(2u);
v___x_3261_ = lean_nat_mul(v___x_3260_, v_size_3259_);
v___x_3262_ = lean_nat_dec_lt(v_size_3254_, v___x_3261_);
lean_dec(v___x_3261_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3290_; 
lean_inc(v_r_3258_);
lean_inc(v_l_3257_);
lean_inc(v_v_3256_);
lean_inc(v_k_3255_);
v_isSharedCheck_3290_ = !lean_is_exclusive(v_l_3241_);
if (v_isSharedCheck_3290_ == 0)
{
lean_object* v_unused_3291_; lean_object* v_unused_3292_; lean_object* v_unused_3293_; lean_object* v_unused_3294_; lean_object* v_unused_3295_; 
v_unused_3291_ = lean_ctor_get(v_l_3241_, 4);
lean_dec(v_unused_3291_);
v_unused_3292_ = lean_ctor_get(v_l_3241_, 3);
lean_dec(v_unused_3292_);
v_unused_3293_ = lean_ctor_get(v_l_3241_, 2);
lean_dec(v_unused_3293_);
v_unused_3294_ = lean_ctor_get(v_l_3241_, 1);
lean_dec(v_unused_3294_);
v_unused_3295_ = lean_ctor_get(v_l_3241_, 0);
lean_dec(v_unused_3295_);
v___x_3264_ = v_l_3241_;
v_isShared_3265_ = v_isSharedCheck_3290_;
goto v_resetjp_3263_;
}
else
{
lean_dec(v_l_3241_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3290_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3280_; 
v___x_3266_ = lean_nat_add(v___x_3236_, v_size_3237_);
v___x_3267_ = lean_nat_add(v___x_3266_, v_size_3238_);
lean_dec(v_size_3238_);
if (lean_obj_tag(v_l_3257_) == 0)
{
lean_object* v_size_3288_; 
v_size_3288_ = lean_ctor_get(v_l_3257_, 0);
lean_inc(v_size_3288_);
v___y_3280_ = v_size_3288_;
goto v___jp_3279_;
}
else
{
lean_object* v___x_3289_; 
v___x_3289_ = lean_unsigned_to_nat(0u);
v___y_3280_ = v___x_3289_;
goto v___jp_3279_;
}
v___jp_3268_:
{
lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3272_ = lean_nat_add(v___y_3269_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec(v___y_3269_);
if (v_isShared_3265_ == 0)
{
lean_ctor_set(v___x_3264_, 4, v_r_3242_);
lean_ctor_set(v___x_3264_, 3, v_r_3258_);
lean_ctor_set(v___x_3264_, 2, v_v_3240_);
lean_ctor_set(v___x_3264_, 1, v_k_3239_);
lean_ctor_set(v___x_3264_, 0, v___x_3272_);
v___x_3274_ = v___x_3264_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3272_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v_k_3239_);
lean_ctor_set(v_reuseFailAlloc_3278_, 2, v_v_3240_);
lean_ctor_set(v_reuseFailAlloc_3278_, 3, v_r_3258_);
lean_ctor_set(v_reuseFailAlloc_3278_, 4, v_r_3242_);
v___x_3274_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
lean_object* v___x_3276_; 
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 4, v___x_3274_);
lean_ctor_set(v___x_3252_, 3, v___y_3270_);
lean_ctor_set(v___x_3252_, 2, v_v_3256_);
lean_ctor_set(v___x_3252_, 1, v_k_3255_);
lean_ctor_set(v___x_3252_, 0, v___x_3267_);
v___x_3276_ = v___x_3252_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3277_, 1, v_k_3255_);
lean_ctor_set(v_reuseFailAlloc_3277_, 2, v_v_3256_);
lean_ctor_set(v_reuseFailAlloc_3277_, 3, v___y_3270_);
lean_ctor_set(v_reuseFailAlloc_3277_, 4, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
v___jp_3279_:
{
lean_object* v___x_3281_; lean_object* v___x_3283_; 
v___x_3281_ = lean_nat_add(v___x_3266_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec(v___x_3266_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 4, v_l_3257_);
lean_ctor_set(v___x_3092_, 0, v___x_3281_);
v___x_3283_ = v___x_3092_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v___x_3281_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v_k_3087_);
lean_ctor_set(v_reuseFailAlloc_3287_, 2, v_v_3088_);
lean_ctor_set(v_reuseFailAlloc_3287_, 3, v_l_3089_);
lean_ctor_set(v_reuseFailAlloc_3287_, 4, v_l_3257_);
v___x_3283_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3284_; 
v___x_3284_ = lean_nat_add(v___x_3236_, v_size_3259_);
if (lean_obj_tag(v_r_3258_) == 0)
{
lean_object* v_size_3285_; 
v_size_3285_ = lean_ctor_get(v_r_3258_, 0);
lean_inc(v_size_3285_);
v___y_3269_ = v___x_3284_;
v___y_3270_ = v___x_3283_;
v___y_3271_ = v_size_3285_;
goto v___jp_3268_;
}
else
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_unsigned_to_nat(0u);
v___y_3269_ = v___x_3284_;
v___y_3270_ = v___x_3283_;
v___y_3271_ = v___x_3286_;
goto v___jp_3268_;
}
}
}
}
}
else
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3300_; 
lean_del_object(v___x_3092_);
v___x_3296_ = lean_nat_add(v___x_3236_, v_size_3237_);
v___x_3297_ = lean_nat_add(v___x_3296_, v_size_3238_);
lean_dec(v_size_3238_);
v___x_3298_ = lean_nat_add(v___x_3296_, v_size_3254_);
lean_dec(v___x_3296_);
lean_inc_ref(v_l_3089_);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 4, v_l_3241_);
lean_ctor_set(v___x_3252_, 3, v_l_3089_);
lean_ctor_set(v___x_3252_, 2, v_v_3088_);
lean_ctor_set(v___x_3252_, 1, v_k_3087_);
lean_ctor_set(v___x_3252_, 0, v___x_3298_);
v___x_3300_ = v___x_3252_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3298_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v_k_3087_);
lean_ctor_set(v_reuseFailAlloc_3313_, 2, v_v_3088_);
lean_ctor_set(v_reuseFailAlloc_3313_, 3, v_l_3089_);
lean_ctor_set(v_reuseFailAlloc_3313_, 4, v_l_3241_);
v___x_3300_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
v_isSharedCheck_3307_ = !lean_is_exclusive(v_l_3089_);
if (v_isSharedCheck_3307_ == 0)
{
lean_object* v_unused_3308_; lean_object* v_unused_3309_; lean_object* v_unused_3310_; lean_object* v_unused_3311_; lean_object* v_unused_3312_; 
v_unused_3308_ = lean_ctor_get(v_l_3089_, 4);
lean_dec(v_unused_3308_);
v_unused_3309_ = lean_ctor_get(v_l_3089_, 3);
lean_dec(v_unused_3309_);
v_unused_3310_ = lean_ctor_get(v_l_3089_, 2);
lean_dec(v_unused_3310_);
v_unused_3311_ = lean_ctor_get(v_l_3089_, 1);
lean_dec(v_unused_3311_);
v_unused_3312_ = lean_ctor_get(v_l_3089_, 0);
lean_dec(v_unused_3312_);
v___x_3302_ = v_l_3089_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_dec(v_l_3089_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 4, v_r_3242_);
lean_ctor_set(v___x_3302_, 3, v___x_3300_);
lean_ctor_set(v___x_3302_, 2, v_v_3240_);
lean_ctor_set(v___x_3302_, 1, v_k_3239_);
lean_ctor_set(v___x_3302_, 0, v___x_3297_);
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v_k_3239_);
lean_ctor_set(v_reuseFailAlloc_3306_, 2, v_v_3240_);
lean_ctor_set(v_reuseFailAlloc_3306_, 3, v___x_3300_);
lean_ctor_set(v_reuseFailAlloc_3306_, 4, v_r_3242_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3320_; 
v_l_3320_ = lean_ctor_get(v_impl_3235_, 3);
lean_inc(v_l_3320_);
if (lean_obj_tag(v_l_3320_) == 0)
{
lean_object* v_r_3321_; lean_object* v_k_3322_; lean_object* v_v_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3346_; 
v_r_3321_ = lean_ctor_get(v_impl_3235_, 4);
v_k_3322_ = lean_ctor_get(v_impl_3235_, 1);
v_v_3323_ = lean_ctor_get(v_impl_3235_, 2);
v_isSharedCheck_3346_ = !lean_is_exclusive(v_impl_3235_);
if (v_isSharedCheck_3346_ == 0)
{
lean_object* v_unused_3347_; lean_object* v_unused_3348_; 
v_unused_3347_ = lean_ctor_get(v_impl_3235_, 3);
lean_dec(v_unused_3347_);
v_unused_3348_ = lean_ctor_get(v_impl_3235_, 0);
lean_dec(v_unused_3348_);
v___x_3325_ = v_impl_3235_;
v_isShared_3326_ = v_isSharedCheck_3346_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_r_3321_);
lean_inc(v_v_3323_);
lean_inc(v_k_3322_);
lean_dec(v_impl_3235_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3346_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v_k_3327_; lean_object* v_v_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3342_; 
v_k_3327_ = lean_ctor_get(v_l_3320_, 1);
v_v_3328_ = lean_ctor_get(v_l_3320_, 2);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_l_3320_);
if (v_isSharedCheck_3342_ == 0)
{
lean_object* v_unused_3343_; lean_object* v_unused_3344_; lean_object* v_unused_3345_; 
v_unused_3343_ = lean_ctor_get(v_l_3320_, 4);
lean_dec(v_unused_3343_);
v_unused_3344_ = lean_ctor_get(v_l_3320_, 3);
lean_dec(v_unused_3344_);
v_unused_3345_ = lean_ctor_get(v_l_3320_, 0);
lean_dec(v_unused_3345_);
v___x_3330_ = v_l_3320_;
v_isShared_3331_ = v_isSharedCheck_3342_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_v_3328_);
lean_inc(v_k_3327_);
lean_dec(v_l_3320_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3342_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; lean_object* v___x_3334_; 
v___x_3332_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3321_, 2);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 4, v_r_3321_);
lean_ctor_set(v___x_3330_, 3, v_r_3321_);
lean_ctor_set(v___x_3330_, 2, v_v_3088_);
lean_ctor_set(v___x_3330_, 1, v_k_3087_);
lean_ctor_set(v___x_3330_, 0, v___x_3236_);
v___x_3334_ = v___x_3330_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_k_3087_);
lean_ctor_set(v_reuseFailAlloc_3341_, 2, v_v_3088_);
lean_ctor_set(v_reuseFailAlloc_3341_, 3, v_r_3321_);
lean_ctor_set(v_reuseFailAlloc_3341_, 4, v_r_3321_);
v___x_3334_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
lean_object* v___x_3336_; 
lean_inc(v_r_3321_);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 3, v_r_3321_);
lean_ctor_set(v___x_3325_, 0, v___x_3236_);
v___x_3336_ = v___x_3325_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_k_3322_);
lean_ctor_set(v_reuseFailAlloc_3340_, 2, v_v_3323_);
lean_ctor_set(v_reuseFailAlloc_3340_, 3, v_r_3321_);
lean_ctor_set(v_reuseFailAlloc_3340_, 4, v_r_3321_);
v___x_3336_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3338_; 
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 4, v___x_3336_);
lean_ctor_set(v___x_3092_, 3, v___x_3334_);
lean_ctor_set(v___x_3092_, 2, v_v_3328_);
lean_ctor_set(v___x_3092_, 1, v_k_3327_);
lean_ctor_set(v___x_3092_, 0, v___x_3332_);
v___x_3338_ = v___x_3092_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_k_3327_);
lean_ctor_set(v_reuseFailAlloc_3339_, 2, v_v_3328_);
lean_ctor_set(v_reuseFailAlloc_3339_, 3, v___x_3334_);
lean_ctor_set(v_reuseFailAlloc_3339_, 4, v___x_3336_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
}
}
else
{
lean_object* v_r_3349_; 
v_r_3349_ = lean_ctor_get(v_impl_3235_, 4);
lean_inc(v_r_3349_);
if (lean_obj_tag(v_r_3349_) == 0)
{
lean_object* v_k_3350_; lean_object* v_v_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3362_; 
v_k_3350_ = lean_ctor_get(v_impl_3235_, 1);
v_v_3351_ = lean_ctor_get(v_impl_3235_, 2);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_impl_3235_);
if (v_isSharedCheck_3362_ == 0)
{
lean_object* v_unused_3363_; lean_object* v_unused_3364_; lean_object* v_unused_3365_; 
v_unused_3363_ = lean_ctor_get(v_impl_3235_, 4);
lean_dec(v_unused_3363_);
v_unused_3364_ = lean_ctor_get(v_impl_3235_, 3);
lean_dec(v_unused_3364_);
v_unused_3365_ = lean_ctor_get(v_impl_3235_, 0);
lean_dec(v_unused_3365_);
v___x_3353_ = v_impl_3235_;
v_isShared_3354_ = v_isSharedCheck_3362_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_v_3351_);
lean_inc(v_k_3350_);
lean_dec(v_impl_3235_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3362_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v___x_3357_; 
v___x_3355_ = lean_unsigned_to_nat(3u);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 4, v_l_3320_);
lean_ctor_set(v___x_3353_, 2, v_v_3088_);
lean_ctor_set(v___x_3353_, 1, v_k_3087_);
lean_ctor_set(v___x_3353_, 0, v___x_3236_);
v___x_3357_ = v___x_3353_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3236_);
lean_ctor_set(v_reuseFailAlloc_3361_, 1, v_k_3087_);
lean_ctor_set(v_reuseFailAlloc_3361_, 2, v_v_3088_);
lean_ctor_set(v_reuseFailAlloc_3361_, 3, v_l_3320_);
lean_ctor_set(v_reuseFailAlloc_3361_, 4, v_l_3320_);
v___x_3357_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
lean_object* v___x_3359_; 
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 4, v_r_3349_);
lean_ctor_set(v___x_3092_, 3, v___x_3357_);
lean_ctor_set(v___x_3092_, 2, v_v_3351_);
lean_ctor_set(v___x_3092_, 1, v_k_3350_);
lean_ctor_set(v___x_3092_, 0, v___x_3355_);
v___x_3359_ = v___x_3092_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3355_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_k_3350_);
lean_ctor_set(v_reuseFailAlloc_3360_, 2, v_v_3351_);
lean_ctor_set(v_reuseFailAlloc_3360_, 3, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3360_, 4, v_r_3349_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
else
{
lean_object* v___x_3366_; lean_object* v___x_3368_; 
v___x_3366_ = lean_unsigned_to_nat(2u);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 4, v_impl_3235_);
lean_ctor_set(v___x_3092_, 3, v_r_3349_);
lean_ctor_set(v___x_3092_, 0, v___x_3366_);
v___x_3368_ = v___x_3092_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3369_, 1, v_k_3087_);
lean_ctor_set(v_reuseFailAlloc_3369_, 2, v_v_3088_);
lean_ctor_set(v_reuseFailAlloc_3369_, 3, v_r_3349_);
lean_ctor_set(v_reuseFailAlloc_3369_, 4, v_impl_3235_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
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
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = lean_unsigned_to_nat(1u);
v___x_3372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
lean_ctor_set(v___x_3372_, 1, v_k_3083_);
lean_ctor_set(v___x_3372_, 2, v_v_3084_);
lean_ctor_set(v___x_3372_, 3, v_t_3085_);
lean_ctor_set(v___x_3372_, 4, v_t_3085_);
return v___x_3372_;
}
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3373_ = lean_box(1);
v___x_3374_ = l_Lake_Package_depsFacetConfig;
v___x_3375_ = l_Lake_Package_depsFacet;
v___x_3376_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3375_, v___x_3374_, v___x_3373_);
return v___x_3376_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3377_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__0, &l_Lake_Package_initFacetConfigs___closed__0_once, _init_l_Lake_Package_initFacetConfigs___closed__0);
v___x_3378_ = l_Lake_Package_transDepsFacetConfig;
v___x_3379_ = l_Lake_Package_transDepsFacet;
v___x_3380_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3379_, v___x_3378_, v___x_3377_);
return v___x_3380_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3381_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__1, &l_Lake_Package_initFacetConfigs___closed__1_once, _init_l_Lake_Package_initFacetConfigs___closed__1);
v___x_3382_ = l_Lake_Package_extraDepFacetConfig;
v___x_3383_ = l_Lake_Package_extraDepFacet;
v___x_3384_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3383_, v___x_3382_, v___x_3381_);
return v___x_3384_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3385_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__2, &l_Lake_Package_initFacetConfigs___closed__2_once, _init_l_Lake_Package_initFacetConfigs___closed__2);
v___x_3386_ = l_Lake_Package_optBuildCacheFacetConfig;
v___x_3387_ = l_Lake_Package_optBuildCacheFacet;
v___x_3388_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3387_, v___x_3386_, v___x_3385_);
return v___x_3388_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3389_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__3, &l_Lake_Package_initFacetConfigs___closed__3_once, _init_l_Lake_Package_initFacetConfigs___closed__3);
v___x_3390_ = l_Lake_Package_buildCacheFacetConfig;
v___x_3391_ = l_Lake_Package_buildCacheFacet;
v___x_3392_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3391_, v___x_3390_, v___x_3389_);
return v___x_3392_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3393_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__4, &l_Lake_Package_initFacetConfigs___closed__4_once, _init_l_Lake_Package_initFacetConfigs___closed__4);
v___x_3394_ = l_Lake_Package_optBarrelFacetConfig;
v___x_3395_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3396_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3395_, v___x_3394_, v___x_3393_);
return v___x_3396_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3397_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__5, &l_Lake_Package_initFacetConfigs___closed__5_once, _init_l_Lake_Package_initFacetConfigs___closed__5);
v___x_3398_ = l_Lake_Package_barrelFacetConfig;
v___x_3399_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3400_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3399_, v___x_3398_, v___x_3397_);
return v___x_3400_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3401_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__6, &l_Lake_Package_initFacetConfigs___closed__6_once, _init_l_Lake_Package_initFacetConfigs___closed__6);
v___x_3402_ = l_Lake_Package_optGitHubReleaseFacetConfig;
v___x_3403_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3404_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3403_, v___x_3402_, v___x_3401_);
return v___x_3404_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3405_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__7, &l_Lake_Package_initFacetConfigs___closed__7_once, _init_l_Lake_Package_initFacetConfigs___closed__7);
v___x_3406_ = l_Lake_Package_gitHubReleaseFacetConfig;
v___x_3407_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3408_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3407_, v___x_3406_, v___x_3405_);
return v___x_3408_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs(void){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__8, &l_Lake_Package_initFacetConfigs___closed__8_once, _init_l_Lake_Package_initFacetConfigs___closed__8);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3410_, lean_object* v_k_3411_, lean_object* v_v_3412_, lean_object* v_t_3413_, lean_object* v_hl_3414_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3411_, v_v_3412_, v_t_3413_);
return v___x_3415_;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs(void){
_start:
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Lake_Package_initFacetConfigs;
return v___x_3416_;
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
