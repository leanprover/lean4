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
uint64_t lean_uint64_of_nat(lean_object*);
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0;
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
v_depPkgs_16_ = lean_ctor_get(v_self_13_, 13);
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
lean_dec_ref(v___x_96_);
v___x_98_ = lean_string_utf8_extract(v___y_92_, v___x_94_, v___x_97_);
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
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_154_; uint64_t v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(1723u);
v___x_155_ = lean_uint64_of_nat(v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(lean_object* v_m_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_buckets_158_; lean_object* v_keyName_159_; lean_object* v___x_160_; uint64_t v___y_162_; 
v_buckets_158_ = lean_ctor_get(v_m_156_, 1);
v_keyName_159_ = lean_ctor_get(v_a_157_, 2);
v___x_160_ = lean_array_get_size(v_buckets_158_);
if (lean_obj_tag(v_keyName_159_) == 0)
{
uint64_t v___x_176_; 
v___x_176_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0);
v___y_162_ = v___x_176_;
goto v___jp_161_;
}
else
{
uint64_t v_hash_177_; 
v_hash_177_ = lean_ctor_get_uint64(v_keyName_159_, sizeof(void*)*2);
v___y_162_ = v_hash_177_;
goto v___jp_161_;
}
v___jp_161_:
{
uint64_t v___x_163_; uint64_t v___x_164_; uint64_t v_fold_165_; uint64_t v___x_166_; uint64_t v___x_167_; uint64_t v___x_168_; size_t v___x_169_; size_t v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_163_ = 32ULL;
v___x_164_ = lean_uint64_shift_right(v___y_162_, v___x_163_);
v_fold_165_ = lean_uint64_xor(v___y_162_, v___x_164_);
v___x_166_ = 16ULL;
v___x_167_ = lean_uint64_shift_right(v_fold_165_, v___x_166_);
v___x_168_ = lean_uint64_xor(v_fold_165_, v___x_167_);
v___x_169_ = lean_uint64_to_usize(v___x_168_);
v___x_170_ = lean_usize_of_nat(v___x_160_);
v___x_171_ = ((size_t)1ULL);
v___x_172_ = lean_usize_sub(v___x_170_, v___x_171_);
v___x_173_ = lean_usize_land(v___x_169_, v___x_172_);
v___x_174_ = lean_array_uget_borrowed(v_buckets_158_, v___x_173_);
v___x_175_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_157_, v___x_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(lean_object* v_m_178_, lean_object* v_a_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_178_, v_a_179_);
lean_dec_ref(v_a_179_);
lean_dec_ref(v_m_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
return v_x_182_;
}
else
{
lean_object* v_key_184_; lean_object* v_value_185_; lean_object* v_tail_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_213_; 
v_key_184_ = lean_ctor_get(v_x_183_, 0);
v_value_185_ = lean_ctor_get(v_x_183_, 1);
v_tail_186_ = lean_ctor_get(v_x_183_, 2);
v_isSharedCheck_213_ = !lean_is_exclusive(v_x_183_);
if (v_isSharedCheck_213_ == 0)
{
v___x_188_ = v_x_183_;
v_isShared_189_ = v_isSharedCheck_213_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_tail_186_);
lean_inc(v_value_185_);
lean_inc(v_key_184_);
lean_dec(v_x_183_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_213_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_keyName_190_; lean_object* v___x_191_; uint64_t v___y_193_; 
v_keyName_190_ = lean_ctor_get(v_key_184_, 2);
v___x_191_ = lean_array_get_size(v_x_182_);
if (lean_obj_tag(v_keyName_190_) == 0)
{
uint64_t v___x_211_; 
v___x_211_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0);
v___y_193_ = v___x_211_;
goto v___jp_192_;
}
else
{
uint64_t v_hash_212_; 
v_hash_212_ = lean_ctor_get_uint64(v_keyName_190_, sizeof(void*)*2);
v___y_193_ = v_hash_212_;
goto v___jp_192_;
}
v___jp_192_:
{
uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v_fold_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v___x_199_; size_t v___x_200_; size_t v___x_201_; size_t v___x_202_; size_t v___x_203_; size_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_194_ = 32ULL;
v___x_195_ = lean_uint64_shift_right(v___y_193_, v___x_194_);
v_fold_196_ = lean_uint64_xor(v___y_193_, v___x_195_);
v___x_197_ = 16ULL;
v___x_198_ = lean_uint64_shift_right(v_fold_196_, v___x_197_);
v___x_199_ = lean_uint64_xor(v_fold_196_, v___x_198_);
v___x_200_ = lean_uint64_to_usize(v___x_199_);
v___x_201_ = lean_usize_of_nat(v___x_191_);
v___x_202_ = ((size_t)1ULL);
v___x_203_ = lean_usize_sub(v___x_201_, v___x_202_);
v___x_204_ = lean_usize_land(v___x_200_, v___x_203_);
v___x_205_ = lean_array_uget_borrowed(v_x_182_, v___x_204_);
lean_inc(v___x_205_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 2, v___x_205_);
v___x_207_ = v___x_188_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_key_184_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_value_185_);
lean_ctor_set(v_reuseFailAlloc_210_, 2, v___x_205_);
v___x_207_ = v_reuseFailAlloc_210_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; 
v___x_208_ = lean_array_uset(v_x_182_, v___x_204_, v___x_207_);
v_x_182_ = v___x_208_;
v_x_183_ = v_tail_186_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_i_214_, lean_object* v_source_215_, lean_object* v_target_216_){
_start:
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_array_get_size(v_source_215_);
v___x_218_ = lean_nat_dec_lt(v_i_214_, v___x_217_);
if (v___x_218_ == 0)
{
lean_dec_ref(v_source_215_);
lean_dec(v_i_214_);
return v_target_216_;
}
else
{
lean_object* v_es_219_; lean_object* v___x_220_; lean_object* v_source_221_; lean_object* v_target_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_es_219_ = lean_array_fget(v_source_215_, v_i_214_);
v___x_220_ = lean_box(0);
v_source_221_ = lean_array_fset(v_source_215_, v_i_214_, v___x_220_);
v_target_222_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(v_target_216_, v_es_219_);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_nat_add(v_i_214_, v___x_223_);
lean_dec(v_i_214_);
v_i_214_ = v___x_224_;
v_source_215_ = v_source_221_;
v_target_216_ = v_target_222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(lean_object* v_data_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v_nbuckets_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_227_ = lean_array_get_size(v_data_226_);
v___x_228_ = lean_unsigned_to_nat(2u);
v_nbuckets_229_ = lean_nat_mul(v___x_227_, v___x_228_);
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_box(0);
v___x_232_ = lean_mk_array(v_nbuckets_229_, v___x_231_);
v___x_233_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v___x_230_, v_data_226_, v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(lean_object* v_m_234_, lean_object* v_a_235_, lean_object* v_b_236_){
_start:
{
lean_object* v_size_237_; lean_object* v_buckets_238_; lean_object* v_keyName_239_; lean_object* v___x_240_; uint64_t v___y_242_; 
v_size_237_ = lean_ctor_get(v_m_234_, 0);
v_buckets_238_ = lean_ctor_get(v_m_234_, 1);
v_keyName_239_ = lean_ctor_get(v_a_235_, 2);
v___x_240_ = lean_array_get_size(v_buckets_238_);
if (lean_obj_tag(v_keyName_239_) == 0)
{
uint64_t v___x_279_; 
v___x_279_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0);
v___y_242_ = v___x_279_;
goto v___jp_241_;
}
else
{
uint64_t v_hash_280_; 
v_hash_280_ = lean_ctor_get_uint64(v_keyName_239_, sizeof(void*)*2);
v___y_242_ = v_hash_280_;
goto v___jp_241_;
}
v___jp_241_:
{
uint64_t v___x_243_; uint64_t v___x_244_; uint64_t v_fold_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v___x_248_; size_t v___x_249_; size_t v___x_250_; size_t v___x_251_; size_t v___x_252_; size_t v___x_253_; lean_object* v_bkt_254_; uint8_t v___x_255_; 
v___x_243_ = 32ULL;
v___x_244_ = lean_uint64_shift_right(v___y_242_, v___x_243_);
v_fold_245_ = lean_uint64_xor(v___y_242_, v___x_244_);
v___x_246_ = 16ULL;
v___x_247_ = lean_uint64_shift_right(v_fold_245_, v___x_246_);
v___x_248_ = lean_uint64_xor(v_fold_245_, v___x_247_);
v___x_249_ = lean_uint64_to_usize(v___x_248_);
v___x_250_ = lean_usize_of_nat(v___x_240_);
v___x_251_ = ((size_t)1ULL);
v___x_252_ = lean_usize_sub(v___x_250_, v___x_251_);
v___x_253_ = lean_usize_land(v___x_249_, v___x_252_);
v_bkt_254_ = lean_array_uget_borrowed(v_buckets_238_, v___x_253_);
v___x_255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_235_, v_bkt_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_276_; 
lean_inc_ref(v_buckets_238_);
lean_inc(v_size_237_);
v_isSharedCheck_276_ = !lean_is_exclusive(v_m_234_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; lean_object* v_unused_278_; 
v_unused_277_ = lean_ctor_get(v_m_234_, 1);
lean_dec(v_unused_277_);
v_unused_278_ = lean_ctor_get(v_m_234_, 0);
lean_dec(v_unused_278_);
v___x_257_ = v_m_234_;
v_isShared_258_ = v_isSharedCheck_276_;
goto v_resetjp_256_;
}
else
{
lean_dec(v_m_234_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_276_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v_size_x27_260_; lean_object* v___x_261_; lean_object* v_buckets_x27_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_259_ = lean_unsigned_to_nat(1u);
v_size_x27_260_ = lean_nat_add(v_size_237_, v___x_259_);
lean_dec(v_size_237_);
lean_inc(v_bkt_254_);
v___x_261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_261_, 0, v_a_235_);
lean_ctor_set(v___x_261_, 1, v_b_236_);
lean_ctor_set(v___x_261_, 2, v_bkt_254_);
v_buckets_x27_262_ = lean_array_uset(v_buckets_238_, v___x_253_, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(4u);
v___x_264_ = lean_nat_mul(v_size_x27_260_, v___x_263_);
v___x_265_ = lean_unsigned_to_nat(3u);
v___x_266_ = lean_nat_div(v___x_264_, v___x_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_array_get_size(v_buckets_x27_262_);
v___x_268_ = lean_nat_dec_le(v___x_266_, v___x_267_);
lean_dec(v___x_266_);
if (v___x_268_ == 0)
{
lean_object* v_val_269_; lean_object* v___x_271_; 
v_val_269_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_buckets_x27_262_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v_val_269_);
lean_ctor_set(v___x_257_, 0, v_size_x27_260_);
v___x_271_ = v___x_257_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_size_x27_260_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_val_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
else
{
lean_object* v___x_274_; 
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v_buckets_x27_262_);
lean_ctor_set(v___x_257_, 0, v_size_x27_260_);
v___x_274_ = v___x_257_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_size_x27_260_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_buckets_x27_262_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_dec(v_b_236_);
lean_dec_ref(v_a_235_);
return v_m_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(lean_object* v_self_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_toHashSet_283_; lean_object* v_toArray_284_; uint8_t v___x_285_; 
v_toHashSet_283_ = lean_ctor_get(v_self_281_, 0);
v_toArray_284_ = lean_ctor_get(v_self_281_, 1);
v___x_285_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_toHashSet_283_, v_a_282_);
if (v___x_285_ == 0)
{
lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_295_; 
lean_inc_ref(v_toArray_284_);
lean_inc_ref(v_toHashSet_283_);
v_isSharedCheck_295_ = !lean_is_exclusive(v_self_281_);
if (v_isSharedCheck_295_ == 0)
{
lean_object* v_unused_296_; lean_object* v_unused_297_; 
v_unused_296_ = lean_ctor_get(v_self_281_, 1);
lean_dec(v_unused_296_);
v_unused_297_ = lean_ctor_get(v_self_281_, 0);
lean_dec(v_unused_297_);
v___x_287_ = v_self_281_;
v_isShared_288_ = v_isSharedCheck_295_;
goto v_resetjp_286_;
}
else
{
lean_dec(v_self_281_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_295_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_289_ = lean_box(0);
lean_inc_ref(v_a_282_);
v___x_290_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_toHashSet_283_, v_a_282_, v___x_289_);
v___x_291_ = lean_array_push(v_toArray_284_, v_a_282_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v___x_291_);
lean_ctor_set(v___x_287_, 0, v___x_290_);
v___x_293_ = v___x_287_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
else
{
lean_dec_ref(v_a_282_);
return v_self_281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(lean_object* v_as_298_, size_t v_i_299_, size_t v_stop_300_, lean_object* v_b_301_){
_start:
{
uint8_t v___x_302_; 
v___x_302_ = lean_usize_dec_eq(v_i_299_, v_stop_300_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; size_t v___x_305_; size_t v___x_306_; 
v___x_303_ = lean_array_uget_borrowed(v_as_298_, v_i_299_);
lean_inc(v___x_303_);
v___x_304_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v_b_301_, v___x_303_);
v___x_305_ = ((size_t)1ULL);
v___x_306_ = lean_usize_add(v_i_299_, v___x_305_);
v_i_299_ = v___x_306_;
v_b_301_ = v___x_304_;
goto _start;
}
else
{
return v_b_301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1___boxed(lean_object* v_as_308_, lean_object* v_i_309_, lean_object* v_stop_310_, lean_object* v_b_311_){
_start:
{
size_t v_i_boxed_312_; size_t v_stop_boxed_313_; lean_object* v_res_314_; 
v_i_boxed_312_ = lean_unbox_usize(v_i_309_);
lean_dec(v_i_309_);
v_stop_boxed_313_ = lean_unbox_usize(v_stop_310_);
lean_dec(v_stop_310_);
v_res_314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_as_308_, v_i_boxed_312_, v_stop_boxed_313_, v_b_311_);
lean_dec_ref(v_as_308_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(lean_object* v_as_315_, size_t v_i_316_, size_t v_stop_317_, lean_object* v_b_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_usize_dec_eq(v_i_316_, v_stop_317_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v_keyName_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_327_ = lean_array_uget_borrowed(v_as_315_, v_i_316_);
v_keyName_328_ = lean_ctor_get(v___x_327_, 2);
v___x_329_ = l_Lake_Package_transDepsFacet;
lean_inc(v_keyName_328_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v_keyName_328_);
v___x_331_ = l_Lake_Package_keyword;
lean_inc(v___x_327_);
v___x_332_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
lean_ctor_set(v___x_332_, 2, v___x_327_);
lean_ctor_set(v___x_332_, 3, v___x_329_);
lean_inc_ref(v___y_319_);
lean_inc_ref(v___y_323_);
lean_inc(v___y_322_);
lean_inc(v___y_321_);
lean_inc(v___y_320_);
v___x_333_ = lean_apply_7(v___y_319_, v___x_332_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, lean_box(0));
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v_a_335_; lean_object* v___x_336_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
v_a_335_ = lean_ctor_get(v___x_333_, 1);
lean_inc(v_a_335_);
lean_dec_ref(v___x_333_);
v___x_336_ = l_Lake_Job_await___redArg(v_a_334_, v_a_335_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v_a_338_; lean_object* v___y_340_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
v_a_338_ = lean_ctor_get(v___x_336_, 1);
lean_inc(v_a_338_);
lean_dec_ref(v___x_336_);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_array_get_size(v_a_337_);
v___x_347_ = lean_nat_dec_lt(v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
lean_dec(v_a_337_);
v___y_340_ = v_b_318_;
goto v___jp_339_;
}
else
{
uint8_t v___x_348_; 
v___x_348_ = lean_nat_dec_le(v___x_346_, v___x_346_);
if (v___x_348_ == 0)
{
if (v___x_347_ == 0)
{
lean_dec(v_a_337_);
v___y_340_ = v_b_318_;
goto v___jp_339_;
}
else
{
size_t v___x_349_; size_t v___x_350_; lean_object* v___x_351_; 
v___x_349_ = ((size_t)0ULL);
v___x_350_ = lean_usize_of_nat(v___x_346_);
v___x_351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_337_, v___x_349_, v___x_350_, v_b_318_);
lean_dec(v_a_337_);
v___y_340_ = v___x_351_;
goto v___jp_339_;
}
}
else
{
size_t v___x_352_; size_t v___x_353_; lean_object* v___x_354_; 
v___x_352_ = ((size_t)0ULL);
v___x_353_ = lean_usize_of_nat(v___x_346_);
v___x_354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_337_, v___x_352_, v___x_353_, v_b_318_);
lean_dec(v_a_337_);
v___y_340_ = v___x_354_;
goto v___jp_339_;
}
}
v___jp_339_:
{
lean_object* v___x_341_; size_t v___x_342_; size_t v___x_343_; 
lean_inc(v___x_327_);
v___x_341_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v___y_340_, v___x_327_);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_add(v_i_316_, v___x_342_);
v_i_316_ = v___x_343_;
v_b_318_ = v___x_341_;
v___y_324_ = v_a_338_;
goto _start;
}
}
else
{
lean_object* v_a_355_; lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec_ref(v___y_319_);
lean_dec_ref(v_b_318_);
v_a_355_ = lean_ctor_get(v___x_336_, 0);
v_a_356_ = lean_ctor_get(v___x_336_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_336_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_inc(v_a_355_);
lean_dec(v___x_336_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_355_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_dec_ref(v___y_319_);
lean_dec_ref(v_b_318_);
v_a_364_ = lean_ctor_get(v___x_333_, 0);
v_a_365_ = lean_ctor_get(v___x_333_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_333_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_inc(v_a_364_);
lean_dec(v___x_333_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_364_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
else
{
lean_object* v___x_373_; 
lean_dec_ref(v___y_319_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v_b_318_);
lean_ctor_set(v___x_373_, 1, v___y_324_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3___boxed(lean_object* v_as_374_, lean_object* v_i_375_, lean_object* v_stop_376_, lean_object* v_b_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
size_t v_i_boxed_385_; size_t v_stop_boxed_386_; lean_object* v_res_387_; 
v_i_boxed_385_ = lean_unbox_usize(v_i_375_);
lean_dec(v_i_375_);
v_stop_boxed_386_ = lean_unbox_usize(v_stop_376_);
lean_dec(v_stop_376_);
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_as_374_, v_i_boxed_385_, v_stop_boxed_386_, v_b_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v_as_374_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(lean_object* v___x_388_, lean_object* v___x_389_, lean_object* v___x_390_, lean_object* v___x_391_, lean_object* v_depPkgs_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_a_401_; lean_object* v_a_402_; lean_object* v___y_422_; uint8_t v___x_434_; 
v___x_434_ = lean_nat_dec_lt(v___x_388_, v___x_390_);
if (v___x_434_ == 0)
{
lean_dec_ref(v___y_393_);
v_a_401_ = v___x_391_;
v_a_402_ = v___y_398_;
goto v___jp_400_;
}
else
{
uint8_t v___x_435_; 
v___x_435_ = lean_nat_dec_le(v___x_390_, v___x_390_);
if (v___x_435_ == 0)
{
if (v___x_434_ == 0)
{
lean_dec_ref(v___y_393_);
v_a_401_ = v___x_391_;
v_a_402_ = v___y_398_;
goto v___jp_400_;
}
else
{
size_t v___x_436_; size_t v___x_437_; lean_object* v___x_438_; 
v___x_436_ = ((size_t)0ULL);
v___x_437_ = lean_usize_of_nat(v___x_390_);
v___x_438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_392_, v___x_436_, v___x_437_, v___x_391_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
v___y_422_ = v___x_438_;
goto v___jp_421_;
}
}
else
{
size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
v___x_439_ = ((size_t)0ULL);
v___x_440_ = lean_usize_of_nat(v___x_390_);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_392_, v___x_439_, v___x_440_, v___x_391_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
v___y_422_ = v___x_441_;
goto v___jp_421_;
}
}
v___jp_400_:
{
lean_object* v_toArray_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_419_; 
v_toArray_403_ = lean_ctor_get(v_a_401_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_a_401_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v_a_401_, 0);
lean_dec(v_unused_420_);
v___x_405_ = v_a_401_;
v_isShared_406_ = v_isSharedCheck_419_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_toArray_403_);
lean_dec(v_a_401_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_419_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_407_ = lean_mk_empty_array_with_capacity(v___x_388_);
v___x_408_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_409_ = 0;
v___x_410_ = 0;
v___x_411_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_412_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_412_, 0, v___x_407_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
lean_ctor_set(v___x_412_, 2, v___x_388_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*3, v___x_409_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*3 + 1, v___x_410_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v___x_412_);
lean_ctor_set(v___x_405_, 0, v_toArray_403_);
v___x_414_ = v___x_405_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_toArray_403_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___x_412_);
v___x_414_ = v_reuseFailAlloc_418_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_task_pure(v___x_414_);
v___x_416_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v___x_389_);
lean_ctor_set(v___x_416_, 2, v___x_408_);
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*3, v___x_410_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v_a_402_);
return v___x_417_;
}
}
}
v___jp_421_:
{
if (lean_obj_tag(v___y_422_) == 0)
{
lean_object* v_a_423_; lean_object* v_a_424_; 
v_a_423_ = lean_ctor_get(v___y_422_, 0);
lean_inc(v_a_423_);
v_a_424_ = lean_ctor_get(v___y_422_, 1);
lean_inc(v_a_424_);
lean_dec_ref(v___y_422_);
v_a_401_ = v_a_423_;
v_a_402_ = v_a_424_;
goto v___jp_400_;
}
else
{
lean_object* v_a_425_; lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec(v___x_389_);
lean_dec(v___x_388_);
v_a_425_ = lean_ctor_get(v___y_422_, 0);
v_a_426_ = lean_ctor_get(v___y_422_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v___y_422_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___y_422_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_inc(v_a_425_);
lean_dec(v___y_422_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_425_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed(lean_object* v___x_442_, lean_object* v___x_443_, lean_object* v___x_444_, lean_object* v___x_445_, lean_object* v_depPkgs_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(v___x_442_, v___x_443_, v___x_444_, v___x_445_, v_depPkgs_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v_depPkgs_446_);
lean_dec(v___x_444_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(lean_object* v_self_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_depPkgs_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___f_468_; lean_object* v___x_469_; 
v_depPkgs_463_ = lean_ctor_get(v_self_455_, 13);
lean_inc_ref(v_depPkgs_463_);
lean_dec_ref(v_self_455_);
v___x_464_ = lean_box(0);
v___x_465_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2;
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_array_get_size(v_depPkgs_463_);
v___f_468_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed), 12, 5);
lean_closure_set(v___f_468_, 0, v___x_466_);
lean_closure_set(v___f_468_, 1, v___x_464_);
lean_closure_set(v___f_468_, 2, v___x_467_);
lean_closure_set(v___f_468_, 3, v___x_465_);
lean_closure_set(v___f_468_, 4, v_depPkgs_463_);
v___x_469_ = l_Lake_ensureJob___redArg(v___x_464_, v___f_468_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___boxed(lean_object* v_self_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(v_self_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec(v_a_473_);
lean_dec(v_a_472_);
return v_res_478_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object* v_00_u03b2_479_, lean_object* v_m_480_, lean_object* v_a_481_){
_start:
{
uint8_t v___x_482_; 
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_480_, v_a_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_483_, lean_object* v_m_484_, lean_object* v_a_485_){
_start:
{
uint8_t v_res_486_; lean_object* v_r_487_; 
v_res_486_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(v_00_u03b2_483_, v_m_484_, v_a_485_);
lean_dec_ref(v_a_485_);
lean_dec_ref(v_m_484_);
v_r_487_ = lean_box(v_res_486_);
return v_r_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1(lean_object* v_00_u03b2_488_, lean_object* v_m_489_, lean_object* v_a_490_, lean_object* v_b_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_m_489_, v_a_490_, v_b_491_);
return v___x_492_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_493_, lean_object* v_a_494_, lean_object* v_x_495_){
_start:
{
uint8_t v___x_496_; 
v___x_496_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_494_, v_x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_497_, lean_object* v_a_498_, lean_object* v_x_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(v_00_u03b2_497_, v_a_498_, v_x_499_);
lean_dec(v_x_499_);
lean_dec_ref(v_a_498_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_502_, lean_object* v_data_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_data_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_505_, lean_object* v_i_506_, lean_object* v_source_507_, lean_object* v_target_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v_i_506_, v_source_507_, v_target_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_510_, lean_object* v_x_511_, lean_object* v_x_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(v_x_511_, v_x_512_);
return v___x_513_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_515_; lean_object* v___f_516_; uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_515_ = 1;
v___f_516_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__0));
v___x_517_ = 0;
v___x_518_ = lean_box(0);
v___x_519_ = ((lean_object*)(l_Lake_Package_transDepsFacetConfig___closed__0));
v___x_520_ = l_Lake_Package_keyword;
v___x_521_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v___x_519_);
lean_ctor_set(v___x_521_, 2, v___x_518_);
lean_ctor_set(v___x_521_, 3, v___f_516_);
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*4, v___x_517_);
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*4 + 1, v___x_515_);
return v___x_521_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig(void){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_obj_once(&l_Lake_Package_transDepsFacetConfig___closed__1, &l_Lake_Package_transDepsFacetConfig___closed__1_once, _init_l_Lake_Package_transDepsFacetConfig___closed__1);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object* v_self_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_config_531_; uint8_t v_preferReleaseBuild_532_; 
v_config_531_ = lean_ctor_get(v_self_523_, 6);
v_preferReleaseBuild_532_ = lean_ctor_get_uint8(v_config_531_, sizeof(void*)*27 + 2);
if (v_preferReleaseBuild_532_ == 0)
{
lean_object* v_keyName_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_keyName_533_ = lean_ctor_get(v_self_523_, 2);
v___x_534_ = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(v_keyName_533_);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v_keyName_533_);
v___x_536_ = l_Lake_Package_keyword;
v___x_537_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
lean_ctor_set(v___x_537_, 2, v_self_523_);
lean_ctor_set(v___x_537_, 3, v___x_534_);
lean_inc_ref(v_a_528_);
lean_inc(v_a_527_);
lean_inc(v_a_526_);
lean_inc(v_a_525_);
v___x_538_ = lean_apply_7(v_a_524_, v___x_537_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, lean_box(0));
return v___x_538_;
}
else
{
lean_object* v_keyName_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_keyName_539_ = lean_ctor_get(v_self_523_, 2);
v___x_540_ = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(v_keyName_539_);
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v_keyName_539_);
v___x_542_ = l_Lake_Package_keyword;
v___x_543_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
lean_ctor_set(v___x_543_, 2, v_self_523_);
lean_ctor_set(v___x_543_, 3, v___x_540_);
lean_inc_ref(v_a_528_);
lean_inc(v_a_527_);
lean_inc(v_a_526_);
lean_inc(v_a_525_);
v___x_544_ = lean_apply_7(v_a_524_, v___x_543_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, lean_box(0));
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___boxed(lean_object* v_self_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(v_self_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec(v_a_548_);
lean_dec(v_a_547_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t v_fmt_556_, uint8_t v_a_557_){
_start:
{
if (v_fmt_556_ == 0)
{
if (v_a_557_ == 0)
{
lean_object* v___x_558_; 
v___x_558_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0));
return v___x_558_;
}
else
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1));
return v___x_559_;
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_560_, 0, v_a_557_);
v___x_561_ = l_Lean_Json_compress(v___x_560_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object* v_fmt_562_, lean_object* v_a_563_){
_start:
{
uint8_t v_fmt_boxed_564_; uint8_t v_a_boxed_565_; lean_object* v_res_566_; 
v_fmt_boxed_564_ = lean_unbox(v_fmt_562_);
v_a_boxed_565_ = lean_unbox(v_a_563_);
v_res_566_ = l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(v_fmt_boxed_564_, v_a_boxed_565_);
return v_res_566_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_569_; uint8_t v___x_570_; lean_object* v___x_571_; lean_object* v___f_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___f_569_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_570_ = 1;
v___x_571_ = l_Lake_instDataKindBool;
v___f_572_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__0));
v___x_573_ = l_Lake_Package_keyword;
v___x_574_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___f_572_);
lean_ctor_set(v___x_574_, 2, v___x_571_);
lean_ctor_set(v___x_574_, 3, v___f_569_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*4, v___x_570_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*4 + 1, v___x_570_);
return v___x_574_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_obj_once(&l_Lake_Package_optBuildCacheFacetConfig___closed__2, &l_Lake_Package_optBuildCacheFacetConfig___closed__2_once, _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(lean_object* v_self_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v___y_587_; uint8_t v___y_588_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_611_; uint8_t v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; uint8_t v___y_615_; lean_object* v_toContext_619_; lean_object* v_lakeEnv_620_; uint8_t v_noCache_621_; lean_object* v_toolchain_622_; uint8_t v_a_624_; lean_object* v_a_625_; 
v_toContext_619_ = lean_ctor_get(v_a_583_, 1);
v_lakeEnv_620_ = lean_ctor_get(v_toContext_619_, 0);
v_noCache_621_ = lean_ctor_get_uint8(v_lakeEnv_620_, sizeof(void*)*19);
v_toolchain_622_ = lean_ctor_get(v_lakeEnv_620_, 18);
if (v_noCache_621_ == 0)
{
uint8_t v___x_640_; 
v___x_640_ = 1;
v_a_624_ = v___x_640_;
v_a_625_ = v_a_584_;
goto v___jp_623_;
}
else
{
uint8_t v___x_641_; 
v___x_641_ = 0;
v_a_624_ = v___x_641_;
v_a_625_ = v_a_584_;
goto v___jp_623_;
}
v___jp_586_:
{
uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_589_ = 1;
v___x_590_ = lean_box(0);
v___x_591_ = lean_unsigned_to_nat(0u);
v___x_592_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_593_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_594_ = 0;
v___x_595_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_596_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_596_, 0, v___x_592_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
lean_ctor_set(v___x_596_, 2, v___x_591_);
lean_ctor_set_uint8(v___x_596_, sizeof(void*)*3, v___x_594_);
lean_ctor_set_uint8(v___x_596_, sizeof(void*)*3 + 1, v___y_588_);
v___x_597_ = lean_box(v___x_589_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___x_596_);
v___x_599_ = lean_task_pure(v___x_598_);
v___x_600_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_590_);
lean_ctor_set(v___x_600_, 2, v___x_593_);
lean_ctor_set_uint8(v___x_600_, sizeof(void*)*3, v___y_588_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___y_587_);
return v___x_601_;
}
v___jp_602_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_605_ = l_Lake_Package_optBuildCacheFacet;
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v___y_604_);
v___x_607_ = l_Lake_Package_keyword;
v___x_608_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
lean_ctor_set(v___x_608_, 2, v_self_578_);
lean_ctor_set(v___x_608_, 3, v___x_605_);
lean_inc_ref(v_a_583_);
lean_inc(v_a_582_);
lean_inc(v_a_581_);
lean_inc(v_a_580_);
v___x_609_ = lean_apply_7(v_a_579_, v___x_608_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v___y_603_, lean_box(0));
return v___x_609_;
}
v___jp_610_:
{
if (v___y_615_ == 0)
{
lean_dec(v___y_613_);
lean_dec_ref(v_a_579_);
lean_dec_ref(v_self_578_);
v___y_587_ = v___y_611_;
v___y_588_ = v___y_615_;
goto v___jp_586_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_616_ = lean_string_utf8_byte_size(v___y_614_);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = lean_nat_dec_eq(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
v___y_603_ = v___y_611_;
v___y_604_ = v___y_613_;
goto v___jp_602_;
}
else
{
lean_dec(v___y_613_);
lean_dec_ref(v_a_579_);
lean_dec_ref(v_self_578_);
v___y_587_ = v___y_611_;
v___y_588_ = v___y_612_;
goto v___jp_586_;
}
}
}
v___jp_623_:
{
lean_object* v_config_626_; lean_object* v_keyName_627_; lean_object* v_dir_628_; lean_object* v_scope_629_; lean_object* v_buildDir_630_; uint8_t v_preferReleaseBuild_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_config_626_ = lean_ctor_get(v_self_578_, 6);
v_keyName_627_ = lean_ctor_get(v_self_578_, 2);
v_dir_628_ = lean_ctor_get(v_self_578_, 4);
v_scope_629_ = lean_ctor_get(v_self_578_, 10);
v_buildDir_630_ = lean_ctor_get(v_config_626_, 5);
v_preferReleaseBuild_631_ = lean_ctor_get_uint8(v_config_626_, sizeof(void*)*27 + 2);
lean_inc_ref(v_buildDir_630_);
v___x_632_ = l_System_FilePath_normalize(v_buildDir_630_);
lean_inc_ref(v_dir_628_);
v___x_633_ = l_Lake_joinRelative(v_dir_628_, v___x_632_);
v___x_634_ = l_System_FilePath_pathExists(v___x_633_);
lean_dec_ref(v___x_633_);
if (v_a_624_ == 0)
{
lean_dec_ref(v_a_579_);
lean_dec_ref(v_self_578_);
v___y_587_ = v_a_625_;
v___y_588_ = v_a_624_;
goto v___jp_586_;
}
else
{
if (v___x_634_ == 0)
{
if (v_preferReleaseBuild_631_ == 0)
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0));
v___x_636_ = lean_string_dec_eq(v_scope_629_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1));
v___x_638_ = lean_string_dec_eq(v_scope_629_, v___x_637_);
lean_inc(v_keyName_627_);
v___y_611_ = v_a_625_;
v___y_612_ = v_preferReleaseBuild_631_;
v___y_613_ = v_keyName_627_;
v___y_614_ = v_toolchain_622_;
v___y_615_ = v___x_638_;
goto v___jp_610_;
}
else
{
lean_inc(v_keyName_627_);
v___y_611_ = v_a_625_;
v___y_612_ = v_preferReleaseBuild_631_;
v___y_613_ = v_keyName_627_;
v___y_614_ = v_toolchain_622_;
v___y_615_ = v___x_636_;
goto v___jp_610_;
}
}
else
{
lean_inc(v_keyName_627_);
v___y_603_ = v_a_625_;
v___y_604_ = v_keyName_627_;
goto v___jp_602_;
}
}
else
{
uint8_t v___x_639_; 
lean_dec_ref(v_a_579_);
lean_dec_ref(v_self_578_);
v___x_639_ = 0;
v___y_587_ = v_a_625_;
v___y_588_ = v___x_639_;
goto v___jp_586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___boxed(lean_object* v_self_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec(v_a_645_);
lean_dec(v_a_644_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object* v_self_655_, lean_object* v_facet_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_toBuildConfig_660_; uint8_t v_verbosity_661_; uint8_t v___x_662_; uint8_t v___x_663_; 
v_toBuildConfig_660_ = lean_ctor_get(v_a_657_, 0);
v_verbosity_661_ = lean_ctor_get_uint8(v_toBuildConfig_660_, sizeof(void*)*3 + 3);
v___x_662_ = 2;
v___x_663_ = l_Lake_instDecidableEqVerbosity(v_verbosity_661_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec(v_facet_656_);
lean_dec_ref(v_self_655_);
v___x_664_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v_a_658_);
return v___x_665_;
}
else
{
lean_object* v_baseName_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_baseName_666_ = lean_ctor_get(v_self_655_, 1);
lean_inc(v_baseName_666_);
lean_dec_ref(v_self_655_);
v___x_667_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_668_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_666_, v___x_663_);
v___x_669_ = lean_string_append(v___x_667_, v___x_668_);
lean_dec_ref(v___x_668_);
v___x_670_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_671_ = lean_string_append(v___x_669_, v___x_670_);
v___x_672_ = l_Lake_Name_eraseHead(v_facet_656_);
v___x_673_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_672_, v___x_663_);
v___x_674_ = lean_string_append(v___x_671_, v___x_673_);
lean_dec_ref(v___x_673_);
v___x_675_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_676_ = lean_string_append(v___x_674_, v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v_a_658_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* v_self_678_, lean_object* v_facet_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(v_self_678_, v_facet_679_, v_a_680_, v_a_681_);
lean_dec_ref(v_a_680_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* v_self_684_, lean_object* v_facet_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_toBuildConfig_693_; uint8_t v_verbosity_694_; uint8_t v___x_695_; uint8_t v___x_696_; 
v_toBuildConfig_693_ = lean_ctor_get(v_a_690_, 0);
v_verbosity_694_ = lean_ctor_get_uint8(v_toBuildConfig_693_, sizeof(void*)*3 + 3);
v___x_695_ = 2;
v___x_696_ = l_Lake_instDecidableEqVerbosity(v_verbosity_694_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; 
lean_dec(v_facet_685_);
lean_dec_ref(v_self_684_);
v___x_697_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v_a_691_);
return v___x_698_;
}
else
{
lean_object* v_baseName_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v_baseName_699_ = lean_ctor_get(v_self_684_, 1);
lean_inc(v_baseName_699_);
lean_dec_ref(v_self_684_);
v___x_700_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_701_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_699_, v___x_696_);
v___x_702_ = lean_string_append(v___x_700_, v___x_701_);
lean_dec_ref(v___x_701_);
v___x_703_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_704_ = lean_string_append(v___x_702_, v___x_703_);
v___x_705_ = l_Lake_Name_eraseHead(v_facet_685_);
v___x_706_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_705_, v___x_696_);
v___x_707_ = lean_string_append(v___x_704_, v___x_706_);
lean_dec_ref(v___x_706_);
v___x_708_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_709_ = lean_string_append(v___x_707_, v___x_708_);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v_a_691_);
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* v_self_711_, lean_object* v_facet_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(v_self_711_, v_facet_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
return v_res_720_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_724_ = l_Lake_Name_eraseHead(v___x_723_);
return v___x_724_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_726_ = l_Lake_Name_eraseHead(v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(lean_object* v_self_727_, uint8_t v_success_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v_a_737_; lean_object* v_a_738_; lean_object* v_a_759_; lean_object* v_a_760_; 
if (v_success_728_ == 0)
{
lean_object* v_config_780_; uint8_t v_preferReleaseBuild_781_; 
v_config_780_ = lean_ctor_get(v_self_727_, 6);
v_preferReleaseBuild_781_ = lean_ctor_get_uint8(v_config_780_, sizeof(void*)*27 + 2);
if (v_preferReleaseBuild_781_ == 0)
{
lean_object* v_toBuildConfig_782_; lean_object* v_baseName_783_; uint8_t v_verbosity_784_; uint8_t v___x_785_; uint8_t v___x_786_; 
v_toBuildConfig_782_ = lean_ctor_get(v___y_733_, 0);
v_baseName_783_ = lean_ctor_get(v_self_727_, 1);
lean_inc(v_baseName_783_);
lean_dec_ref(v_self_727_);
v_verbosity_784_ = lean_ctor_get_uint8(v_toBuildConfig_782_, sizeof(void*)*3 + 3);
v___x_785_ = 2;
v___x_786_ = l_Lake_instDecidableEqVerbosity(v_verbosity_784_, v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; 
lean_dec(v_baseName_783_);
v___x_787_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_737_ = v___x_787_;
v_a_738_ = v___y_734_;
goto v___jp_736_;
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_788_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_789_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_783_, v___x_786_);
v___x_790_ = lean_string_append(v___x_788_, v___x_789_);
lean_dec_ref(v___x_789_);
v___x_791_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_792_ = lean_string_append(v___x_790_, v___x_791_);
v___x_793_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2);
v___x_794_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_793_, v___x_786_);
v___x_795_ = lean_string_append(v___x_792_, v___x_794_);
lean_dec_ref(v___x_794_);
v___x_796_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_797_ = lean_string_append(v___x_795_, v___x_796_);
v_a_737_ = v___x_797_;
v_a_738_ = v___y_734_;
goto v___jp_736_;
}
}
else
{
lean_object* v_toBuildConfig_798_; lean_object* v_baseName_799_; uint8_t v_verbosity_800_; uint8_t v___x_801_; uint8_t v___x_802_; 
v_toBuildConfig_798_ = lean_ctor_get(v___y_733_, 0);
v_baseName_799_ = lean_ctor_get(v_self_727_, 1);
lean_inc(v_baseName_799_);
lean_dec_ref(v_self_727_);
v_verbosity_800_ = lean_ctor_get_uint8(v_toBuildConfig_798_, sizeof(void*)*3 + 3);
v___x_801_ = 2;
v___x_802_ = l_Lake_instDecidableEqVerbosity(v_verbosity_800_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; 
lean_dec(v_baseName_799_);
v___x_803_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_759_ = v___x_803_;
v_a_760_ = v___y_734_;
goto v___jp_758_;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_804_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_805_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_799_, v___x_802_);
v___x_806_ = lean_string_append(v___x_804_, v___x_805_);
lean_dec_ref(v___x_805_);
v___x_807_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_808_ = lean_string_append(v___x_806_, v___x_807_);
v___x_809_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
v___x_810_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_809_, v___x_802_);
v___x_811_ = lean_string_append(v___x_808_, v___x_810_);
lean_dec_ref(v___x_810_);
v___x_812_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_813_ = lean_string_append(v___x_811_, v___x_812_);
v_a_759_ = v___x_813_;
v_a_760_ = v___y_734_;
goto v___jp_758_;
}
}
}
else
{
lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec_ref(v_self_727_);
v___x_814_ = lean_box(0);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v___y_734_);
return v___x_815_;
}
v___jp_736_:
{
lean_object* v_log_739_; uint8_t v_action_740_; uint8_t v_wantsRebuild_741_; lean_object* v_trace_742_; lean_object* v_buildTime_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_757_; 
v_log_739_ = lean_ctor_get(v_a_738_, 0);
v_action_740_ = lean_ctor_get_uint8(v_a_738_, sizeof(void*)*3);
v_wantsRebuild_741_ = lean_ctor_get_uint8(v_a_738_, sizeof(void*)*3 + 1);
v_trace_742_ = lean_ctor_get(v_a_738_, 1);
v_buildTime_743_ = lean_ctor_get(v_a_738_, 2);
v_isSharedCheck_757_ = !lean_is_exclusive(v_a_738_);
if (v_isSharedCheck_757_ == 0)
{
v___x_745_ = v_a_738_;
v_isShared_746_ = v_isSharedCheck_757_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_buildTime_743_);
lean_inc(v_trace_742_);
lean_inc(v_log_739_);
lean_dec(v_a_738_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_757_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_747_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0));
v___x_748_ = lean_string_append(v___x_747_, v_a_737_);
lean_dec_ref(v_a_737_);
v___x_749_ = 0;
v___x_750_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set_uint8(v___x_750_, sizeof(void*)*1, v___x_749_);
v___x_751_ = lean_box(0);
v___x_752_ = lean_array_push(v_log_739_, v___x_750_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_752_);
v___x_754_ = v___x_745_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_trace_742_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_buildTime_743_);
lean_ctor_set_uint8(v_reuseFailAlloc_756_, sizeof(void*)*3, v_action_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_756_, sizeof(void*)*3 + 1, v_wantsRebuild_741_);
v___x_754_ = v_reuseFailAlloc_756_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; 
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_751_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
return v___x_755_;
}
}
}
v___jp_758_:
{
lean_object* v_log_761_; uint8_t v_action_762_; uint8_t v_wantsRebuild_763_; lean_object* v_trace_764_; lean_object* v_buildTime_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_779_; 
v_log_761_ = lean_ctor_get(v_a_760_, 0);
v_action_762_ = lean_ctor_get_uint8(v_a_760_, sizeof(void*)*3);
v_wantsRebuild_763_ = lean_ctor_get_uint8(v_a_760_, sizeof(void*)*3 + 1);
v_trace_764_ = lean_ctor_get(v_a_760_, 1);
v_buildTime_765_ = lean_ctor_get(v_a_760_, 2);
v_isSharedCheck_779_ = !lean_is_exclusive(v_a_760_);
if (v_isSharedCheck_779_ == 0)
{
v___x_767_ = v_a_760_;
v_isShared_768_ = v_isSharedCheck_779_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_buildTime_765_);
lean_inc(v_trace_764_);
lean_inc(v_log_761_);
lean_dec(v_a_760_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_779_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_769_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1));
v___x_770_ = lean_string_append(v___x_769_, v_a_759_);
lean_dec_ref(v_a_759_);
v___x_771_ = 2;
v___x_772_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set_uint8(v___x_772_, sizeof(void*)*1, v___x_771_);
v___x_773_ = lean_box(0);
v___x_774_ = lean_array_push(v_log_761_, v___x_772_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_774_);
v___x_776_ = v___x_767_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_trace_764_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_buildTime_765_);
lean_ctor_set_uint8(v_reuseFailAlloc_778_, sizeof(void*)*3, v_action_762_);
lean_ctor_set_uint8(v_reuseFailAlloc_778_, sizeof(void*)*3 + 1, v_wantsRebuild_763_);
v___x_776_ = v_reuseFailAlloc_778_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; 
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_773_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
return v___x_777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* v_self_816_, lean_object* v_success_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
uint8_t v_success_boxed_825_; lean_object* v_res_826_; 
v_success_boxed_825_ = lean_unbox(v_success_817_);
v_res_826_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(v_self_816_, v_success_boxed_825_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* v_self_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___x_835_; 
lean_inc_ref(v_a_828_);
lean_inc_ref(v_self_827_);
v___x_835_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_850_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
v_a_837_ = lean_ctor_get(v___x_835_, 1);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_850_ == 0)
{
v___x_839_ = v___x_835_;
v_isShared_840_ = v_isSharedCheck_850_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_inc(v_a_836_);
lean_dec(v___x_835_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_850_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___f_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
v___f_841_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(v___f_841_, 0, v_self_827_);
v___x_842_ = l_Lake_instDataKindUnit;
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = 0;
v___x_845_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_846_ = l_Lake_Job_mapM___redArg(v___x_842_, v_a_836_, v___f_841_, v___x_843_, v___x_844_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v___x_845_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_846_);
v___x_848_ = v___x_839_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v_a_837_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
else
{
lean_object* v_a_851_; lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref(v_a_828_);
lean_dec_ref(v_self_827_);
v_a_851_ = lean_ctor_get(v___x_835_, 0);
v_a_852_ = lean_ctor_get(v___x_835_, 1);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_835_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_inc(v_a_851_);
lean_dec(v___x_835_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_851_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(lean_object* v_self_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
lean_dec_ref(v_a_865_);
lean_dec(v_a_864_);
lean_dec(v_a_863_);
lean_dec(v_a_862_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* v_self_869_, lean_object* v_as_870_, size_t v_sz_871_, size_t v_i_872_, lean_object* v_b_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
uint8_t v___x_881_; 
v___x_881_ = lean_usize_dec_lt(v_i_872_, v_sz_871_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; 
lean_dec_ref(v___y_874_);
lean_dec_ref(v_self_869_);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v_b_873_);
lean_ctor_set(v___x_882_, 1, v___y_879_);
return v___x_882_;
}
else
{
lean_object* v_a_883_; lean_object* v___x_884_; 
v_a_883_ = lean_array_uget_borrowed(v_as_870_, v_i_872_);
lean_inc_ref(v___y_874_);
lean_inc(v_a_883_);
lean_inc_ref(v_self_869_);
v___x_884_ = l_Lake_Package_fetchTargetJob(v_self_869_, v_a_883_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v_a_886_; lean_object* v___x_887_; size_t v___x_888_; size_t v___x_889_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
v_a_886_ = lean_ctor_get(v___x_884_, 1);
lean_inc(v_a_886_);
lean_dec_ref(v___x_884_);
v___x_887_ = l_Lake_Job_mix___redArg(v_b_873_, v_a_885_);
v___x_888_ = ((size_t)1ULL);
v___x_889_ = lean_usize_add(v_i_872_, v___x_888_);
v_i_872_ = v___x_889_;
v_b_873_ = v___x_887_;
v___y_879_ = v_a_886_;
goto _start;
}
else
{
lean_object* v_a_891_; lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref(v___y_874_);
lean_dec_ref(v_b_873_);
lean_dec_ref(v_self_869_);
v_a_891_ = lean_ctor_get(v___x_884_, 0);
v_a_892_ = lean_ctor_get(v___x_884_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_884_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_inc(v_a_891_);
lean_dec(v___x_884_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_891_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* v_self_900_, lean_object* v_as_901_, lean_object* v_sz_902_, lean_object* v_i_903_, lean_object* v_b_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
size_t v_sz_boxed_912_; size_t v_i_boxed_913_; lean_object* v_res_914_; 
v_sz_boxed_912_ = lean_unbox_usize(v_sz_902_);
lean_dec(v_sz_902_);
v_i_boxed_913_ = lean_unbox_usize(v_i_903_);
lean_dec(v_i_903_);
v_res_914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_900_, v_as_901_, v_sz_boxed_912_, v_i_boxed_913_, v_b_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v_as_901_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object* v_config_915_, lean_object* v_self_916_, lean_object* v_____r_917_, lean_object* v_job_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_extraDepTargets_926_; size_t v_sz_927_; size_t v___x_928_; lean_object* v___x_929_; 
v_extraDepTargets_926_ = lean_ctor_get(v_config_915_, 2);
v_sz_927_ = lean_array_size(v_extraDepTargets_926_);
v___x_928_ = ((size_t)0ULL);
v___x_929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_916_, v_extraDepTargets_926_, v_sz_927_, v___x_928_, v_job_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object* v_config_930_, lean_object* v_self_931_, lean_object* v_____r_932_, lean_object* v_job_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(v_config_930_, v_self_931_, v_____r_932_, v_job_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v_config_930_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(uint8_t v___x_942_, lean_object* v_self_943_, lean_object* v_job_944_, lean_object* v___f_945_, lean_object* v___x_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
if (v___x_942_ == 0)
{
lean_object* v___x_954_; 
lean_inc_ref(v___y_947_);
v___x_954_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_943_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v_a_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
v_a_956_ = lean_ctor_get(v___x_954_, 1);
lean_inc(v_a_956_);
lean_dec_ref(v___x_954_);
v___x_957_ = l_Lake_Job_add___redArg(v_job_944_, v_a_955_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
lean_inc(v___y_949_);
lean_inc(v___y_948_);
v___x_958_ = lean_apply_9(v___f_945_, v___x_946_, v___x_957_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v_a_956_, lean_box(0));
return v___x_958_;
}
else
{
lean_dec_ref(v___y_947_);
lean_dec_ref(v___f_945_);
lean_dec_ref(v_job_944_);
return v___x_954_;
}
}
else
{
lean_object* v___x_959_; 
lean_dec_ref(v_self_943_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
lean_inc(v___y_949_);
lean_inc(v___y_948_);
v___x_959_ = lean_apply_9(v___f_945_, v___x_946_, v_job_944_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, lean_box(0));
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* v___x_960_, lean_object* v_self_961_, lean_object* v_job_962_, lean_object* v___f_963_, lean_object* v___x_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
uint8_t v___x_4162__boxed_972_; lean_object* v_res_973_; 
v___x_4162__boxed_972_ = lean_unbox(v___x_960_);
v_res_973_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(v___x_4162__boxed_972_, v_self_961_, v_job_962_, v___f_963_, v___x_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec(v___y_967_);
lean_dec(v___y_966_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object* v_self_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_wsIdx_984_; lean_object* v_baseName_985_; lean_object* v_config_986_; lean_object* v___f_987_; lean_object* v___x_988_; uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_job_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___y_1009_; lean_object* v___x_1010_; 
v_wsIdx_984_ = lean_ctor_get(v_self_976_, 0);
v_baseName_985_ = lean_ctor_get(v_self_976_, 1);
v_config_986_ = lean_ctor_get(v_self_976_, 6);
lean_inc_ref(v_self_976_);
lean_inc_ref(v_config_986_);
v___f_987_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed), 11, 2);
lean_closure_set(v___f_987_, 0, v_config_986_);
lean_closure_set(v___f_987_, 1, v_self_976_);
v___x_988_ = l_Lake_instDataKindUnit;
v___x_989_ = 1;
lean_inc(v_baseName_985_);
v___x_990_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_985_, v___x_989_);
v___x_991_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0));
v___x_992_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1));
v___x_993_ = lean_string_append(v___x_992_, v___x_990_);
v___x_994_ = lean_string_append(v___x_993_, v___x_991_);
v___x_995_ = lean_box(0);
v___x_996_ = lean_box(0);
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_999_ = 0;
v___x_1000_ = 0;
v___x_1001_ = l_Lake_BuildTrace_nil(v___x_994_);
v___x_1002_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1002_, 0, v___x_998_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
lean_ctor_set(v___x_1002_, 2, v___x_997_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*3, v___x_999_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*3 + 1, v___x_1000_);
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_995_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_task_pure(v___x_1003_);
v___x_1005_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_job_1006_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_1006_, 0, v___x_1004_);
lean_ctor_set(v_job_1006_, 1, v___x_996_);
lean_ctor_set(v_job_1006_, 2, v___x_1005_);
lean_ctor_set_uint8(v_job_1006_, sizeof(void*)*3, v___x_1000_);
v___x_1007_ = lean_nat_dec_eq(v_wsIdx_984_, v___x_997_);
v___x_1008_ = lean_box(v___x_1007_);
v___y_1009_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 12, 5);
lean_closure_set(v___y_1009_, 0, v___x_1008_);
lean_closure_set(v___y_1009_, 1, v_self_976_);
lean_closure_set(v___y_1009_, 2, v_job_1006_);
lean_closure_set(v___y_1009_, 3, v___f_987_);
lean_closure_set(v___y_1009_, 4, v___x_995_);
v___x_1010_ = l_Lake_ensureJob___redArg(v___x_988_, v___y_1009_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1036_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_a_1012_ = lean_ctor_get(v___x_1010_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1014_ = v___x_1010_;
v_isShared_1015_ = v_isSharedCheck_1036_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1036_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v_task_1016_; lean_object* v_kind_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1034_; 
v_task_1016_ = lean_ctor_get(v_a_1011_, 0);
v_kind_1017_ = lean_ctor_get(v_a_1011_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_a_1011_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v_a_1011_, 2);
lean_dec(v_unused_1035_);
v___x_1019_ = v_a_1011_;
v_isShared_1020_ = v_isSharedCheck_1034_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_kind_1017_);
lean_inc(v_task_1016_);
lean_dec(v_a_1011_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1034_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v_registeredJobs_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_job_1025_; 
v_registeredJobs_1021_ = lean_ctor_get(v_a_981_, 3);
v___x_1022_ = lean_st_ref_take(v_registeredJobs_1021_);
v___x_1023_ = lean_string_append(v___x_990_, v___x_991_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 2, v___x_1023_);
v_job_1025_ = v___x_1019_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_task_1016_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_kind_1017_);
lean_ctor_set(v_reuseFailAlloc_1033_, 2, v___x_1023_);
v_job_1025_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1031_; 
lean_ctor_set_uint8(v_job_1025_, sizeof(void*)*3, v___x_1000_);
lean_inc_ref(v_job_1025_);
v___x_1026_ = l_Lake_Job_toOpaque___redArg(v_job_1025_);
v___x_1027_ = lean_array_push(v___x_1022_, v___x_1026_);
v___x_1028_ = lean_st_ref_set(v_registeredJobs_1021_, v___x_1027_);
v___x_1029_ = l_Lake_Job_renew___redArg(v_job_1025_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1029_);
v___x_1031_ = v___x_1014_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v_a_1012_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_990_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(lean_object* v_self_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(v_self_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec(v_a_1039_);
return v_res_1045_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_box(0);
v___x_1047_ = l_Lean_Json_compress(v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t v_fmt_1048_){
_start:
{
if (v_fmt_1048_ == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_1051_){
_start:
{
uint8_t v_fmt_boxed_1052_; lean_object* v_res_1053_; 
v_fmt_boxed_1052_ = lean_unbox(v_fmt_1051_);
v_res_1053_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_boxed_1052_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(uint8_t v_fmt_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_1054_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object* v_fmt_1057_, lean_object* v_a_1058_){
_start:
{
uint8_t v_fmt_boxed_1059_; lean_object* v_res_1060_; 
v_fmt_boxed_1059_ = lean_unbox(v_fmt_1057_);
v_res_1060_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(v_fmt_boxed_1059_, v_a_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v___y_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
uint8_t v___y_67__boxed_1066_; lean_object* v_res_1067_; 
v___y_67__boxed_1066_ = lean_unbox(v___y_1064_);
v_res_1067_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_67__boxed_1066_, v___y_1065_);
return v_res_1067_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1070_; uint8_t v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___f_1070_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_1071_ = 1;
v___x_1072_ = l_Lake_instDataKindUnit;
v___x_1073_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__1));
v___x_1074_ = l_Lake_Package_keyword;
v___x_1075_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1073_);
lean_ctor_set(v___x_1075_, 2, v___x_1072_);
lean_ctor_set(v___x_1075_, 3, v___f_1070_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*4, v___x_1071_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*4 + 1, v___x_1071_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_obj_once(&l_Lake_Package_extraDepFacetConfig___closed__2, &l_Lake_Package_extraDepFacetConfig___closed__2_once, _init_l_Lake_Package_extraDepFacetConfig___closed__2);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object* v_self_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_origName_1096_; lean_object* v_dir_1097_; lean_object* v_scope_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_origName_1096_ = lean_ctor_get(v_self_1092_, 3);
lean_inc(v_origName_1096_);
v_dir_1097_ = lean_ctor_get(v_self_1092_, 4);
lean_inc_ref(v_dir_1097_);
v_scope_1098_ = lean_ctor_get(v_self_1092_, 10);
lean_inc_ref(v_scope_1098_);
lean_dec_ref(v_self_1092_);
v___x_1099_ = lean_string_utf8_byte_size(v_scope_1098_);
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = lean_nat_dec_eq(v___x_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
v___x_1103_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1102_, v_dir_1097_);
if (lean_obj_tag(v___x_1103_) == 1)
{
lean_object* v_toContext_1104_; lean_object* v_lakeEnv_1105_; lean_object* v_log_1106_; uint8_t v_action_1107_; uint8_t v_wantsRebuild_1108_; lean_object* v_trace_1109_; lean_object* v_buildTime_1110_; lean_object* v_val_1111_; lean_object* v_toolchain_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_toContext_1104_ = lean_ctor_get(v_a_1093_, 1);
v_lakeEnv_1105_ = lean_ctor_get(v_toContext_1104_, 0);
v_log_1106_ = lean_ctor_get(v_a_1094_, 0);
v_action_1107_ = lean_ctor_get_uint8(v_a_1094_, sizeof(void*)*3);
v_wantsRebuild_1108_ = lean_ctor_get_uint8(v_a_1094_, sizeof(void*)*3 + 1);
v_trace_1109_ = lean_ctor_get(v_a_1094_, 1);
v_buildTime_1110_ = lean_ctor_get(v_a_1094_, 2);
v_val_1111_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_val_1111_);
lean_dec_ref(v___x_1103_);
v_toolchain_1112_ = lean_ctor_get(v_lakeEnv_1105_, 18);
v___x_1113_ = lean_string_utf8_byte_size(v_toolchain_1112_);
v___x_1114_ = lean_nat_dec_eq(v___x_1113_, v___x_1100_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1115_ = l_Lean_Name_toString(v_origName_1096_, v___x_1101_);
lean_inc_ref(v_lakeEnv_1105_);
v___x_1116_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_1105_, v_scope_1098_, v___x_1115_);
v___x_1117_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1));
v___x_1118_ = lean_string_append(v___x_1116_, v___x_1117_);
v___x_1119_ = lean_string_append(v___x_1118_, v_val_1111_);
lean_dec(v_val_1111_);
v___x_1120_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2));
v___x_1121_ = lean_string_append(v___x_1119_, v___x_1120_);
v___x_1122_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc_ref(v_toolchain_1112_);
v___x_1123_ = l_Lake_uriEncode(v_toolchain_1112_, v___x_1122_);
v___x_1124_ = lean_string_append(v___x_1121_, v___x_1123_);
lean_dec_ref(v___x_1123_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
lean_ctor_set(v___x_1125_, 1, v_a_1094_);
return v___x_1125_;
}
else
{
lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1136_; 
lean_inc(v_buildTime_1110_);
lean_inc_ref(v_trace_1109_);
lean_inc_ref(v_log_1106_);
lean_dec(v_val_1111_);
lean_dec_ref(v_scope_1098_);
lean_dec(v_origName_1096_);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_a_1094_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; lean_object* v_unused_1138_; lean_object* v_unused_1139_; 
v_unused_1137_ = lean_ctor_get(v_a_1094_, 2);
lean_dec(v_unused_1137_);
v_unused_1138_ = lean_ctor_get(v_a_1094_, 1);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_a_1094_, 0);
lean_dec(v_unused_1139_);
v___x_1127_ = v_a_1094_;
v_isShared_1128_ = v_isSharedCheck_1136_;
goto v_resetjp_1126_;
}
else
{
lean_dec(v_a_1094_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1136_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1129_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4));
v___x_1130_ = lean_array_get_size(v_log_1106_);
v___x_1131_ = lean_array_push(v_log_1106_, v___x_1129_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1131_);
v___x_1133_ = v___x_1127_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_trace_1109_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_buildTime_1110_);
lean_ctor_set_uint8(v_reuseFailAlloc_1135_, sizeof(void*)*3, v_action_1107_);
lean_ctor_set_uint8(v_reuseFailAlloc_1135_, sizeof(void*)*3 + 1, v_wantsRebuild_1108_);
v___x_1133_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1130_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_log_1140_; uint8_t v_action_1141_; uint8_t v_wantsRebuild_1142_; lean_object* v_trace_1143_; lean_object* v_buildTime_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1155_; 
lean_dec(v___x_1103_);
lean_dec_ref(v_scope_1098_);
lean_dec(v_origName_1096_);
v_log_1140_ = lean_ctor_get(v_a_1094_, 0);
v_action_1141_ = lean_ctor_get_uint8(v_a_1094_, sizeof(void*)*3);
v_wantsRebuild_1142_ = lean_ctor_get_uint8(v_a_1094_, sizeof(void*)*3 + 1);
v_trace_1143_ = lean_ctor_get(v_a_1094_, 1);
v_buildTime_1144_ = lean_ctor_get(v_a_1094_, 2);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_a_1094_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1146_ = v_a_1094_;
v_isShared_1147_ = v_isSharedCheck_1155_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_buildTime_1144_);
lean_inc(v_trace_1143_);
lean_inc(v_log_1140_);
lean_dec(v_a_1094_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1155_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1148_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6));
v___x_1149_ = lean_array_get_size(v_log_1140_);
v___x_1150_ = lean_array_push(v_log_1140_, v___x_1148_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1150_);
v___x_1152_ = v___x_1146_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_trace_1143_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_buildTime_1144_);
lean_ctor_set_uint8(v_reuseFailAlloc_1154_, sizeof(void*)*3, v_action_1141_);
lean_ctor_set_uint8(v_reuseFailAlloc_1154_, sizeof(void*)*3 + 1, v_wantsRebuild_1142_);
v___x_1152_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1149_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
return v___x_1153_;
}
}
}
}
else
{
lean_object* v_log_1156_; uint8_t v_action_1157_; uint8_t v_wantsRebuild_1158_; lean_object* v_trace_1159_; lean_object* v_buildTime_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1171_; 
lean_dec_ref(v_scope_1098_);
lean_dec_ref(v_dir_1097_);
lean_dec(v_origName_1096_);
v_log_1156_ = lean_ctor_get(v_a_1094_, 0);
v_action_1157_ = lean_ctor_get_uint8(v_a_1094_, sizeof(void*)*3);
v_wantsRebuild_1158_ = lean_ctor_get_uint8(v_a_1094_, sizeof(void*)*3 + 1);
v_trace_1159_ = lean_ctor_get(v_a_1094_, 1);
v_buildTime_1160_ = lean_ctor_get(v_a_1094_, 2);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_a_1094_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1162_ = v_a_1094_;
v_isShared_1163_ = v_isSharedCheck_1171_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_buildTime_1160_);
lean_inc(v_trace_1159_);
lean_inc(v_log_1156_);
lean_dec(v_a_1094_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1171_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1164_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8));
v___x_1165_ = lean_array_get_size(v_log_1156_);
v___x_1166_ = lean_array_push(v_log_1156_, v___x_1164_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1166_);
v___x_1168_ = v___x_1162_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_trace_1159_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_buildTime_1160_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*3, v_action_1157_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*3 + 1, v_wantsRebuild_1158_);
v___x_1168_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1165_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___boxed(lean_object* v_self_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1172_, v_a_1173_, v_a_1174_);
lean_dec_ref(v_a_1173_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object* v_self_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1177_, v_a_1182_, v_a_1183_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object* v_self_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(v_self_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec(v_a_1190_);
lean_dec(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec_ref(v_a_1187_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object* v_self_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_rev_1208_; lean_object* v_log_1209_; uint8_t v_action_1210_; uint8_t v_wantsRebuild_1211_; lean_object* v_trace_1212_; lean_object* v_buildTime_1213_; lean_object* v_dir_1222_; lean_object* v_config_1223_; lean_object* v_remoteUrl_1224_; lean_object* v_buildArchive_1225_; lean_object* v___y_1227_; uint8_t v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; uint8_t v___y_1231_; lean_object* v_val_1232_; lean_object* v___y_1252_; lean_object* v_releaseRepo_1283_; 
v_dir_1222_ = lean_ctor_get(v_self_1204_, 4);
lean_inc_ref(v_dir_1222_);
v_config_1223_ = lean_ctor_get(v_self_1204_, 6);
lean_inc_ref(v_config_1223_);
v_remoteUrl_1224_ = lean_ctor_get(v_self_1204_, 11);
lean_inc_ref(v_remoteUrl_1224_);
v_buildArchive_1225_ = lean_ctor_get(v_self_1204_, 20);
lean_inc_ref(v_buildArchive_1225_);
lean_dec_ref(v_self_1204_);
v_releaseRepo_1283_ = lean_ctor_get(v_config_1223_, 10);
lean_inc(v_releaseRepo_1283_);
lean_dec_ref(v_config_1223_);
if (lean_obj_tag(v_releaseRepo_1283_) == 0)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1284_ = lean_string_utf8_byte_size(v_remoteUrl_1224_);
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = lean_nat_dec_eq(v___x_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_dec_ref(v_remoteUrl_1224_);
v___y_1252_ = v_releaseRepo_1283_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1287_, 0, v_remoteUrl_1224_);
v___y_1252_ = v___x_1287_;
goto v___jp_1251_;
}
}
else
{
lean_dec_ref(v_remoteUrl_1224_);
v___y_1252_ = v_releaseRepo_1283_;
goto v___jp_1251_;
}
v___jp_1207_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1214_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0));
v___x_1215_ = lean_string_append(v___x_1214_, v_rev_1208_);
lean_dec_ref(v_rev_1208_);
v___x_1216_ = 3;
v___x_1217_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set_uint8(v___x_1217_, sizeof(void*)*1, v___x_1216_);
v___x_1218_ = lean_array_get_size(v_log_1209_);
v___x_1219_ = lean_array_push(v_log_1209_, v___x_1217_);
v___x_1220_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
lean_ctor_set(v___x_1220_, 1, v_trace_1212_);
lean_ctor_set(v___x_1220_, 2, v_buildTime_1213_);
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*3, v_action_1210_);
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*3 + 1, v_wantsRebuild_1211_);
v___x_1221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1218_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
return v___x_1221_;
}
v___jp_1226_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
lean_inc_ref(v_dir_1222_);
v___x_1234_ = l_Lake_GitRepo_findTag_x3f(v___x_1233_, v_dir_1222_);
if (lean_obj_tag(v___x_1234_) == 1)
{
lean_object* v_val_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec_ref(v_dir_1222_);
v_val_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_val_1235_);
lean_dec_ref(v___x_1234_);
v___x_1236_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1236_, 0, v___y_1230_);
lean_ctor_set(v___x_1236_, 1, v___y_1229_);
lean_ctor_set(v___x_1236_, 2, v___y_1227_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*3, v___y_1228_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*3 + 1, v___y_1231_);
v___x_1237_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1));
v___x_1238_ = lean_string_append(v_val_1232_, v___x_1237_);
v___x_1239_ = lean_string_append(v___x_1238_, v_val_1235_);
lean_dec(v_val_1235_);
v___x_1240_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2));
v___x_1241_ = lean_string_append(v___x_1239_, v___x_1240_);
v___x_1242_ = lean_string_append(v___x_1241_, v_buildArchive_1225_);
lean_dec_ref(v_buildArchive_1225_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v___x_1236_);
return v___x_1243_;
}
else
{
lean_object* v___x_1244_; 
lean_dec(v___x_1234_);
lean_dec_ref(v_val_1232_);
lean_dec_ref(v_buildArchive_1225_);
v___x_1244_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1233_, v_dir_1222_);
if (lean_obj_tag(v___x_1244_) == 1)
{
lean_object* v_val_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_val_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_val_1245_);
lean_dec_ref(v___x_1244_);
v___x_1246_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3));
v___x_1247_ = lean_string_append(v___x_1246_, v_val_1245_);
lean_dec(v_val_1245_);
v___x_1248_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4));
v___x_1249_ = lean_string_append(v___x_1247_, v___x_1248_);
v_rev_1208_ = v___x_1249_;
v_log_1209_ = v___y_1230_;
v_action_1210_ = v___y_1228_;
v_wantsRebuild_1211_ = v___y_1231_;
v_trace_1212_ = v___y_1229_;
v_buildTime_1213_ = v___y_1227_;
goto v___jp_1207_;
}
else
{
lean_object* v___x_1250_; 
lean_dec(v___x_1244_);
v___x_1250_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_rev_1208_ = v___x_1250_;
v_log_1209_ = v___y_1230_;
v_action_1210_ = v___y_1228_;
v_wantsRebuild_1211_ = v___y_1231_;
v_trace_1212_ = v___y_1229_;
v_buildTime_1213_ = v___y_1227_;
goto v___jp_1207_;
}
}
}
v___jp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_dir_1222_);
v___x_1254_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v___x_1253_, v_dir_1222_);
if (lean_obj_tag(v___y_1252_) == 0)
{
if (lean_obj_tag(v___x_1254_) == 1)
{
lean_object* v_log_1255_; uint8_t v_action_1256_; uint8_t v_wantsRebuild_1257_; lean_object* v_trace_1258_; lean_object* v_buildTime_1259_; lean_object* v_val_1260_; 
v_log_1255_ = lean_ctor_get(v_a_1205_, 0);
lean_inc_ref(v_log_1255_);
v_action_1256_ = lean_ctor_get_uint8(v_a_1205_, sizeof(void*)*3);
v_wantsRebuild_1257_ = lean_ctor_get_uint8(v_a_1205_, sizeof(void*)*3 + 1);
v_trace_1258_ = lean_ctor_get(v_a_1205_, 1);
lean_inc_ref(v_trace_1258_);
v_buildTime_1259_ = lean_ctor_get(v_a_1205_, 2);
lean_inc(v_buildTime_1259_);
lean_dec_ref(v_a_1205_);
v_val_1260_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_val_1260_);
lean_dec_ref(v___x_1254_);
v___y_1227_ = v_buildTime_1259_;
v___y_1228_ = v_action_1256_;
v___y_1229_ = v_trace_1258_;
v___y_1230_ = v_log_1255_;
v___y_1231_ = v_wantsRebuild_1257_;
v_val_1232_ = v_val_1260_;
goto v___jp_1226_;
}
else
{
lean_object* v_log_1261_; uint8_t v_action_1262_; uint8_t v_wantsRebuild_1263_; lean_object* v_trace_1264_; lean_object* v_buildTime_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1276_; 
lean_dec(v___x_1254_);
lean_dec_ref(v_buildArchive_1225_);
lean_dec_ref(v_dir_1222_);
v_log_1261_ = lean_ctor_get(v_a_1205_, 0);
v_action_1262_ = lean_ctor_get_uint8(v_a_1205_, sizeof(void*)*3);
v_wantsRebuild_1263_ = lean_ctor_get_uint8(v_a_1205_, sizeof(void*)*3 + 1);
v_trace_1264_ = lean_ctor_get(v_a_1205_, 1);
v_buildTime_1265_ = lean_ctor_get(v_a_1205_, 2);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_a_1205_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1267_ = v_a_1205_;
v_isShared_1268_ = v_isSharedCheck_1276_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_buildTime_1265_);
lean_inc(v_trace_1264_);
lean_inc(v_log_1261_);
lean_dec(v_a_1205_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1276_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1269_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6));
v___x_1270_ = lean_array_get_size(v_log_1261_);
v___x_1271_ = lean_array_push(v_log_1261_, v___x_1269_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v___x_1271_);
v___x_1273_ = v___x_1267_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_trace_1264_);
lean_ctor_set(v_reuseFailAlloc_1275_, 2, v_buildTime_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1275_, sizeof(void*)*3, v_action_1262_);
lean_ctor_set_uint8(v_reuseFailAlloc_1275_, sizeof(void*)*3 + 1, v_wantsRebuild_1263_);
v___x_1273_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1270_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
return v___x_1274_;
}
}
}
}
else
{
lean_object* v_log_1277_; uint8_t v_action_1278_; uint8_t v_wantsRebuild_1279_; lean_object* v_trace_1280_; lean_object* v_buildTime_1281_; lean_object* v_val_1282_; 
lean_dec(v___x_1254_);
v_log_1277_ = lean_ctor_get(v_a_1205_, 0);
lean_inc_ref(v_log_1277_);
v_action_1278_ = lean_ctor_get_uint8(v_a_1205_, sizeof(void*)*3);
v_wantsRebuild_1279_ = lean_ctor_get_uint8(v_a_1205_, sizeof(void*)*3 + 1);
v_trace_1280_ = lean_ctor_get(v_a_1205_, 1);
lean_inc_ref(v_trace_1280_);
v_buildTime_1281_ = lean_ctor_get(v_a_1205_, 2);
lean_inc(v_buildTime_1281_);
lean_dec_ref(v_a_1205_);
v_val_1282_ = lean_ctor_get(v___y_1252_, 0);
lean_inc(v_val_1282_);
lean_dec_ref(v___y_1252_);
v___y_1227_ = v_buildTime_1281_;
v___y_1228_ = v_action_1278_;
v___y_1229_ = v_trace_1280_;
v___y_1230_ = v_log_1277_;
v___y_1231_ = v_wantsRebuild_1279_;
v_val_1232_ = v_val_1282_;
goto v___jp_1226_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(lean_object* v_self_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1288_, v_a_1289_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object* v_self_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1292_, v_a_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object* v_self_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(v_self_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(lean_object* v_val_1310_, lean_object* v_a_x3f_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; lean_object* v_log_1315_; uint8_t v_action_1316_; uint8_t v_wantsRebuild_1317_; lean_object* v_trace_1318_; lean_object* v_buildTime_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1330_; 
v___x_1314_ = lean_io_mono_ms_now();
v_log_1315_ = lean_ctor_get(v___y_1312_, 0);
v_action_1316_ = lean_ctor_get_uint8(v___y_1312_, sizeof(void*)*3);
v_wantsRebuild_1317_ = lean_ctor_get_uint8(v___y_1312_, sizeof(void*)*3 + 1);
v_trace_1318_ = lean_ctor_get(v___y_1312_, 1);
v_buildTime_1319_ = lean_ctor_get(v___y_1312_, 2);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___y_1312_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1321_ = v___y_1312_;
v_isShared_1322_ = v_isSharedCheck_1330_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_buildTime_1319_);
lean_inc(v_trace_1318_);
lean_inc(v_log_1315_);
lean_dec(v___y_1312_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1330_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1323_ = lean_nat_sub(v___x_1314_, v_val_1310_);
lean_dec(v___x_1314_);
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_nat_add(v_buildTime_1319_, v___x_1323_);
lean_dec(v___x_1323_);
lean_dec(v_buildTime_1319_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 2, v___x_1325_);
v___x_1327_ = v___x_1321_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_log_1315_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_trace_1318_);
lean_ctor_set(v_reuseFailAlloc_1329_, 2, v___x_1325_);
lean_ctor_set_uint8(v_reuseFailAlloc_1329_, sizeof(void*)*3, v_action_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1329_, sizeof(void*)*3 + 1, v_wantsRebuild_1317_);
v___x_1327_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1324_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
return v___x_1328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0___boxed(lean_object* v_val_1331_, lean_object* v_a_x3f_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v_val_1331_, v_a_x3f_1332_, v___y_1333_);
lean_dec(v_a_x3f_1332_);
lean_dec(v_val_1331_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(lean_object* v_url_1341_, lean_object* v_archiveFile_1342_, lean_object* v_headers_1343_, lean_object* v_depTrace_1344_, lean_object* v_traceFile_1345_, uint8_t v_action_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_a_1351_; lean_object* v_a_1352_; lean_object* v_log_1355_; uint8_t v_action_1356_; uint8_t v_wantsRebuild_1357_; lean_object* v_trace_1358_; lean_object* v_buildTime_1359_; lean_object* v_toBuildConfig_1365_; lean_object* v_log_1366_; uint8_t v_action_1367_; uint8_t v_wantsRebuild_1368_; lean_object* v_trace_1369_; lean_object* v_buildTime_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1460_; 
v_toBuildConfig_1365_ = lean_ctor_get(v_a_1347_, 0);
v_log_1366_ = lean_ctor_get(v_a_1348_, 0);
v_action_1367_ = lean_ctor_get_uint8(v_a_1348_, sizeof(void*)*3);
v_wantsRebuild_1368_ = lean_ctor_get_uint8(v_a_1348_, sizeof(void*)*3 + 1);
v_trace_1369_ = lean_ctor_get(v_a_1348_, 1);
v_buildTime_1370_ = lean_ctor_get(v_a_1348_, 2);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_a_1348_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1372_ = v_a_1348_;
v_isShared_1373_ = v_isSharedCheck_1460_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_buildTime_1370_);
lean_inc(v_trace_1369_);
lean_inc(v_log_1366_);
lean_dec(v_a_1348_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1460_;
goto v_resetjp_1371_;
}
v___jp_1350_:
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_a_1351_);
lean_ctor_set(v___x_1353_, 1, v_a_1352_);
return v___x_1353_;
}
v___jp_1354_:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1360_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1));
v___x_1361_ = lean_array_get_size(v_log_1355_);
v___x_1362_ = lean_array_push(v_log_1355_, v___x_1360_);
v___x_1363_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
lean_ctor_set(v___x_1363_, 1, v_trace_1358_);
lean_ctor_set(v___x_1363_, 2, v_buildTime_1359_);
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*3, v_action_1356_);
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*3 + 1, v_wantsRebuild_1357_);
v___x_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1361_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
return v___x_1364_;
}
v_resetjp_1371_:
{
uint8_t v_noBuild_1374_; uint8_t v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_noBuild_1374_ = lean_ctor_get_uint8(v_toBuildConfig_1365_, sizeof(void*)*3 + 2);
v___x_1375_ = l_Lake_JobAction_merge(v_action_1367_, v_action_1346_);
v___x_1376_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2));
lean_inc_ref(v_traceFile_1345_);
v___x_1377_ = l_System_FilePath_addExtension(v_traceFile_1345_, v___x_1376_);
if (v_noBuild_1374_ == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v_a_1381_; lean_object* v_a_1382_; 
v___x_1378_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1366_);
v___x_1379_ = l_Lake_download(v_url_1341_, v_archiveFile_1342_, v_headers_1343_, v_log_1366_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1386_; lean_object* v_a_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_a_1386_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1386_);
v_a_1387_ = lean_ctor_get(v___x_1379_, 1);
lean_inc(v_a_1387_);
lean_dec_ref(v___x_1379_);
v___x_1388_ = lean_array_get_size(v_log_1366_);
lean_dec_ref(v_log_1366_);
v___x_1389_ = lean_array_get_size(v_a_1387_);
v___x_1390_ = l_Array_extract___redArg(v_a_1387_, v___x_1388_, v___x_1389_);
v___x_1391_ = lean_box(0);
v___x_1392_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1344_, v___x_1391_, v___x_1390_);
v___x_1393_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1345_, v___x_1392_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1430_; 
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1430_ == 0)
{
lean_object* v_unused_1431_; 
v_unused_1431_ = lean_ctor_get(v___x_1393_, 0);
lean_dec(v_unused_1431_);
v___x_1395_ = v___x_1393_;
v_isShared_1396_ = v_isSharedCheck_1430_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v___x_1393_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1430_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lake_removeFileIfExists(v___x_1377_);
lean_dec_ref(v___x_1377_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1420_; 
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; 
v_unused_1421_ = lean_ctor_get(v___x_1397_, 0);
lean_dec(v_unused_1421_);
v___x_1399_ = v___x_1397_;
v_isShared_1400_ = v_isSharedCheck_1420_;
goto v_resetjp_1398_;
}
else
{
lean_dec(v___x_1397_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1420_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v_a_1387_);
v___x_1402_ = v___x_1372_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1387_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_trace_1369_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_buildTime_1370_);
lean_ctor_set_uint8(v_reuseFailAlloc_1419_, sizeof(void*)*3 + 1, v_wantsRebuild_1368_);
v___x_1402_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1404_; 
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*3, v___x_1375_);
lean_inc(v_a_1386_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v_a_1386_);
v___x_1404_ = v___x_1399_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1386_);
v___x_1404_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1406_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set_tag(v___x_1395_, 1);
lean_ctor_set(v___x_1395_, 0, v___x_1404_);
v___x_1406_ = v___x_1395_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
v___x_1407_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1378_, v___x_1406_, v___x_1402_);
lean_dec_ref(v___x_1406_);
lean_dec(v___x_1378_);
v_a_1408_ = lean_ctor_get(v___x_1407_, 1);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; 
v_unused_1416_ = lean_ctor_get(v___x_1407_, 0);
lean_dec(v_unused_1416_);
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v_a_1386_);
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1386_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
lean_del_object(v___x_1395_);
lean_dec(v_a_1386_);
v_a_1422_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1422_);
lean_dec_ref(v___x_1397_);
v___x_1423_ = lean_io_error_to_string(v_a_1422_);
v___x_1424_ = 3;
v___x_1425_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set_uint8(v___x_1425_, sizeof(void*)*1, v___x_1424_);
v___x_1426_ = lean_array_push(v_a_1387_, v___x_1425_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1426_);
v___x_1428_ = v___x_1372_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_trace_1369_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v_buildTime_1370_);
lean_ctor_set_uint8(v_reuseFailAlloc_1429_, sizeof(void*)*3 + 1, v_wantsRebuild_1368_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_ctor_set_uint8(v___x_1428_, sizeof(void*)*3, v___x_1375_);
v_a_1381_ = v___x_1389_;
v_a_1382_ = v___x_1428_;
goto v___jp_1380_;
}
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
lean_dec(v_a_1386_);
lean_dec_ref(v___x_1377_);
v_a_1432_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1432_);
lean_dec_ref(v___x_1393_);
v___x_1433_ = lean_io_error_to_string(v_a_1432_);
v___x_1434_ = 3;
v___x_1435_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set_uint8(v___x_1435_, sizeof(void*)*1, v___x_1434_);
v___x_1436_ = lean_array_push(v_a_1387_, v___x_1435_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1436_);
v___x_1438_ = v___x_1372_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_trace_1369_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_buildTime_1370_);
lean_ctor_set_uint8(v_reuseFailAlloc_1439_, sizeof(void*)*3 + 1, v_wantsRebuild_1368_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*3, v___x_1375_);
v_a_1381_ = v___x_1389_;
v_a_1382_ = v___x_1438_;
goto v___jp_1380_;
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v_a_1441_; lean_object* v___x_1443_; 
lean_dec_ref(v___x_1377_);
lean_dec_ref(v_log_1366_);
lean_dec_ref(v_traceFile_1345_);
v_a_1440_ = lean_ctor_get(v___x_1379_, 0);
lean_inc(v_a_1440_);
v_a_1441_ = lean_ctor_get(v___x_1379_, 1);
lean_inc(v_a_1441_);
lean_dec_ref(v___x_1379_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v_a_1441_);
v___x_1443_ = v___x_1372_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1441_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_trace_1369_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_buildTime_1370_);
lean_ctor_set_uint8(v_reuseFailAlloc_1444_, sizeof(void*)*3 + 1, v_wantsRebuild_1368_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_ctor_set_uint8(v___x_1443_, sizeof(void*)*3, v___x_1375_);
v_a_1381_ = v_a_1440_;
v_a_1382_ = v___x_1443_;
goto v___jp_1380_;
}
}
v___jp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v_a_1385_; 
v___x_1383_ = lean_box(0);
v___x_1384_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1378_, v___x_1383_, v_a_1382_);
lean_dec(v___x_1378_);
v_a_1385_ = lean_ctor_get(v___x_1384_, 1);
lean_inc(v_a_1385_);
lean_dec_ref(v___x_1384_);
v_a_1351_ = v_a_1381_;
v_a_1352_ = v_a_1385_;
goto v___jp_1350_;
}
}
else
{
uint8_t v___x_1445_; 
lean_dec_ref(v_archiveFile_1342_);
lean_dec_ref(v_url_1341_);
v___x_1445_ = l_System_FilePath_pathExists(v_traceFile_1345_);
lean_dec_ref(v_traceFile_1345_);
if (v___x_1445_ == 0)
{
lean_dec_ref(v___x_1377_);
lean_del_object(v___x_1372_);
v_log_1355_ = v_log_1366_;
v_action_1356_ = v___x_1375_;
v_wantsRebuild_1357_ = v_noBuild_1374_;
v_trace_1358_ = v_trace_1369_;
v_buildTime_1359_ = v_buildTime_1370_;
goto v___jp_1354_;
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1446_ = lean_box(0);
v___x_1447_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1448_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1344_, v___x_1446_, v___x_1447_);
v___x_1449_ = l_Lake_BuildMetadata_writeFile(v___x_1377_, v___x_1448_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_dec_ref(v___x_1449_);
lean_del_object(v___x_1372_);
v_log_1355_ = v_log_1366_;
v_action_1356_ = v___x_1375_;
v_wantsRebuild_1357_ = v_noBuild_1374_;
v_trace_1358_ = v_trace_1369_;
v_buildTime_1359_ = v_buildTime_1370_;
goto v___jp_1354_;
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref(v___x_1449_);
v___x_1451_ = lean_io_error_to_string(v_a_1450_);
v___x_1452_ = 3;
v___x_1453_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1453_, 0, v___x_1451_);
lean_ctor_set_uint8(v___x_1453_, sizeof(void*)*1, v___x_1452_);
v___x_1454_ = lean_array_get_size(v_log_1366_);
v___x_1455_ = lean_array_push(v_log_1366_, v___x_1453_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1455_);
v___x_1457_ = v___x_1372_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_trace_1369_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_buildTime_1370_);
v___x_1457_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; 
lean_ctor_set_uint8(v___x_1457_, sizeof(void*)*3, v___x_1375_);
lean_ctor_set_uint8(v___x_1457_, sizeof(void*)*3 + 1, v_noBuild_1374_);
v___x_1458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1454_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
return v___x_1458_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___boxed(lean_object* v_url_1461_, lean_object* v_archiveFile_1462_, lean_object* v_headers_1463_, lean_object* v_depTrace_1464_, lean_object* v_traceFile_1465_, lean_object* v_action_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
uint8_t v_action_boxed_1470_; lean_object* v_res_1471_; 
v_action_boxed_1470_ = lean_unbox(v_action_1466_);
v_res_1471_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1461_, v_archiveFile_1462_, v_headers_1463_, v_depTrace_1464_, v_traceFile_1465_, v_action_boxed_1470_, v_a_1467_, v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec_ref(v_depTrace_1464_);
lean_dec_ref(v_headers_1463_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(lean_object* v_url_1472_, lean_object* v_archiveFile_1473_, lean_object* v_headers_1474_, lean_object* v_a_1475_, lean_object* v_depTrace_1476_, lean_object* v_traceFile_1477_, uint8_t v_action_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1472_, v_archiveFile_1473_, v_headers_1474_, v_depTrace_1476_, v_traceFile_1477_, v_action_1478_, v_a_1482_, v_a_1483_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___boxed(lean_object* v_url_1486_, lean_object* v_archiveFile_1487_, lean_object* v_headers_1488_, lean_object* v_a_1489_, lean_object* v_depTrace_1490_, lean_object* v_traceFile_1491_, lean_object* v_action_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_){
_start:
{
uint8_t v_action_boxed_1499_; lean_object* v_res_1500_; 
v_action_boxed_1499_ = lean_unbox(v_action_1492_);
v_res_1500_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(v_url_1486_, v_archiveFile_1487_, v_headers_1488_, v_a_1489_, v_depTrace_1490_, v_traceFile_1491_, v_action_boxed_1499_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec_ref(v_depTrace_1490_);
lean_dec_ref(v_a_1489_);
lean_dec_ref(v_headers_1488_);
return v_res_1500_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(lean_object* v_x_1501_, lean_object* v_x_1502_){
_start:
{
if (lean_obj_tag(v_x_1501_) == 0)
{
if (lean_obj_tag(v_x_1502_) == 0)
{
uint8_t v___x_1503_; 
v___x_1503_ = 1;
return v___x_1503_;
}
else
{
uint8_t v___x_1504_; 
v___x_1504_ = 0;
return v___x_1504_;
}
}
else
{
if (lean_obj_tag(v_x_1502_) == 0)
{
uint8_t v___x_1505_; 
v___x_1505_ = 0;
return v___x_1505_;
}
else
{
lean_object* v_val_1506_; lean_object* v_val_1507_; uint64_t v___x_1508_; uint64_t v___x_1509_; uint8_t v___x_1510_; 
v_val_1506_ = lean_ctor_get(v_x_1501_, 0);
v_val_1507_ = lean_ctor_get(v_x_1502_, 0);
v___x_1508_ = lean_unbox_uint64(v_val_1506_);
v___x_1509_ = lean_unbox_uint64(v_val_1507_);
v___x_1510_ = lean_uint64_dec_eq(v___x_1508_, v___x_1509_);
return v___x_1510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(lean_object* v_x_1511_, lean_object* v_x_1512_){
_start:
{
uint8_t v_res_1513_; lean_object* v_r_1514_; 
v_res_1513_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v_x_1511_, v_x_1512_);
lean_dec(v_x_1512_);
lean_dec(v_x_1511_);
v_r_1514_ = lean_box(v_res_1513_);
return v_r_1514_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object* v_info_1515_, lean_object* v_self_1516_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_io_metadata(v_info_1515_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v_modified_1520_; uint8_t v___x_1521_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref(v___x_1518_);
v_modified_1520_ = lean_ctor_get(v_a_1519_, 1);
lean_inc_ref(v_modified_1520_);
lean_dec(v_a_1519_);
v___x_1521_ = l_IO_FS_instOrdSystemTime_ord(v_self_1516_, v_modified_1520_);
lean_dec_ref(v_modified_1520_);
if (v___x_1521_ == 0)
{
uint8_t v___x_1522_; 
v___x_1522_ = 1;
return v___x_1522_;
}
else
{
uint8_t v___x_1523_; 
v___x_1523_ = 0;
return v___x_1523_;
}
}
else
{
uint8_t v___x_1524_; 
lean_dec_ref(v___x_1518_);
v___x_1524_ = 0;
return v___x_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object* v_info_1525_, lean_object* v_self_1526_, lean_object* v_a_1527_){
_start:
{
uint8_t v_res_1528_; lean_object* v_r_1529_; 
v_res_1528_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1525_, v_self_1526_);
lean_dec_ref(v_self_1526_);
lean_dec_ref(v_info_1525_);
v_r_1529_ = lean_box(v_res_1528_);
return v_r_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(lean_object* v_info_1530_, lean_object* v_depTrace_1531_, lean_object* v_depHash_1532_, lean_object* v_oldTrace_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
uint64_t v_hash_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v_hash_1537_ = lean_ctor_get_uint64(v_depTrace_1531_, sizeof(void*)*3);
v___x_1538_ = lean_box_uint64(v_hash_1537_);
v___x_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
v___x_1540_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v___x_1539_, v_depHash_1532_);
lean_dec_ref(v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v_toBuildConfig_1541_; uint8_t v_oldMode_1542_; 
v_toBuildConfig_1541_ = lean_ctor_get(v_a_1534_, 0);
v_oldMode_1542_ = lean_ctor_get_uint8(v_toBuildConfig_1541_, sizeof(void*)*3);
if (v_oldMode_1542_ == 0)
{
uint8_t v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1543_ = 0;
v___x_1544_ = lean_box(v___x_1543_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v_a_1535_);
return v___x_1545_;
}
else
{
uint8_t v___x_1546_; 
v___x_1546_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1530_, v_oldTrace_1533_);
if (v___x_1546_ == 0)
{
uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = 0;
v___x_1548_ = lean_box(v___x_1547_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v_a_1535_);
return v___x_1549_;
}
else
{
uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = 1;
v___x_1551_ = lean_box(v___x_1550_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
lean_ctor_set(v___x_1552_, 1, v_a_1535_);
return v___x_1552_;
}
}
}
else
{
uint8_t v___x_1553_; 
v___x_1553_ = l_System_FilePath_pathExists(v_info_1530_);
if (v___x_1553_ == 0)
{
uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = 0;
v___x_1555_ = lean_box(v___x_1554_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v_a_1535_);
return v___x_1556_;
}
else
{
uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = 2;
v___x_1558_ = lean_box(v___x_1557_);
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v_a_1535_);
return v___x_1559_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(lean_object* v_info_1560_, lean_object* v_depTrace_1561_, lean_object* v_depHash_1562_, lean_object* v_oldTrace_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1560_, v_depTrace_1561_, v_depHash_1562_, v_oldTrace_1563_, v_a_1564_, v_a_1565_);
lean_dec_ref(v_a_1564_);
lean_dec_ref(v_oldTrace_1563_);
lean_dec(v_depHash_1562_);
lean_dec_ref(v_depTrace_1561_);
lean_dec_ref(v_info_1560_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(lean_object* v_a_1568_, lean_object* v_info_1569_, lean_object* v_depTrace_1570_, lean_object* v_savedTrace_1571_, lean_object* v_oldTrace_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_){
_start:
{
if (lean_obj_tag(v_savedTrace_1571_) == 2)
{
lean_object* v_data_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1629_; 
v_data_1579_ = lean_ctor_get(v_savedTrace_1571_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_savedTrace_1571_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1581_ = v_savedTrace_1571_;
v_isShared_1582_ = v_isSharedCheck_1629_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_data_1579_);
lean_dec(v_savedTrace_1571_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1629_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
uint64_t v_depHash_1583_; lean_object* v_log_1584_; lean_object* v___x_1585_; lean_object* v___x_1587_; 
v_depHash_1583_ = lean_ctor_get_uint64(v_data_1579_, sizeof(void*)*3);
v_log_1584_ = lean_ctor_get(v_data_1579_, 2);
lean_inc_ref(v_log_1584_);
lean_dec_ref(v_data_1579_);
v___x_1585_ = lean_box_uint64(v_depHash_1583_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set_tag(v___x_1581_, 1);
lean_ctor_set(v___x_1581_, 0, v___x_1585_);
v___x_1587_ = v___x_1581_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1588_; lean_object* v_a_1589_; lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1627_; 
v___x_1588_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1569_, v_depTrace_1570_, v___x_1587_, v_oldTrace_1572_, v_a_1576_, v_a_1577_);
lean_dec_ref(v___x_1587_);
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_a_1590_ = lean_ctor_get(v___x_1588_, 1);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1592_ = v___x_1588_;
v_isShared_1593_ = v_isSharedCheck_1627_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1627_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___y_1595_; uint8_t v___x_1599_; uint8_t v___x_1600_; uint8_t v___x_1601_; 
v___x_1599_ = 0;
v___x_1600_ = lean_unbox(v_a_1589_);
v___x_1601_ = l_Lake_instDecidableEqOutputStatus(v___x_1600_, v___x_1599_);
if (v___x_1601_ == 0)
{
lean_object* v_log_1602_; uint8_t v_action_1603_; uint8_t v_wantsRebuild_1604_; lean_object* v_trace_1605_; lean_object* v_buildTime_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1626_; 
v_log_1602_ = lean_ctor_get(v_a_1590_, 0);
v_action_1603_ = lean_ctor_get_uint8(v_a_1590_, sizeof(void*)*3);
v_wantsRebuild_1604_ = lean_ctor_get_uint8(v_a_1590_, sizeof(void*)*3 + 1);
v_trace_1605_ = lean_ctor_get(v_a_1590_, 1);
v_buildTime_1606_ = lean_ctor_get(v_a_1590_, 2);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_a_1590_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1608_ = v_a_1590_;
v_isShared_1609_ = v_isSharedCheck_1626_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_buildTime_1606_);
lean_inc(v_trace_1605_);
lean_inc(v_log_1602_);
lean_dec(v_a_1590_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1626_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
uint8_t v___x_1610_; uint8_t v___x_1611_; lean_object* v___x_1613_; 
v___x_1610_ = 2;
v___x_1611_ = l_Lake_JobAction_merge(v_action_1603_, v___x_1610_);
if (v_isShared_1609_ == 0)
{
v___x_1613_ = v___x_1608_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_log_1602_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_trace_1605_);
lean_ctor_set(v_reuseFailAlloc_1625_, 2, v_buildTime_1606_);
lean_ctor_set_uint8(v_reuseFailAlloc_1625_, sizeof(void*)*3 + 1, v_wantsRebuild_1604_);
v___x_1613_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1614_; 
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3, v___x_1611_);
v___x_1614_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1584_, v_a_1568_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v___x_1613_);
lean_dec_ref(v_log_1584_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 1);
lean_inc(v_a_1615_);
lean_dec_ref(v___x_1614_);
v___y_1595_ = v_a_1615_;
goto v___jp_1594_;
}
else
{
lean_object* v_a_1616_; lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_del_object(v___x_1592_);
lean_dec(v_a_1589_);
v_a_1616_ = lean_ctor_get(v___x_1614_, 0);
v_a_1617_ = lean_ctor_get(v___x_1614_, 1);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1614_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_inc(v_a_1616_);
lean_dec(v___x_1614_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1616_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_1584_);
v___y_1595_ = v_a_1590_;
goto v___jp_1594_;
}
v___jp_1594_:
{
lean_object* v___x_1597_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 1, v___y_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1589_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v___y_1595_);
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
}
else
{
lean_object* v_toBuildConfig_1630_; uint8_t v_oldMode_1631_; 
lean_dec(v_savedTrace_1571_);
v_toBuildConfig_1630_ = lean_ctor_get(v_a_1576_, 0);
v_oldMode_1631_ = lean_ctor_get_uint8(v_toBuildConfig_1630_, sizeof(void*)*3);
if (v_oldMode_1631_ == 0)
{
uint8_t v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = 0;
v___x_1633_ = lean_box(v___x_1632_);
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
lean_ctor_set(v___x_1634_, 1, v_a_1577_);
return v___x_1634_;
}
else
{
uint8_t v___x_1635_; 
v___x_1635_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1569_, v_oldTrace_1572_);
if (v___x_1635_ == 0)
{
uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = 0;
v___x_1637_ = lean_box(v___x_1636_);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v_a_1577_);
return v___x_1638_;
}
else
{
uint8_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1639_ = 1;
v___x_1640_ = lean_box(v___x_1639_);
v___x_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
lean_ctor_set(v___x_1641_, 1, v_a_1577_);
return v___x_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object* v_a_1642_, lean_object* v_info_1643_, lean_object* v_depTrace_1644_, lean_object* v_savedTrace_1645_, lean_object* v_oldTrace_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_1642_, v_info_1643_, v_depTrace_1644_, v_savedTrace_1645_, v_oldTrace_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_oldTrace_1646_);
lean_dec_ref(v_depTrace_1644_);
lean_dec_ref(v_info_1643_);
lean_dec_ref(v_a_1642_);
return v_res_1653_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_nat_to_int(v___x_1658_);
return v___x_1659_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4(void){
_start:
{
uint32_t v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1660_ = 0;
v___x_1661_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3);
v___x_1662_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
lean_ctor_set_uint32(v___x_1662_, sizeof(void*)*1, v___x_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(lean_object* v_self_1663_, lean_object* v_url_1664_, lean_object* v_archiveFile_1665_, lean_object* v_headers_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_){
_start:
{
lean_object* v_a_1675_; lean_object* v_a_1676_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; uint8_t v___y_1682_; lean_object* v___y_1683_; uint8_t v___y_1684_; uint8_t v_a_1710_; lean_object* v_a_1711_; lean_object* v_log_1730_; uint8_t v_action_1731_; uint8_t v_wantsRebuild_1732_; lean_object* v_trace_1733_; lean_object* v_buildTime_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1773_; 
v_log_1730_ = lean_ctor_get(v_a_1672_, 0);
v_action_1731_ = lean_ctor_get_uint8(v_a_1672_, sizeof(void*)*3);
v_wantsRebuild_1732_ = lean_ctor_get_uint8(v_a_1672_, sizeof(void*)*3 + 1);
v_trace_1733_ = lean_ctor_get(v_a_1672_, 1);
v_buildTime_1734_ = lean_ctor_get(v_a_1672_, 2);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_a_1672_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1736_ = v_a_1672_;
v_isShared_1737_ = v_isSharedCheck_1773_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_buildTime_1734_);
lean_inc(v_trace_1733_);
lean_inc(v_log_1730_);
lean_dec(v_a_1672_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1773_;
goto v_resetjp_1735_;
}
v___jp_1674_:
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1677_, 0, v_a_1675_);
lean_ctor_set(v___x_1677_, 1, v_a_1676_);
return v___x_1677_;
}
v___jp_1678_:
{
uint8_t v___x_1685_; lean_object* v___x_1686_; uint8_t v___x_1687_; uint8_t v___x_1688_; 
v___x_1685_ = 1;
v___x_1686_ = l_Lake_untar(v_archiveFile_1665_, v___y_1683_, v___x_1685_, v___y_1680_);
v___x_1687_ = 3;
v___x_1688_ = l_Lake_JobAction_merge(v___y_1684_, v___x_1687_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1689_; lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1698_; 
v_a_1689_ = lean_ctor_get(v___x_1686_, 0);
v_a_1690_ = lean_ctor_get(v___x_1686_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1692_ = v___x_1686_;
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_inc(v_a_1689_);
lean_dec(v___x_1686_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1694_, 0, v_a_1690_);
lean_ctor_set(v___x_1694_, 1, v___y_1681_);
lean_ctor_set(v___x_1694_, 2, v___y_1679_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*3, v___x_1688_);
lean_ctor_set_uint8(v___x_1694_, sizeof(void*)*3 + 1, v___y_1682_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 1, v___x_1694_);
v___x_1696_ = v___x_1692_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1689_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1708_; 
v_a_1699_ = lean_ctor_get(v___x_1686_, 0);
v_a_1700_ = lean_ctor_get(v___x_1686_, 1);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1702_ = v___x_1686_;
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_inc(v_a_1699_);
lean_dec(v___x_1686_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1704_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1704_, 0, v_a_1700_);
lean_ctor_set(v___x_1704_, 1, v___y_1681_);
lean_ctor_set(v___x_1704_, 2, v___y_1679_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*3, v___x_1688_);
lean_ctor_set_uint8(v___x_1704_, sizeof(void*)*3 + 1, v___y_1682_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v___x_1704_);
v___x_1706_ = v___x_1702_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1699_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
v___jp_1709_:
{
lean_object* v_config_1712_; lean_object* v_dir_1713_; lean_object* v_buildDir_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_config_1712_ = lean_ctor_get(v_self_1663_, 6);
lean_inc_ref(v_config_1712_);
v_dir_1713_ = lean_ctor_get(v_self_1663_, 4);
lean_inc_ref(v_dir_1713_);
lean_dec_ref(v_self_1663_);
v_buildDir_1714_ = lean_ctor_get(v_config_1712_, 5);
lean_inc_ref(v_buildDir_1714_);
lean_dec_ref(v_config_1712_);
v___x_1715_ = l_System_FilePath_normalize(v_buildDir_1714_);
v___x_1716_ = l_Lake_joinRelative(v_dir_1713_, v___x_1715_);
v___x_1717_ = l_System_FilePath_pathExists(v___x_1716_);
if (v_a_1710_ == 0)
{
lean_object* v_log_1718_; uint8_t v_action_1719_; uint8_t v_wantsRebuild_1720_; lean_object* v_trace_1721_; lean_object* v_buildTime_1722_; 
v_log_1718_ = lean_ctor_get(v_a_1711_, 0);
lean_inc_ref(v_log_1718_);
v_action_1719_ = lean_ctor_get_uint8(v_a_1711_, sizeof(void*)*3);
v_wantsRebuild_1720_ = lean_ctor_get_uint8(v_a_1711_, sizeof(void*)*3 + 1);
v_trace_1721_ = lean_ctor_get(v_a_1711_, 1);
lean_inc_ref(v_trace_1721_);
v_buildTime_1722_ = lean_ctor_get(v_a_1711_, 2);
lean_inc(v_buildTime_1722_);
lean_dec_ref(v_a_1711_);
v___y_1679_ = v_buildTime_1722_;
v___y_1680_ = v_log_1718_;
v___y_1681_ = v_trace_1721_;
v___y_1682_ = v_wantsRebuild_1720_;
v___y_1683_ = v___x_1716_;
v___y_1684_ = v_action_1719_;
goto v___jp_1678_;
}
else
{
if (v___x_1717_ == 0)
{
lean_object* v_log_1723_; uint8_t v_action_1724_; uint8_t v_wantsRebuild_1725_; lean_object* v_trace_1726_; lean_object* v_buildTime_1727_; 
v_log_1723_ = lean_ctor_get(v_a_1711_, 0);
lean_inc_ref(v_log_1723_);
v_action_1724_ = lean_ctor_get_uint8(v_a_1711_, sizeof(void*)*3);
v_wantsRebuild_1725_ = lean_ctor_get_uint8(v_a_1711_, sizeof(void*)*3 + 1);
v_trace_1726_ = lean_ctor_get(v_a_1711_, 1);
lean_inc_ref(v_trace_1726_);
v_buildTime_1727_ = lean_ctor_get(v_a_1711_, 2);
lean_inc(v_buildTime_1727_);
lean_dec_ref(v_a_1711_);
v___y_1679_ = v_buildTime_1727_;
v___y_1680_ = v_log_1723_;
v___y_1681_ = v_trace_1726_;
v___y_1682_ = v_wantsRebuild_1725_;
v___y_1683_ = v___x_1716_;
v___y_1684_ = v_action_1724_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec_ref(v___x_1716_);
lean_dec_ref(v_archiveFile_1665_);
v___x_1728_ = lean_box(0);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
lean_ctor_set(v___x_1729_, 1, v_a_1711_);
return v___x_1729_;
}
}
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v_traceFile_1739_; lean_object* v___x_1740_; 
v___x_1738_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0));
lean_inc_ref(v_archiveFile_1665_);
v_traceFile_1739_ = l_System_FilePath_addExtension(v_archiveFile_1665_, v___x_1738_);
lean_inc_ref(v_traceFile_1739_);
v___x_1740_ = l_Lake_readTraceFile(v_traceFile_1739_, v_log_1730_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v_a_1742_; lean_object* v___x_1743_; uint64_t v___x_1744_; uint64_t v___x_1745_; uint64_t v_depTrace_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1751_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
v_a_1742_ = lean_ctor_get(v___x_1740_, 1);
lean_inc(v_a_1742_);
lean_dec_ref(v___x_1740_);
v___x_1743_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1));
v___x_1744_ = l_Lake_Hash_nil;
v___x_1745_ = lean_string_hash(v_url_1664_);
v_depTrace_1746_ = lean_uint64_mix_hash(v___x_1744_, v___x_1745_);
v___x_1747_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2));
v___x_1748_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
v___x_1749_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1749_, 0, v___x_1747_);
lean_ctor_set(v___x_1749_, 1, v___x_1743_);
lean_ctor_set(v___x_1749_, 2, v___x_1748_);
lean_ctor_set_uint64(v___x_1749_, sizeof(void*)*3, v_depTrace_1746_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v_a_1742_);
v___x_1751_ = v___x_1736_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1742_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_trace_1733_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v_buildTime_1734_);
lean_ctor_set_uint8(v_reuseFailAlloc_1767_, sizeof(void*)*3, v_action_1731_);
lean_ctor_set_uint8(v_reuseFailAlloc_1767_, sizeof(void*)*3 + 1, v_wantsRebuild_1732_);
v___x_1751_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_1667_, v_archiveFile_1665_, v___x_1749_, v_a_1741_, v___x_1748_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v___x_1751_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v_a_1754_; uint8_t v___x_1755_; uint8_t v___x_1756_; uint8_t v___x_1757_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
v_a_1754_ = lean_ctor_get(v___x_1752_, 1);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1752_);
v___x_1755_ = 0;
v___x_1756_ = lean_unbox(v_a_1753_);
lean_dec(v_a_1753_);
v___x_1757_ = l_Lake_instDecidableEqOutputStatus(v___x_1756_, v___x_1755_);
if (v___x_1757_ == 0)
{
uint8_t v___x_1758_; 
lean_dec_ref(v___x_1749_);
lean_dec_ref(v_traceFile_1739_);
lean_dec_ref(v_url_1664_);
v___x_1758_ = 1;
v_a_1710_ = v___x_1758_;
v_a_1711_ = v_a_1754_;
goto v___jp_1709_;
}
else
{
uint8_t v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = 4;
lean_inc_ref(v_archiveFile_1665_);
v___x_1760_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1664_, v_archiveFile_1665_, v_headers_1666_, v___x_1749_, v_traceFile_1739_, v___x_1759_, v_a_1671_, v_a_1754_);
lean_dec_ref(v___x_1749_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; uint8_t v___x_1762_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 1);
lean_inc(v_a_1761_);
lean_dec_ref(v___x_1760_);
v___x_1762_ = 0;
v_a_1710_ = v___x_1762_;
v_a_1711_ = v_a_1761_;
goto v___jp_1709_;
}
else
{
lean_object* v_a_1763_; lean_object* v_a_1764_; 
lean_dec_ref(v_archiveFile_1665_);
lean_dec_ref(v_self_1663_);
v_a_1763_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1763_);
v_a_1764_ = lean_ctor_get(v___x_1760_, 1);
lean_inc(v_a_1764_);
lean_dec_ref(v___x_1760_);
v_a_1675_ = v_a_1763_;
v_a_1676_ = v_a_1764_;
goto v___jp_1674_;
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v_a_1766_; 
lean_dec_ref(v___x_1749_);
lean_dec_ref(v_traceFile_1739_);
lean_dec_ref(v_archiveFile_1665_);
lean_dec_ref(v_url_1664_);
lean_dec_ref(v_self_1663_);
v_a_1765_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1765_);
v_a_1766_ = lean_ctor_get(v___x_1752_, 1);
lean_inc(v_a_1766_);
lean_dec_ref(v___x_1752_);
v_a_1675_ = v_a_1765_;
v_a_1676_ = v_a_1766_;
goto v___jp_1674_;
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v_a_1769_; lean_object* v___x_1771_; 
lean_dec_ref(v_traceFile_1739_);
lean_dec_ref(v_archiveFile_1665_);
lean_dec_ref(v_url_1664_);
lean_dec_ref(v_self_1663_);
v_a_1768_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1768_);
v_a_1769_ = lean_ctor_get(v___x_1740_, 1);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1740_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v_a_1769_);
v___x_1771_ = v___x_1736_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1769_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_trace_1733_);
lean_ctor_set(v_reuseFailAlloc_1772_, 2, v_buildTime_1734_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, sizeof(void*)*3, v_action_1731_);
lean_ctor_set_uint8(v_reuseFailAlloc_1772_, sizeof(void*)*3 + 1, v_wantsRebuild_1732_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
v_a_1675_ = v_a_1768_;
v_a_1676_ = v___x_1771_;
goto v___jp_1674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object* v_self_1774_, lean_object* v_url_1775_, lean_object* v_archiveFile_1776_, lean_object* v_headers_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_self_1774_, v_url_1775_, v_archiveFile_1776_, v_headers_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
lean_dec_ref(v_headers_1777_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object* v_a_1786_, lean_object* v_info_1787_, lean_object* v_depTrace_1788_, lean_object* v_depHash_1789_, lean_object* v_oldTrace_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1787_, v_depTrace_1788_, v_depHash_1789_, v_oldTrace_1790_, v_a_1794_, v_a_1795_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object* v_a_1798_, lean_object* v_info_1799_, lean_object* v_depTrace_1800_, lean_object* v_depHash_1801_, lean_object* v_oldTrace_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_1798_, v_info_1799_, v_depTrace_1800_, v_depHash_1801_, v_oldTrace_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec_ref(v_oldTrace_1802_);
lean_dec(v_depHash_1801_);
lean_dec_ref(v_depTrace_1800_);
lean_dec_ref(v_info_1799_);
lean_dec_ref(v_a_1798_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_getUrl_1810_, lean_object* v_pkg_1811_, lean_object* v_archiveFile_1812_, lean_object* v_headers_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
uint8_t v_r_1822_; lean_object* v___y_1823_; lean_object* v_a_1827_; lean_object* v___x_1843_; 
lean_inc_ref(v___y_1818_);
lean_inc(v___y_1817_);
lean_inc(v___y_1816_);
lean_inc(v___y_1815_);
lean_inc_ref(v___y_1814_);
lean_inc_ref(v_pkg_1811_);
v___x_1843_ = lean_apply_8(v_getUrl_1810_, v_pkg_1811_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, lean_box(0));
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v_a_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
v_a_1845_ = lean_ctor_get(v___x_1843_, 1);
lean_inc(v_a_1845_);
lean_dec_ref(v___x_1843_);
lean_inc_ref(v_pkg_1811_);
v___x_1846_ = lean_apply_1(v_archiveFile_1812_, v_pkg_1811_);
v___x_1847_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_1811_, v_a_1844_, v___x_1846_, v_headers_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v_a_1845_);
lean_dec_ref(v___y_1814_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; uint8_t v___x_1849_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 1);
lean_inc(v_a_1848_);
lean_dec_ref(v___x_1847_);
v___x_1849_ = 1;
v_r_1822_ = v___x_1849_;
v___y_1823_ = v_a_1848_;
goto v___jp_1821_;
}
else
{
lean_object* v_a_1850_; 
v_a_1850_ = lean_ctor_get(v___x_1847_, 1);
lean_inc(v_a_1850_);
lean_dec_ref(v___x_1847_);
v_a_1827_ = v_a_1850_;
goto v___jp_1826_;
}
}
else
{
lean_object* v_a_1851_; 
lean_dec_ref(v___y_1814_);
lean_dec_ref(v_archiveFile_1812_);
lean_dec_ref(v_pkg_1811_);
v_a_1851_ = lean_ctor_get(v___x_1843_, 1);
lean_inc(v_a_1851_);
lean_dec_ref(v___x_1843_);
v_a_1827_ = v_a_1851_;
goto v___jp_1826_;
}
v___jp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_box(v_r_1822_);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v___y_1823_);
return v___x_1825_;
}
v___jp_1826_:
{
lean_object* v_log_1828_; uint8_t v_action_1829_; uint8_t v_wantsRebuild_1830_; lean_object* v_trace_1831_; lean_object* v_buildTime_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1842_; 
v_log_1828_ = lean_ctor_get(v_a_1827_, 0);
v_action_1829_ = lean_ctor_get_uint8(v_a_1827_, sizeof(void*)*3);
v_wantsRebuild_1830_ = lean_ctor_get_uint8(v_a_1827_, sizeof(void*)*3 + 1);
v_trace_1831_ = lean_ctor_get(v_a_1827_, 1);
v_buildTime_1832_ = lean_ctor_get(v_a_1827_, 2);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_a_1827_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1834_ = v_a_1827_;
v_isShared_1835_ = v_isSharedCheck_1842_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_buildTime_1832_);
lean_inc(v_trace_1831_);
lean_inc(v_log_1828_);
lean_dec(v_a_1827_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1842_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
uint8_t v___x_1836_; uint8_t v___x_1837_; lean_object* v___x_1839_; 
v___x_1836_ = 4;
v___x_1837_ = l_Lake_JobAction_merge(v_action_1829_, v___x_1836_);
if (v_isShared_1835_ == 0)
{
v___x_1839_ = v___x_1834_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_log_1828_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_trace_1831_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_buildTime_1832_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*3 + 1, v_wantsRebuild_1830_);
v___x_1839_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
uint8_t v___x_1840_; 
lean_ctor_set_uint8(v___x_1839_, sizeof(void*)*3, v___x_1837_);
v___x_1840_ = 0;
v_r_1822_ = v___x_1840_;
v___y_1823_ = v___x_1839_;
goto v___jp_1821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_getUrl_1852_, lean_object* v_pkg_1853_, lean_object* v_archiveFile_1854_, lean_object* v_headers_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(v_getUrl_1852_, v_pkg_1853_, v_archiveFile_1854_, v_headers_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v_headers_1855_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* v_getUrl_1864_, lean_object* v_archiveFile_1865_, lean_object* v_headers_1866_, lean_object* v___x_1867_, lean_object* v_facet_1868_, lean_object* v_pkg_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v___f_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_inc_ref(v_pkg_1869_);
v___f_1877_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1877_, 0, v_getUrl_1864_);
lean_closure_set(v___f_1877_, 1, v_pkg_1869_);
lean_closure_set(v___f_1877_, 2, v_archiveFile_1865_);
lean_closure_set(v___f_1877_, 3, v_headers_1866_);
v___x_1878_ = lean_unsigned_to_nat(0u);
v___x_1879_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_1867_);
v___x_1880_ = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(v___x_1880_, 0, lean_box(0));
lean_closure_set(v___x_1880_, 1, v___x_1867_);
lean_closure_set(v___x_1880_, 2, v___f_1877_);
lean_closure_set(v___x_1880_, 3, v___x_1878_);
lean_closure_set(v___x_1880_, 4, v___x_1879_);
v___x_1881_ = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM___boxed), 9, 2);
lean_closure_set(v___x_1881_, 0, lean_box(0));
lean_closure_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM___boxed), 9, 2);
lean_closure_set(v___x_1882_, 0, lean_box(0));
lean_closure_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = l_Lake_ensureJob___redArg(v___x_1867_, v___x_1882_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1916_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_a_1885_ = lean_ctor_get(v___x_1883_, 1);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1887_ = v___x_1883_;
v_isShared_1888_ = v_isSharedCheck_1916_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1916_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v_task_1889_; lean_object* v_kind_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1914_; 
v_task_1889_ = lean_ctor_get(v_a_1884_, 0);
v_kind_1890_ = lean_ctor_get(v_a_1884_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_a_1884_);
if (v_isSharedCheck_1914_ == 0)
{
lean_object* v_unused_1915_; 
v_unused_1915_ = lean_ctor_get(v_a_1884_, 2);
lean_dec(v_unused_1915_);
v___x_1892_ = v_a_1884_;
v_isShared_1893_ = v_isSharedCheck_1914_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_kind_1890_);
lean_inc(v_task_1889_);
lean_dec(v_a_1884_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1914_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v_registeredJobs_1894_; lean_object* v___x_1895_; lean_object* v_baseName_1896_; uint8_t v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v_job_1905_; 
v_registeredJobs_1894_ = lean_ctor_get(v___y_1874_, 3);
v___x_1895_ = lean_st_ref_take(v_registeredJobs_1894_);
v_baseName_1896_ = lean_ctor_get(v_pkg_1869_, 1);
lean_inc(v_baseName_1896_);
lean_dec_ref(v_pkg_1869_);
v___x_1897_ = 1;
v___x_1898_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1896_, v___x_1897_);
v___x_1899_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1900_ = lean_string_append(v___x_1898_, v___x_1899_);
v___x_1901_ = l_Lake_Name_eraseHead(v_facet_1868_);
v___x_1902_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1901_, v___x_1897_);
v___x_1903_ = lean_string_append(v___x_1900_, v___x_1902_);
lean_dec_ref(v___x_1902_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 2, v___x_1903_);
v_job_1905_ = v___x_1892_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_task_1889_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_kind_1890_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v___x_1903_);
v_job_1905_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
lean_ctor_set_uint8(v_job_1905_, sizeof(void*)*3, v___x_1897_);
lean_inc_ref(v_job_1905_);
v___x_1906_ = l_Lake_Job_toOpaque___redArg(v_job_1905_);
v___x_1907_ = lean_array_push(v___x_1895_, v___x_1906_);
v___x_1908_ = lean_st_ref_set(v_registeredJobs_1894_, v___x_1907_);
v___x_1909_ = l_Lake_Job_renew___redArg(v_job_1905_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1909_);
v___x_1911_ = v___x_1887_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_a_1885_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_1869_);
lean_dec(v_facet_1868_);
return v___x_1883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v_getUrl_1917_, lean_object* v_archiveFile_1918_, lean_object* v_headers_1919_, lean_object* v___x_1920_, lean_object* v_facet_1921_, lean_object* v_pkg_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_1917_, v_archiveFile_1918_, v_headers_1919_, v___x_1920_, v_facet_1921_, v_pkg_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec(v___y_1924_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object* v_facet_1938_, lean_object* v_archiveFile_1939_, lean_object* v_getUrl_1940_, lean_object* v_headers_1941_){
_start:
{
lean_object* v___x_1942_; lean_object* v___f_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1942_ = l_Lake_instDataKindBool;
v___f_1943_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_1943_, 0, v_getUrl_1940_);
lean_closure_set(v___f_1943_, 1, v_archiveFile_1939_);
lean_closure_set(v___f_1943_, 2, v_headers_1941_);
lean_closure_set(v___f_1943_, 3, v___x_1942_);
lean_closure_set(v___f_1943_, 4, v_facet_1938_);
v___x_1944_ = l_Lake_Package_keyword;
v___x_1945_ = 1;
v___x_1946_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_1947_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1947_, 0, v___x_1944_);
lean_ctor_set(v___x_1947_, 1, v___f_1943_);
lean_ctor_set(v___x_1947_, 2, v___x_1942_);
lean_ctor_set(v___x_1947_, 3, v___x_1946_);
lean_ctor_set_uint8(v___x_1947_, sizeof(void*)*4, v___x_1945_);
lean_ctor_set_uint8(v___x_1947_, sizeof(void*)*4 + 1, v___x_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* v_facet_1948_, lean_object* v_archiveFile_1949_, lean_object* v_getUrl_1950_, lean_object* v_headers_1951_, lean_object* v_inst_1952_){
_start:
{
lean_object* v___x_1953_; lean_object* v___f_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1953_ = l_Lake_instDataKindBool;
v___f_1954_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_1954_, 0, v_getUrl_1950_);
lean_closure_set(v___f_1954_, 1, v_archiveFile_1949_);
lean_closure_set(v___f_1954_, 2, v_headers_1951_);
lean_closure_set(v___f_1954_, 3, v___x_1953_);
lean_closure_set(v___f_1954_, 4, v_facet_1948_);
v___x_1955_ = l_Lake_Package_keyword;
v___x_1956_ = 1;
v___x_1957_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_1958_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1958_, 0, v___x_1955_);
lean_ctor_set(v___x_1958_, 1, v___f_1954_);
lean_ctor_set(v___x_1958_, 2, v___x_1953_);
lean_ctor_set(v___x_1958_, 3, v___x_1957_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*4, v___x_1956_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*4 + 1, v___x_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_what_1960_, lean_object* v_baseName_1961_, lean_object* v_optFacet_1962_, uint8_t v_success_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_a_1972_; lean_object* v_a_1973_; 
if (v_success_1963_ == 0)
{
lean_object* v_toBuildConfig_1994_; uint8_t v_verbosity_1995_; uint8_t v___x_1996_; uint8_t v___x_1997_; 
v_toBuildConfig_1994_ = lean_ctor_get(v___y_1968_, 0);
v_verbosity_1995_ = lean_ctor_get_uint8(v_toBuildConfig_1994_, sizeof(void*)*3 + 3);
v___x_1996_ = 2;
v___x_1997_ = l_Lake_instDecidableEqVerbosity(v_verbosity_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; 
lean_dec(v_optFacet_1962_);
lean_dec(v_baseName_1961_);
v___x_1998_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_1972_ = v___x_1998_;
v_a_1973_ = v___y_1969_;
goto v___jp_1971_;
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_1999_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2000_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1961_, v___x_1997_);
v___x_2001_ = lean_string_append(v___x_1999_, v___x_2000_);
lean_dec_ref(v___x_2000_);
v___x_2002_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2003_ = lean_string_append(v___x_2001_, v___x_2002_);
v___x_2004_ = l_Lake_Name_eraseHead(v_optFacet_1962_);
v___x_2005_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2004_, v___x_1997_);
v___x_2006_ = lean_string_append(v___x_2003_, v___x_2005_);
lean_dec_ref(v___x_2005_);
v___x_2007_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2008_ = lean_string_append(v___x_2006_, v___x_2007_);
v_a_1972_ = v___x_2008_;
v_a_1973_ = v___y_1969_;
goto v___jp_1971_;
}
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec(v_optFacet_1962_);
lean_dec(v_baseName_1961_);
v___x_2009_ = lean_box(0);
v___x_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
lean_ctor_set(v___x_2010_, 1, v___y_1969_);
return v___x_2010_;
}
v___jp_1971_:
{
lean_object* v_log_1974_; uint8_t v_action_1975_; uint8_t v_wantsRebuild_1976_; lean_object* v_trace_1977_; lean_object* v_buildTime_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1993_; 
v_log_1974_ = lean_ctor_get(v_a_1973_, 0);
v_action_1975_ = lean_ctor_get_uint8(v_a_1973_, sizeof(void*)*3);
v_wantsRebuild_1976_ = lean_ctor_get_uint8(v_a_1973_, sizeof(void*)*3 + 1);
v_trace_1977_ = lean_ctor_get(v_a_1973_, 1);
v_buildTime_1978_ = lean_ctor_get(v_a_1973_, 2);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_a_1973_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1980_ = v_a_1973_;
v_isShared_1981_ = v_isSharedCheck_1993_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_buildTime_1978_);
lean_inc(v_trace_1977_);
lean_inc(v_log_1974_);
lean_dec(v_a_1973_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1993_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1982_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0));
v___x_1983_ = lean_string_append(v___x_1982_, v_what_1960_);
v___x_1984_ = lean_string_append(v___x_1983_, v_a_1972_);
lean_dec_ref(v_a_1972_);
v___x_1985_ = 3;
v___x_1986_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1986_, 0, v___x_1984_);
lean_ctor_set_uint8(v___x_1986_, sizeof(void*)*1, v___x_1985_);
v___x_1987_ = lean_array_get_size(v_log_1974_);
v___x_1988_ = lean_array_push(v_log_1974_, v___x_1986_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1988_);
v___x_1990_ = v___x_1980_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_trace_1977_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_buildTime_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*3, v_action_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1992_, sizeof(void*)*3 + 1, v_wantsRebuild_1976_);
v___x_1990_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1991_; 
v___x_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1987_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
return v___x_1991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_what_2011_, lean_object* v_baseName_2012_, lean_object* v_optFacet_2013_, lean_object* v_success_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
uint8_t v_success_boxed_2022_; lean_object* v_res_2023_; 
v_success_boxed_2022_ = lean_unbox(v_success_2014_);
v_res_2023_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(v_what_2011_, v_baseName_2012_, v_optFacet_2013_, v_success_boxed_2022_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec_ref(v_what_2011_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object* v___x_2024_, lean_object* v___x_2025_, lean_object* v___f_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___x_2034_; 
lean_inc_ref(v___y_2027_);
lean_inc_ref(v___y_2031_);
lean_inc(v___y_2030_);
lean_inc(v___y_2029_);
lean_inc(v___y_2028_);
v___x_2034_ = lean_apply_7(v___y_2027_, v___x_2024_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, lean_box(0));
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2047_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
v_a_2036_ = lean_ctor_get(v___x_2034_, 1);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2038_ = v___x_2034_;
v_isShared_2039_ = v_isSharedCheck_2047_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_inc(v_a_2035_);
lean_dec(v___x_2034_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2047_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; uint8_t v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2040_ = lean_unsigned_to_nat(0u);
v___x_2041_ = 0;
v___x_2042_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2043_ = l_Lake_Job_mapM___redArg(v___x_2025_, v_a_2035_, v___f_2026_, v___x_2040_, v___x_2041_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___x_2042_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2043_);
v___x_2045_ = v___x_2038_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_a_2036_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec_ref(v___y_2027_);
lean_dec_ref(v___f_2026_);
lean_dec(v___x_2025_);
v_a_2048_ = lean_ctor_get(v___x_2034_, 0);
v_a_2049_ = lean_ctor_get(v___x_2034_, 1);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2034_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_inc(v_a_2048_);
lean_dec(v___x_2034_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2048_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v___x_2057_, lean_object* v___x_2058_, lean_object* v___f_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(v___x_2057_, v___x_2058_, v___f_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec(v___y_2061_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object* v_what_2068_, lean_object* v_optFacet_2069_, lean_object* v___x_2070_, lean_object* v_facet_2071_, lean_object* v_pkg_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v_baseName_2080_; lean_object* v_keyName_2081_; lean_object* v___f_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___f_2086_; lean_object* v___x_2087_; 
v_baseName_2080_ = lean_ctor_get(v_pkg_2072_, 1);
lean_inc_n(v_baseName_2080_, 2);
v_keyName_2081_ = lean_ctor_get(v_pkg_2072_, 2);
lean_inc(v_optFacet_2069_);
v___f_2082_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2082_, 0, v_what_2068_);
lean_closure_set(v___f_2082_, 1, v_baseName_2080_);
lean_closure_set(v___f_2082_, 2, v_optFacet_2069_);
lean_inc(v_keyName_2081_);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_keyName_2081_);
v___x_2084_ = l_Lake_Package_keyword;
v___x_2085_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2083_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
lean_ctor_set(v___x_2085_, 2, v_pkg_2072_);
lean_ctor_set(v___x_2085_, 3, v_optFacet_2069_);
lean_inc(v___x_2070_);
v___f_2086_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2086_, 0, v___x_2085_);
lean_closure_set(v___f_2086_, 1, v___x_2070_);
lean_closure_set(v___f_2086_, 2, v___f_2082_);
v___x_2087_ = l_Lake_ensureJob___redArg(v___x_2070_, v___f_2086_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2120_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_a_2089_ = lean_ctor_get(v___x_2087_, 1);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2091_ = v___x_2087_;
v_isShared_2092_ = v_isSharedCheck_2120_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2120_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_task_2093_; lean_object* v_kind_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2118_; 
v_task_2093_ = lean_ctor_get(v_a_2088_, 0);
v_kind_2094_ = lean_ctor_get(v_a_2088_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_a_2088_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; 
v_unused_2119_ = lean_ctor_get(v_a_2088_, 2);
lean_dec(v_unused_2119_);
v___x_2096_ = v_a_2088_;
v_isShared_2097_ = v_isSharedCheck_2118_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_kind_2094_);
lean_inc(v_task_2093_);
lean_dec(v_a_2088_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2118_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v_registeredJobs_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; lean_object* v_job_2109_; 
v_registeredJobs_2098_ = lean_ctor_get(v___y_2077_, 3);
v___x_2099_ = lean_st_ref_take(v_registeredJobs_2098_);
v___x_2100_ = 1;
v___x_2101_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2080_, v___x_2100_);
v___x_2102_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2103_ = lean_string_append(v___x_2101_, v___x_2102_);
v___x_2104_ = l_Lake_Name_eraseHead(v_facet_2071_);
v___x_2105_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2104_, v___x_2100_);
v___x_2106_ = lean_string_append(v___x_2103_, v___x_2105_);
lean_dec_ref(v___x_2105_);
v___x_2107_ = 0;
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 2, v___x_2106_);
v_job_2109_ = v___x_2096_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_task_2093_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_kind_2094_);
lean_ctor_set(v_reuseFailAlloc_2117_, 2, v___x_2106_);
v_job_2109_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
lean_ctor_set_uint8(v_job_2109_, sizeof(void*)*3, v___x_2107_);
lean_inc_ref(v_job_2109_);
v___x_2110_ = l_Lake_Job_toOpaque___redArg(v_job_2109_);
v___x_2111_ = lean_array_push(v___x_2099_, v___x_2110_);
v___x_2112_ = lean_st_ref_set(v_registeredJobs_2098_, v___x_2111_);
v___x_2113_ = l_Lake_Job_renew___redArg(v_job_2109_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2113_);
v___x_2115_ = v___x_2091_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_a_2089_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2080_);
lean_dec(v_facet_2071_);
return v___x_2087_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object* v_what_2121_, lean_object* v_optFacet_2122_, lean_object* v___x_2123_, lean_object* v_facet_2124_, lean_object* v_pkg_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(v_what_2121_, v_optFacet_2122_, v___x_2123_, v_facet_2124_, v_pkg_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec(v___y_2127_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object* v_facet_2141_, lean_object* v_optFacet_2142_, lean_object* v_what_2143_){
_start:
{
lean_object* v___x_2144_; lean_object* v___f_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2144_ = l_Lake_instDataKindUnit;
v___f_2145_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2145_, 0, v_what_2143_);
lean_closure_set(v___f_2145_, 1, v_optFacet_2142_);
lean_closure_set(v___f_2145_, 2, v___x_2144_);
lean_closure_set(v___f_2145_, 3, v_facet_2141_);
v___x_2146_ = l_Lake_Package_keyword;
v___x_2147_ = 1;
v___x_2148_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2149_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2149_, 0, v___x_2146_);
lean_ctor_set(v___x_2149_, 1, v___f_2145_);
lean_ctor_set(v___x_2149_, 2, v___x_2144_);
lean_ctor_set(v___x_2149_, 3, v___x_2148_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*4, v___x_2147_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*4 + 1, v___x_2147_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* v_facet_2150_, lean_object* v_optFacet_2151_, lean_object* v_what_2152_, lean_object* v_inst_2153_, lean_object* v_inst_2154_){
_start:
{
lean_object* v___x_2155_; lean_object* v___f_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2155_ = l_Lake_instDataKindUnit;
v___f_2156_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2156_, 0, v_what_2152_);
lean_closure_set(v___f_2156_, 1, v_optFacet_2151_);
lean_closure_set(v___f_2156_, 2, v___x_2155_);
lean_closure_set(v___f_2156_, 3, v_facet_2150_);
v___x_2157_ = l_Lake_Package_keyword;
v___x_2158_ = 1;
v___x_2159_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2160_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2160_, 0, v___x_2157_);
lean_ctor_set(v___x_2160_, 1, v___f_2156_);
lean_ctor_set(v___x_2160_, 2, v___x_2155_);
lean_ctor_set(v___x_2160_, 3, v___x_2159_);
lean_ctor_set_uint8(v___x_2160_, sizeof(void*)*4, v___x_2158_);
lean_ctor_set_uint8(v___x_2160_, sizeof(void*)*4 + 1, v___x_2158_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* v_baseName_2162_, lean_object* v___x_2163_, uint8_t v_success_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_a_2173_; lean_object* v_a_2174_; 
if (v_success_2164_ == 0)
{
lean_object* v_toBuildConfig_2194_; uint8_t v_verbosity_2195_; uint8_t v___x_2196_; uint8_t v___x_2197_; 
v_toBuildConfig_2194_ = lean_ctor_get(v___y_2169_, 0);
v_verbosity_2195_ = lean_ctor_get_uint8(v_toBuildConfig_2194_, sizeof(void*)*3 + 3);
v___x_2196_ = 2;
v___x_2197_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; 
lean_dec(v___x_2163_);
lean_dec(v_baseName_2162_);
v___x_2198_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2173_ = v___x_2198_;
v_a_2174_ = v___y_2170_;
goto v___jp_2172_;
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2199_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2200_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2162_, v___x_2197_);
v___x_2201_ = lean_string_append(v___x_2199_, v___x_2200_);
lean_dec_ref(v___x_2200_);
v___x_2202_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2203_ = lean_string_append(v___x_2201_, v___x_2202_);
v___x_2204_ = l_Lake_Name_eraseHead(v___x_2163_);
v___x_2205_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2204_, v___x_2197_);
v___x_2206_ = lean_string_append(v___x_2203_, v___x_2205_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2208_ = lean_string_append(v___x_2206_, v___x_2207_);
v_a_2173_ = v___x_2208_;
v_a_2174_ = v___y_2170_;
goto v___jp_2172_;
}
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_dec(v___x_2163_);
lean_dec(v_baseName_2162_);
v___x_2209_ = lean_box(0);
v___x_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___y_2170_);
return v___x_2210_;
}
v___jp_2172_:
{
lean_object* v_log_2175_; uint8_t v_action_2176_; uint8_t v_wantsRebuild_2177_; lean_object* v_trace_2178_; lean_object* v_buildTime_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2193_; 
v_log_2175_ = lean_ctor_get(v_a_2174_, 0);
v_action_2176_ = lean_ctor_get_uint8(v_a_2174_, sizeof(void*)*3);
v_wantsRebuild_2177_ = lean_ctor_get_uint8(v_a_2174_, sizeof(void*)*3 + 1);
v_trace_2178_ = lean_ctor_get(v_a_2174_, 1);
v_buildTime_2179_ = lean_ctor_get(v_a_2174_, 2);
v_isSharedCheck_2193_ = !lean_is_exclusive(v_a_2174_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2181_ = v_a_2174_;
v_isShared_2182_ = v_isSharedCheck_2193_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_buildTime_2179_);
lean_inc(v_trace_2178_);
lean_inc(v_log_2175_);
lean_dec(v_a_2174_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2193_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
v___x_2183_ = ((lean_object*)(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0));
v___x_2184_ = lean_string_append(v___x_2183_, v_a_2173_);
lean_dec_ref(v_a_2173_);
v___x_2185_ = 3;
v___x_2186_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2186_, 0, v___x_2184_);
lean_ctor_set_uint8(v___x_2186_, sizeof(void*)*1, v___x_2185_);
v___x_2187_ = lean_array_get_size(v_log_2175_);
v___x_2188_ = lean_array_push(v_log_2175_, v___x_2186_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v___x_2188_);
v___x_2190_ = v___x_2181_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_trace_2178_);
lean_ctor_set(v_reuseFailAlloc_2192_, 2, v_buildTime_2179_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, sizeof(void*)*3, v_action_2176_);
lean_ctor_set_uint8(v_reuseFailAlloc_2192_, sizeof(void*)*3 + 1, v_wantsRebuild_2177_);
v___x_2190_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2191_; 
v___x_2191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2187_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
return v___x_2191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object* v_baseName_2211_, lean_object* v___x_2212_, lean_object* v_success_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
uint8_t v_success_boxed_2221_; lean_object* v_res_2222_; 
v_success_boxed_2221_ = lean_unbox(v_success_2213_);
v_res_2222_ = l_Lake_Package_buildCacheFacetConfig___lam__1(v_baseName_2211_, v___x_2212_, v_success_boxed_2221_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* v___x_2223_, lean_object* v___x_2224_, lean_object* v___x_2225_, lean_object* v_pkg_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_baseName_2234_; lean_object* v_keyName_2235_; lean_object* v___f_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___f_2240_; lean_object* v___x_2241_; 
v_baseName_2234_ = lean_ctor_get(v_pkg_2226_, 1);
lean_inc_n(v_baseName_2234_, 2);
v_keyName_2235_ = lean_ctor_get(v_pkg_2226_, 2);
lean_inc(v___x_2223_);
v___f_2236_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2236_, 0, v_baseName_2234_);
lean_closure_set(v___f_2236_, 1, v___x_2223_);
lean_inc(v_keyName_2235_);
v___x_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2237_, 0, v_keyName_2235_);
v___x_2238_ = l_Lake_Package_keyword;
v___x_2239_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2237_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
lean_ctor_set(v___x_2239_, 2, v_pkg_2226_);
lean_ctor_set(v___x_2239_, 3, v___x_2223_);
lean_inc(v___x_2224_);
v___f_2240_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2240_, 0, v___x_2239_);
lean_closure_set(v___f_2240_, 1, v___x_2224_);
lean_closure_set(v___f_2240_, 2, v___f_2236_);
v___x_2241_ = l_Lake_ensureJob___redArg(v___x_2224_, v___f_2240_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2274_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_a_2243_ = lean_ctor_get(v___x_2241_, 1);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2245_ = v___x_2241_;
v_isShared_2246_ = v_isSharedCheck_2274_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2274_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v_task_2247_; lean_object* v_kind_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2272_; 
v_task_2247_ = lean_ctor_get(v_a_2242_, 0);
v_kind_2248_ = lean_ctor_get(v_a_2242_, 1);
v_isSharedCheck_2272_ = !lean_is_exclusive(v_a_2242_);
if (v_isSharedCheck_2272_ == 0)
{
lean_object* v_unused_2273_; 
v_unused_2273_ = lean_ctor_get(v_a_2242_, 2);
lean_dec(v_unused_2273_);
v___x_2250_ = v_a_2242_;
v_isShared_2251_ = v_isSharedCheck_2272_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_kind_2248_);
lean_inc(v_task_2247_);
lean_dec(v_a_2242_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2272_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v_registeredJobs_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; lean_object* v_job_2263_; 
v_registeredJobs_2252_ = lean_ctor_get(v___y_2231_, 3);
v___x_2253_ = lean_st_ref_take(v_registeredJobs_2252_);
v___x_2254_ = 1;
v___x_2255_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2234_, v___x_2254_);
v___x_2256_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2257_ = lean_string_append(v___x_2255_, v___x_2256_);
v___x_2258_ = l_Lake_Name_eraseHead(v___x_2225_);
v___x_2259_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2258_, v___x_2254_);
v___x_2260_ = lean_string_append(v___x_2257_, v___x_2259_);
lean_dec_ref(v___x_2259_);
v___x_2261_ = 0;
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 2, v___x_2260_);
v_job_2263_ = v___x_2250_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_task_2247_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_kind_2248_);
lean_ctor_set(v_reuseFailAlloc_2271_, 2, v___x_2260_);
v_job_2263_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
lean_ctor_set_uint8(v_job_2263_, sizeof(void*)*3, v___x_2261_);
lean_inc_ref(v_job_2263_);
v___x_2264_ = l_Lake_Job_toOpaque___redArg(v_job_2263_);
v___x_2265_ = lean_array_push(v___x_2253_, v___x_2264_);
v___x_2266_ = lean_st_ref_set(v_registeredJobs_2252_, v___x_2265_);
v___x_2267_ = l_Lake_Job_renew___redArg(v_job_2263_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2267_);
v___x_2269_ = v___x_2245_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_a_2243_);
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
}
else
{
lean_dec(v_baseName_2234_);
lean_dec(v___x_2225_);
return v___x_2241_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object* v___x_2275_, lean_object* v___x_2276_, lean_object* v___x_2277_, lean_object* v_pkg_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lake_Package_buildCacheFacetConfig___lam__2(v___x_2275_, v___x_2276_, v___x_2277_, v_pkg_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec(v___y_2281_);
lean_dec(v___y_2280_);
return v_res_2286_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___f_2290_; 
v___x_2287_ = l_Lake_Package_buildCacheFacet;
v___x_2288_ = l_Lake_instDataKindUnit;
v___x_2289_ = l_Lake_Package_optBuildCacheFacet;
v___f_2290_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2290_, 0, v___x_2289_);
lean_closure_set(v___f_2290_, 1, v___x_2288_);
lean_closure_set(v___f_2290_, 2, v___x_2287_);
return v___f_2290_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2291_; uint8_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___f_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___f_2291_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2292_ = 1;
v___x_2293_ = l_Lake_instDataKindUnit;
v___f_2294_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__0, &l_Lake_Package_buildCacheFacetConfig___closed__0_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__0);
v___x_2295_ = l_Lake_Package_keyword;
v___x_2296_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_ctor_set(v___x_2296_, 1, v___f_2294_);
lean_ctor_set(v___x_2296_, 2, v___x_2293_);
lean_ctor_set(v___x_2296_, 3, v___f_2291_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*4, v___x_2292_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*4 + 1, v___x_2292_);
return v___x_2296_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig(void){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__1, &l_Lake_Package_buildCacheFacetConfig___closed__1_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__1);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* v_pkg_2299_, lean_object* v___x_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
uint8_t v_r_2309_; lean_object* v___y_2310_; lean_object* v_a_2314_; lean_object* v___x_2330_; 
lean_inc_ref(v_pkg_2299_);
v___x_2330_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_pkg_2299_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v_a_2332_; lean_object* v_dir_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
v_a_2332_ = lean_ctor_get(v___x_2330_, 1);
lean_inc(v_a_2332_);
lean_dec_ref(v___x_2330_);
v_dir_2333_ = lean_ctor_get(v_pkg_2299_, 4);
v___x_2334_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_2333_);
v___x_2335_ = l_Lake_joinRelative(v_dir_2333_, v___x_2334_);
v___x_2336_ = ((lean_object*)(l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0));
v___x_2337_ = l_Lake_joinRelative(v___x_2335_, v___x_2336_);
v___x_2338_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2299_, v_a_2331_, v___x_2337_, v___x_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v_a_2332_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; uint8_t v___x_2340_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 1);
lean_inc(v_a_2339_);
lean_dec_ref(v___x_2338_);
v___x_2340_ = 1;
v_r_2309_ = v___x_2340_;
v___y_2310_ = v_a_2339_;
goto v___jp_2308_;
}
else
{
lean_object* v_a_2341_; 
v_a_2341_ = lean_ctor_get(v___x_2338_, 1);
lean_inc(v_a_2341_);
lean_dec_ref(v___x_2338_);
v_a_2314_ = v_a_2341_;
goto v___jp_2313_;
}
}
else
{
lean_object* v_a_2342_; 
lean_dec_ref(v_pkg_2299_);
v_a_2342_ = lean_ctor_get(v___x_2330_, 1);
lean_inc(v_a_2342_);
lean_dec_ref(v___x_2330_);
v_a_2314_ = v_a_2342_;
goto v___jp_2313_;
}
v___jp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_box(v_r_2309_);
v___x_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v___y_2310_);
return v___x_2312_;
}
v___jp_2313_:
{
lean_object* v_log_2315_; uint8_t v_action_2316_; uint8_t v_wantsRebuild_2317_; lean_object* v_trace_2318_; lean_object* v_buildTime_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2329_; 
v_log_2315_ = lean_ctor_get(v_a_2314_, 0);
v_action_2316_ = lean_ctor_get_uint8(v_a_2314_, sizeof(void*)*3);
v_wantsRebuild_2317_ = lean_ctor_get_uint8(v_a_2314_, sizeof(void*)*3 + 1);
v_trace_2318_ = lean_ctor_get(v_a_2314_, 1);
v_buildTime_2319_ = lean_ctor_get(v_a_2314_, 2);
v_isSharedCheck_2329_ = !lean_is_exclusive(v_a_2314_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2321_ = v_a_2314_;
v_isShared_2322_ = v_isSharedCheck_2329_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_buildTime_2319_);
lean_inc(v_trace_2318_);
lean_inc(v_log_2315_);
lean_dec(v_a_2314_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2329_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
uint8_t v___x_2323_; uint8_t v___x_2324_; lean_object* v___x_2326_; 
v___x_2323_ = 4;
v___x_2324_ = l_Lake_JobAction_merge(v_action_2316_, v___x_2323_);
if (v_isShared_2322_ == 0)
{
v___x_2326_ = v___x_2321_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_log_2315_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_trace_2318_);
lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_buildTime_2319_);
lean_ctor_set_uint8(v_reuseFailAlloc_2328_, sizeof(void*)*3 + 1, v_wantsRebuild_2317_);
v___x_2326_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
uint8_t v___x_2327_; 
lean_ctor_set_uint8(v___x_2326_, sizeof(void*)*3, v___x_2324_);
v___x_2327_ = 0;
v_r_2309_ = v___x_2327_;
v___y_2310_ = v___x_2326_;
goto v___jp_2308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* v_pkg_2343_, lean_object* v___x_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lake_Package_optBarrelFacetConfig___lam__0(v_pkg_2343_, v___x_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec_ref(v___x_2344_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* v___x_2353_, lean_object* v___f_2354_, lean_object* v___x_2355_, lean_object* v___x_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = l_Lake_Job_async___redArg(v___x_2353_, v___f_2354_, v___x_2355_, v___x_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
v___x_2365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
lean_ctor_set(v___x_2365_, 1, v___y_2362_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object* v___x_2366_, lean_object* v___f_2367_, lean_object* v___x_2368_, lean_object* v___x_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lake_Package_optBarrelFacetConfig___lam__1(v___x_2366_, v___f_2367_, v___x_2368_, v___x_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec(v___y_2371_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* v___x_2378_, lean_object* v___x_2379_, lean_object* v___x_2380_, lean_object* v_pkg_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___f_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___f_2392_; lean_object* v___x_2393_; 
lean_inc_ref(v_pkg_2381_);
v___f_2389_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2389_, 0, v_pkg_2381_);
lean_closure_set(v___f_2389_, 1, v___x_2378_);
v___x_2390_ = lean_unsigned_to_nat(0u);
v___x_2391_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2379_);
v___f_2392_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2392_, 0, v___x_2379_);
lean_closure_set(v___f_2392_, 1, v___f_2389_);
lean_closure_set(v___f_2392_, 2, v___x_2390_);
lean_closure_set(v___f_2392_, 3, v___x_2391_);
v___x_2393_ = l_Lake_ensureJob___redArg(v___x_2379_, v___f_2392_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2426_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_a_2395_ = lean_ctor_get(v___x_2393_, 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2397_ = v___x_2393_;
v_isShared_2398_ = v_isSharedCheck_2426_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2426_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v_task_2399_; lean_object* v_kind_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2424_; 
v_task_2399_ = lean_ctor_get(v_a_2394_, 0);
v_kind_2400_ = lean_ctor_get(v_a_2394_, 1);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_a_2394_);
if (v_isSharedCheck_2424_ == 0)
{
lean_object* v_unused_2425_; 
v_unused_2425_ = lean_ctor_get(v_a_2394_, 2);
lean_dec(v_unused_2425_);
v___x_2402_ = v_a_2394_;
v_isShared_2403_ = v_isSharedCheck_2424_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_kind_2400_);
lean_inc(v_task_2399_);
lean_dec(v_a_2394_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2424_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v_registeredJobs_2404_; lean_object* v___x_2405_; lean_object* v_baseName_2406_; uint8_t v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v_job_2415_; 
v_registeredJobs_2404_ = lean_ctor_get(v___y_2386_, 3);
v___x_2405_ = lean_st_ref_take(v_registeredJobs_2404_);
v_baseName_2406_ = lean_ctor_get(v_pkg_2381_, 1);
lean_inc(v_baseName_2406_);
lean_dec_ref(v_pkg_2381_);
v___x_2407_ = 1;
v___x_2408_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2406_, v___x_2407_);
v___x_2409_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2410_ = lean_string_append(v___x_2408_, v___x_2409_);
v___x_2411_ = l_Lake_Name_eraseHead(v___x_2380_);
v___x_2412_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2411_, v___x_2407_);
v___x_2413_ = lean_string_append(v___x_2410_, v___x_2412_);
lean_dec_ref(v___x_2412_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 2, v___x_2413_);
v_job_2415_ = v___x_2402_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_task_2399_);
lean_ctor_set(v_reuseFailAlloc_2423_, 1, v_kind_2400_);
lean_ctor_set(v_reuseFailAlloc_2423_, 2, v___x_2413_);
v_job_2415_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
lean_ctor_set_uint8(v_job_2415_, sizeof(void*)*3, v___x_2407_);
lean_inc_ref(v_job_2415_);
v___x_2416_ = l_Lake_Job_toOpaque___redArg(v_job_2415_);
v___x_2417_ = lean_array_push(v___x_2405_, v___x_2416_);
v___x_2418_ = lean_st_ref_set(v_registeredJobs_2404_, v___x_2417_);
v___x_2419_ = l_Lake_Job_renew___redArg(v_job_2415_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2419_);
v___x_2421_ = v___x_2397_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2419_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_a_2395_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_2381_);
lean_dec(v___x_2380_);
return v___x_2393_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object* v___x_2427_, lean_object* v___x_2428_, lean_object* v___x_2429_, lean_object* v_pkg_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lake_Package_optBarrelFacetConfig___lam__2(v___x_2427_, v___x_2428_, v___x_2429_, v_pkg_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec(v___y_2432_);
return v_res_2438_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___f_2442_; 
v___x_2439_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_2440_ = l_Lake_instDataKindBool;
v___x_2441_ = l_Lake_Reservoir_lakeHeaders;
v___f_2442_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2442_, 0, v___x_2441_);
lean_closure_set(v___f_2442_, 1, v___x_2440_);
lean_closure_set(v___f_2442_, 2, v___x_2439_);
return v___f_2442_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2443_; uint8_t v___x_2444_; lean_object* v___x_2445_; lean_object* v___f_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___f_2443_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_2444_ = 1;
v___x_2445_ = l_Lake_instDataKindBool;
v___f_2446_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__0, &l_Lake_Package_optBarrelFacetConfig___closed__0_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__0);
v___x_2447_ = l_Lake_Package_keyword;
v___x_2448_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v___f_2446_);
lean_ctor_set(v___x_2448_, 2, v___x_2445_);
lean_ctor_set(v___x_2448_, 3, v___f_2443_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*4, v___x_2444_);
lean_ctor_set_uint8(v___x_2448_, sizeof(void*)*4 + 1, v___x_2444_);
return v___x_2448_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig(void){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__1, &l_Lake_Package_optBarrelFacetConfig___closed__1_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__1);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* v_baseName_2451_, lean_object* v___x_2452_, uint8_t v_success_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v_a_2462_; lean_object* v_a_2463_; 
if (v_success_2453_ == 0)
{
lean_object* v_toBuildConfig_2483_; uint8_t v_verbosity_2484_; uint8_t v___x_2485_; uint8_t v___x_2486_; 
v_toBuildConfig_2483_ = lean_ctor_get(v___y_2458_, 0);
v_verbosity_2484_ = lean_ctor_get_uint8(v_toBuildConfig_2483_, sizeof(void*)*3 + 3);
v___x_2485_ = 2;
v___x_2486_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2484_, v___x_2485_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
lean_dec(v___x_2452_);
lean_dec(v_baseName_2451_);
v___x_2487_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2462_ = v___x_2487_;
v_a_2463_ = v___y_2459_;
goto v___jp_2461_;
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2488_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2489_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2451_, v___x_2486_);
v___x_2490_ = lean_string_append(v___x_2488_, v___x_2489_);
lean_dec_ref(v___x_2489_);
v___x_2491_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2492_ = lean_string_append(v___x_2490_, v___x_2491_);
v___x_2493_ = l_Lake_Name_eraseHead(v___x_2452_);
v___x_2494_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2493_, v___x_2486_);
v___x_2495_ = lean_string_append(v___x_2492_, v___x_2494_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2497_ = lean_string_append(v___x_2495_, v___x_2496_);
v_a_2462_ = v___x_2497_;
v_a_2463_ = v___y_2459_;
goto v___jp_2461_;
}
}
else
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec(v___x_2452_);
lean_dec(v_baseName_2451_);
v___x_2498_ = lean_box(0);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v___y_2459_);
return v___x_2499_;
}
v___jp_2461_:
{
lean_object* v_log_2464_; uint8_t v_action_2465_; uint8_t v_wantsRebuild_2466_; lean_object* v_trace_2467_; lean_object* v_buildTime_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2482_; 
v_log_2464_ = lean_ctor_get(v_a_2463_, 0);
v_action_2465_ = lean_ctor_get_uint8(v_a_2463_, sizeof(void*)*3);
v_wantsRebuild_2466_ = lean_ctor_get_uint8(v_a_2463_, sizeof(void*)*3 + 1);
v_trace_2467_ = lean_ctor_get(v_a_2463_, 1);
v_buildTime_2468_ = lean_ctor_get(v_a_2463_, 2);
v_isSharedCheck_2482_ = !lean_is_exclusive(v_a_2463_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2470_ = v_a_2463_;
v_isShared_2471_ = v_isSharedCheck_2482_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_buildTime_2468_);
lean_inc(v_trace_2467_);
lean_inc(v_log_2464_);
lean_dec(v_a_2463_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2482_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
v___x_2472_ = ((lean_object*)(l_Lake_Package_barrelFacetConfig___lam__1___closed__0));
v___x_2473_ = lean_string_append(v___x_2472_, v_a_2462_);
lean_dec_ref(v_a_2462_);
v___x_2474_ = 3;
v___x_2475_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*1, v___x_2474_);
v___x_2476_ = lean_array_get_size(v_log_2464_);
v___x_2477_ = lean_array_push(v_log_2464_, v___x_2475_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2477_);
v___x_2479_ = v___x_2470_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v_trace_2467_);
lean_ctor_set(v_reuseFailAlloc_2481_, 2, v_buildTime_2468_);
lean_ctor_set_uint8(v_reuseFailAlloc_2481_, sizeof(void*)*3, v_action_2465_);
lean_ctor_set_uint8(v_reuseFailAlloc_2481_, sizeof(void*)*3 + 1, v_wantsRebuild_2466_);
v___x_2479_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; 
v___x_2480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2476_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
return v___x_2480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object* v_baseName_2500_, lean_object* v___x_2501_, lean_object* v_success_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
uint8_t v_success_boxed_2510_; lean_object* v_res_2511_; 
v_success_boxed_2510_ = lean_unbox(v_success_2502_);
v_res_2511_ = l_Lake_Package_barrelFacetConfig___lam__1(v_baseName_2500_, v___x_2501_, v_success_boxed_2510_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* v___x_2512_, lean_object* v___x_2513_, lean_object* v___x_2514_, lean_object* v_pkg_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_baseName_2523_; lean_object* v_keyName_2524_; lean_object* v___f_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___f_2529_; lean_object* v___x_2530_; 
v_baseName_2523_ = lean_ctor_get(v_pkg_2515_, 1);
lean_inc_n(v_baseName_2523_, 2);
v_keyName_2524_ = lean_ctor_get(v_pkg_2515_, 2);
lean_inc(v___x_2512_);
v___f_2525_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2525_, 0, v_baseName_2523_);
lean_closure_set(v___f_2525_, 1, v___x_2512_);
lean_inc(v_keyName_2524_);
v___x_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2526_, 0, v_keyName_2524_);
v___x_2527_ = l_Lake_Package_keyword;
v___x_2528_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2526_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
lean_ctor_set(v___x_2528_, 2, v_pkg_2515_);
lean_ctor_set(v___x_2528_, 3, v___x_2512_);
lean_inc(v___x_2513_);
v___f_2529_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2529_, 0, v___x_2528_);
lean_closure_set(v___f_2529_, 1, v___x_2513_);
lean_closure_set(v___f_2529_, 2, v___f_2525_);
v___x_2530_ = l_Lake_ensureJob___redArg(v___x_2513_, v___f_2529_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2563_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_a_2532_ = lean_ctor_get(v___x_2530_, 1);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2534_ = v___x_2530_;
v_isShared_2535_ = v_isSharedCheck_2563_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2563_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v_task_2536_; lean_object* v_kind_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2561_; 
v_task_2536_ = lean_ctor_get(v_a_2531_, 0);
v_kind_2537_ = lean_ctor_get(v_a_2531_, 1);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_a_2531_);
if (v_isSharedCheck_2561_ == 0)
{
lean_object* v_unused_2562_; 
v_unused_2562_ = lean_ctor_get(v_a_2531_, 2);
lean_dec(v_unused_2562_);
v___x_2539_ = v_a_2531_;
v_isShared_2540_ = v_isSharedCheck_2561_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_kind_2537_);
lean_inc(v_task_2536_);
lean_dec(v_a_2531_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2561_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v_registeredJobs_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; lean_object* v_job_2552_; 
v_registeredJobs_2541_ = lean_ctor_get(v___y_2520_, 3);
v___x_2542_ = lean_st_ref_take(v_registeredJobs_2541_);
v___x_2543_ = 1;
v___x_2544_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2523_, v___x_2543_);
v___x_2545_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2546_ = lean_string_append(v___x_2544_, v___x_2545_);
v___x_2547_ = l_Lake_Name_eraseHead(v___x_2514_);
v___x_2548_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2547_, v___x_2543_);
v___x_2549_ = lean_string_append(v___x_2546_, v___x_2548_);
lean_dec_ref(v___x_2548_);
v___x_2550_ = 0;
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 2, v___x_2549_);
v_job_2552_ = v___x_2539_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_task_2536_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_kind_2537_);
lean_ctor_set(v_reuseFailAlloc_2560_, 2, v___x_2549_);
v_job_2552_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
lean_ctor_set_uint8(v_job_2552_, sizeof(void*)*3, v___x_2550_);
lean_inc_ref(v_job_2552_);
v___x_2553_ = l_Lake_Job_toOpaque___redArg(v_job_2552_);
v___x_2554_ = lean_array_push(v___x_2542_, v___x_2553_);
v___x_2555_ = lean_st_ref_set(v_registeredJobs_2541_, v___x_2554_);
v___x_2556_ = l_Lake_Job_renew___redArg(v_job_2552_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2556_);
v___x_2558_ = v___x_2534_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_a_2532_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2523_);
lean_dec(v___x_2514_);
return v___x_2530_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object* v___x_2564_, lean_object* v___x_2565_, lean_object* v___x_2566_, lean_object* v_pkg_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lake_Package_barrelFacetConfig___lam__2(v___x_2564_, v___x_2565_, v___x_2566_, v_pkg_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec(v___y_2569_);
return v_res_2575_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___f_2579_; 
v___x_2576_ = l_Lake_Package_reservoirBarrelFacet;
v___x_2577_ = l_Lake_instDataKindUnit;
v___x_2578_ = l_Lake_Package_optReservoirBarrelFacet;
v___f_2579_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2579_, 0, v___x_2578_);
lean_closure_set(v___f_2579_, 1, v___x_2577_);
lean_closure_set(v___f_2579_, 2, v___x_2576_);
return v___f_2579_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2580_; uint8_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___f_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___f_2580_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2581_ = 1;
v___x_2582_ = l_Lake_instDataKindUnit;
v___f_2583_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__0, &l_Lake_Package_barrelFacetConfig___closed__0_once, _init_l_Lake_Package_barrelFacetConfig___closed__0);
v___x_2584_ = l_Lake_Package_keyword;
v___x_2585_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
lean_ctor_set(v___x_2585_, 1, v___f_2583_);
lean_ctor_set(v___x_2585_, 2, v___x_2582_);
lean_ctor_set(v___x_2585_, 3, v___f_2580_);
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*4, v___x_2581_);
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*4 + 1, v___x_2581_);
return v___x_2585_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig(void){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__1, &l_Lake_Package_barrelFacetConfig___closed__1_once, _init_l_Lake_Package_barrelFacetConfig___closed__1);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object* v_pkg_2587_, lean_object* v___x_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
uint8_t v_r_2597_; lean_object* v___y_2598_; lean_object* v_a_2602_; lean_object* v___x_2618_; 
lean_inc_ref(v_pkg_2587_);
v___x_2618_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_pkg_2587_, v___y_2594_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v_a_2620_; lean_object* v_dir_2621_; lean_object* v_buildArchive_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
v_a_2620_ = lean_ctor_get(v___x_2618_, 1);
lean_inc(v_a_2620_);
lean_dec_ref(v___x_2618_);
v_dir_2621_ = lean_ctor_get(v_pkg_2587_, 4);
v_buildArchive_2622_ = lean_ctor_get(v_pkg_2587_, 20);
v___x_2623_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_2621_);
v___x_2624_ = l_Lake_joinRelative(v_dir_2621_, v___x_2623_);
lean_inc_ref(v_buildArchive_2622_);
v___x_2625_ = l_Lake_joinRelative(v___x_2624_, v_buildArchive_2622_);
v___x_2626_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2587_, v_a_2619_, v___x_2625_, v___x_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v_a_2620_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; uint8_t v___x_2628_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 1);
lean_inc(v_a_2627_);
lean_dec_ref(v___x_2626_);
v___x_2628_ = 1;
v_r_2597_ = v___x_2628_;
v___y_2598_ = v_a_2627_;
goto v___jp_2596_;
}
else
{
lean_object* v_a_2629_; 
v_a_2629_ = lean_ctor_get(v___x_2626_, 1);
lean_inc(v_a_2629_);
lean_dec_ref(v___x_2626_);
v_a_2602_ = v_a_2629_;
goto v___jp_2601_;
}
}
else
{
lean_object* v_a_2630_; 
lean_dec_ref(v_pkg_2587_);
v_a_2630_ = lean_ctor_get(v___x_2618_, 1);
lean_inc(v_a_2630_);
lean_dec_ref(v___x_2618_);
v_a_2602_ = v_a_2630_;
goto v___jp_2601_;
}
v___jp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = lean_box(v_r_2597_);
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_ctor_set(v___x_2600_, 1, v___y_2598_);
return v___x_2600_;
}
v___jp_2601_:
{
lean_object* v_log_2603_; uint8_t v_action_2604_; uint8_t v_wantsRebuild_2605_; lean_object* v_trace_2606_; lean_object* v_buildTime_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2617_; 
v_log_2603_ = lean_ctor_get(v_a_2602_, 0);
v_action_2604_ = lean_ctor_get_uint8(v_a_2602_, sizeof(void*)*3);
v_wantsRebuild_2605_ = lean_ctor_get_uint8(v_a_2602_, sizeof(void*)*3 + 1);
v_trace_2606_ = lean_ctor_get(v_a_2602_, 1);
v_buildTime_2607_ = lean_ctor_get(v_a_2602_, 2);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_a_2602_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2609_ = v_a_2602_;
v_isShared_2610_ = v_isSharedCheck_2617_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_buildTime_2607_);
lean_inc(v_trace_2606_);
lean_inc(v_log_2603_);
lean_dec(v_a_2602_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2617_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
uint8_t v___x_2611_; uint8_t v___x_2612_; lean_object* v___x_2614_; 
v___x_2611_ = 4;
v___x_2612_ = l_Lake_JobAction_merge(v_action_2604_, v___x_2611_);
if (v_isShared_2610_ == 0)
{
v___x_2614_ = v___x_2609_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_log_2603_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_trace_2606_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v_buildTime_2607_);
lean_ctor_set_uint8(v_reuseFailAlloc_2616_, sizeof(void*)*3 + 1, v_wantsRebuild_2605_);
v___x_2614_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
uint8_t v___x_2615_; 
lean_ctor_set_uint8(v___x_2614_, sizeof(void*)*3, v___x_2612_);
v___x_2615_ = 0;
v_r_2597_ = v___x_2615_;
v___y_2598_ = v___x_2614_;
goto v___jp_2596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object* v_pkg_2631_, lean_object* v___x_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(v_pkg_2631_, v___x_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v___x_2632_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object* v___x_2641_, lean_object* v___x_2642_, lean_object* v___x_2643_, lean_object* v___x_2644_, lean_object* v_pkg_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v___f_2653_; lean_object* v___x_2654_; lean_object* v___f_2655_; lean_object* v___x_2656_; 
lean_inc_ref(v_pkg_2645_);
v___f_2653_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2653_, 0, v_pkg_2645_);
lean_closure_set(v___f_2653_, 1, v___x_2641_);
v___x_2654_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2642_);
v___f_2655_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2655_, 0, v___x_2642_);
lean_closure_set(v___f_2655_, 1, v___f_2653_);
lean_closure_set(v___f_2655_, 2, v___x_2643_);
lean_closure_set(v___f_2655_, 3, v___x_2654_);
v___x_2656_ = l_Lake_ensureJob___redArg(v___x_2642_, v___f_2655_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2689_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
v_a_2658_ = lean_ctor_get(v___x_2656_, 1);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2660_ = v___x_2656_;
v_isShared_2661_ = v_isSharedCheck_2689_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_inc(v_a_2657_);
lean_dec(v___x_2656_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2689_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v_task_2662_; lean_object* v_kind_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2687_; 
v_task_2662_ = lean_ctor_get(v_a_2657_, 0);
v_kind_2663_ = lean_ctor_get(v_a_2657_, 1);
v_isSharedCheck_2687_ = !lean_is_exclusive(v_a_2657_);
if (v_isSharedCheck_2687_ == 0)
{
lean_object* v_unused_2688_; 
v_unused_2688_ = lean_ctor_get(v_a_2657_, 2);
lean_dec(v_unused_2688_);
v___x_2665_ = v_a_2657_;
v_isShared_2666_ = v_isSharedCheck_2687_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_kind_2663_);
lean_inc(v_task_2662_);
lean_dec(v_a_2657_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2687_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v_registeredJobs_2667_; lean_object* v___x_2668_; lean_object* v_baseName_2669_; uint8_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v_job_2678_; 
v_registeredJobs_2667_ = lean_ctor_get(v___y_2650_, 3);
v___x_2668_ = lean_st_ref_take(v_registeredJobs_2667_);
v_baseName_2669_ = lean_ctor_get(v_pkg_2645_, 1);
lean_inc(v_baseName_2669_);
lean_dec_ref(v_pkg_2645_);
v___x_2670_ = 1;
v___x_2671_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2669_, v___x_2670_);
v___x_2672_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2673_ = lean_string_append(v___x_2671_, v___x_2672_);
v___x_2674_ = l_Lake_Name_eraseHead(v___x_2644_);
v___x_2675_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2674_, v___x_2670_);
v___x_2676_ = lean_string_append(v___x_2673_, v___x_2675_);
lean_dec_ref(v___x_2675_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 2, v___x_2676_);
v_job_2678_ = v___x_2665_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_task_2662_);
lean_ctor_set(v_reuseFailAlloc_2686_, 1, v_kind_2663_);
lean_ctor_set(v_reuseFailAlloc_2686_, 2, v___x_2676_);
v_job_2678_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
lean_ctor_set_uint8(v_job_2678_, sizeof(void*)*3, v___x_2670_);
lean_inc_ref(v_job_2678_);
v___x_2679_ = l_Lake_Job_toOpaque___redArg(v_job_2678_);
v___x_2680_ = lean_array_push(v___x_2668_, v___x_2679_);
v___x_2681_ = lean_st_ref_set(v_registeredJobs_2667_, v___x_2680_);
v___x_2682_ = l_Lake_Job_renew___redArg(v_job_2678_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2682_);
v___x_2684_ = v___x_2660_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
lean_ctor_set(v_reuseFailAlloc_2685_, 1, v_a_2658_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_2645_);
lean_dec(v___x_2644_);
return v___x_2656_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_2690_, lean_object* v___x_2691_, lean_object* v___x_2692_, lean_object* v___x_2693_, lean_object* v_pkg_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(v___x_2690_, v___x_2691_, v___x_2692_, v___x_2693_, v_pkg_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec(v___y_2696_);
return v_res_2702_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___f_2709_; 
v___x_2705_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_2706_ = lean_unsigned_to_nat(0u);
v___x_2707_ = l_Lake_instDataKindBool;
v___x_2708_ = ((lean_object*)(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0));
v___f_2709_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2709_, 0, v___x_2708_);
lean_closure_set(v___f_2709_, 1, v___x_2707_);
lean_closure_set(v___f_2709_, 2, v___x_2706_);
lean_closure_set(v___f_2709_, 3, v___x_2705_);
return v___f_2709_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2710_; uint8_t v___x_2711_; lean_object* v___x_2712_; lean_object* v___f_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___f_2710_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_2711_ = 1;
v___x_2712_ = l_Lake_instDataKindBool;
v___f_2713_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__1, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1);
v___x_2714_ = l_Lake_Package_keyword;
v___x_2715_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
lean_ctor_set(v___x_2715_, 1, v___f_2713_);
lean_ctor_set(v___x_2715_, 2, v___x_2712_);
lean_ctor_set(v___x_2715_, 3, v___f_2710_);
lean_ctor_set_uint8(v___x_2715_, sizeof(void*)*4, v___x_2711_);
lean_ctor_set_uint8(v___x_2715_, sizeof(void*)*4 + 1, v___x_2711_);
return v___x_2715_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__2, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* v_baseName_2718_, lean_object* v___x_2719_, uint8_t v_success_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_a_2729_; lean_object* v_a_2730_; 
if (v_success_2720_ == 0)
{
lean_object* v_toBuildConfig_2750_; uint8_t v_verbosity_2751_; uint8_t v___x_2752_; uint8_t v___x_2753_; 
v_toBuildConfig_2750_ = lean_ctor_get(v___y_2725_, 0);
v_verbosity_2751_ = lean_ctor_get_uint8(v_toBuildConfig_2750_, sizeof(void*)*3 + 3);
v___x_2752_ = 2;
v___x_2753_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2751_, v___x_2752_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; 
lean_dec(v___x_2719_);
lean_dec(v_baseName_2718_);
v___x_2754_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2729_ = v___x_2754_;
v_a_2730_ = v___y_2726_;
goto v___jp_2728_;
}
else
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2755_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2756_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2718_, v___x_2753_);
v___x_2757_ = lean_string_append(v___x_2755_, v___x_2756_);
lean_dec_ref(v___x_2756_);
v___x_2758_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2759_ = lean_string_append(v___x_2757_, v___x_2758_);
v___x_2760_ = l_Lake_Name_eraseHead(v___x_2719_);
v___x_2761_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2760_, v___x_2753_);
v___x_2762_ = lean_string_append(v___x_2759_, v___x_2761_);
lean_dec_ref(v___x_2761_);
v___x_2763_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2764_ = lean_string_append(v___x_2762_, v___x_2763_);
v_a_2729_ = v___x_2764_;
v_a_2730_ = v___y_2726_;
goto v___jp_2728_;
}
}
else
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
lean_dec(v___x_2719_);
lean_dec(v_baseName_2718_);
v___x_2765_ = lean_box(0);
v___x_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
lean_ctor_set(v___x_2766_, 1, v___y_2726_);
return v___x_2766_;
}
v___jp_2728_:
{
lean_object* v_log_2731_; uint8_t v_action_2732_; uint8_t v_wantsRebuild_2733_; lean_object* v_trace_2734_; lean_object* v_buildTime_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2749_; 
v_log_2731_ = lean_ctor_get(v_a_2730_, 0);
v_action_2732_ = lean_ctor_get_uint8(v_a_2730_, sizeof(void*)*3);
v_wantsRebuild_2733_ = lean_ctor_get_uint8(v_a_2730_, sizeof(void*)*3 + 1);
v_trace_2734_ = lean_ctor_get(v_a_2730_, 1);
v_buildTime_2735_ = lean_ctor_get(v_a_2730_, 2);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_a_2730_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2737_ = v_a_2730_;
v_isShared_2738_ = v_isSharedCheck_2749_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_buildTime_2735_);
lean_inc(v_trace_2734_);
lean_inc(v_log_2731_);
lean_dec(v_a_2730_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2749_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2746_; 
v___x_2739_ = ((lean_object*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0));
v___x_2740_ = lean_string_append(v___x_2739_, v_a_2729_);
lean_dec_ref(v_a_2729_);
v___x_2741_ = 3;
v___x_2742_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set_uint8(v___x_2742_, sizeof(void*)*1, v___x_2741_);
v___x_2743_ = lean_array_get_size(v_log_2731_);
v___x_2744_ = lean_array_push(v_log_2731_, v___x_2742_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2744_);
v___x_2746_ = v___x_2737_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v_trace_2734_);
lean_ctor_set(v_reuseFailAlloc_2748_, 2, v_buildTime_2735_);
lean_ctor_set_uint8(v_reuseFailAlloc_2748_, sizeof(void*)*3, v_action_2732_);
lean_ctor_set_uint8(v_reuseFailAlloc_2748_, sizeof(void*)*3 + 1, v_wantsRebuild_2733_);
v___x_2746_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_object* v___x_2747_; 
v___x_2747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2743_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
return v___x_2747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object* v_baseName_2767_, lean_object* v___x_2768_, lean_object* v_success_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
uint8_t v_success_boxed_2777_; lean_object* v_res_2778_; 
v_success_boxed_2777_ = lean_unbox(v_success_2769_);
v_res_2778_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(v_baseName_2767_, v___x_2768_, v_success_boxed_2777_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* v___x_2779_, lean_object* v___x_2780_, lean_object* v___x_2781_, lean_object* v_pkg_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v_baseName_2790_; lean_object* v_keyName_2791_; lean_object* v___f_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___f_2796_; lean_object* v___x_2797_; 
v_baseName_2790_ = lean_ctor_get(v_pkg_2782_, 1);
lean_inc_n(v_baseName_2790_, 2);
v_keyName_2791_ = lean_ctor_get(v_pkg_2782_, 2);
lean_inc(v___x_2779_);
v___f_2792_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2792_, 0, v_baseName_2790_);
lean_closure_set(v___f_2792_, 1, v___x_2779_);
lean_inc(v_keyName_2791_);
v___x_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2793_, 0, v_keyName_2791_);
v___x_2794_ = l_Lake_Package_keyword;
v___x_2795_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
lean_ctor_set(v___x_2795_, 2, v_pkg_2782_);
lean_ctor_set(v___x_2795_, 3, v___x_2779_);
lean_inc(v___x_2780_);
v___f_2796_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2796_, 0, v___x_2795_);
lean_closure_set(v___f_2796_, 1, v___x_2780_);
lean_closure_set(v___f_2796_, 2, v___f_2792_);
v___x_2797_ = l_Lake_ensureJob___redArg(v___x_2780_, v___f_2796_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2830_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
v_a_2799_ = lean_ctor_get(v___x_2797_, 1);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2801_ = v___x_2797_;
v_isShared_2802_ = v_isSharedCheck_2830_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_inc(v_a_2798_);
lean_dec(v___x_2797_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2830_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v_task_2803_; lean_object* v_kind_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2828_; 
v_task_2803_ = lean_ctor_get(v_a_2798_, 0);
v_kind_2804_ = lean_ctor_get(v_a_2798_, 1);
v_isSharedCheck_2828_ = !lean_is_exclusive(v_a_2798_);
if (v_isSharedCheck_2828_ == 0)
{
lean_object* v_unused_2829_; 
v_unused_2829_ = lean_ctor_get(v_a_2798_, 2);
lean_dec(v_unused_2829_);
v___x_2806_ = v_a_2798_;
v_isShared_2807_ = v_isSharedCheck_2828_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_kind_2804_);
lean_inc(v_task_2803_);
lean_dec(v_a_2798_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2828_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v_registeredJobs_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; lean_object* v_job_2819_; 
v_registeredJobs_2808_ = lean_ctor_get(v___y_2787_, 3);
v___x_2809_ = lean_st_ref_take(v_registeredJobs_2808_);
v___x_2810_ = 1;
v___x_2811_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2790_, v___x_2810_);
v___x_2812_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2813_ = lean_string_append(v___x_2811_, v___x_2812_);
v___x_2814_ = l_Lake_Name_eraseHead(v___x_2781_);
v___x_2815_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2814_, v___x_2810_);
v___x_2816_ = lean_string_append(v___x_2813_, v___x_2815_);
lean_dec_ref(v___x_2815_);
v___x_2817_ = 0;
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 2, v___x_2816_);
v_job_2819_ = v___x_2806_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_task_2803_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v_kind_2804_);
lean_ctor_set(v_reuseFailAlloc_2827_, 2, v___x_2816_);
v_job_2819_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2825_; 
lean_ctor_set_uint8(v_job_2819_, sizeof(void*)*3, v___x_2817_);
lean_inc_ref(v_job_2819_);
v___x_2820_ = l_Lake_Job_toOpaque___redArg(v_job_2819_);
v___x_2821_ = lean_array_push(v___x_2809_, v___x_2820_);
v___x_2822_ = lean_st_ref_set(v_registeredJobs_2808_, v___x_2821_);
v___x_2823_ = l_Lake_Job_renew___redArg(v_job_2819_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v___x_2823_);
v___x_2825_ = v___x_2801_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_a_2799_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2790_);
lean_dec(v___x_2781_);
return v___x_2797_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_2831_, lean_object* v___x_2832_, lean_object* v___x_2833_, lean_object* v_pkg_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(v___x_2831_, v___x_2832_, v___x_2833_, v_pkg_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec(v___y_2836_);
return v_res_2842_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___f_2846_; 
v___x_2843_ = l_Lake_Package_gitHubReleaseFacet;
v___x_2844_ = l_Lake_instDataKindUnit;
v___x_2845_ = l_Lake_Package_optGitHubReleaseFacet;
v___f_2846_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2846_, 0, v___x_2845_);
lean_closure_set(v___f_2846_, 1, v___x_2844_);
lean_closure_set(v___f_2846_, 2, v___x_2843_);
return v___f_2846_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2847_; uint8_t v___x_2848_; lean_object* v___x_2849_; lean_object* v___f_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___f_2847_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2848_ = 1;
v___x_2849_ = l_Lake_instDataKindUnit;
v___f_2850_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__0, &l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0);
v___x_2851_ = l_Lake_Package_keyword;
v___x_2852_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
lean_ctor_set(v___x_2852_, 1, v___f_2850_);
lean_ctor_set(v___x_2852_, 2, v___x_2849_);
lean_ctor_set(v___x_2852_, 3, v___f_2847_);
lean_ctor_set_uint8(v___x_2852_, sizeof(void*)*4, v___x_2848_);
lean_ctor_set_uint8(v___x_2852_, sizeof(void*)*4 + 1, v___x_2848_);
return v___x_2852_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__1, &l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* v_build_2854_, uint8_t v_x_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_log_2863_; uint8_t v_action_2864_; uint8_t v_wantsRebuild_2865_; lean_object* v_buildTime_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2875_; 
v_log_2863_ = lean_ctor_get(v___y_2861_, 0);
v_action_2864_ = lean_ctor_get_uint8(v___y_2861_, sizeof(void*)*3);
v_wantsRebuild_2865_ = lean_ctor_get_uint8(v___y_2861_, sizeof(void*)*3 + 1);
v_buildTime_2866_ = lean_ctor_get(v___y_2861_, 2);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___y_2861_);
if (v_isSharedCheck_2875_ == 0)
{
lean_object* v_unused_2876_; 
v_unused_2876_ = lean_ctor_get(v___y_2861_, 1);
lean_dec(v_unused_2876_);
v___x_2868_ = v___y_2861_;
v_isShared_2869_ = v_isSharedCheck_2875_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_buildTime_2866_);
lean_inc(v_log_2863_);
lean_dec(v___y_2861_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2875_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2872_; 
v___x_2870_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 1, v___x_2870_);
v___x_2872_ = v___x_2868_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_log_2863_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2874_, 2, v_buildTime_2866_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, sizeof(void*)*3, v_action_2864_);
lean_ctor_set_uint8(v_reuseFailAlloc_2874_, sizeof(void*)*3 + 1, v_wantsRebuild_2865_);
v___x_2872_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2873_; 
lean_inc_ref(v___y_2860_);
lean_inc(v___y_2859_);
lean_inc(v___y_2858_);
lean_inc(v___y_2857_);
v___x_2873_ = lean_apply_7(v_build_2854_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___x_2872_, lean_box(0));
return v___x_2873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* v_build_2877_, lean_object* v_x_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
uint8_t v_x_1923__boxed_2886_; lean_object* v_res_2887_; 
v_x_1923__boxed_2886_ = lean_unbox(v_x_2878_);
v_res_2887_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(v_build_2877_, v_x_1923__boxed_2886_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec(v___y_2880_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* v_self_2888_, lean_object* v_build_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v_wsIdx_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v_wsIdx_2897_ = lean_ctor_get(v_self_2888_, 0);
v___x_2898_ = lean_unsigned_to_nat(0u);
v___x_2899_ = lean_nat_dec_eq(v_wsIdx_2897_, v___x_2898_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; 
lean_inc_ref(v_a_2890_);
v___x_2900_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_2888_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2913_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
v_a_2902_ = lean_ctor_get(v___x_2900_, 1);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2904_ = v___x_2900_;
v_isShared_2905_ = v_isSharedCheck_2913_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_inc(v_a_2901_);
lean_dec(v___x_2900_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2913_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___f_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___f_2906_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2906_, 0, v_build_2889_);
v___x_2907_ = lean_box(0);
v___x_2908_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2909_ = l_Lake_Job_bindM___redArg(v___x_2907_, v_a_2901_, v___f_2906_, v___x_2898_, v___x_2899_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v___x_2908_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 0, v___x_2909_);
v___x_2911_ = v___x_2904_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_a_2902_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec_ref(v_a_2890_);
lean_dec_ref(v_build_2889_);
v_a_2914_ = lean_ctor_get(v___x_2900_, 0);
v_a_2915_ = lean_ctor_get(v___x_2900_, 1);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2900_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_inc(v_a_2914_);
lean_dec(v___x_2900_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2914_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
else
{
uint8_t v___x_2923_; uint8_t v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
lean_dec_ref(v_self_2888_);
v___x_2923_ = 0;
v___x_2924_ = 0;
v___x_2925_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2926_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2926_, 0, v_a_2895_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
lean_ctor_set(v___x_2926_, 2, v___x_2898_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*3, v___x_2923_);
lean_ctor_set_uint8(v___x_2926_, sizeof(void*)*3 + 1, v___x_2924_);
lean_inc_ref(v_a_2894_);
lean_inc(v_a_2893_);
lean_inc(v_a_2892_);
lean_inc(v_a_2891_);
v___x_2927_ = lean_apply_7(v_build_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v___x_2926_, lean_box(0));
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2937_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 1);
v_a_2929_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2931_ = v___x_2927_;
v_isShared_2932_ = v_isSharedCheck_2937_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2928_);
lean_inc(v_a_2929_);
lean_dec(v___x_2927_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2937_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v_log_2933_; lean_object* v___x_2935_; 
v_log_2933_ = lean_ctor_get(v_a_2928_, 0);
lean_inc_ref(v_log_2933_);
lean_dec(v_a_2928_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 1, v_log_2933_);
v___x_2935_ = v___x_2931_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2929_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_log_2933_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2947_; 
v_a_2938_ = lean_ctor_get(v___x_2927_, 1);
v_a_2939_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2941_ = v___x_2927_;
v_isShared_2942_ = v_isSharedCheck_2947_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2938_);
lean_inc(v_a_2939_);
lean_dec(v___x_2927_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2947_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v_log_2943_; lean_object* v___x_2945_; 
v_log_2943_ = lean_ctor_get(v_a_2938_, 0);
lean_inc_ref(v_log_2943_);
lean_dec(v_a_2938_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v_log_2943_);
v___x_2945_ = v___x_2941_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2939_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_log_2943_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___boxed(lean_object* v_self_2948_, lean_object* v_build_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_2948_, v_build_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
lean_dec_ref(v_a_2954_);
lean_dec(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec(v_a_2951_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* v_00_u03b1_2958_, lean_object* v_self_2959_, lean_object* v_build_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_2959_, v_build_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___boxed(lean_object* v_00_u03b1_2969_, lean_object* v_self_2970_, lean_object* v_build_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Lake_Package_afterBuildCacheAsync(v_00_u03b1_2969_, v_self_2970_, v_build_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
lean_dec_ref(v_a_2976_);
lean_dec(v_a_2975_);
lean_dec(v_a_2974_);
lean_dec(v_a_2973_);
return v_res_2979_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* v_build_2980_, uint8_t v_x_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v_log_2989_; uint8_t v_action_2990_; uint8_t v_wantsRebuild_2991_; lean_object* v_buildTime_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3001_; 
v_log_2989_ = lean_ctor_get(v___y_2987_, 0);
v_action_2990_ = lean_ctor_get_uint8(v___y_2987_, sizeof(void*)*3);
v_wantsRebuild_2991_ = lean_ctor_get_uint8(v___y_2987_, sizeof(void*)*3 + 1);
v_buildTime_2992_ = lean_ctor_get(v___y_2987_, 2);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___y_2987_);
if (v_isSharedCheck_3001_ == 0)
{
lean_object* v_unused_3002_; 
v_unused_3002_ = lean_ctor_get(v___y_2987_, 1);
lean_dec(v_unused_3002_);
v___x_2994_ = v___y_2987_;
v_isShared_2995_ = v_isSharedCheck_3001_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_buildTime_2992_);
lean_inc(v_log_2989_);
lean_dec(v___y_2987_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3001_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; lean_object* v___x_2998_; 
v___x_2996_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 1, v___x_2996_);
v___x_2998_ = v___x_2994_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_log_2989_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v___x_2996_);
lean_ctor_set(v_reuseFailAlloc_3000_, 2, v_buildTime_2992_);
lean_ctor_set_uint8(v_reuseFailAlloc_3000_, sizeof(void*)*3, v_action_2990_);
lean_ctor_set_uint8(v_reuseFailAlloc_3000_, sizeof(void*)*3 + 1, v_wantsRebuild_2991_);
v___x_2998_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_2999_; 
lean_inc_ref(v___y_2986_);
lean_inc(v___y_2985_);
lean_inc(v___y_2984_);
lean_inc(v___y_2983_);
v___x_2999_ = lean_apply_7(v_build_2980_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___x_2998_, lean_box(0));
return v___x_2999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* v_build_3003_, lean_object* v_x_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
uint8_t v_x_1946__boxed_3012_; lean_object* v_res_3013_; 
v_x_1946__boxed_3012_ = lean_unbox(v_x_3004_);
v_res_3013_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(v_build_3003_, v_x_1946__boxed_3012_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec(v___y_3006_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* v_self_3014_, lean_object* v_build_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v_wsIdx_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; 
v_wsIdx_3023_ = lean_ctor_get(v_self_3014_, 0);
v___x_3024_ = lean_unsigned_to_nat(0u);
v___x_3025_ = lean_nat_dec_eq(v_wsIdx_3023_, v___x_3024_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; 
lean_inc_ref(v_a_3016_);
v___x_3026_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3014_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3039_; 
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
v_a_3028_ = lean_ctor_get(v___x_3026_, 1);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3030_ = v___x_3026_;
v_isShared_3031_ = v_isSharedCheck_3039_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_inc(v_a_3027_);
lean_dec(v___x_3026_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3039_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___f_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3037_; 
v___f_3032_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3032_, 0, v_build_3015_);
v___x_3033_ = lean_box(0);
v___x_3034_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3035_ = l_Lake_Job_mapM___redArg(v___x_3033_, v_a_3027_, v___f_3032_, v___x_3024_, v___x_3025_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v___x_3034_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 0, v___x_3035_);
v___x_3037_ = v___x_3030_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v_a_3028_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec_ref(v_a_3016_);
lean_dec_ref(v_build_3015_);
v_a_3040_ = lean_ctor_get(v___x_3026_, 0);
v_a_3041_ = lean_ctor_get(v___x_3026_, 1);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3026_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_inc(v_a_3040_);
lean_dec(v___x_3026_);
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
else
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
lean_dec_ref(v_self_3014_);
v___x_3049_ = lean_box(0);
v___x_3050_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_3051_ = l_Lake_Job_async___redArg(v___x_3049_, v_build_3015_, v___x_3024_, v___x_3050_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
v___x_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
lean_ctor_set(v___x_3052_, 1, v_a_3021_);
return v___x_3052_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___boxed(lean_object* v_self_3053_, lean_object* v_build_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3053_, v_build_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_);
lean_dec_ref(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec(v_a_3057_);
lean_dec(v_a_3056_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* v_00_u03b1_3063_, lean_object* v_self_3064_, lean_object* v_build_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3064_, v_build_3065_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v_a_3070_, v_a_3071_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___boxed(lean_object* v_00_u03b1_3074_, lean_object* v_self_3075_, lean_object* v_build_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_Lake_Package_afterBuildCacheSync(v_00_u03b1_3074_, v_self_3075_, v_build_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_);
lean_dec_ref(v_a_3081_);
lean_dec(v_a_3080_);
lean_dec(v_a_3079_);
lean_dec(v_a_3078_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(lean_object* v_k_3085_, lean_object* v_v_3086_, lean_object* v_t_3087_){
_start:
{
if (lean_obj_tag(v_t_3087_) == 0)
{
lean_object* v_size_3088_; lean_object* v_k_3089_; lean_object* v_v_3090_; lean_object* v_l_3091_; lean_object* v_r_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3372_; 
v_size_3088_ = lean_ctor_get(v_t_3087_, 0);
v_k_3089_ = lean_ctor_get(v_t_3087_, 1);
v_v_3090_ = lean_ctor_get(v_t_3087_, 2);
v_l_3091_ = lean_ctor_get(v_t_3087_, 3);
v_r_3092_ = lean_ctor_get(v_t_3087_, 4);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_t_3087_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3094_ = v_t_3087_;
v_isShared_3095_ = v_isSharedCheck_3372_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_r_3092_);
lean_inc(v_l_3091_);
lean_inc(v_v_3090_);
lean_inc(v_k_3089_);
lean_inc(v_size_3088_);
lean_dec(v_t_3087_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3372_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
uint8_t v___x_3096_; 
v___x_3096_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3085_, v_k_3089_);
switch(v___x_3096_)
{
case 0:
{
lean_object* v_impl_3097_; lean_object* v___x_3098_; 
lean_dec(v_size_3088_);
v_impl_3097_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3085_, v_v_3086_, v_l_3091_);
v___x_3098_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3092_) == 0)
{
lean_object* v_size_3099_; lean_object* v_size_3100_; lean_object* v_k_3101_; lean_object* v_v_3102_; lean_object* v_l_3103_; lean_object* v_r_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; uint8_t v___x_3107_; 
v_size_3099_ = lean_ctor_get(v_r_3092_, 0);
v_size_3100_ = lean_ctor_get(v_impl_3097_, 0);
lean_inc(v_size_3100_);
v_k_3101_ = lean_ctor_get(v_impl_3097_, 1);
lean_inc(v_k_3101_);
v_v_3102_ = lean_ctor_get(v_impl_3097_, 2);
lean_inc(v_v_3102_);
v_l_3103_ = lean_ctor_get(v_impl_3097_, 3);
lean_inc(v_l_3103_);
v_r_3104_ = lean_ctor_get(v_impl_3097_, 4);
lean_inc(v_r_3104_);
v___x_3105_ = lean_unsigned_to_nat(3u);
v___x_3106_ = lean_nat_mul(v___x_3105_, v_size_3099_);
v___x_3107_ = lean_nat_dec_lt(v___x_3106_, v_size_3100_);
lean_dec(v___x_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3111_; 
lean_dec(v_r_3104_);
lean_dec(v_l_3103_);
lean_dec(v_v_3102_);
lean_dec(v_k_3101_);
v___x_3108_ = lean_nat_add(v___x_3098_, v_size_3100_);
lean_dec(v_size_3100_);
v___x_3109_ = lean_nat_add(v___x_3108_, v_size_3099_);
lean_dec(v___x_3108_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 3, v_impl_3097_);
lean_ctor_set(v___x_3094_, 0, v___x_3109_);
v___x_3111_ = v___x_3094_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3109_);
lean_ctor_set(v_reuseFailAlloc_3112_, 1, v_k_3089_);
lean_ctor_set(v_reuseFailAlloc_3112_, 2, v_v_3090_);
lean_ctor_set(v_reuseFailAlloc_3112_, 3, v_impl_3097_);
lean_ctor_set(v_reuseFailAlloc_3112_, 4, v_r_3092_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
else
{
lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3178_; 
v_isSharedCheck_3178_ = !lean_is_exclusive(v_impl_3097_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; lean_object* v_unused_3180_; lean_object* v_unused_3181_; lean_object* v_unused_3182_; lean_object* v_unused_3183_; 
v_unused_3179_ = lean_ctor_get(v_impl_3097_, 4);
lean_dec(v_unused_3179_);
v_unused_3180_ = lean_ctor_get(v_impl_3097_, 3);
lean_dec(v_unused_3180_);
v_unused_3181_ = lean_ctor_get(v_impl_3097_, 2);
lean_dec(v_unused_3181_);
v_unused_3182_ = lean_ctor_get(v_impl_3097_, 1);
lean_dec(v_unused_3182_);
v_unused_3183_ = lean_ctor_get(v_impl_3097_, 0);
lean_dec(v_unused_3183_);
v___x_3114_ = v_impl_3097_;
v_isShared_3115_ = v_isSharedCheck_3178_;
goto v_resetjp_3113_;
}
else
{
lean_dec(v_impl_3097_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3178_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v_size_3116_; lean_object* v_size_3117_; lean_object* v_k_3118_; lean_object* v_v_3119_; lean_object* v_l_3120_; lean_object* v_r_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; uint8_t v___x_3124_; 
v_size_3116_ = lean_ctor_get(v_l_3103_, 0);
v_size_3117_ = lean_ctor_get(v_r_3104_, 0);
v_k_3118_ = lean_ctor_get(v_r_3104_, 1);
v_v_3119_ = lean_ctor_get(v_r_3104_, 2);
v_l_3120_ = lean_ctor_get(v_r_3104_, 3);
v_r_3121_ = lean_ctor_get(v_r_3104_, 4);
v___x_3122_ = lean_unsigned_to_nat(2u);
v___x_3123_ = lean_nat_mul(v___x_3122_, v_size_3116_);
v___x_3124_ = lean_nat_dec_lt(v_size_3117_, v___x_3123_);
lean_dec(v___x_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3153_; 
lean_inc(v_r_3121_);
lean_inc(v_l_3120_);
lean_inc(v_v_3119_);
lean_inc(v_k_3118_);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_r_3104_);
if (v_isSharedCheck_3153_ == 0)
{
lean_object* v_unused_3154_; lean_object* v_unused_3155_; lean_object* v_unused_3156_; lean_object* v_unused_3157_; lean_object* v_unused_3158_; 
v_unused_3154_ = lean_ctor_get(v_r_3104_, 4);
lean_dec(v_unused_3154_);
v_unused_3155_ = lean_ctor_get(v_r_3104_, 3);
lean_dec(v_unused_3155_);
v_unused_3156_ = lean_ctor_get(v_r_3104_, 2);
lean_dec(v_unused_3156_);
v_unused_3157_ = lean_ctor_get(v_r_3104_, 1);
lean_dec(v_unused_3157_);
v_unused_3158_ = lean_ctor_get(v_r_3104_, 0);
lean_dec(v_unused_3158_);
v___x_3126_ = v_r_3104_;
v_isShared_3127_ = v_isSharedCheck_3153_;
goto v_resetjp_3125_;
}
else
{
lean_dec(v_r_3104_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3153_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___x_3141_; lean_object* v___y_3143_; 
v___x_3128_ = lean_nat_add(v___x_3098_, v_size_3100_);
lean_dec(v_size_3100_);
v___x_3129_ = lean_nat_add(v___x_3128_, v_size_3099_);
lean_dec(v___x_3128_);
v___x_3141_ = lean_nat_add(v___x_3098_, v_size_3116_);
if (lean_obj_tag(v_l_3120_) == 0)
{
lean_object* v_size_3151_; 
v_size_3151_ = lean_ctor_get(v_l_3120_, 0);
lean_inc(v_size_3151_);
v___y_3143_ = v_size_3151_;
goto v___jp_3142_;
}
else
{
lean_object* v___x_3152_; 
v___x_3152_ = lean_unsigned_to_nat(0u);
v___y_3143_ = v___x_3152_;
goto v___jp_3142_;
}
v___jp_3130_:
{
lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3134_ = lean_nat_add(v___y_3132_, v___y_3133_);
lean_dec(v___y_3133_);
lean_dec(v___y_3132_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 4, v_r_3092_);
lean_ctor_set(v___x_3126_, 3, v_r_3121_);
lean_ctor_set(v___x_3126_, 2, v_v_3090_);
lean_ctor_set(v___x_3126_, 1, v_k_3089_);
lean_ctor_set(v___x_3126_, 0, v___x_3134_);
v___x_3136_ = v___x_3126_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3140_, 1, v_k_3089_);
lean_ctor_set(v_reuseFailAlloc_3140_, 2, v_v_3090_);
lean_ctor_set(v_reuseFailAlloc_3140_, 3, v_r_3121_);
lean_ctor_set(v_reuseFailAlloc_3140_, 4, v_r_3092_);
v___x_3136_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3138_; 
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 4, v___x_3136_);
lean_ctor_set(v___x_3114_, 3, v___y_3131_);
lean_ctor_set(v___x_3114_, 2, v_v_3119_);
lean_ctor_set(v___x_3114_, 1, v_k_3118_);
lean_ctor_set(v___x_3114_, 0, v___x_3129_);
v___x_3138_ = v___x_3114_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3129_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v_k_3118_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v_v_3119_);
lean_ctor_set(v_reuseFailAlloc_3139_, 3, v___y_3131_);
lean_ctor_set(v_reuseFailAlloc_3139_, 4, v___x_3136_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
v___jp_3142_:
{
lean_object* v___x_3144_; lean_object* v___x_3146_; 
v___x_3144_ = lean_nat_add(v___x_3141_, v___y_3143_);
lean_dec(v___y_3143_);
lean_dec(v___x_3141_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 4, v_l_3120_);
lean_ctor_set(v___x_3094_, 3, v_l_3103_);
lean_ctor_set(v___x_3094_, 2, v_v_3102_);
lean_ctor_set(v___x_3094_, 1, v_k_3101_);
lean_ctor_set(v___x_3094_, 0, v___x_3144_);
v___x_3146_ = v___x_3094_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3144_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v_k_3101_);
lean_ctor_set(v_reuseFailAlloc_3150_, 2, v_v_3102_);
lean_ctor_set(v_reuseFailAlloc_3150_, 3, v_l_3103_);
lean_ctor_set(v_reuseFailAlloc_3150_, 4, v_l_3120_);
v___x_3146_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_nat_add(v___x_3098_, v_size_3099_);
if (lean_obj_tag(v_r_3121_) == 0)
{
lean_object* v_size_3148_; 
v_size_3148_ = lean_ctor_get(v_r_3121_, 0);
lean_inc(v_size_3148_);
v___y_3131_ = v___x_3146_;
v___y_3132_ = v___x_3147_;
v___y_3133_ = v_size_3148_;
goto v___jp_3130_;
}
else
{
lean_object* v___x_3149_; 
v___x_3149_ = lean_unsigned_to_nat(0u);
v___y_3131_ = v___x_3146_;
v___y_3132_ = v___x_3147_;
v___y_3133_ = v___x_3149_;
goto v___jp_3130_;
}
}
}
}
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3164_; 
lean_del_object(v___x_3094_);
v___x_3159_ = lean_nat_add(v___x_3098_, v_size_3100_);
lean_dec(v_size_3100_);
v___x_3160_ = lean_nat_add(v___x_3159_, v_size_3099_);
lean_dec(v___x_3159_);
v___x_3161_ = lean_nat_add(v___x_3098_, v_size_3099_);
v___x_3162_ = lean_nat_add(v___x_3161_, v_size_3117_);
lean_dec(v___x_3161_);
lean_inc_ref(v_r_3092_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 4, v_r_3092_);
lean_ctor_set(v___x_3114_, 3, v_r_3104_);
lean_ctor_set(v___x_3114_, 2, v_v_3090_);
lean_ctor_set(v___x_3114_, 1, v_k_3089_);
lean_ctor_set(v___x_3114_, 0, v___x_3162_);
v___x_3164_ = v___x_3114_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_k_3089_);
lean_ctor_set(v_reuseFailAlloc_3177_, 2, v_v_3090_);
lean_ctor_set(v_reuseFailAlloc_3177_, 3, v_r_3104_);
lean_ctor_set(v_reuseFailAlloc_3177_, 4, v_r_3092_);
v___x_3164_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
v_isSharedCheck_3171_ = !lean_is_exclusive(v_r_3092_);
if (v_isSharedCheck_3171_ == 0)
{
lean_object* v_unused_3172_; lean_object* v_unused_3173_; lean_object* v_unused_3174_; lean_object* v_unused_3175_; lean_object* v_unused_3176_; 
v_unused_3172_ = lean_ctor_get(v_r_3092_, 4);
lean_dec(v_unused_3172_);
v_unused_3173_ = lean_ctor_get(v_r_3092_, 3);
lean_dec(v_unused_3173_);
v_unused_3174_ = lean_ctor_get(v_r_3092_, 2);
lean_dec(v_unused_3174_);
v_unused_3175_ = lean_ctor_get(v_r_3092_, 1);
lean_dec(v_unused_3175_);
v_unused_3176_ = lean_ctor_get(v_r_3092_, 0);
lean_dec(v_unused_3176_);
v___x_3166_ = v_r_3092_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_dec(v_r_3092_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 4, v___x_3164_);
lean_ctor_set(v___x_3166_, 3, v_l_3103_);
lean_ctor_set(v___x_3166_, 2, v_v_3102_);
lean_ctor_set(v___x_3166_, 1, v_k_3101_);
lean_ctor_set(v___x_3166_, 0, v___x_3160_);
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3160_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v_k_3101_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_v_3102_);
lean_ctor_set(v_reuseFailAlloc_3170_, 3, v_l_3103_);
lean_ctor_set(v_reuseFailAlloc_3170_, 4, v___x_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3184_; 
v_l_3184_ = lean_ctor_get(v_impl_3097_, 3);
lean_inc(v_l_3184_);
if (lean_obj_tag(v_l_3184_) == 0)
{
lean_object* v_r_3185_; lean_object* v_k_3186_; lean_object* v_v_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3198_; 
v_r_3185_ = lean_ctor_get(v_impl_3097_, 4);
v_k_3186_ = lean_ctor_get(v_impl_3097_, 1);
v_v_3187_ = lean_ctor_get(v_impl_3097_, 2);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_impl_3097_);
if (v_isSharedCheck_3198_ == 0)
{
lean_object* v_unused_3199_; lean_object* v_unused_3200_; 
v_unused_3199_ = lean_ctor_get(v_impl_3097_, 3);
lean_dec(v_unused_3199_);
v_unused_3200_ = lean_ctor_get(v_impl_3097_, 0);
lean_dec(v_unused_3200_);
v___x_3189_ = v_impl_3097_;
v_isShared_3190_ = v_isSharedCheck_3198_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_r_3185_);
lean_inc(v_v_3187_);
lean_inc(v_k_3186_);
lean_dec(v_impl_3097_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3198_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3191_; lean_object* v___x_3193_; 
v___x_3191_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3185_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 3, v_r_3185_);
lean_ctor_set(v___x_3189_, 2, v_v_3090_);
lean_ctor_set(v___x_3189_, 1, v_k_3089_);
lean_ctor_set(v___x_3189_, 0, v___x_3098_);
v___x_3193_ = v___x_3189_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3098_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v_k_3089_);
lean_ctor_set(v_reuseFailAlloc_3197_, 2, v_v_3090_);
lean_ctor_set(v_reuseFailAlloc_3197_, 3, v_r_3185_);
lean_ctor_set(v_reuseFailAlloc_3197_, 4, v_r_3185_);
v___x_3193_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3195_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 4, v___x_3193_);
lean_ctor_set(v___x_3094_, 3, v_l_3184_);
lean_ctor_set(v___x_3094_, 2, v_v_3187_);
lean_ctor_set(v___x_3094_, 1, v_k_3186_);
lean_ctor_set(v___x_3094_, 0, v___x_3191_);
v___x_3195_ = v___x_3094_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v_k_3186_);
lean_ctor_set(v_reuseFailAlloc_3196_, 2, v_v_3187_);
lean_ctor_set(v_reuseFailAlloc_3196_, 3, v_l_3184_);
lean_ctor_set(v_reuseFailAlloc_3196_, 4, v___x_3193_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
else
{
lean_object* v_r_3201_; 
v_r_3201_ = lean_ctor_get(v_impl_3097_, 4);
lean_inc(v_r_3201_);
if (lean_obj_tag(v_r_3201_) == 0)
{
lean_object* v_k_3202_; lean_object* v_v_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3226_; 
v_k_3202_ = lean_ctor_get(v_impl_3097_, 1);
v_v_3203_ = lean_ctor_get(v_impl_3097_, 2);
v_isSharedCheck_3226_ = !lean_is_exclusive(v_impl_3097_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; lean_object* v_unused_3228_; lean_object* v_unused_3229_; 
v_unused_3227_ = lean_ctor_get(v_impl_3097_, 4);
lean_dec(v_unused_3227_);
v_unused_3228_ = lean_ctor_get(v_impl_3097_, 3);
lean_dec(v_unused_3228_);
v_unused_3229_ = lean_ctor_get(v_impl_3097_, 0);
lean_dec(v_unused_3229_);
v___x_3205_ = v_impl_3097_;
v_isShared_3206_ = v_isSharedCheck_3226_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_v_3203_);
lean_inc(v_k_3202_);
lean_dec(v_impl_3097_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3226_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v_k_3207_; lean_object* v_v_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3222_; 
v_k_3207_ = lean_ctor_get(v_r_3201_, 1);
v_v_3208_ = lean_ctor_get(v_r_3201_, 2);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_r_3201_);
if (v_isSharedCheck_3222_ == 0)
{
lean_object* v_unused_3223_; lean_object* v_unused_3224_; lean_object* v_unused_3225_; 
v_unused_3223_ = lean_ctor_get(v_r_3201_, 4);
lean_dec(v_unused_3223_);
v_unused_3224_ = lean_ctor_get(v_r_3201_, 3);
lean_dec(v_unused_3224_);
v_unused_3225_ = lean_ctor_get(v_r_3201_, 0);
lean_dec(v_unused_3225_);
v___x_3210_ = v_r_3201_;
v_isShared_3211_ = v_isSharedCheck_3222_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_v_3208_);
lean_inc(v_k_3207_);
lean_dec(v_r_3201_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3222_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3212_ = lean_unsigned_to_nat(3u);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 4, v_l_3184_);
lean_ctor_set(v___x_3210_, 3, v_l_3184_);
lean_ctor_set(v___x_3210_, 2, v_v_3203_);
lean_ctor_set(v___x_3210_, 1, v_k_3202_);
lean_ctor_set(v___x_3210_, 0, v___x_3098_);
v___x_3214_ = v___x_3210_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3098_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_k_3202_);
lean_ctor_set(v_reuseFailAlloc_3221_, 2, v_v_3203_);
lean_ctor_set(v_reuseFailAlloc_3221_, 3, v_l_3184_);
lean_ctor_set(v_reuseFailAlloc_3221_, 4, v_l_3184_);
v___x_3214_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3216_; 
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 4, v_l_3184_);
lean_ctor_set(v___x_3205_, 2, v_v_3090_);
lean_ctor_set(v___x_3205_, 1, v_k_3089_);
lean_ctor_set(v___x_3205_, 0, v___x_3098_);
v___x_3216_ = v___x_3205_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3098_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_k_3089_);
lean_ctor_set(v_reuseFailAlloc_3220_, 2, v_v_3090_);
lean_ctor_set(v_reuseFailAlloc_3220_, 3, v_l_3184_);
lean_ctor_set(v_reuseFailAlloc_3220_, 4, v_l_3184_);
v___x_3216_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3218_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 4, v___x_3216_);
lean_ctor_set(v___x_3094_, 3, v___x_3214_);
lean_ctor_set(v___x_3094_, 2, v_v_3208_);
lean_ctor_set(v___x_3094_, 1, v_k_3207_);
lean_ctor_set(v___x_3094_, 0, v___x_3212_);
v___x_3218_ = v___x_3094_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3212_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v_k_3207_);
lean_ctor_set(v_reuseFailAlloc_3219_, 2, v_v_3208_);
lean_ctor_set(v_reuseFailAlloc_3219_, 3, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3219_, 4, v___x_3216_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
}
}
else
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3230_ = lean_unsigned_to_nat(2u);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 4, v_r_3201_);
lean_ctor_set(v___x_3094_, 3, v_impl_3097_);
lean_ctor_set(v___x_3094_, 0, v___x_3230_);
v___x_3232_ = v___x_3094_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_k_3089_);
lean_ctor_set(v_reuseFailAlloc_3233_, 2, v_v_3090_);
lean_ctor_set(v_reuseFailAlloc_3233_, 3, v_impl_3097_);
lean_ctor_set(v_reuseFailAlloc_3233_, 4, v_r_3201_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3235_; 
lean_dec(v_v_3090_);
lean_dec(v_k_3089_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 2, v_v_3086_);
lean_ctor_set(v___x_3094_, 1, v_k_3085_);
v___x_3235_ = v___x_3094_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_size_3088_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v_k_3085_);
lean_ctor_set(v_reuseFailAlloc_3236_, 2, v_v_3086_);
lean_ctor_set(v_reuseFailAlloc_3236_, 3, v_l_3091_);
lean_ctor_set(v_reuseFailAlloc_3236_, 4, v_r_3092_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
default: 
{
lean_object* v_impl_3237_; lean_object* v___x_3238_; 
lean_dec(v_size_3088_);
v_impl_3237_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3085_, v_v_3086_, v_r_3092_);
v___x_3238_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3091_) == 0)
{
lean_object* v_size_3239_; lean_object* v_size_3240_; lean_object* v_k_3241_; lean_object* v_v_3242_; lean_object* v_l_3243_; lean_object* v_r_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; 
v_size_3239_ = lean_ctor_get(v_l_3091_, 0);
v_size_3240_ = lean_ctor_get(v_impl_3237_, 0);
lean_inc(v_size_3240_);
v_k_3241_ = lean_ctor_get(v_impl_3237_, 1);
lean_inc(v_k_3241_);
v_v_3242_ = lean_ctor_get(v_impl_3237_, 2);
lean_inc(v_v_3242_);
v_l_3243_ = lean_ctor_get(v_impl_3237_, 3);
lean_inc(v_l_3243_);
v_r_3244_ = lean_ctor_get(v_impl_3237_, 4);
lean_inc(v_r_3244_);
v___x_3245_ = lean_unsigned_to_nat(3u);
v___x_3246_ = lean_nat_mul(v___x_3245_, v_size_3239_);
v___x_3247_ = lean_nat_dec_lt(v___x_3246_, v_size_3240_);
lean_dec(v___x_3246_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3251_; 
lean_dec(v_r_3244_);
lean_dec(v_l_3243_);
lean_dec(v_v_3242_);
lean_dec(v_k_3241_);
v___x_3248_ = lean_nat_add(v___x_3238_, v_size_3239_);
v___x_3249_ = lean_nat_add(v___x_3248_, v_size_3240_);
lean_dec(v_size_3240_);
lean_dec(v___x_3248_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 4, v_impl_3237_);
lean_ctor_set(v___x_3094_, 0, v___x_3249_);
v___x_3251_ = v___x_3094_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3252_, 1, v_k_3089_);
lean_ctor_set(v_reuseFailAlloc_3252_, 2, v_v_3090_);
lean_ctor_set(v_reuseFailAlloc_3252_, 3, v_l_3091_);
lean_ctor_set(v_reuseFailAlloc_3252_, 4, v_impl_3237_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
else
{
lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3316_; 
v_isSharedCheck_3316_ = !lean_is_exclusive(v_impl_3237_);
if (v_isSharedCheck_3316_ == 0)
{
lean_object* v_unused_3317_; lean_object* v_unused_3318_; lean_object* v_unused_3319_; lean_object* v_unused_3320_; lean_object* v_unused_3321_; 
v_unused_3317_ = lean_ctor_get(v_impl_3237_, 4);
lean_dec(v_unused_3317_);
v_unused_3318_ = lean_ctor_get(v_impl_3237_, 3);
lean_dec(v_unused_3318_);
v_unused_3319_ = lean_ctor_get(v_impl_3237_, 2);
lean_dec(v_unused_3319_);
v_unused_3320_ = lean_ctor_get(v_impl_3237_, 1);
lean_dec(v_unused_3320_);
v_unused_3321_ = lean_ctor_get(v_impl_3237_, 0);
lean_dec(v_unused_3321_);
v___x_3254_ = v_impl_3237_;
v_isShared_3255_ = v_isSharedCheck_3316_;
goto v_resetjp_3253_;
}
else
{
lean_dec(v_impl_3237_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3316_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v_size_3256_; lean_object* v_k_3257_; lean_object* v_v_3258_; lean_object* v_l_3259_; lean_object* v_r_3260_; lean_object* v_size_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; 
v_size_3256_ = lean_ctor_get(v_l_3243_, 0);
v_k_3257_ = lean_ctor_get(v_l_3243_, 1);
v_v_3258_ = lean_ctor_get(v_l_3243_, 2);
v_l_3259_ = lean_ctor_get(v_l_3243_, 3);
v_r_3260_ = lean_ctor_get(v_l_3243_, 4);
v_size_3261_ = lean_ctor_get(v_r_3244_, 0);
v___x_3262_ = lean_unsigned_to_nat(2u);
v___x_3263_ = lean_nat_mul(v___x_3262_, v_size_3261_);
v___x_3264_ = lean_nat_dec_lt(v_size_3256_, v___x_3263_);
lean_dec(v___x_3263_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3292_; 
lean_inc(v_r_3260_);
lean_inc(v_l_3259_);
lean_inc(v_v_3258_);
lean_inc(v_k_3257_);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_l_3243_);
if (v_isSharedCheck_3292_ == 0)
{
lean_object* v_unused_3293_; lean_object* v_unused_3294_; lean_object* v_unused_3295_; lean_object* v_unused_3296_; lean_object* v_unused_3297_; 
v_unused_3293_ = lean_ctor_get(v_l_3243_, 4);
lean_dec(v_unused_3293_);
v_unused_3294_ = lean_ctor_get(v_l_3243_, 3);
lean_dec(v_unused_3294_);
v_unused_3295_ = lean_ctor_get(v_l_3243_, 2);
lean_dec(v_unused_3295_);
v_unused_3296_ = lean_ctor_get(v_l_3243_, 1);
lean_dec(v_unused_3296_);
v_unused_3297_ = lean_ctor_get(v_l_3243_, 0);
lean_dec(v_unused_3297_);
v___x_3266_ = v_l_3243_;
v_isShared_3267_ = v_isSharedCheck_3292_;
goto v_resetjp_3265_;
}
else
{
lean_dec(v_l_3243_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3292_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3282_; 
v___x_3268_ = lean_nat_add(v___x_3238_, v_size_3239_);
v___x_3269_ = lean_nat_add(v___x_3268_, v_size_3240_);
lean_dec(v_size_3240_);
if (lean_obj_tag(v_l_3259_) == 0)
{
lean_object* v_size_3290_; 
v_size_3290_ = lean_ctor_get(v_l_3259_, 0);
lean_inc(v_size_3290_);
v___y_3282_ = v_size_3290_;
goto v___jp_3281_;
}
else
{
lean_object* v___x_3291_; 
v___x_3291_ = lean_unsigned_to_nat(0u);
v___y_3282_ = v___x_3291_;
goto v___jp_3281_;
}
v___jp_3270_:
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
v___x_3274_ = lean_nat_add(v___y_3271_, v___y_3273_);
lean_dec(v___y_3273_);
lean_dec(v___y_3271_);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 4, v_r_3244_);
lean_ctor_set(v___x_3266_, 3, v_r_3260_);
lean_ctor_set(v___x_3266_, 2, v_v_3242_);
lean_ctor_set(v___x_3266_, 1, v_k_3241_);
lean_ctor_set(v___x_3266_, 0, v___x_3274_);
v___x_3276_ = v___x_3266_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3274_);
lean_ctor_set(v_reuseFailAlloc_3280_, 1, v_k_3241_);
lean_ctor_set(v_reuseFailAlloc_3280_, 2, v_v_3242_);
lean_ctor_set(v_reuseFailAlloc_3280_, 3, v_r_3260_);
lean_ctor_set(v_reuseFailAlloc_3280_, 4, v_r_3244_);
v___x_3276_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
lean_object* v___x_3278_; 
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 4, v___x_3276_);
lean_ctor_set(v___x_3254_, 3, v___y_3272_);
lean_ctor_set(v___x_3254_, 2, v_v_3258_);
lean_ctor_set(v___x_3254_, 1, v_k_3257_);
lean_ctor_set(v___x_3254_, 0, v___x_3269_);
v___x_3278_ = v___x_3254_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3269_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_k_3257_);
lean_ctor_set(v_reuseFailAlloc_3279_, 2, v_v_3258_);
lean_ctor_set(v_reuseFailAlloc_3279_, 3, v___y_3272_);
lean_ctor_set(v_reuseFailAlloc_3279_, 4, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
v___jp_3281_:
{
lean_object* v___x_3283_; lean_object* v___x_3285_; 
v___x_3283_ = lean_nat_add(v___x_3268_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec(v___x_3268_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 4, v_l_3259_);
lean_ctor_set(v___x_3094_, 0, v___x_3283_);
v___x_3285_ = v___x_3094_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v___x_3283_);
lean_ctor_set(v_reuseFailAlloc_3289_, 1, v_k_3089_);
lean_ctor_set(v_reuseFailAlloc_3289_, 2, v_v_3090_);
lean_ctor_set(v_reuseFailAlloc_3289_, 3, v_l_3091_);
lean_ctor_set(v_reuseFailAlloc_3289_, 4, v_l_3259_);
v___x_3285_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_nat_add(v___x_3238_, v_size_3261_);
if (lean_obj_tag(v_r_3260_) == 0)
{
lean_object* v_size_3287_; 
v_size_3287_ = lean_ctor_get(v_r_3260_, 0);
lean_inc(v_size_3287_);
v___y_3271_ = v___x_3286_;
v___y_3272_ = v___x_3285_;
v___y_3273_ = v_size_3287_;
goto v___jp_3270_;
}
else
{
lean_object* v___x_3288_; 
v___x_3288_ = lean_unsigned_to_nat(0u);
v___y_3271_ = v___x_3286_;
v___y_3272_ = v___x_3285_;
v___y_3273_ = v___x_3288_;
goto v___jp_3270_;
}
}
}
}
}
else
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
lean_del_object(v___x_3094_);
v___x_3298_ = lean_nat_add(v___x_3238_, v_size_3239_);
v___x_3299_ = lean_nat_add(v___x_3298_, v_size_3240_);
lean_dec(v_size_3240_);
v___x_3300_ = lean_nat_add(v___x_3298_, v_size_3256_);
lean_dec(v___x_3298_);
lean_inc_ref(v_l_3091_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 4, v_l_3243_);
lean_ctor_set(v___x_3254_, 3, v_l_3091_);
lean_ctor_set(v___x_3254_, 2, v_v_3090_);
lean_ctor_set(v___x_3254_, 1, v_k_3089_);
lean_ctor_set(v___x_3254_, 0, v___x_3300_);
v___x_3302_ = v___x_3254_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3300_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_k_3089_);
lean_ctor_set(v_reuseFailAlloc_3315_, 2, v_v_3090_);
lean_ctor_set(v_reuseFailAlloc_3315_, 3, v_l_3091_);
lean_ctor_set(v_reuseFailAlloc_3315_, 4, v_l_3243_);
v___x_3302_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
v_isSharedCheck_3309_ = !lean_is_exclusive(v_l_3091_);
if (v_isSharedCheck_3309_ == 0)
{
lean_object* v_unused_3310_; lean_object* v_unused_3311_; lean_object* v_unused_3312_; lean_object* v_unused_3313_; lean_object* v_unused_3314_; 
v_unused_3310_ = lean_ctor_get(v_l_3091_, 4);
lean_dec(v_unused_3310_);
v_unused_3311_ = lean_ctor_get(v_l_3091_, 3);
lean_dec(v_unused_3311_);
v_unused_3312_ = lean_ctor_get(v_l_3091_, 2);
lean_dec(v_unused_3312_);
v_unused_3313_ = lean_ctor_get(v_l_3091_, 1);
lean_dec(v_unused_3313_);
v_unused_3314_ = lean_ctor_get(v_l_3091_, 0);
lean_dec(v_unused_3314_);
v___x_3304_ = v_l_3091_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_dec(v_l_3091_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 4, v_r_3244_);
lean_ctor_set(v___x_3304_, 3, v___x_3302_);
lean_ctor_set(v___x_3304_, 2, v_v_3242_);
lean_ctor_set(v___x_3304_, 1, v_k_3241_);
lean_ctor_set(v___x_3304_, 0, v___x_3299_);
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3299_);
lean_ctor_set(v_reuseFailAlloc_3308_, 1, v_k_3241_);
lean_ctor_set(v_reuseFailAlloc_3308_, 2, v_v_3242_);
lean_ctor_set(v_reuseFailAlloc_3308_, 3, v___x_3302_);
lean_ctor_set(v_reuseFailAlloc_3308_, 4, v_r_3244_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3322_; 
v_l_3322_ = lean_ctor_get(v_impl_3237_, 3);
lean_inc(v_l_3322_);
if (lean_obj_tag(v_l_3322_) == 0)
{
lean_object* v_r_3323_; lean_object* v_k_3324_; lean_object* v_v_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3348_; 
v_r_3323_ = lean_ctor_get(v_impl_3237_, 4);
v_k_3324_ = lean_ctor_get(v_impl_3237_, 1);
v_v_3325_ = lean_ctor_get(v_impl_3237_, 2);
v_isSharedCheck_3348_ = !lean_is_exclusive(v_impl_3237_);
if (v_isSharedCheck_3348_ == 0)
{
lean_object* v_unused_3349_; lean_object* v_unused_3350_; 
v_unused_3349_ = lean_ctor_get(v_impl_3237_, 3);
lean_dec(v_unused_3349_);
v_unused_3350_ = lean_ctor_get(v_impl_3237_, 0);
lean_dec(v_unused_3350_);
v___x_3327_ = v_impl_3237_;
v_isShared_3328_ = v_isSharedCheck_3348_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_r_3323_);
lean_inc(v_v_3325_);
lean_inc(v_k_3324_);
lean_dec(v_impl_3237_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3348_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v_k_3329_; lean_object* v_v_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3344_; 
v_k_3329_ = lean_ctor_get(v_l_3322_, 1);
v_v_3330_ = lean_ctor_get(v_l_3322_, 2);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_l_3322_);
if (v_isSharedCheck_3344_ == 0)
{
lean_object* v_unused_3345_; lean_object* v_unused_3346_; lean_object* v_unused_3347_; 
v_unused_3345_ = lean_ctor_get(v_l_3322_, 4);
lean_dec(v_unused_3345_);
v_unused_3346_ = lean_ctor_get(v_l_3322_, 3);
lean_dec(v_unused_3346_);
v_unused_3347_ = lean_ctor_get(v_l_3322_, 0);
lean_dec(v_unused_3347_);
v___x_3332_ = v_l_3322_;
v_isShared_3333_ = v_isSharedCheck_3344_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_v_3330_);
lean_inc(v_k_3329_);
lean_dec(v_l_3322_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3344_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3334_; lean_object* v___x_3336_; 
v___x_3334_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3323_, 2);
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 4, v_r_3323_);
lean_ctor_set(v___x_3332_, 3, v_r_3323_);
lean_ctor_set(v___x_3332_, 2, v_v_3090_);
lean_ctor_set(v___x_3332_, 1, v_k_3089_);
lean_ctor_set(v___x_3332_, 0, v___x_3238_);
v___x_3336_ = v___x_3332_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3343_, 1, v_k_3089_);
lean_ctor_set(v_reuseFailAlloc_3343_, 2, v_v_3090_);
lean_ctor_set(v_reuseFailAlloc_3343_, 3, v_r_3323_);
lean_ctor_set(v_reuseFailAlloc_3343_, 4, v_r_3323_);
v___x_3336_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3338_; 
lean_inc(v_r_3323_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 3, v_r_3323_);
lean_ctor_set(v___x_3327_, 0, v___x_3238_);
v___x_3338_ = v___x_3327_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_k_3324_);
lean_ctor_set(v_reuseFailAlloc_3342_, 2, v_v_3325_);
lean_ctor_set(v_reuseFailAlloc_3342_, 3, v_r_3323_);
lean_ctor_set(v_reuseFailAlloc_3342_, 4, v_r_3323_);
v___x_3338_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
lean_object* v___x_3340_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 4, v___x_3338_);
lean_ctor_set(v___x_3094_, 3, v___x_3336_);
lean_ctor_set(v___x_3094_, 2, v_v_3330_);
lean_ctor_set(v___x_3094_, 1, v_k_3329_);
lean_ctor_set(v___x_3094_, 0, v___x_3334_);
v___x_3340_ = v___x_3094_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3334_);
lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_k_3329_);
lean_ctor_set(v_reuseFailAlloc_3341_, 2, v_v_3330_);
lean_ctor_set(v_reuseFailAlloc_3341_, 3, v___x_3336_);
lean_ctor_set(v_reuseFailAlloc_3341_, 4, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
}
}
else
{
lean_object* v_r_3351_; 
v_r_3351_ = lean_ctor_get(v_impl_3237_, 4);
lean_inc(v_r_3351_);
if (lean_obj_tag(v_r_3351_) == 0)
{
lean_object* v_k_3352_; lean_object* v_v_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3364_; 
v_k_3352_ = lean_ctor_get(v_impl_3237_, 1);
v_v_3353_ = lean_ctor_get(v_impl_3237_, 2);
v_isSharedCheck_3364_ = !lean_is_exclusive(v_impl_3237_);
if (v_isSharedCheck_3364_ == 0)
{
lean_object* v_unused_3365_; lean_object* v_unused_3366_; lean_object* v_unused_3367_; 
v_unused_3365_ = lean_ctor_get(v_impl_3237_, 4);
lean_dec(v_unused_3365_);
v_unused_3366_ = lean_ctor_get(v_impl_3237_, 3);
lean_dec(v_unused_3366_);
v_unused_3367_ = lean_ctor_get(v_impl_3237_, 0);
lean_dec(v_unused_3367_);
v___x_3355_ = v_impl_3237_;
v_isShared_3356_ = v_isSharedCheck_3364_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_v_3353_);
lean_inc(v_k_3352_);
lean_dec(v_impl_3237_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3364_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
v___x_3357_ = lean_unsigned_to_nat(3u);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 4, v_l_3322_);
lean_ctor_set(v___x_3355_, 2, v_v_3090_);
lean_ctor_set(v___x_3355_, 1, v_k_3089_);
lean_ctor_set(v___x_3355_, 0, v___x_3238_);
v___x_3359_ = v___x_3355_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_k_3089_);
lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_v_3090_);
lean_ctor_set(v_reuseFailAlloc_3363_, 3, v_l_3322_);
lean_ctor_set(v_reuseFailAlloc_3363_, 4, v_l_3322_);
v___x_3359_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3361_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 4, v_r_3351_);
lean_ctor_set(v___x_3094_, 3, v___x_3359_);
lean_ctor_set(v___x_3094_, 2, v_v_3353_);
lean_ctor_set(v___x_3094_, 1, v_k_3352_);
lean_ctor_set(v___x_3094_, 0, v___x_3357_);
v___x_3361_ = v___x_3094_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3357_);
lean_ctor_set(v_reuseFailAlloc_3362_, 1, v_k_3352_);
lean_ctor_set(v_reuseFailAlloc_3362_, 2, v_v_3353_);
lean_ctor_set(v_reuseFailAlloc_3362_, 3, v___x_3359_);
lean_ctor_set(v_reuseFailAlloc_3362_, 4, v_r_3351_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3368_ = lean_unsigned_to_nat(2u);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 4, v_impl_3237_);
lean_ctor_set(v___x_3094_, 3, v_r_3351_);
lean_ctor_set(v___x_3094_, 0, v___x_3368_);
v___x_3370_ = v___x_3094_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3368_);
lean_ctor_set(v_reuseFailAlloc_3371_, 1, v_k_3089_);
lean_ctor_set(v_reuseFailAlloc_3371_, 2, v_v_3090_);
lean_ctor_set(v_reuseFailAlloc_3371_, 3, v_r_3351_);
lean_ctor_set(v_reuseFailAlloc_3371_, 4, v_impl_3237_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
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
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = lean_unsigned_to_nat(1u);
v___x_3374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
lean_ctor_set(v___x_3374_, 1, v_k_3085_);
lean_ctor_set(v___x_3374_, 2, v_v_3086_);
lean_ctor_set(v___x_3374_, 3, v_t_3087_);
lean_ctor_set(v___x_3374_, 4, v_t_3087_);
return v___x_3374_;
}
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3375_ = lean_box(1);
v___x_3376_ = l_Lake_Package_depsFacetConfig;
v___x_3377_ = l_Lake_Package_depsFacet;
v___x_3378_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3377_, v___x_3376_, v___x_3375_);
return v___x_3378_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3379_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__0, &l_Lake_Package_initFacetConfigs___closed__0_once, _init_l_Lake_Package_initFacetConfigs___closed__0);
v___x_3380_ = l_Lake_Package_transDepsFacetConfig;
v___x_3381_ = l_Lake_Package_transDepsFacet;
v___x_3382_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3381_, v___x_3380_, v___x_3379_);
return v___x_3382_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3383_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__1, &l_Lake_Package_initFacetConfigs___closed__1_once, _init_l_Lake_Package_initFacetConfigs___closed__1);
v___x_3384_ = l_Lake_Package_extraDepFacetConfig;
v___x_3385_ = l_Lake_Package_extraDepFacet;
v___x_3386_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3385_, v___x_3384_, v___x_3383_);
return v___x_3386_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3387_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__2, &l_Lake_Package_initFacetConfigs___closed__2_once, _init_l_Lake_Package_initFacetConfigs___closed__2);
v___x_3388_ = l_Lake_Package_optBuildCacheFacetConfig;
v___x_3389_ = l_Lake_Package_optBuildCacheFacet;
v___x_3390_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3389_, v___x_3388_, v___x_3387_);
return v___x_3390_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3391_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__3, &l_Lake_Package_initFacetConfigs___closed__3_once, _init_l_Lake_Package_initFacetConfigs___closed__3);
v___x_3392_ = l_Lake_Package_buildCacheFacetConfig;
v___x_3393_ = l_Lake_Package_buildCacheFacet;
v___x_3394_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3393_, v___x_3392_, v___x_3391_);
return v___x_3394_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3395_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__4, &l_Lake_Package_initFacetConfigs___closed__4_once, _init_l_Lake_Package_initFacetConfigs___closed__4);
v___x_3396_ = l_Lake_Package_optBarrelFacetConfig;
v___x_3397_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3398_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3397_, v___x_3396_, v___x_3395_);
return v___x_3398_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3399_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__5, &l_Lake_Package_initFacetConfigs___closed__5_once, _init_l_Lake_Package_initFacetConfigs___closed__5);
v___x_3400_ = l_Lake_Package_barrelFacetConfig;
v___x_3401_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3402_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3401_, v___x_3400_, v___x_3399_);
return v___x_3402_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3403_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__6, &l_Lake_Package_initFacetConfigs___closed__6_once, _init_l_Lake_Package_initFacetConfigs___closed__6);
v___x_3404_ = l_Lake_Package_optGitHubReleaseFacetConfig;
v___x_3405_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3406_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3405_, v___x_3404_, v___x_3403_);
return v___x_3406_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3407_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__7, &l_Lake_Package_initFacetConfigs___closed__7_once, _init_l_Lake_Package_initFacetConfigs___closed__7);
v___x_3408_ = l_Lake_Package_gitHubReleaseFacetConfig;
v___x_3409_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3410_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3409_, v___x_3408_, v___x_3407_);
return v___x_3410_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs(void){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__8, &l_Lake_Package_initFacetConfigs___closed__8_once, _init_l_Lake_Package_initFacetConfigs___closed__8);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3412_, lean_object* v_k_3413_, lean_object* v_v_3414_, lean_object* v_t_3415_, lean_object* v_hl_3416_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3413_, v_v_3414_, v_t_3415_);
return v___x_3417_;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs(void){
_start:
{
lean_object* v___x_3418_; 
v___x_3418_ = l_Lake_Package_initFacetConfigs;
return v___x_3418_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Package(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
