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
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
extern lean_object* l_Lake_Package_optBuildCacheFacet;
extern lean_object* l_Lake_Package_keyword;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_dec_ref_known(v___x_333_, 2);
v___x_336_ = l_Lake_Job_await___redArg(v_a_334_, v_a_335_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v_a_338_; lean_object* v___y_340_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
v_a_338_ = lean_ctor_get(v___x_336_, 1);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_336_, 2);
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
lean_dec_ref_known(v___y_422_, 2);
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
v_depPkgs_463_ = lean_ctor_get(v_self_455_, 14);
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
lean_object* v_config_586_; lean_object* v_keyName_587_; lean_object* v_dir_588_; lean_object* v_scope_589_; lean_object* v_buildDir_590_; uint8_t v_preferReleaseBuild_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; uint8_t v___y_602_; lean_object* v_toContext_616_; lean_object* v_lakeEnv_617_; uint8_t v_noCache_618_; lean_object* v_toolchain_619_; uint8_t v___y_621_; uint8_t v___y_627_; uint8_t v___x_632_; 
v_config_586_ = lean_ctor_get(v_self_578_, 6);
v_keyName_587_ = lean_ctor_get(v_self_578_, 2);
v_dir_588_ = lean_ctor_get(v_self_578_, 4);
v_scope_589_ = lean_ctor_get(v_self_578_, 10);
v_buildDir_590_ = lean_ctor_get(v_config_586_, 5);
v_preferReleaseBuild_591_ = lean_ctor_get_uint8(v_config_586_, sizeof(void*)*27 + 2);
lean_inc_ref(v_buildDir_590_);
v___x_592_ = l_System_FilePath_normalize(v_buildDir_590_);
lean_inc_ref(v_dir_588_);
v___x_593_ = l_Lake_joinRelative(v_dir_588_, v___x_592_);
v___x_594_ = l_System_FilePath_pathExists(v___x_593_);
lean_dec_ref(v___x_593_);
v_toContext_616_ = lean_ctor_get(v_a_583_, 1);
v_lakeEnv_617_ = lean_ctor_get(v_toContext_616_, 0);
v_noCache_618_ = lean_ctor_get_uint8(v_lakeEnv_617_, sizeof(void*)*20);
v_toolchain_619_ = lean_ctor_get(v_lakeEnv_617_, 19);
v___x_632_ = lean_bool_not(v_noCache_618_);
if (v___x_632_ == 0)
{
v___y_627_ = v___x_632_;
goto v___jp_626_;
}
else
{
uint8_t v___x_633_; 
v___x_633_ = lean_bool_not(v___x_594_);
v___y_627_ = v___x_633_;
goto v___jp_626_;
}
v___jp_595_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_596_ = l_Lake_Package_optBuildCacheFacet;
lean_inc(v_keyName_587_);
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_keyName_587_);
v___x_598_ = l_Lake_Package_keyword;
v___x_599_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
lean_ctor_set(v___x_599_, 2, v_self_578_);
lean_ctor_set(v___x_599_, 3, v___x_596_);
lean_inc_ref(v_a_583_);
lean_inc(v_a_582_);
lean_inc(v_a_581_);
lean_inc(v_a_580_);
v___x_600_ = lean_apply_7(v_a_579_, v___x_599_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, lean_box(0));
return v___x_600_;
}
v___jp_601_:
{
uint8_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_603_ = 1;
v___x_604_ = lean_box(0);
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_607_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_608_ = 0;
v___x_609_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_610_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_610_, 0, v___x_606_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
lean_ctor_set(v___x_610_, 2, v___x_605_);
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*3, v___x_608_);
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*3 + 1, v___y_602_);
v___x_611_ = lean_box(v___x_603_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_610_);
v___x_613_ = lean_task_pure(v___x_612_);
v___x_614_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_604_);
lean_ctor_set(v___x_614_, 2, v___x_607_);
lean_ctor_set_uint8(v___x_614_, sizeof(void*)*3, v___y_602_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v_a_584_);
return v___x_615_;
}
v___jp_620_:
{
if (v___y_621_ == 0)
{
lean_dec_ref(v_a_579_);
lean_dec_ref(v_self_578_);
v___y_602_ = v___y_621_;
goto v___jp_601_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; uint8_t v___x_625_; 
v___x_622_ = lean_string_utf8_byte_size(v_toolchain_619_);
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_nat_dec_eq(v___x_622_, v___x_623_);
v___x_625_ = lean_bool_not(v___x_624_);
if (v___x_625_ == 0)
{
lean_dec_ref(v_a_579_);
lean_dec_ref(v_self_578_);
v___y_602_ = v___x_625_;
goto v___jp_601_;
}
else
{
goto v___jp_595_;
}
}
}
v___jp_626_:
{
if (v___y_627_ == 0)
{
lean_dec_ref(v_a_579_);
lean_dec_ref(v_self_578_);
v___y_602_ = v___y_627_;
goto v___jp_601_;
}
else
{
if (v_preferReleaseBuild_591_ == 0)
{
lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_628_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0));
v___x_629_ = lean_string_dec_eq(v_scope_589_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1));
v___x_631_ = lean_string_dec_eq(v_scope_589_, v___x_630_);
v___y_621_ = v___x_631_;
goto v___jp_620_;
}
else
{
v___y_621_ = v___x_629_;
goto v___jp_620_;
}
}
else
{
goto v___jp_595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___boxed(lean_object* v_self_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec(v_a_637_);
lean_dec(v_a_636_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object* v_self_647_, lean_object* v_facet_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_toBuildConfig_652_; uint8_t v_verbosity_653_; uint8_t v___x_654_; uint8_t v___x_655_; 
v_toBuildConfig_652_ = lean_ctor_get(v_a_649_, 0);
v_verbosity_653_ = lean_ctor_get_uint8(v_toBuildConfig_652_, sizeof(void*)*3 + 3);
v___x_654_ = 2;
v___x_655_ = l_Lake_instDecidableEqVerbosity(v_verbosity_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; 
lean_dec(v_facet_648_);
lean_dec_ref(v_self_647_);
v___x_656_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v_a_650_);
return v___x_657_;
}
else
{
lean_object* v_baseName_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_baseName_658_ = lean_ctor_get(v_self_647_, 1);
lean_inc(v_baseName_658_);
lean_dec_ref(v_self_647_);
v___x_659_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_660_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_658_, v___x_655_);
v___x_661_ = lean_string_append(v___x_659_, v___x_660_);
lean_dec_ref(v___x_660_);
v___x_662_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_663_ = lean_string_append(v___x_661_, v___x_662_);
v___x_664_ = l_Lake_Name_eraseHead(v_facet_648_);
v___x_665_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_664_, v___x_655_);
v___x_666_ = lean_string_append(v___x_663_, v___x_665_);
lean_dec_ref(v___x_665_);
v___x_667_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_668_ = lean_string_append(v___x_666_, v___x_667_);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v_a_650_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* v_self_670_, lean_object* v_facet_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(v_self_670_, v_facet_671_, v_a_672_, v_a_673_);
lean_dec_ref(v_a_672_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* v_self_676_, lean_object* v_facet_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_toBuildConfig_685_; uint8_t v_verbosity_686_; uint8_t v___x_687_; uint8_t v___x_688_; 
v_toBuildConfig_685_ = lean_ctor_get(v_a_682_, 0);
v_verbosity_686_ = lean_ctor_get_uint8(v_toBuildConfig_685_, sizeof(void*)*3 + 3);
v___x_687_ = 2;
v___x_688_ = l_Lake_instDecidableEqVerbosity(v_verbosity_686_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec(v_facet_677_);
lean_dec_ref(v_self_676_);
v___x_689_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v_a_683_);
return v___x_690_;
}
else
{
lean_object* v_baseName_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_baseName_691_ = lean_ctor_get(v_self_676_, 1);
lean_inc(v_baseName_691_);
lean_dec_ref(v_self_676_);
v___x_692_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_693_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_691_, v___x_688_);
v___x_694_ = lean_string_append(v___x_692_, v___x_693_);
lean_dec_ref(v___x_693_);
v___x_695_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_696_ = lean_string_append(v___x_694_, v___x_695_);
v___x_697_ = l_Lake_Name_eraseHead(v_facet_677_);
v___x_698_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_697_, v___x_688_);
v___x_699_ = lean_string_append(v___x_696_, v___x_698_);
lean_dec_ref(v___x_698_);
v___x_700_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_701_ = lean_string_append(v___x_699_, v___x_700_);
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v_a_683_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* v_self_703_, lean_object* v_facet_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(v_self_703_, v_facet_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
return v_res_712_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_716_ = l_Lake_Name_eraseHead(v___x_715_);
return v___x_716_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_718_ = l_Lake_Name_eraseHead(v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(lean_object* v_self_719_, uint8_t v_success_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_a_729_; lean_object* v_a_730_; lean_object* v_a_751_; lean_object* v_a_752_; 
if (v_success_720_ == 0)
{
lean_object* v_config_772_; uint8_t v_preferReleaseBuild_773_; 
v_config_772_ = lean_ctor_get(v_self_719_, 6);
v_preferReleaseBuild_773_ = lean_ctor_get_uint8(v_config_772_, sizeof(void*)*27 + 2);
if (v_preferReleaseBuild_773_ == 0)
{
lean_object* v_toBuildConfig_774_; lean_object* v_baseName_775_; uint8_t v_verbosity_776_; uint8_t v___x_777_; uint8_t v___x_778_; 
v_toBuildConfig_774_ = lean_ctor_get(v___y_725_, 0);
v_baseName_775_ = lean_ctor_get(v_self_719_, 1);
lean_inc(v_baseName_775_);
lean_dec_ref(v_self_719_);
v_verbosity_776_ = lean_ctor_get_uint8(v_toBuildConfig_774_, sizeof(void*)*3 + 3);
v___x_777_ = 2;
v___x_778_ = l_Lake_instDecidableEqVerbosity(v_verbosity_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
lean_dec(v_baseName_775_);
v___x_779_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_729_ = v___x_779_;
v_a_730_ = v___y_726_;
goto v___jp_728_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_780_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_781_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_775_, v___x_778_);
v___x_782_ = lean_string_append(v___x_780_, v___x_781_);
lean_dec_ref(v___x_781_);
v___x_783_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_784_ = lean_string_append(v___x_782_, v___x_783_);
v___x_785_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2);
v___x_786_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_785_, v___x_778_);
v___x_787_ = lean_string_append(v___x_784_, v___x_786_);
lean_dec_ref(v___x_786_);
v___x_788_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_789_ = lean_string_append(v___x_787_, v___x_788_);
v_a_729_ = v___x_789_;
v_a_730_ = v___y_726_;
goto v___jp_728_;
}
}
else
{
lean_object* v_toBuildConfig_790_; lean_object* v_baseName_791_; uint8_t v_verbosity_792_; uint8_t v___x_793_; uint8_t v___x_794_; 
v_toBuildConfig_790_ = lean_ctor_get(v___y_725_, 0);
v_baseName_791_ = lean_ctor_get(v_self_719_, 1);
lean_inc(v_baseName_791_);
lean_dec_ref(v_self_719_);
v_verbosity_792_ = lean_ctor_get_uint8(v_toBuildConfig_790_, sizeof(void*)*3 + 3);
v___x_793_ = 2;
v___x_794_ = l_Lake_instDecidableEqVerbosity(v_verbosity_792_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
lean_dec(v_baseName_791_);
v___x_795_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_751_ = v___x_795_;
v_a_752_ = v___y_726_;
goto v___jp_750_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_796_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_797_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_791_, v___x_794_);
v___x_798_ = lean_string_append(v___x_796_, v___x_797_);
lean_dec_ref(v___x_797_);
v___x_799_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_800_ = lean_string_append(v___x_798_, v___x_799_);
v___x_801_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
v___x_802_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_801_, v___x_794_);
v___x_803_ = lean_string_append(v___x_800_, v___x_802_);
lean_dec_ref(v___x_802_);
v___x_804_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_805_ = lean_string_append(v___x_803_, v___x_804_);
v_a_751_ = v___x_805_;
v_a_752_ = v___y_726_;
goto v___jp_750_;
}
}
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec_ref(v_self_719_);
v___x_806_ = lean_box(0);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v___y_726_);
return v___x_807_;
}
v___jp_728_:
{
lean_object* v_log_731_; uint8_t v_action_732_; uint8_t v_wantsRebuild_733_; lean_object* v_trace_734_; lean_object* v_buildTime_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_749_; 
v_log_731_ = lean_ctor_get(v_a_730_, 0);
v_action_732_ = lean_ctor_get_uint8(v_a_730_, sizeof(void*)*3);
v_wantsRebuild_733_ = lean_ctor_get_uint8(v_a_730_, sizeof(void*)*3 + 1);
v_trace_734_ = lean_ctor_get(v_a_730_, 1);
v_buildTime_735_ = lean_ctor_get(v_a_730_, 2);
v_isSharedCheck_749_ = !lean_is_exclusive(v_a_730_);
if (v_isSharedCheck_749_ == 0)
{
v___x_737_ = v_a_730_;
v_isShared_738_ = v_isSharedCheck_749_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_buildTime_735_);
lean_inc(v_trace_734_);
lean_inc(v_log_731_);
lean_dec(v_a_730_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_749_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_739_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0));
v___x_740_ = lean_string_append(v___x_739_, v_a_729_);
lean_dec_ref(v_a_729_);
v___x_741_ = 0;
v___x_742_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set_uint8(v___x_742_, sizeof(void*)*1, v___x_741_);
v___x_743_ = lean_box(0);
v___x_744_ = lean_array_push(v_log_731_, v___x_742_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_744_);
v___x_746_ = v___x_737_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_744_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_trace_734_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_buildTime_735_);
lean_ctor_set_uint8(v_reuseFailAlloc_748_, sizeof(void*)*3, v_action_732_);
lean_ctor_set_uint8(v_reuseFailAlloc_748_, sizeof(void*)*3 + 1, v_wantsRebuild_733_);
v___x_746_ = v_reuseFailAlloc_748_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; 
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_743_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
return v___x_747_;
}
}
}
v___jp_750_:
{
lean_object* v_log_753_; uint8_t v_action_754_; uint8_t v_wantsRebuild_755_; lean_object* v_trace_756_; lean_object* v_buildTime_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_771_; 
v_log_753_ = lean_ctor_get(v_a_752_, 0);
v_action_754_ = lean_ctor_get_uint8(v_a_752_, sizeof(void*)*3);
v_wantsRebuild_755_ = lean_ctor_get_uint8(v_a_752_, sizeof(void*)*3 + 1);
v_trace_756_ = lean_ctor_get(v_a_752_, 1);
v_buildTime_757_ = lean_ctor_get(v_a_752_, 2);
v_isSharedCheck_771_ = !lean_is_exclusive(v_a_752_);
if (v_isSharedCheck_771_ == 0)
{
v___x_759_ = v_a_752_;
v_isShared_760_ = v_isSharedCheck_771_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_buildTime_757_);
lean_inc(v_trace_756_);
lean_inc(v_log_753_);
lean_dec(v_a_752_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_771_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_761_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1));
v___x_762_ = lean_string_append(v___x_761_, v_a_751_);
lean_dec_ref(v_a_751_);
v___x_763_ = 2;
v___x_764_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_764_, 0, v___x_762_);
lean_ctor_set_uint8(v___x_764_, sizeof(void*)*1, v___x_763_);
v___x_765_ = lean_box(0);
v___x_766_ = lean_array_push(v_log_753_, v___x_764_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_766_);
v___x_768_ = v___x_759_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_trace_756_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_buildTime_757_);
lean_ctor_set_uint8(v_reuseFailAlloc_770_, sizeof(void*)*3, v_action_754_);
lean_ctor_set_uint8(v_reuseFailAlloc_770_, sizeof(void*)*3 + 1, v_wantsRebuild_755_);
v___x_768_ = v_reuseFailAlloc_770_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; 
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_765_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* v_self_808_, lean_object* v_success_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
uint8_t v_success_boxed_817_; lean_object* v_res_818_; 
v_success_boxed_817_ = lean_unbox(v_success_809_);
v_res_818_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(v_self_808_, v_success_boxed_817_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* v_self_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_827_; 
lean_inc_ref(v_a_820_);
lean_inc_ref(v_self_819_);
v___x_827_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_842_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_a_829_ = lean_ctor_get(v___x_827_, 1);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_842_ == 0)
{
v___x_831_ = v___x_827_;
v_isShared_832_ = v_isSharedCheck_842_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_842_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___f_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v___f_833_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(v___f_833_, 0, v_self_819_);
v___x_834_ = l_Lake_instDataKindUnit;
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = 0;
v___x_837_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_838_ = l_Lake_Job_mapM___redArg(v___x_834_, v_a_828_, v___f_833_, v___x_835_, v___x_836_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v___x_837_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_838_);
v___x_840_ = v___x_831_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_a_829_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
else
{
lean_object* v_a_843_; lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec_ref(v_a_820_);
lean_dec_ref(v_self_819_);
v_a_843_ = lean_ctor_get(v___x_827_, 0);
v_a_844_ = lean_ctor_get(v___x_827_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_827_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_inc(v_a_843_);
lean_dec(v___x_827_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_843_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(lean_object* v_self_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec(v_a_855_);
lean_dec(v_a_854_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* v_self_861_, lean_object* v_as_862_, size_t v_sz_863_, size_t v_i_864_, lean_object* v_b_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
uint8_t v___x_873_; 
v___x_873_ = lean_usize_dec_lt(v_i_864_, v_sz_863_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec_ref(v___y_866_);
lean_dec_ref(v_self_861_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v_b_865_);
lean_ctor_set(v___x_874_, 1, v___y_871_);
return v___x_874_;
}
else
{
lean_object* v_a_875_; lean_object* v___x_876_; 
v_a_875_ = lean_array_uget_borrowed(v_as_862_, v_i_864_);
lean_inc_ref(v___y_866_);
lean_inc(v_a_875_);
lean_inc_ref(v_self_861_);
v___x_876_ = l_Lake_Package_fetchTargetJob(v_self_861_, v_a_875_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v_a_878_; lean_object* v___x_879_; size_t v___x_880_; size_t v___x_881_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
v_a_878_ = lean_ctor_get(v___x_876_, 1);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_876_, 2);
v___x_879_ = l_Lake_Job_mix___redArg(v_b_865_, v_a_877_);
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_add(v_i_864_, v___x_880_);
v_i_864_ = v___x_881_;
v_b_865_ = v___x_879_;
v___y_871_ = v_a_878_;
goto _start;
}
else
{
lean_object* v_a_883_; lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v___y_866_);
lean_dec_ref(v_b_865_);
lean_dec_ref(v_self_861_);
v_a_883_ = lean_ctor_get(v___x_876_, 0);
v_a_884_ = lean_ctor_get(v___x_876_, 1);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_876_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_inc(v_a_883_);
lean_dec(v___x_876_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_883_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* v_self_892_, lean_object* v_as_893_, lean_object* v_sz_894_, lean_object* v_i_895_, lean_object* v_b_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
size_t v_sz_boxed_904_; size_t v_i_boxed_905_; lean_object* v_res_906_; 
v_sz_boxed_904_ = lean_unbox_usize(v_sz_894_);
lean_dec(v_sz_894_);
v_i_boxed_905_ = lean_unbox_usize(v_i_895_);
lean_dec(v_i_895_);
v_res_906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_892_, v_as_893_, v_sz_boxed_904_, v_i_boxed_905_, v_b_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v_as_893_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object* v_config_907_, lean_object* v_self_908_, lean_object* v_____r_909_, lean_object* v_job_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_extraDepTargets_918_; size_t v_sz_919_; size_t v___x_920_; lean_object* v___x_921_; 
v_extraDepTargets_918_ = lean_ctor_get(v_config_907_, 2);
v_sz_919_ = lean_array_size(v_extraDepTargets_918_);
v___x_920_ = ((size_t)0ULL);
v___x_921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_908_, v_extraDepTargets_918_, v_sz_919_, v___x_920_, v_job_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object* v_config_922_, lean_object* v_self_923_, lean_object* v_____r_924_, lean_object* v_job_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(v_config_922_, v_self_923_, v_____r_924_, v_job_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v_config_922_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(uint8_t v___x_934_, lean_object* v_self_935_, lean_object* v_job_936_, lean_object* v___f_937_, lean_object* v___x_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
if (v___x_934_ == 0)
{
lean_object* v___x_946_; 
lean_inc_ref(v___y_939_);
v___x_946_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_935_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v_a_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
v_a_948_ = lean_ctor_get(v___x_946_, 1);
lean_inc(v_a_948_);
lean_dec_ref_known(v___x_946_, 2);
v___x_949_ = l_Lake_Job_add___redArg(v_job_936_, v_a_947_);
lean_inc_ref(v___y_943_);
lean_inc(v___y_942_);
lean_inc(v___y_941_);
lean_inc(v___y_940_);
v___x_950_ = lean_apply_9(v___f_937_, v___x_938_, v___x_949_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v_a_948_, lean_box(0));
return v___x_950_;
}
else
{
lean_dec_ref(v___y_939_);
lean_dec_ref(v___f_937_);
lean_dec_ref(v_job_936_);
return v___x_946_;
}
}
else
{
lean_object* v___x_951_; 
lean_dec_ref(v_self_935_);
lean_inc_ref(v___y_943_);
lean_inc(v___y_942_);
lean_inc(v___y_941_);
lean_inc(v___y_940_);
v___x_951_ = lean_apply_9(v___f_937_, v___x_938_, v_job_936_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, lean_box(0));
return v___x_951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* v___x_952_, lean_object* v_self_953_, lean_object* v_job_954_, lean_object* v___f_955_, lean_object* v___x_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
uint8_t v___x_4162__boxed_964_; lean_object* v_res_965_; 
v___x_4162__boxed_964_ = lean_unbox(v___x_952_);
v_res_965_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(v___x_4162__boxed_964_, v_self_953_, v_job_954_, v___f_955_, v___x_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec(v___y_959_);
lean_dec(v___y_958_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object* v_self_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_wsIdx_976_; lean_object* v_baseName_977_; lean_object* v_config_978_; lean_object* v___f_979_; lean_object* v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; uint8_t v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v_job_998_; uint8_t v___x_999_; lean_object* v___x_1000_; lean_object* v___y_1001_; lean_object* v___x_1002_; 
v_wsIdx_976_ = lean_ctor_get(v_self_968_, 0);
v_baseName_977_ = lean_ctor_get(v_self_968_, 1);
v_config_978_ = lean_ctor_get(v_self_968_, 6);
lean_inc_ref(v_self_968_);
lean_inc_ref(v_config_978_);
v___f_979_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed), 11, 2);
lean_closure_set(v___f_979_, 0, v_config_978_);
lean_closure_set(v___f_979_, 1, v_self_968_);
v___x_980_ = l_Lake_instDataKindUnit;
v___x_981_ = 1;
lean_inc(v_baseName_977_);
v___x_982_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_977_, v___x_981_);
v___x_983_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0));
v___x_984_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1));
v___x_985_ = lean_string_append(v___x_984_, v___x_982_);
v___x_986_ = lean_string_append(v___x_985_, v___x_983_);
v___x_987_ = lean_box(0);
v___x_988_ = lean_box(0);
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_991_ = 0;
v___x_992_ = 0;
v___x_993_ = l_Lake_BuildTrace_nil(v___x_986_);
v___x_994_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_994_, 0, v___x_990_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
lean_ctor_set(v___x_994_, 2, v___x_989_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*3, v___x_991_);
lean_ctor_set_uint8(v___x_994_, sizeof(void*)*3 + 1, v___x_992_);
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_987_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = lean_task_pure(v___x_995_);
v___x_997_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_job_998_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_998_, 0, v___x_996_);
lean_ctor_set(v_job_998_, 1, v___x_988_);
lean_ctor_set(v_job_998_, 2, v___x_997_);
lean_ctor_set_uint8(v_job_998_, sizeof(void*)*3, v___x_992_);
v___x_999_ = lean_nat_dec_eq(v_wsIdx_976_, v___x_989_);
v___x_1000_ = lean_box(v___x_999_);
v___y_1001_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 12, 5);
lean_closure_set(v___y_1001_, 0, v___x_1000_);
lean_closure_set(v___y_1001_, 1, v_self_968_);
lean_closure_set(v___y_1001_, 2, v_job_998_);
lean_closure_set(v___y_1001_, 3, v___f_979_);
lean_closure_set(v___y_1001_, 4, v___x_987_);
v___x_1002_ = l_Lake_ensureJob___redArg(v___x_980_, v___y_1001_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1028_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_a_1004_ = lean_ctor_get(v___x_1002_, 1);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1006_ = v___x_1002_;
v_isShared_1007_ = v_isSharedCheck_1028_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1028_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_task_1008_; lean_object* v_kind_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1026_; 
v_task_1008_ = lean_ctor_get(v_a_1003_, 0);
v_kind_1009_ = lean_ctor_get(v_a_1003_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_a_1003_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v_a_1003_, 2);
lean_dec(v_unused_1027_);
v___x_1011_ = v_a_1003_;
v_isShared_1012_ = v_isSharedCheck_1026_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_kind_1009_);
lean_inc(v_task_1008_);
lean_dec(v_a_1003_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1026_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v_registeredJobs_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v_job_1017_; 
v_registeredJobs_1013_ = lean_ctor_get(v_a_973_, 3);
v___x_1014_ = lean_st_ref_take(v_registeredJobs_1013_);
v___x_1015_ = lean_string_append(v___x_982_, v___x_983_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 2, v___x_1015_);
v_job_1017_ = v___x_1011_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_task_1008_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_kind_1009_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v___x_1015_);
v_job_1017_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
lean_ctor_set_uint8(v_job_1017_, sizeof(void*)*3, v___x_992_);
lean_inc_ref(v_job_1017_);
v___x_1018_ = l_Lake_Job_toOpaque___redArg(v_job_1017_);
v___x_1019_ = lean_array_push(v___x_1014_, v___x_1018_);
v___x_1020_ = lean_st_ref_set(v_registeredJobs_1013_, v___x_1019_);
v___x_1021_ = l_Lake_Job_renew___redArg(v_job_1017_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1021_);
v___x_1023_ = v___x_1006_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_a_1004_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_982_);
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(lean_object* v_self_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(v_self_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec(v_a_1031_);
return v_res_1037_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_box(0);
v___x_1039_ = l_Lean_Json_compress(v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t v_fmt_1040_){
_start:
{
if (v_fmt_1040_ == 0)
{
lean_object* v___x_1041_; 
v___x_1041_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_1043_){
_start:
{
uint8_t v_fmt_boxed_1044_; lean_object* v_res_1045_; 
v_fmt_boxed_1044_ = lean_unbox(v_fmt_1043_);
v_res_1045_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_boxed_1044_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(uint8_t v_fmt_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_1046_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object* v_fmt_1049_, lean_object* v_a_1050_){
_start:
{
uint8_t v_fmt_boxed_1051_; lean_object* v_res_1052_; 
v_fmt_boxed_1051_ = lean_unbox(v_fmt_1049_);
v_res_1052_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(v_fmt_boxed_1051_, v_a_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v___y_1053_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
uint8_t v___y_67__boxed_1058_; lean_object* v_res_1059_; 
v___y_67__boxed_1058_ = lean_unbox(v___y_1056_);
v_res_1059_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_67__boxed_1058_, v___y_1057_);
return v_res_1059_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1062_; uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___f_1062_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_1063_ = 1;
v___x_1064_ = l_Lake_instDataKindUnit;
v___x_1065_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__1));
v___x_1066_ = l_Lake_Package_keyword;
v___x_1067_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_1065_);
lean_ctor_set(v___x_1067_, 2, v___x_1064_);
lean_ctor_set(v___x_1067_, 3, v___f_1062_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*4, v___x_1063_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*4 + 1, v___x_1063_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_obj_once(&l_Lake_Package_extraDepFacetConfig___closed__2, &l_Lake_Package_extraDepFacetConfig___closed__2_once, _init_l_Lake_Package_extraDepFacetConfig___closed__2);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object* v_self_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_){
_start:
{
lean_object* v_origName_1088_; lean_object* v_dir_1089_; lean_object* v_scope_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v_origName_1088_ = lean_ctor_get(v_self_1084_, 3);
lean_inc(v_origName_1088_);
v_dir_1089_ = lean_ctor_get(v_self_1084_, 4);
lean_inc_ref(v_dir_1089_);
v_scope_1090_ = lean_ctor_get(v_self_1084_, 10);
lean_inc_ref(v_scope_1090_);
lean_dec_ref(v_self_1084_);
v___x_1091_ = lean_string_utf8_byte_size(v_scope_1090_);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_nat_dec_eq(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
v___x_1095_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1094_, v_dir_1089_);
if (lean_obj_tag(v___x_1095_) == 1)
{
lean_object* v_toContext_1096_; lean_object* v_lakeEnv_1097_; lean_object* v_log_1098_; uint8_t v_action_1099_; uint8_t v_wantsRebuild_1100_; lean_object* v_trace_1101_; lean_object* v_buildTime_1102_; lean_object* v_val_1103_; lean_object* v_toolchain_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v_toContext_1096_ = lean_ctor_get(v_a_1085_, 1);
v_lakeEnv_1097_ = lean_ctor_get(v_toContext_1096_, 0);
v_log_1098_ = lean_ctor_get(v_a_1086_, 0);
v_action_1099_ = lean_ctor_get_uint8(v_a_1086_, sizeof(void*)*3);
v_wantsRebuild_1100_ = lean_ctor_get_uint8(v_a_1086_, sizeof(void*)*3 + 1);
v_trace_1101_ = lean_ctor_get(v_a_1086_, 1);
v_buildTime_1102_ = lean_ctor_get(v_a_1086_, 2);
v_val_1103_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_val_1103_);
lean_dec_ref_known(v___x_1095_, 1);
v_toolchain_1104_ = lean_ctor_get(v_lakeEnv_1097_, 19);
v___x_1105_ = lean_string_utf8_byte_size(v_toolchain_1104_);
v___x_1106_ = lean_nat_dec_eq(v___x_1105_, v___x_1092_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1107_ = l_Lean_Name_toString(v_origName_1088_, v___x_1093_);
lean_inc_ref(v_lakeEnv_1097_);
v___x_1108_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_1097_, v_scope_1090_, v___x_1107_);
v___x_1109_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1));
v___x_1110_ = lean_string_append(v___x_1108_, v___x_1109_);
v___x_1111_ = lean_string_append(v___x_1110_, v_val_1103_);
lean_dec(v_val_1103_);
v___x_1112_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2));
v___x_1113_ = lean_string_append(v___x_1111_, v___x_1112_);
v___x_1114_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc_ref(v_toolchain_1104_);
v___x_1115_ = l_Lake_uriEncode(v_toolchain_1104_, v___x_1114_);
v___x_1116_ = lean_string_append(v___x_1113_, v___x_1115_);
lean_dec_ref(v___x_1115_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
lean_ctor_set(v___x_1117_, 1, v_a_1086_);
return v___x_1117_;
}
else
{
lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1128_; 
lean_inc(v_buildTime_1102_);
lean_inc_ref(v_trace_1101_);
lean_inc_ref(v_log_1098_);
lean_dec(v_val_1103_);
lean_dec_ref(v_scope_1090_);
lean_dec(v_origName_1088_);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_a_1086_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; lean_object* v_unused_1130_; lean_object* v_unused_1131_; 
v_unused_1129_ = lean_ctor_get(v_a_1086_, 2);
lean_dec(v_unused_1129_);
v_unused_1130_ = lean_ctor_get(v_a_1086_, 1);
lean_dec(v_unused_1130_);
v_unused_1131_ = lean_ctor_get(v_a_1086_, 0);
lean_dec(v_unused_1131_);
v___x_1119_ = v_a_1086_;
v_isShared_1120_ = v_isSharedCheck_1128_;
goto v_resetjp_1118_;
}
else
{
lean_dec(v_a_1086_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1128_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1121_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4));
v___x_1122_ = lean_array_get_size(v_log_1098_);
v___x_1123_ = lean_array_push(v_log_1098_, v___x_1121_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1123_);
v___x_1125_ = v___x_1119_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_trace_1101_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v_buildTime_1102_);
lean_ctor_set_uint8(v_reuseFailAlloc_1127_, sizeof(void*)*3, v_action_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1127_, sizeof(void*)*3 + 1, v_wantsRebuild_1100_);
v___x_1125_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1122_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
return v___x_1126_;
}
}
}
}
else
{
lean_object* v_log_1132_; uint8_t v_action_1133_; uint8_t v_wantsRebuild_1134_; lean_object* v_trace_1135_; lean_object* v_buildTime_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v___x_1095_);
lean_dec_ref(v_scope_1090_);
lean_dec(v_origName_1088_);
v_log_1132_ = lean_ctor_get(v_a_1086_, 0);
v_action_1133_ = lean_ctor_get_uint8(v_a_1086_, sizeof(void*)*3);
v_wantsRebuild_1134_ = lean_ctor_get_uint8(v_a_1086_, sizeof(void*)*3 + 1);
v_trace_1135_ = lean_ctor_get(v_a_1086_, 1);
v_buildTime_1136_ = lean_ctor_get(v_a_1086_, 2);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_a_1086_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1138_ = v_a_1086_;
v_isShared_1139_ = v_isSharedCheck_1147_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_buildTime_1136_);
lean_inc(v_trace_1135_);
lean_inc(v_log_1132_);
lean_dec(v_a_1086_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1147_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1140_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6));
v___x_1141_ = lean_array_get_size(v_log_1132_);
v___x_1142_ = lean_array_push(v_log_1132_, v___x_1140_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1142_);
v___x_1144_ = v___x_1138_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v_trace_1135_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_buildTime_1136_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, sizeof(void*)*3, v_action_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1146_, sizeof(void*)*3 + 1, v_wantsRebuild_1134_);
v___x_1144_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1141_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
return v___x_1145_;
}
}
}
}
else
{
lean_object* v_log_1148_; uint8_t v_action_1149_; uint8_t v_wantsRebuild_1150_; lean_object* v_trace_1151_; lean_object* v_buildTime_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1163_; 
lean_dec_ref(v_scope_1090_);
lean_dec_ref(v_dir_1089_);
lean_dec(v_origName_1088_);
v_log_1148_ = lean_ctor_get(v_a_1086_, 0);
v_action_1149_ = lean_ctor_get_uint8(v_a_1086_, sizeof(void*)*3);
v_wantsRebuild_1150_ = lean_ctor_get_uint8(v_a_1086_, sizeof(void*)*3 + 1);
v_trace_1151_ = lean_ctor_get(v_a_1086_, 1);
v_buildTime_1152_ = lean_ctor_get(v_a_1086_, 2);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_a_1086_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1154_ = v_a_1086_;
v_isShared_1155_ = v_isSharedCheck_1163_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_buildTime_1152_);
lean_inc(v_trace_1151_);
lean_inc(v_log_1148_);
lean_dec(v_a_1086_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1163_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1156_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8));
v___x_1157_ = lean_array_get_size(v_log_1148_);
v___x_1158_ = lean_array_push(v_log_1148_, v___x_1156_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1158_);
v___x_1160_ = v___x_1154_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_trace_1151_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v_buildTime_1152_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, sizeof(void*)*3, v_action_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1162_, sizeof(void*)*3 + 1, v_wantsRebuild_1150_);
v___x_1160_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1157_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
return v___x_1161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___boxed(lean_object* v_self_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1164_, v_a_1165_, v_a_1166_);
lean_dec_ref(v_a_1165_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object* v_self_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1169_, v_a_1174_, v_a_1175_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object* v_self_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(v_self_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object* v_self_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_rev_1200_; lean_object* v_log_1201_; uint8_t v_action_1202_; uint8_t v_wantsRebuild_1203_; lean_object* v_trace_1204_; lean_object* v_buildTime_1205_; lean_object* v_dir_1214_; lean_object* v_config_1215_; lean_object* v_remoteUrl_1216_; lean_object* v_buildArchive_1217_; lean_object* v___y_1219_; uint8_t v___y_1220_; lean_object* v___y_1221_; uint8_t v___y_1222_; lean_object* v___y_1223_; lean_object* v_val_1224_; lean_object* v___y_1244_; lean_object* v_releaseRepo_1275_; 
v_dir_1214_ = lean_ctor_get(v_self_1196_, 4);
lean_inc_ref(v_dir_1214_);
v_config_1215_ = lean_ctor_get(v_self_1196_, 6);
lean_inc_ref(v_config_1215_);
v_remoteUrl_1216_ = lean_ctor_get(v_self_1196_, 11);
lean_inc_ref(v_remoteUrl_1216_);
v_buildArchive_1217_ = lean_ctor_get(v_self_1196_, 21);
lean_inc_ref(v_buildArchive_1217_);
lean_dec_ref(v_self_1196_);
v_releaseRepo_1275_ = lean_ctor_get(v_config_1215_, 10);
lean_inc(v_releaseRepo_1275_);
lean_dec_ref(v_config_1215_);
if (lean_obj_tag(v_releaseRepo_1275_) == 0)
{
lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1276_ = lean_string_utf8_byte_size(v_remoteUrl_1216_);
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = lean_nat_dec_eq(v___x_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1279_, 0, v_remoteUrl_1216_);
v___y_1244_ = v___x_1279_;
goto v___jp_1243_;
}
else
{
lean_dec_ref(v_remoteUrl_1216_);
v___y_1244_ = v_releaseRepo_1275_;
goto v___jp_1243_;
}
}
else
{
lean_dec_ref(v_remoteUrl_1216_);
v___y_1244_ = v_releaseRepo_1275_;
goto v___jp_1243_;
}
v___jp_1199_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1206_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0));
v___x_1207_ = lean_string_append(v___x_1206_, v_rev_1200_);
lean_dec_ref(v_rev_1200_);
v___x_1208_ = 3;
v___x_1209_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set_uint8(v___x_1209_, sizeof(void*)*1, v___x_1208_);
v___x_1210_ = lean_array_get_size(v_log_1201_);
v___x_1211_ = lean_array_push(v_log_1201_, v___x_1209_);
v___x_1212_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v_trace_1204_);
lean_ctor_set(v___x_1212_, 2, v_buildTime_1205_);
lean_ctor_set_uint8(v___x_1212_, sizeof(void*)*3, v_action_1202_);
lean_ctor_set_uint8(v___x_1212_, sizeof(void*)*3 + 1, v_wantsRebuild_1203_);
v___x_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1210_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
return v___x_1213_;
}
v___jp_1218_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
lean_inc_ref(v_dir_1214_);
v___x_1226_ = l_Lake_GitRepo_findTag_x3f(v___x_1225_, v_dir_1214_);
if (lean_obj_tag(v___x_1226_) == 1)
{
lean_object* v_val_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec_ref(v_dir_1214_);
v_val_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_val_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v___x_1228_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1228_, 0, v___y_1219_);
lean_ctor_set(v___x_1228_, 1, v___y_1223_);
lean_ctor_set(v___x_1228_, 2, v___y_1221_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*3, v___y_1220_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*3 + 1, v___y_1222_);
v___x_1229_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1));
v___x_1230_ = lean_string_append(v_val_1224_, v___x_1229_);
v___x_1231_ = lean_string_append(v___x_1230_, v_val_1227_);
lean_dec(v_val_1227_);
v___x_1232_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2));
v___x_1233_ = lean_string_append(v___x_1231_, v___x_1232_);
v___x_1234_ = lean_string_append(v___x_1233_, v_buildArchive_1217_);
lean_dec_ref(v_buildArchive_1217_);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
lean_ctor_set(v___x_1235_, 1, v___x_1228_);
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; 
lean_dec(v___x_1226_);
lean_dec_ref(v_val_1224_);
lean_dec_ref(v_buildArchive_1217_);
v___x_1236_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1225_, v_dir_1214_);
if (lean_obj_tag(v___x_1236_) == 1)
{
lean_object* v_val_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_val_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_val_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1238_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3));
v___x_1239_ = lean_string_append(v___x_1238_, v_val_1237_);
lean_dec(v_val_1237_);
v___x_1240_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4));
v___x_1241_ = lean_string_append(v___x_1239_, v___x_1240_);
v_rev_1200_ = v___x_1241_;
v_log_1201_ = v___y_1219_;
v_action_1202_ = v___y_1220_;
v_wantsRebuild_1203_ = v___y_1222_;
v_trace_1204_ = v___y_1223_;
v_buildTime_1205_ = v___y_1221_;
goto v___jp_1199_;
}
else
{
lean_object* v___x_1242_; 
lean_dec(v___x_1236_);
v___x_1242_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_rev_1200_ = v___x_1242_;
v_log_1201_ = v___y_1219_;
v_action_1202_ = v___y_1220_;
v_wantsRebuild_1203_ = v___y_1222_;
v_trace_1204_ = v___y_1223_;
v_buildTime_1205_ = v___y_1221_;
goto v___jp_1199_;
}
}
}
v___jp_1243_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1245_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_dir_1214_);
v___x_1246_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v___x_1245_, v_dir_1214_);
if (lean_obj_tag(v___y_1244_) == 0)
{
if (lean_obj_tag(v___x_1246_) == 1)
{
lean_object* v_log_1247_; uint8_t v_action_1248_; uint8_t v_wantsRebuild_1249_; lean_object* v_trace_1250_; lean_object* v_buildTime_1251_; lean_object* v_val_1252_; 
v_log_1247_ = lean_ctor_get(v_a_1197_, 0);
lean_inc_ref(v_log_1247_);
v_action_1248_ = lean_ctor_get_uint8(v_a_1197_, sizeof(void*)*3);
v_wantsRebuild_1249_ = lean_ctor_get_uint8(v_a_1197_, sizeof(void*)*3 + 1);
v_trace_1250_ = lean_ctor_get(v_a_1197_, 1);
lean_inc_ref(v_trace_1250_);
v_buildTime_1251_ = lean_ctor_get(v_a_1197_, 2);
lean_inc(v_buildTime_1251_);
lean_dec_ref(v_a_1197_);
v_val_1252_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_val_1252_);
lean_dec_ref_known(v___x_1246_, 1);
v___y_1219_ = v_log_1247_;
v___y_1220_ = v_action_1248_;
v___y_1221_ = v_buildTime_1251_;
v___y_1222_ = v_wantsRebuild_1249_;
v___y_1223_ = v_trace_1250_;
v_val_1224_ = v_val_1252_;
goto v___jp_1218_;
}
else
{
lean_object* v_log_1253_; uint8_t v_action_1254_; uint8_t v_wantsRebuild_1255_; lean_object* v_trace_1256_; lean_object* v_buildTime_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v___x_1246_);
lean_dec_ref(v_buildArchive_1217_);
lean_dec_ref(v_dir_1214_);
v_log_1253_ = lean_ctor_get(v_a_1197_, 0);
v_action_1254_ = lean_ctor_get_uint8(v_a_1197_, sizeof(void*)*3);
v_wantsRebuild_1255_ = lean_ctor_get_uint8(v_a_1197_, sizeof(void*)*3 + 1);
v_trace_1256_ = lean_ctor_get(v_a_1197_, 1);
v_buildTime_1257_ = lean_ctor_get(v_a_1197_, 2);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_a_1197_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1259_ = v_a_1197_;
v_isShared_1260_ = v_isSharedCheck_1268_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_buildTime_1257_);
lean_inc(v_trace_1256_);
lean_inc(v_log_1253_);
lean_dec(v_a_1197_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1268_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1265_; 
v___x_1261_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6));
v___x_1262_ = lean_array_get_size(v_log_1253_);
v___x_1263_ = lean_array_push(v_log_1253_, v___x_1261_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1263_);
v___x_1265_ = v___x_1259_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_trace_1256_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_buildTime_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3, v_action_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*3 + 1, v_wantsRebuild_1255_);
v___x_1265_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1262_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
return v___x_1266_;
}
}
}
}
else
{
lean_object* v_log_1269_; uint8_t v_action_1270_; uint8_t v_wantsRebuild_1271_; lean_object* v_trace_1272_; lean_object* v_buildTime_1273_; lean_object* v_val_1274_; 
lean_dec(v___x_1246_);
v_log_1269_ = lean_ctor_get(v_a_1197_, 0);
lean_inc_ref(v_log_1269_);
v_action_1270_ = lean_ctor_get_uint8(v_a_1197_, sizeof(void*)*3);
v_wantsRebuild_1271_ = lean_ctor_get_uint8(v_a_1197_, sizeof(void*)*3 + 1);
v_trace_1272_ = lean_ctor_get(v_a_1197_, 1);
lean_inc_ref(v_trace_1272_);
v_buildTime_1273_ = lean_ctor_get(v_a_1197_, 2);
lean_inc(v_buildTime_1273_);
lean_dec_ref(v_a_1197_);
v_val_1274_ = lean_ctor_get(v___y_1244_, 0);
lean_inc(v_val_1274_);
lean_dec_ref_known(v___y_1244_, 1);
v___y_1219_ = v_log_1269_;
v___y_1220_ = v_action_1270_;
v___y_1221_ = v_buildTime_1273_;
v___y_1222_ = v_wantsRebuild_1271_;
v___y_1223_ = v_trace_1272_;
v_val_1224_ = v_val_1274_;
goto v___jp_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(lean_object* v_self_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1280_, v_a_1281_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object* v_self_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1284_, v_a_1290_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object* v_self_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(v_self_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(lean_object* v_val_1302_, lean_object* v_a_x3f_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; lean_object* v_log_1307_; uint8_t v_action_1308_; uint8_t v_wantsRebuild_1309_; lean_object* v_trace_1310_; lean_object* v_buildTime_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1322_; 
v___x_1306_ = lean_io_mono_ms_now();
v_log_1307_ = lean_ctor_get(v___y_1304_, 0);
v_action_1308_ = lean_ctor_get_uint8(v___y_1304_, sizeof(void*)*3);
v_wantsRebuild_1309_ = lean_ctor_get_uint8(v___y_1304_, sizeof(void*)*3 + 1);
v_trace_1310_ = lean_ctor_get(v___y_1304_, 1);
v_buildTime_1311_ = lean_ctor_get(v___y_1304_, 2);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___y_1304_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1313_ = v___y_1304_;
v_isShared_1314_ = v_isSharedCheck_1322_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_buildTime_1311_);
lean_inc(v_trace_1310_);
lean_inc(v_log_1307_);
lean_dec(v___y_1304_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1322_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1315_ = lean_nat_sub(v___x_1306_, v_val_1302_);
lean_dec(v___x_1306_);
v___x_1316_ = lean_box(0);
v___x_1317_ = lean_nat_add(v_buildTime_1311_, v___x_1315_);
lean_dec(v___x_1315_);
lean_dec(v_buildTime_1311_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 2, v___x_1317_);
v___x_1319_ = v___x_1313_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_log_1307_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_trace_1310_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v___x_1317_);
lean_ctor_set_uint8(v_reuseFailAlloc_1321_, sizeof(void*)*3, v_action_1308_);
lean_ctor_set_uint8(v_reuseFailAlloc_1321_, sizeof(void*)*3 + 1, v_wantsRebuild_1309_);
v___x_1319_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1316_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
return v___x_1320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0___boxed(lean_object* v_val_1323_, lean_object* v_a_x3f_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v_val_1323_, v_a_x3f_1324_, v___y_1325_);
lean_dec(v_a_x3f_1324_);
lean_dec(v_val_1323_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(lean_object* v_url_1333_, lean_object* v_archiveFile_1334_, lean_object* v_headers_1335_, lean_object* v_depTrace_1336_, lean_object* v_traceFile_1337_, uint8_t v_action_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_a_1343_; lean_object* v_a_1344_; lean_object* v_log_1347_; uint8_t v_action_1348_; uint8_t v_wantsRebuild_1349_; lean_object* v_trace_1350_; lean_object* v_buildTime_1351_; lean_object* v_toBuildConfig_1357_; lean_object* v_log_1358_; uint8_t v_action_1359_; uint8_t v_wantsRebuild_1360_; lean_object* v_trace_1361_; lean_object* v_buildTime_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1452_; 
v_toBuildConfig_1357_ = lean_ctor_get(v_a_1339_, 0);
v_log_1358_ = lean_ctor_get(v_a_1340_, 0);
v_action_1359_ = lean_ctor_get_uint8(v_a_1340_, sizeof(void*)*3);
v_wantsRebuild_1360_ = lean_ctor_get_uint8(v_a_1340_, sizeof(void*)*3 + 1);
v_trace_1361_ = lean_ctor_get(v_a_1340_, 1);
v_buildTime_1362_ = lean_ctor_get(v_a_1340_, 2);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_a_1340_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1364_ = v_a_1340_;
v_isShared_1365_ = v_isSharedCheck_1452_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_buildTime_1362_);
lean_inc(v_trace_1361_);
lean_inc(v_log_1358_);
lean_dec(v_a_1340_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1452_;
goto v_resetjp_1363_;
}
v___jp_1342_:
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1345_, 0, v_a_1343_);
lean_ctor_set(v___x_1345_, 1, v_a_1344_);
return v___x_1345_;
}
v___jp_1346_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1352_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1));
v___x_1353_ = lean_array_get_size(v_log_1347_);
v___x_1354_ = lean_array_push(v_log_1347_, v___x_1352_);
v___x_1355_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v_trace_1350_);
lean_ctor_set(v___x_1355_, 2, v_buildTime_1351_);
lean_ctor_set_uint8(v___x_1355_, sizeof(void*)*3, v_action_1348_);
lean_ctor_set_uint8(v___x_1355_, sizeof(void*)*3 + 1, v_wantsRebuild_1349_);
v___x_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1353_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
return v___x_1356_;
}
v_resetjp_1363_:
{
uint8_t v_noBuild_1366_; uint8_t v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v_noBuild_1366_ = lean_ctor_get_uint8(v_toBuildConfig_1357_, sizeof(void*)*3 + 2);
v___x_1367_ = l_Lake_JobAction_merge(v_action_1359_, v_action_1338_);
v___x_1368_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2));
lean_inc_ref(v_traceFile_1337_);
v___x_1369_ = l_System_FilePath_addExtension(v_traceFile_1337_, v___x_1368_);
if (v_noBuild_1366_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v_a_1373_; lean_object* v_a_1374_; 
v___x_1370_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1358_);
v___x_1371_ = l_Lake_download(v_url_1333_, v_archiveFile_1334_, v_headers_1335_, v_log_1358_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1378_; lean_object* v_a_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_a_1378_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1378_);
v_a_1379_ = lean_ctor_get(v___x_1371_, 1);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1371_, 2);
v___x_1380_ = lean_array_get_size(v_log_1358_);
lean_dec_ref(v_log_1358_);
v___x_1381_ = lean_array_get_size(v_a_1379_);
v___x_1382_ = l_Array_extract___redArg(v_a_1379_, v___x_1380_, v___x_1381_);
v___x_1383_ = lean_box(0);
v___x_1384_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1336_, v___x_1383_, v___x_1382_);
v___x_1385_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1337_, v___x_1384_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1422_; 
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; 
v_unused_1423_ = lean_ctor_get(v___x_1385_, 0);
lean_dec(v_unused_1423_);
v___x_1387_ = v___x_1385_;
v_isShared_1388_ = v_isSharedCheck_1422_;
goto v_resetjp_1386_;
}
else
{
lean_dec(v___x_1385_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1422_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lake_removeFileIfExists(v___x_1369_);
lean_dec_ref(v___x_1369_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1412_; 
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v___x_1389_, 0);
lean_dec(v_unused_1413_);
v___x_1391_ = v___x_1389_;
v_isShared_1392_ = v_isSharedCheck_1412_;
goto v_resetjp_1390_;
}
else
{
lean_dec(v___x_1389_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1412_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v_a_1379_);
v___x_1394_ = v___x_1364_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1379_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_trace_1361_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_buildTime_1362_);
lean_ctor_set_uint8(v_reuseFailAlloc_1411_, sizeof(void*)*3 + 1, v_wantsRebuild_1360_);
v___x_1394_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1396_; 
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*3, v___x_1367_);
lean_inc(v_a_1378_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v_a_1378_);
v___x_1396_ = v___x_1391_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1378_);
v___x_1396_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1398_; 
if (v_isShared_1388_ == 0)
{
lean_ctor_set_tag(v___x_1387_, 1);
lean_ctor_set(v___x_1387_, 0, v___x_1396_);
v___x_1398_ = v___x_1387_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1399_; lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
v___x_1399_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1370_, v___x_1398_, v___x_1394_);
lean_dec_ref(v___x_1398_);
lean_dec(v___x_1370_);
v_a_1400_ = lean_ctor_get(v___x_1399_, 1);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v___x_1399_, 0);
lean_dec(v_unused_1408_);
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v_a_1378_);
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1378_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
lean_del_object(v___x_1387_);
lean_dec(v_a_1378_);
v_a_1414_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1415_ = lean_io_error_to_string(v_a_1414_);
v___x_1416_ = 3;
v___x_1417_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1417_, 0, v___x_1415_);
lean_ctor_set_uint8(v___x_1417_, sizeof(void*)*1, v___x_1416_);
v___x_1418_ = lean_array_push(v_a_1379_, v___x_1417_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1418_);
v___x_1420_ = v___x_1364_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_trace_1361_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_buildTime_1362_);
lean_ctor_set_uint8(v_reuseFailAlloc_1421_, sizeof(void*)*3 + 1, v_wantsRebuild_1360_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_ctor_set_uint8(v___x_1420_, sizeof(void*)*3, v___x_1367_);
v_a_1373_ = v___x_1381_;
v_a_1374_ = v___x_1420_;
goto v___jp_1372_;
}
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
lean_dec(v_a_1378_);
lean_dec_ref(v___x_1369_);
v_a_1424_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1385_, 1);
v___x_1425_ = lean_io_error_to_string(v_a_1424_);
v___x_1426_ = 3;
v___x_1427_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1427_, 0, v___x_1425_);
lean_ctor_set_uint8(v___x_1427_, sizeof(void*)*1, v___x_1426_);
v___x_1428_ = lean_array_push(v_a_1379_, v___x_1427_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1428_);
v___x_1430_ = v___x_1364_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_trace_1361_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_buildTime_1362_);
lean_ctor_set_uint8(v_reuseFailAlloc_1431_, sizeof(void*)*3 + 1, v_wantsRebuild_1360_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_ctor_set_uint8(v___x_1430_, sizeof(void*)*3, v___x_1367_);
v_a_1373_ = v___x_1381_;
v_a_1374_ = v___x_1430_;
goto v___jp_1372_;
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v_a_1433_; lean_object* v___x_1435_; 
lean_dec_ref(v___x_1369_);
lean_dec_ref(v_log_1358_);
lean_dec_ref(v_traceFile_1337_);
v_a_1432_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1432_);
v_a_1433_ = lean_ctor_get(v___x_1371_, 1);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___x_1371_, 2);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v_a_1433_);
v___x_1435_ = v___x_1364_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1433_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_trace_1361_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_buildTime_1362_);
lean_ctor_set_uint8(v_reuseFailAlloc_1436_, sizeof(void*)*3 + 1, v_wantsRebuild_1360_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_ctor_set_uint8(v___x_1435_, sizeof(void*)*3, v___x_1367_);
v_a_1373_ = v_a_1432_;
v_a_1374_ = v___x_1435_;
goto v___jp_1372_;
}
}
v___jp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v_a_1377_; 
v___x_1375_ = lean_box(0);
v___x_1376_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1370_, v___x_1375_, v_a_1374_);
lean_dec(v___x_1370_);
v_a_1377_ = lean_ctor_get(v___x_1376_, 1);
lean_inc(v_a_1377_);
lean_dec_ref(v___x_1376_);
v_a_1343_ = v_a_1373_;
v_a_1344_ = v_a_1377_;
goto v___jp_1342_;
}
}
else
{
uint8_t v___x_1437_; 
lean_dec_ref(v_archiveFile_1334_);
lean_dec_ref(v_url_1333_);
v___x_1437_ = l_System_FilePath_pathExists(v_traceFile_1337_);
lean_dec_ref(v_traceFile_1337_);
if (v___x_1437_ == 0)
{
lean_dec_ref(v___x_1369_);
lean_del_object(v___x_1364_);
v_log_1347_ = v_log_1358_;
v_action_1348_ = v___x_1367_;
v_wantsRebuild_1349_ = v_noBuild_1366_;
v_trace_1350_ = v_trace_1361_;
v_buildTime_1351_ = v_buildTime_1362_;
goto v___jp_1346_;
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1438_ = lean_box(0);
v___x_1439_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1440_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1336_, v___x_1438_, v___x_1439_);
v___x_1441_ = l_Lake_BuildMetadata_writeFile(v___x_1369_, v___x_1440_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_dec_ref_known(v___x_1441_, 1);
lean_del_object(v___x_1364_);
v_log_1347_ = v_log_1358_;
v_action_1348_ = v___x_1367_;
v_wantsRebuild_1349_ = v_noBuild_1366_;
v_trace_1350_ = v_trace_1361_;
v_buildTime_1351_ = v_buildTime_1362_;
goto v___jp_1346_;
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1441_, 1);
v___x_1443_ = lean_io_error_to_string(v_a_1442_);
v___x_1444_ = 3;
v___x_1445_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set_uint8(v___x_1445_, sizeof(void*)*1, v___x_1444_);
v___x_1446_ = lean_array_get_size(v_log_1358_);
v___x_1447_ = lean_array_push(v_log_1358_, v___x_1445_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1447_);
v___x_1449_ = v___x_1364_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_trace_1361_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_buildTime_1362_);
v___x_1449_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; 
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3, v___x_1367_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 1, v_noBuild_1366_);
v___x_1450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1446_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
return v___x_1450_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___boxed(lean_object* v_url_1453_, lean_object* v_archiveFile_1454_, lean_object* v_headers_1455_, lean_object* v_depTrace_1456_, lean_object* v_traceFile_1457_, lean_object* v_action_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
uint8_t v_action_boxed_1462_; lean_object* v_res_1463_; 
v_action_boxed_1462_ = lean_unbox(v_action_1458_);
v_res_1463_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1453_, v_archiveFile_1454_, v_headers_1455_, v_depTrace_1456_, v_traceFile_1457_, v_action_boxed_1462_, v_a_1459_, v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec_ref(v_depTrace_1456_);
lean_dec_ref(v_headers_1455_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(lean_object* v_url_1464_, lean_object* v_archiveFile_1465_, lean_object* v_headers_1466_, lean_object* v_a_1467_, lean_object* v_depTrace_1468_, lean_object* v_traceFile_1469_, uint8_t v_action_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1464_, v_archiveFile_1465_, v_headers_1466_, v_depTrace_1468_, v_traceFile_1469_, v_action_1470_, v_a_1474_, v_a_1475_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___boxed(lean_object* v_url_1478_, lean_object* v_archiveFile_1479_, lean_object* v_headers_1480_, lean_object* v_a_1481_, lean_object* v_depTrace_1482_, lean_object* v_traceFile_1483_, lean_object* v_action_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_){
_start:
{
uint8_t v_action_boxed_1491_; lean_object* v_res_1492_; 
v_action_boxed_1491_ = lean_unbox(v_action_1484_);
v_res_1492_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(v_url_1478_, v_archiveFile_1479_, v_headers_1480_, v_a_1481_, v_depTrace_1482_, v_traceFile_1483_, v_action_boxed_1491_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_);
lean_dec_ref(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec(v_a_1485_);
lean_dec_ref(v_depTrace_1482_);
lean_dec_ref(v_a_1481_);
lean_dec_ref(v_headers_1480_);
return v_res_1492_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(lean_object* v_x_1493_, lean_object* v_x_1494_){
_start:
{
if (lean_obj_tag(v_x_1493_) == 0)
{
if (lean_obj_tag(v_x_1494_) == 0)
{
uint8_t v___x_1495_; 
v___x_1495_ = 1;
return v___x_1495_;
}
else
{
uint8_t v___x_1496_; 
v___x_1496_ = 0;
return v___x_1496_;
}
}
else
{
if (lean_obj_tag(v_x_1494_) == 0)
{
uint8_t v___x_1497_; 
v___x_1497_ = 0;
return v___x_1497_;
}
else
{
lean_object* v_val_1498_; lean_object* v_val_1499_; uint64_t v___x_1500_; uint64_t v___x_1501_; uint8_t v___x_1502_; 
v_val_1498_ = lean_ctor_get(v_x_1493_, 0);
v_val_1499_ = lean_ctor_get(v_x_1494_, 0);
v___x_1500_ = lean_unbox_uint64(v_val_1498_);
v___x_1501_ = lean_unbox_uint64(v_val_1499_);
v___x_1502_ = lean_uint64_dec_eq(v___x_1500_, v___x_1501_);
return v___x_1502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(lean_object* v_x_1503_, lean_object* v_x_1504_){
_start:
{
uint8_t v_res_1505_; lean_object* v_r_1506_; 
v_res_1505_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v_x_1503_, v_x_1504_);
lean_dec(v_x_1504_);
lean_dec(v_x_1503_);
v_r_1506_ = lean_box(v_res_1505_);
return v_r_1506_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object* v_info_1507_, lean_object* v_self_1508_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_io_metadata(v_info_1507_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v_modified_1512_; uint8_t v___x_1513_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref_known(v___x_1510_, 1);
v_modified_1512_ = lean_ctor_get(v_a_1511_, 1);
lean_inc_ref(v_modified_1512_);
lean_dec(v_a_1511_);
v___x_1513_ = l_IO_FS_instOrdSystemTime_ord(v_self_1508_, v_modified_1512_);
lean_dec_ref(v_modified_1512_);
if (v___x_1513_ == 0)
{
uint8_t v___x_1514_; 
v___x_1514_ = 1;
return v___x_1514_;
}
else
{
uint8_t v___x_1515_; 
v___x_1515_ = 0;
return v___x_1515_;
}
}
else
{
uint8_t v___x_1516_; 
lean_dec_ref_known(v___x_1510_, 1);
v___x_1516_ = 0;
return v___x_1516_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object* v_info_1517_, lean_object* v_self_1518_, lean_object* v_a_1519_){
_start:
{
uint8_t v_res_1520_; lean_object* v_r_1521_; 
v_res_1520_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1517_, v_self_1518_);
lean_dec_ref(v_self_1518_);
lean_dec_ref(v_info_1517_);
v_r_1521_ = lean_box(v_res_1520_);
return v_r_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(lean_object* v_info_1522_, lean_object* v_depTrace_1523_, lean_object* v_depHash_1524_, lean_object* v_oldTrace_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
uint64_t v_hash_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v_hash_1529_ = lean_ctor_get_uint64(v_depTrace_1523_, sizeof(void*)*3);
v___x_1530_ = lean_box_uint64(v_hash_1529_);
v___x_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
v___x_1532_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v___x_1531_, v_depHash_1524_);
lean_dec_ref_known(v___x_1531_, 1);
if (v___x_1532_ == 0)
{
lean_object* v_toBuildConfig_1533_; uint8_t v_oldMode_1534_; 
v_toBuildConfig_1533_ = lean_ctor_get(v_a_1526_, 0);
v_oldMode_1534_ = lean_ctor_get_uint8(v_toBuildConfig_1533_, sizeof(void*)*3);
if (v_oldMode_1534_ == 0)
{
uint8_t v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = 0;
v___x_1536_ = lean_box(v___x_1535_);
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
lean_ctor_set(v___x_1537_, 1, v_a_1527_);
return v___x_1537_;
}
else
{
uint8_t v___x_1538_; 
v___x_1538_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1522_, v_oldTrace_1525_);
if (v___x_1538_ == 0)
{
uint8_t v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1539_ = 0;
v___x_1540_ = lean_box(v___x_1539_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v_a_1527_);
return v___x_1541_;
}
else
{
uint8_t v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = 1;
v___x_1543_ = lean_box(v___x_1542_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1543_);
lean_ctor_set(v___x_1544_, 1, v_a_1527_);
return v___x_1544_;
}
}
}
else
{
uint8_t v___x_1545_; 
v___x_1545_ = l_System_FilePath_pathExists(v_info_1522_);
if (v___x_1545_ == 0)
{
uint8_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = 0;
v___x_1547_ = lean_box(v___x_1546_);
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
lean_ctor_set(v___x_1548_, 1, v_a_1527_);
return v___x_1548_;
}
else
{
uint8_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = 2;
v___x_1550_ = lean_box(v___x_1549_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
lean_ctor_set(v___x_1551_, 1, v_a_1527_);
return v___x_1551_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(lean_object* v_info_1552_, lean_object* v_depTrace_1553_, lean_object* v_depHash_1554_, lean_object* v_oldTrace_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1552_, v_depTrace_1553_, v_depHash_1554_, v_oldTrace_1555_, v_a_1556_, v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec_ref(v_oldTrace_1555_);
lean_dec(v_depHash_1554_);
lean_dec_ref(v_depTrace_1553_);
lean_dec_ref(v_info_1552_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(lean_object* v_a_1560_, lean_object* v_info_1561_, lean_object* v_depTrace_1562_, lean_object* v_savedTrace_1563_, lean_object* v_oldTrace_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_){
_start:
{
if (lean_obj_tag(v_savedTrace_1563_) == 2)
{
lean_object* v_data_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1622_; 
v_data_1571_ = lean_ctor_get(v_savedTrace_1563_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_savedTrace_1563_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1573_ = v_savedTrace_1563_;
v_isShared_1574_ = v_isSharedCheck_1622_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_data_1571_);
lean_dec(v_savedTrace_1563_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1622_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
uint64_t v_depHash_1575_; lean_object* v_log_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
v_depHash_1575_ = lean_ctor_get_uint64(v_data_1571_, sizeof(void*)*3);
v_log_1576_ = lean_ctor_get(v_data_1571_, 2);
lean_inc_ref(v_log_1576_);
lean_dec_ref(v_data_1571_);
v___x_1577_ = lean_box_uint64(v_depHash_1575_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 1);
lean_ctor_set(v___x_1573_, 0, v___x_1577_);
v___x_1579_ = v___x_1573_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1580_; lean_object* v_a_1581_; lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1620_; 
v___x_1580_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1561_, v_depTrace_1562_, v___x_1579_, v_oldTrace_1564_, v_a_1568_, v_a_1569_);
lean_dec_ref(v___x_1579_);
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_a_1582_ = lean_ctor_get(v___x_1580_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1584_ = v___x_1580_;
v_isShared_1585_ = v_isSharedCheck_1620_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1620_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___y_1587_; uint8_t v___x_1591_; uint8_t v___x_1592_; uint8_t v___x_1593_; uint8_t v___x_1594_; 
v___x_1591_ = 0;
v___x_1592_ = lean_unbox(v_a_1581_);
v___x_1593_ = l_Lake_instDecidableEqOutputStatus(v___x_1592_, v___x_1591_);
v___x_1594_ = lean_bool_not(v___x_1593_);
if (v___x_1594_ == 0)
{
lean_dec_ref(v_log_1576_);
v___y_1587_ = v_a_1582_;
goto v___jp_1586_;
}
else
{
lean_object* v_log_1595_; uint8_t v_action_1596_; uint8_t v_wantsRebuild_1597_; lean_object* v_trace_1598_; lean_object* v_buildTime_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1619_; 
v_log_1595_ = lean_ctor_get(v_a_1582_, 0);
v_action_1596_ = lean_ctor_get_uint8(v_a_1582_, sizeof(void*)*3);
v_wantsRebuild_1597_ = lean_ctor_get_uint8(v_a_1582_, sizeof(void*)*3 + 1);
v_trace_1598_ = lean_ctor_get(v_a_1582_, 1);
v_buildTime_1599_ = lean_ctor_get(v_a_1582_, 2);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_a_1582_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1601_ = v_a_1582_;
v_isShared_1602_ = v_isSharedCheck_1619_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_buildTime_1599_);
lean_inc(v_trace_1598_);
lean_inc(v_log_1595_);
lean_dec(v_a_1582_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1619_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
uint8_t v___x_1603_; uint8_t v___x_1604_; lean_object* v___x_1606_; 
v___x_1603_ = 2;
v___x_1604_ = l_Lake_JobAction_merge(v_action_1596_, v___x_1603_);
if (v_isShared_1602_ == 0)
{
v___x_1606_ = v___x_1601_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_log_1595_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_trace_1598_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v_buildTime_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1618_, sizeof(void*)*3 + 1, v_wantsRebuild_1597_);
v___x_1606_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1607_; 
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*3, v___x_1604_);
v___x_1607_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1576_, v_a_1560_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v___x_1606_);
lean_dec_ref(v_log_1576_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 1);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 2);
v___y_1587_ = v_a_1608_;
goto v___jp_1586_;
}
else
{
lean_object* v_a_1609_; lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_del_object(v___x_1584_);
lean_dec(v_a_1581_);
v_a_1609_ = lean_ctor_get(v___x_1607_, 0);
v_a_1610_ = lean_ctor_get(v___x_1607_, 1);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1607_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_inc(v_a_1609_);
lean_dec(v___x_1607_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1609_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
}
v___jp_1586_:
{
lean_object* v___x_1589_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 1, v___y_1587_);
v___x_1589_ = v___x_1584_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1581_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v___y_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_1623_; uint8_t v_oldMode_1624_; 
lean_dec(v_savedTrace_1563_);
v_toBuildConfig_1623_ = lean_ctor_get(v_a_1568_, 0);
v_oldMode_1624_ = lean_ctor_get_uint8(v_toBuildConfig_1623_, sizeof(void*)*3);
if (v_oldMode_1624_ == 0)
{
uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1625_ = 0;
v___x_1626_ = lean_box(v___x_1625_);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v_a_1569_);
return v___x_1627_;
}
else
{
uint8_t v___x_1628_; 
v___x_1628_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1561_, v_oldTrace_1564_);
if (v___x_1628_ == 0)
{
uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1629_ = 0;
v___x_1630_ = lean_box(v___x_1629_);
v___x_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v_a_1569_);
return v___x_1631_;
}
else
{
uint8_t v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = 1;
v___x_1633_ = lean_box(v___x_1632_);
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
lean_ctor_set(v___x_1634_, 1, v_a_1569_);
return v___x_1634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object* v_a_1635_, lean_object* v_info_1636_, lean_object* v_depTrace_1637_, lean_object* v_savedTrace_1638_, lean_object* v_oldTrace_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_1635_, v_info_1636_, v_depTrace_1637_, v_savedTrace_1638_, v_oldTrace_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec_ref(v_oldTrace_1639_);
lean_dec_ref(v_depTrace_1637_);
lean_dec_ref(v_info_1636_);
lean_dec_ref(v_a_1635_);
return v_res_1646_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_unsigned_to_nat(0u);
v___x_1652_ = lean_nat_to_int(v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4(void){
_start:
{
uint32_t v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = 0;
v___x_1654_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3);
v___x_1655_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
lean_ctor_set_uint32(v___x_1655_, sizeof(void*)*1, v___x_1653_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(lean_object* v_self_1656_, lean_object* v_url_1657_, lean_object* v_archiveFile_1658_, lean_object* v_headers_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_a_1668_; lean_object* v_a_1669_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; uint8_t v___y_1675_; uint8_t v___y_1676_; lean_object* v___y_1677_; uint8_t v_a_1703_; lean_object* v_a_1704_; lean_object* v_log_1723_; uint8_t v_action_1724_; uint8_t v_wantsRebuild_1725_; lean_object* v_trace_1726_; lean_object* v_buildTime_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1765_; 
v_log_1723_ = lean_ctor_get(v_a_1665_, 0);
v_action_1724_ = lean_ctor_get_uint8(v_a_1665_, sizeof(void*)*3);
v_wantsRebuild_1725_ = lean_ctor_get_uint8(v_a_1665_, sizeof(void*)*3 + 1);
v_trace_1726_ = lean_ctor_get(v_a_1665_, 1);
v_buildTime_1727_ = lean_ctor_get(v_a_1665_, 2);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_a_1665_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1729_ = v_a_1665_;
v_isShared_1730_ = v_isSharedCheck_1765_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_buildTime_1727_);
lean_inc(v_trace_1726_);
lean_inc(v_log_1723_);
lean_dec(v_a_1665_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1765_;
goto v_resetjp_1728_;
}
v___jp_1667_:
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1670_, 0, v_a_1668_);
lean_ctor_set(v___x_1670_, 1, v_a_1669_);
return v___x_1670_;
}
v___jp_1671_:
{
uint8_t v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; uint8_t v___x_1681_; 
v___x_1678_ = 1;
v___x_1679_ = l_Lake_untar(v_archiveFile_1658_, v___y_1677_, v___x_1678_, v___y_1674_);
v___x_1680_ = 3;
v___x_1681_ = l_Lake_JobAction_merge(v___y_1676_, v___x_1680_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1682_; lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1691_; 
v_a_1682_ = lean_ctor_get(v___x_1679_, 0);
v_a_1683_ = lean_ctor_get(v___x_1679_, 1);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1685_ = v___x_1679_;
v_isShared_1686_ = v_isSharedCheck_1691_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_inc(v_a_1682_);
lean_dec(v___x_1679_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1691_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1687_, 0, v_a_1683_);
lean_ctor_set(v___x_1687_, 1, v___y_1672_);
lean_ctor_set(v___x_1687_, 2, v___y_1673_);
lean_ctor_set_uint8(v___x_1687_, sizeof(void*)*3, v___x_1681_);
lean_ctor_set_uint8(v___x_1687_, sizeof(void*)*3 + 1, v___y_1675_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 1, v___x_1687_);
v___x_1689_ = v___x_1685_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1682_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1701_; 
v_a_1692_ = lean_ctor_get(v___x_1679_, 0);
v_a_1693_ = lean_ctor_get(v___x_1679_, 1);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1695_ = v___x_1679_;
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_inc(v_a_1692_);
lean_dec(v___x_1679_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1701_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1697_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1697_, 0, v_a_1693_);
lean_ctor_set(v___x_1697_, 1, v___y_1672_);
lean_ctor_set(v___x_1697_, 2, v___y_1673_);
lean_ctor_set_uint8(v___x_1697_, sizeof(void*)*3, v___x_1681_);
lean_ctor_set_uint8(v___x_1697_, sizeof(void*)*3 + 1, v___y_1675_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 1, v___x_1697_);
v___x_1699_ = v___x_1695_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1692_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
v___jp_1702_:
{
lean_object* v_config_1705_; lean_object* v_dir_1706_; lean_object* v_buildDir_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; 
v_config_1705_ = lean_ctor_get(v_self_1656_, 6);
lean_inc_ref(v_config_1705_);
v_dir_1706_ = lean_ctor_get(v_self_1656_, 4);
lean_inc_ref(v_dir_1706_);
lean_dec_ref(v_self_1656_);
v_buildDir_1707_ = lean_ctor_get(v_config_1705_, 5);
lean_inc_ref(v_buildDir_1707_);
lean_dec_ref(v_config_1705_);
v___x_1708_ = l_System_FilePath_normalize(v_buildDir_1707_);
v___x_1709_ = l_Lake_joinRelative(v_dir_1706_, v___x_1708_);
v___x_1710_ = l_System_FilePath_pathExists(v___x_1709_);
if (v_a_1703_ == 0)
{
lean_object* v_log_1711_; uint8_t v_action_1712_; uint8_t v_wantsRebuild_1713_; lean_object* v_trace_1714_; lean_object* v_buildTime_1715_; 
v_log_1711_ = lean_ctor_get(v_a_1704_, 0);
lean_inc_ref(v_log_1711_);
v_action_1712_ = lean_ctor_get_uint8(v_a_1704_, sizeof(void*)*3);
v_wantsRebuild_1713_ = lean_ctor_get_uint8(v_a_1704_, sizeof(void*)*3 + 1);
v_trace_1714_ = lean_ctor_get(v_a_1704_, 1);
lean_inc_ref(v_trace_1714_);
v_buildTime_1715_ = lean_ctor_get(v_a_1704_, 2);
lean_inc(v_buildTime_1715_);
lean_dec_ref(v_a_1704_);
v___y_1672_ = v_trace_1714_;
v___y_1673_ = v_buildTime_1715_;
v___y_1674_ = v_log_1711_;
v___y_1675_ = v_wantsRebuild_1713_;
v___y_1676_ = v_action_1712_;
v___y_1677_ = v___x_1709_;
goto v___jp_1671_;
}
else
{
if (v___x_1710_ == 0)
{
lean_object* v_log_1716_; uint8_t v_action_1717_; uint8_t v_wantsRebuild_1718_; lean_object* v_trace_1719_; lean_object* v_buildTime_1720_; 
v_log_1716_ = lean_ctor_get(v_a_1704_, 0);
lean_inc_ref(v_log_1716_);
v_action_1717_ = lean_ctor_get_uint8(v_a_1704_, sizeof(void*)*3);
v_wantsRebuild_1718_ = lean_ctor_get_uint8(v_a_1704_, sizeof(void*)*3 + 1);
v_trace_1719_ = lean_ctor_get(v_a_1704_, 1);
lean_inc_ref(v_trace_1719_);
v_buildTime_1720_ = lean_ctor_get(v_a_1704_, 2);
lean_inc(v_buildTime_1720_);
lean_dec_ref(v_a_1704_);
v___y_1672_ = v_trace_1719_;
v___y_1673_ = v_buildTime_1720_;
v___y_1674_ = v_log_1716_;
v___y_1675_ = v_wantsRebuild_1718_;
v___y_1676_ = v_action_1717_;
v___y_1677_ = v___x_1709_;
goto v___jp_1671_;
}
else
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec_ref(v___x_1709_);
lean_dec_ref(v_archiveFile_1658_);
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v_a_1704_);
return v___x_1722_;
}
}
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v_traceFile_1732_; lean_object* v___x_1733_; 
v___x_1731_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0));
lean_inc_ref(v_archiveFile_1658_);
v_traceFile_1732_ = l_System_FilePath_addExtension(v_archiveFile_1658_, v___x_1731_);
lean_inc_ref(v_traceFile_1732_);
v___x_1733_ = l_Lake_readTraceFile(v_traceFile_1732_, v_log_1723_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v_a_1735_; lean_object* v___x_1736_; uint64_t v___x_1737_; uint64_t v___x_1738_; uint64_t v_depTrace_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
v_a_1735_ = lean_ctor_get(v___x_1733_, 1);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1733_, 2);
v___x_1736_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1));
v___x_1737_ = l_Lake_Hash_nil;
v___x_1738_ = lean_string_hash(v_url_1657_);
v_depTrace_1739_ = lean_uint64_mix_hash(v___x_1737_, v___x_1738_);
v___x_1740_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2));
v___x_1741_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
v___x_1742_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1742_, 0, v___x_1740_);
lean_ctor_set(v___x_1742_, 1, v___x_1736_);
lean_ctor_set(v___x_1742_, 2, v___x_1741_);
lean_ctor_set_uint64(v___x_1742_, sizeof(void*)*3, v_depTrace_1739_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v_a_1735_);
v___x_1744_ = v___x_1729_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1735_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_trace_1726_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_buildTime_1727_);
lean_ctor_set_uint8(v_reuseFailAlloc_1759_, sizeof(void*)*3, v_action_1724_);
lean_ctor_set_uint8(v_reuseFailAlloc_1759_, sizeof(void*)*3 + 1, v_wantsRebuild_1725_);
v___x_1744_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_1660_, v_archiveFile_1658_, v___x_1742_, v_a_1734_, v___x_1741_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v___x_1744_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v_a_1747_; uint8_t v___x_1748_; uint8_t v___x_1749_; uint8_t v___x_1750_; uint8_t v___x_1751_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
v_a_1747_ = lean_ctor_get(v___x_1745_, 1);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1745_, 2);
v___x_1748_ = 0;
v___x_1749_ = lean_unbox(v_a_1746_);
lean_dec(v_a_1746_);
v___x_1750_ = l_Lake_instDecidableEqOutputStatus(v___x_1749_, v___x_1748_);
v___x_1751_ = lean_bool_not(v___x_1750_);
if (v___x_1751_ == 0)
{
uint8_t v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = 4;
lean_inc_ref(v_archiveFile_1658_);
v___x_1753_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1657_, v_archiveFile_1658_, v_headers_1659_, v___x_1742_, v_traceFile_1732_, v___x_1752_, v_a_1664_, v_a_1747_);
lean_dec_ref_known(v___x_1742_, 3);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 1);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 2);
v_a_1703_ = v___x_1751_;
v_a_1704_ = v_a_1754_;
goto v___jp_1702_;
}
else
{
lean_object* v_a_1755_; lean_object* v_a_1756_; 
lean_dec_ref(v_archiveFile_1658_);
lean_dec_ref(v_self_1656_);
v_a_1755_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1755_);
v_a_1756_ = lean_ctor_get(v___x_1753_, 1);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1753_, 2);
v_a_1668_ = v_a_1755_;
v_a_1669_ = v_a_1756_;
goto v___jp_1667_;
}
}
else
{
lean_dec_ref_known(v___x_1742_, 3);
lean_dec_ref(v_traceFile_1732_);
lean_dec_ref(v_url_1657_);
v_a_1703_ = v___x_1751_;
v_a_1704_ = v_a_1747_;
goto v___jp_1702_;
}
}
else
{
lean_object* v_a_1757_; lean_object* v_a_1758_; 
lean_dec_ref_known(v___x_1742_, 3);
lean_dec_ref(v_traceFile_1732_);
lean_dec_ref(v_archiveFile_1658_);
lean_dec_ref(v_url_1657_);
lean_dec_ref(v_self_1656_);
v_a_1757_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1757_);
v_a_1758_ = lean_ctor_get(v___x_1745_, 1);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1745_, 2);
v_a_1668_ = v_a_1757_;
v_a_1669_ = v_a_1758_;
goto v___jp_1667_;
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v_a_1761_; lean_object* v___x_1763_; 
lean_dec_ref(v_traceFile_1732_);
lean_dec_ref(v_archiveFile_1658_);
lean_dec_ref(v_url_1657_);
lean_dec_ref(v_self_1656_);
v_a_1760_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1760_);
v_a_1761_ = lean_ctor_get(v___x_1733_, 1);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1733_, 2);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v_a_1761_);
v___x_1763_ = v___x_1729_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1761_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_trace_1726_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_buildTime_1727_);
lean_ctor_set_uint8(v_reuseFailAlloc_1764_, sizeof(void*)*3, v_action_1724_);
lean_ctor_set_uint8(v_reuseFailAlloc_1764_, sizeof(void*)*3 + 1, v_wantsRebuild_1725_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
v_a_1668_ = v_a_1760_;
v_a_1669_ = v___x_1763_;
goto v___jp_1667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object* v_self_1766_, lean_object* v_url_1767_, lean_object* v_archiveFile_1768_, lean_object* v_headers_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_self_1766_, v_url_1767_, v_archiveFile_1768_, v_headers_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec(v_a_1771_);
lean_dec_ref(v_a_1770_);
lean_dec_ref(v_headers_1769_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object* v_a_1778_, lean_object* v_info_1779_, lean_object* v_depTrace_1780_, lean_object* v_depHash_1781_, lean_object* v_oldTrace_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1779_, v_depTrace_1780_, v_depHash_1781_, v_oldTrace_1782_, v_a_1786_, v_a_1787_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object* v_a_1790_, lean_object* v_info_1791_, lean_object* v_depTrace_1792_, lean_object* v_depHash_1793_, lean_object* v_oldTrace_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_1790_, v_info_1791_, v_depTrace_1792_, v_depHash_1793_, v_oldTrace_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_oldTrace_1794_);
lean_dec(v_depHash_1793_);
lean_dec_ref(v_depTrace_1792_);
lean_dec_ref(v_info_1791_);
lean_dec_ref(v_a_1790_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_getUrl_1802_, lean_object* v_pkg_1803_, lean_object* v_archiveFile_1804_, lean_object* v_headers_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
uint8_t v_r_1814_; lean_object* v___y_1815_; lean_object* v_a_1819_; lean_object* v___x_1835_; 
lean_inc_ref(v___y_1810_);
lean_inc(v___y_1809_);
lean_inc(v___y_1808_);
lean_inc(v___y_1807_);
lean_inc_ref(v___y_1806_);
lean_inc_ref(v_pkg_1803_);
v___x_1835_ = lean_apply_8(v_getUrl_1802_, v_pkg_1803_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, lean_box(0));
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v_a_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
v_a_1837_ = lean_ctor_get(v___x_1835_, 1);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1835_, 2);
lean_inc_ref(v_pkg_1803_);
v___x_1838_ = lean_apply_1(v_archiveFile_1804_, v_pkg_1803_);
v___x_1839_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_1803_, v_a_1836_, v___x_1838_, v_headers_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v_a_1837_);
lean_dec_ref(v___y_1806_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; uint8_t v___x_1841_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 1);
lean_inc(v_a_1840_);
lean_dec_ref_known(v___x_1839_, 2);
v___x_1841_ = 1;
v_r_1814_ = v___x_1841_;
v___y_1815_ = v_a_1840_;
goto v___jp_1813_;
}
else
{
lean_object* v_a_1842_; 
v_a_1842_ = lean_ctor_get(v___x_1839_, 1);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1839_, 2);
v_a_1819_ = v_a_1842_;
goto v___jp_1818_;
}
}
else
{
lean_object* v_a_1843_; 
lean_dec_ref(v___y_1806_);
lean_dec_ref(v_archiveFile_1804_);
lean_dec_ref(v_pkg_1803_);
v_a_1843_ = lean_ctor_get(v___x_1835_, 1);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1835_, 2);
v_a_1819_ = v_a_1843_;
goto v___jp_1818_;
}
v___jp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = lean_box(v_r_1814_);
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
lean_ctor_set(v___x_1817_, 1, v___y_1815_);
return v___x_1817_;
}
v___jp_1818_:
{
lean_object* v_log_1820_; uint8_t v_action_1821_; uint8_t v_wantsRebuild_1822_; lean_object* v_trace_1823_; lean_object* v_buildTime_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1834_; 
v_log_1820_ = lean_ctor_get(v_a_1819_, 0);
v_action_1821_ = lean_ctor_get_uint8(v_a_1819_, sizeof(void*)*3);
v_wantsRebuild_1822_ = lean_ctor_get_uint8(v_a_1819_, sizeof(void*)*3 + 1);
v_trace_1823_ = lean_ctor_get(v_a_1819_, 1);
v_buildTime_1824_ = lean_ctor_get(v_a_1819_, 2);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_a_1819_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1826_ = v_a_1819_;
v_isShared_1827_ = v_isSharedCheck_1834_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_buildTime_1824_);
lean_inc(v_trace_1823_);
lean_inc(v_log_1820_);
lean_dec(v_a_1819_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1834_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
uint8_t v___x_1828_; uint8_t v___x_1829_; lean_object* v___x_1831_; 
v___x_1828_ = 4;
v___x_1829_ = l_Lake_JobAction_merge(v_action_1821_, v___x_1828_);
if (v_isShared_1827_ == 0)
{
v___x_1831_ = v___x_1826_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_log_1820_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_trace_1823_);
lean_ctor_set(v_reuseFailAlloc_1833_, 2, v_buildTime_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1833_, sizeof(void*)*3 + 1, v_wantsRebuild_1822_);
v___x_1831_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
uint8_t v___x_1832_; 
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*3, v___x_1829_);
v___x_1832_ = 0;
v_r_1814_ = v___x_1832_;
v___y_1815_ = v___x_1831_;
goto v___jp_1813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_getUrl_1844_, lean_object* v_pkg_1845_, lean_object* v_archiveFile_1846_, lean_object* v_headers_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(v_getUrl_1844_, v_pkg_1845_, v_archiveFile_1846_, v_headers_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v_headers_1847_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* v_getUrl_1856_, lean_object* v_archiveFile_1857_, lean_object* v_headers_1858_, lean_object* v___x_1859_, lean_object* v_facet_1860_, lean_object* v_pkg_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___f_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_inc_ref(v_pkg_1861_);
v___f_1869_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1869_, 0, v_getUrl_1856_);
lean_closure_set(v___f_1869_, 1, v_pkg_1861_);
lean_closure_set(v___f_1869_, 2, v_archiveFile_1857_);
lean_closure_set(v___f_1869_, 3, v_headers_1858_);
v___x_1870_ = lean_unsigned_to_nat(0u);
v___x_1871_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_1859_);
v___x_1872_ = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(v___x_1872_, 0, lean_box(0));
lean_closure_set(v___x_1872_, 1, v___x_1859_);
lean_closure_set(v___x_1872_, 2, v___f_1869_);
lean_closure_set(v___x_1872_, 3, v___x_1870_);
lean_closure_set(v___x_1872_, 4, v___x_1871_);
v___x_1873_ = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM___boxed), 9, 2);
lean_closure_set(v___x_1873_, 0, lean_box(0));
lean_closure_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM___boxed), 9, 2);
lean_closure_set(v___x_1874_, 0, lean_box(0));
lean_closure_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = l_Lake_ensureJob___redArg(v___x_1859_, v___x_1874_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1908_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
v_a_1877_ = lean_ctor_get(v___x_1875_, 1);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1879_ = v___x_1875_;
v_isShared_1880_ = v_isSharedCheck_1908_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_inc(v_a_1876_);
lean_dec(v___x_1875_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1908_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_task_1881_; lean_object* v_kind_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1906_; 
v_task_1881_ = lean_ctor_get(v_a_1876_, 0);
v_kind_1882_ = lean_ctor_get(v_a_1876_, 1);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_a_1876_);
if (v_isSharedCheck_1906_ == 0)
{
lean_object* v_unused_1907_; 
v_unused_1907_ = lean_ctor_get(v_a_1876_, 2);
lean_dec(v_unused_1907_);
v___x_1884_ = v_a_1876_;
v_isShared_1885_ = v_isSharedCheck_1906_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_kind_1882_);
lean_inc(v_task_1881_);
lean_dec(v_a_1876_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1906_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v_registeredJobs_1886_; lean_object* v___x_1887_; lean_object* v_baseName_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v_job_1897_; 
v_registeredJobs_1886_ = lean_ctor_get(v___y_1866_, 3);
v___x_1887_ = lean_st_ref_take(v_registeredJobs_1886_);
v_baseName_1888_ = lean_ctor_get(v_pkg_1861_, 1);
lean_inc(v_baseName_1888_);
lean_dec_ref(v_pkg_1861_);
v___x_1889_ = 1;
v___x_1890_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1888_, v___x_1889_);
v___x_1891_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1892_ = lean_string_append(v___x_1890_, v___x_1891_);
v___x_1893_ = l_Lake_Name_eraseHead(v_facet_1860_);
v___x_1894_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1893_, v___x_1889_);
v___x_1895_ = lean_string_append(v___x_1892_, v___x_1894_);
lean_dec_ref(v___x_1894_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 2, v___x_1895_);
v_job_1897_ = v___x_1884_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_task_1881_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_kind_1882_);
lean_ctor_set(v_reuseFailAlloc_1905_, 2, v___x_1895_);
v_job_1897_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
lean_ctor_set_uint8(v_job_1897_, sizeof(void*)*3, v___x_1889_);
lean_inc_ref(v_job_1897_);
v___x_1898_ = l_Lake_Job_toOpaque___redArg(v_job_1897_);
v___x_1899_ = lean_array_push(v___x_1887_, v___x_1898_);
v___x_1900_ = lean_st_ref_set(v_registeredJobs_1886_, v___x_1899_);
v___x_1901_ = l_Lake_Job_renew___redArg(v_job_1897_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1901_);
v___x_1903_ = v___x_1879_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_a_1877_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_1861_);
lean_dec(v_facet_1860_);
return v___x_1875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v_getUrl_1909_, lean_object* v_archiveFile_1910_, lean_object* v_headers_1911_, lean_object* v___x_1912_, lean_object* v_facet_1913_, lean_object* v_pkg_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_1909_, v_archiveFile_1910_, v_headers_1911_, v___x_1912_, v_facet_1913_, v_pkg_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec(v___y_1916_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object* v_facet_1930_, lean_object* v_archiveFile_1931_, lean_object* v_getUrl_1932_, lean_object* v_headers_1933_){
_start:
{
lean_object* v___x_1934_; lean_object* v___f_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1934_ = l_Lake_instDataKindBool;
v___f_1935_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_1935_, 0, v_getUrl_1932_);
lean_closure_set(v___f_1935_, 1, v_archiveFile_1931_);
lean_closure_set(v___f_1935_, 2, v_headers_1933_);
lean_closure_set(v___f_1935_, 3, v___x_1934_);
lean_closure_set(v___f_1935_, 4, v_facet_1930_);
v___x_1936_ = l_Lake_Package_keyword;
v___x_1937_ = 1;
v___x_1938_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_1939_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1939_, 0, v___x_1936_);
lean_ctor_set(v___x_1939_, 1, v___f_1935_);
lean_ctor_set(v___x_1939_, 2, v___x_1934_);
lean_ctor_set(v___x_1939_, 3, v___x_1938_);
lean_ctor_set_uint8(v___x_1939_, sizeof(void*)*4, v___x_1937_);
lean_ctor_set_uint8(v___x_1939_, sizeof(void*)*4 + 1, v___x_1937_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* v_facet_1940_, lean_object* v_archiveFile_1941_, lean_object* v_getUrl_1942_, lean_object* v_headers_1943_, lean_object* v_inst_1944_){
_start:
{
lean_object* v___x_1945_; lean_object* v___f_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1945_ = l_Lake_instDataKindBool;
v___f_1946_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_1946_, 0, v_getUrl_1942_);
lean_closure_set(v___f_1946_, 1, v_archiveFile_1941_);
lean_closure_set(v___f_1946_, 2, v_headers_1943_);
lean_closure_set(v___f_1946_, 3, v___x_1945_);
lean_closure_set(v___f_1946_, 4, v_facet_1940_);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_what_1952_, lean_object* v_baseName_1953_, lean_object* v_optFacet_1954_, uint8_t v_success_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_a_1964_; lean_object* v_a_1965_; 
if (v_success_1955_ == 0)
{
lean_object* v_toBuildConfig_1986_; uint8_t v_verbosity_1987_; uint8_t v___x_1988_; uint8_t v___x_1989_; 
v_toBuildConfig_1986_ = lean_ctor_get(v___y_1960_, 0);
v_verbosity_1987_ = lean_ctor_get_uint8(v_toBuildConfig_1986_, sizeof(void*)*3 + 3);
v___x_1988_ = 2;
v___x_1989_ = l_Lake_instDecidableEqVerbosity(v_verbosity_1987_, v___x_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; 
lean_dec(v_optFacet_1954_);
lean_dec(v_baseName_1953_);
v___x_1990_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_1964_ = v___x_1990_;
v_a_1965_ = v___y_1961_;
goto v___jp_1963_;
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1991_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1992_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1953_, v___x_1989_);
v___x_1993_ = lean_string_append(v___x_1991_, v___x_1992_);
lean_dec_ref(v___x_1992_);
v___x_1994_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1995_ = lean_string_append(v___x_1993_, v___x_1994_);
v___x_1996_ = l_Lake_Name_eraseHead(v_optFacet_1954_);
v___x_1997_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1996_, v___x_1989_);
v___x_1998_ = lean_string_append(v___x_1995_, v___x_1997_);
lean_dec_ref(v___x_1997_);
v___x_1999_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2000_ = lean_string_append(v___x_1998_, v___x_1999_);
v_a_1964_ = v___x_2000_;
v_a_1965_ = v___y_1961_;
goto v___jp_1963_;
}
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_dec(v_optFacet_1954_);
lean_dec(v_baseName_1953_);
v___x_2001_ = lean_box(0);
v___x_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
lean_ctor_set(v___x_2002_, 1, v___y_1961_);
return v___x_2002_;
}
v___jp_1963_:
{
lean_object* v_log_1966_; uint8_t v_action_1967_; uint8_t v_wantsRebuild_1968_; lean_object* v_trace_1969_; lean_object* v_buildTime_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1985_; 
v_log_1966_ = lean_ctor_get(v_a_1965_, 0);
v_action_1967_ = lean_ctor_get_uint8(v_a_1965_, sizeof(void*)*3);
v_wantsRebuild_1968_ = lean_ctor_get_uint8(v_a_1965_, sizeof(void*)*3 + 1);
v_trace_1969_ = lean_ctor_get(v_a_1965_, 1);
v_buildTime_1970_ = lean_ctor_get(v_a_1965_, 2);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_a_1965_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1972_ = v_a_1965_;
v_isShared_1973_ = v_isSharedCheck_1985_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_buildTime_1970_);
lean_inc(v_trace_1969_);
lean_inc(v_log_1966_);
lean_dec(v_a_1965_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1985_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1974_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0));
v___x_1975_ = lean_string_append(v___x_1974_, v_what_1952_);
v___x_1976_ = lean_string_append(v___x_1975_, v_a_1964_);
lean_dec_ref(v_a_1964_);
v___x_1977_ = 3;
v___x_1978_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1978_, 0, v___x_1976_);
lean_ctor_set_uint8(v___x_1978_, sizeof(void*)*1, v___x_1977_);
v___x_1979_ = lean_array_get_size(v_log_1966_);
v___x_1980_ = lean_array_push(v_log_1966_, v___x_1978_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1980_);
v___x_1982_ = v___x_1972_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_trace_1969_);
lean_ctor_set(v_reuseFailAlloc_1984_, 2, v_buildTime_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1984_, sizeof(void*)*3, v_action_1967_);
lean_ctor_set_uint8(v_reuseFailAlloc_1984_, sizeof(void*)*3 + 1, v_wantsRebuild_1968_);
v___x_1982_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1983_; 
v___x_1983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1979_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
return v___x_1983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_what_2003_, lean_object* v_baseName_2004_, lean_object* v_optFacet_2005_, lean_object* v_success_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
uint8_t v_success_boxed_2014_; lean_object* v_res_2015_; 
v_success_boxed_2014_ = lean_unbox(v_success_2006_);
v_res_2015_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(v_what_2003_, v_baseName_2004_, v_optFacet_2005_, v_success_boxed_2014_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec_ref(v_what_2003_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object* v___x_2016_, lean_object* v___x_2017_, lean_object* v___f_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; 
lean_inc_ref(v___y_2019_);
lean_inc_ref(v___y_2023_);
lean_inc(v___y_2022_);
lean_inc(v___y_2021_);
lean_inc(v___y_2020_);
v___x_2026_ = lean_apply_7(v___y_2019_, v___x_2016_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, lean_box(0));
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2039_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_a_2028_ = lean_ctor_get(v___x_2026_, 1);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2030_ = v___x_2026_;
v_isShared_2031_ = v_isSharedCheck_2039_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2039_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; uint8_t v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = 0;
v___x_2034_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2035_ = l_Lake_Job_mapM___redArg(v___x_2017_, v_a_2027_, v___f_2018_, v___x_2032_, v___x_2033_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___x_2034_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2035_);
v___x_2037_ = v___x_2030_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v_a_2028_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v___y_2019_);
lean_dec_ref(v___f_2018_);
lean_dec(v___x_2017_);
v_a_2040_ = lean_ctor_get(v___x_2026_, 0);
v_a_2041_ = lean_ctor_get(v___x_2026_, 1);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2026_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_inc(v_a_2040_);
lean_dec(v___x_2026_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2040_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v___x_2049_, lean_object* v___x_2050_, lean_object* v___f_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(v___x_2049_, v___x_2050_, v___f_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec(v___y_2053_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object* v_what_2060_, lean_object* v_optFacet_2061_, lean_object* v___x_2062_, lean_object* v_facet_2063_, lean_object* v_pkg_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_baseName_2072_; lean_object* v_keyName_2073_; lean_object* v___f_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___f_2078_; lean_object* v___x_2079_; 
v_baseName_2072_ = lean_ctor_get(v_pkg_2064_, 1);
lean_inc_n(v_baseName_2072_, 2);
v_keyName_2073_ = lean_ctor_get(v_pkg_2064_, 2);
lean_inc(v_optFacet_2061_);
v___f_2074_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2074_, 0, v_what_2060_);
lean_closure_set(v___f_2074_, 1, v_baseName_2072_);
lean_closure_set(v___f_2074_, 2, v_optFacet_2061_);
lean_inc(v_keyName_2073_);
v___x_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2075_, 0, v_keyName_2073_);
v___x_2076_ = l_Lake_Package_keyword;
v___x_2077_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2075_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
lean_ctor_set(v___x_2077_, 2, v_pkg_2064_);
lean_ctor_set(v___x_2077_, 3, v_optFacet_2061_);
lean_inc(v___x_2062_);
v___f_2078_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2078_, 0, v___x_2077_);
lean_closure_set(v___f_2078_, 1, v___x_2062_);
lean_closure_set(v___f_2078_, 2, v___f_2074_);
v___x_2079_ = l_Lake_ensureJob___redArg(v___x_2062_, v___f_2078_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2112_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_a_2081_ = lean_ctor_get(v___x_2079_, 1);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2083_ = v___x_2079_;
v_isShared_2084_ = v_isSharedCheck_2112_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2112_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_task_2085_; lean_object* v_kind_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2110_; 
v_task_2085_ = lean_ctor_get(v_a_2080_, 0);
v_kind_2086_ = lean_ctor_get(v_a_2080_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_a_2080_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; 
v_unused_2111_ = lean_ctor_get(v_a_2080_, 2);
lean_dec(v_unused_2111_);
v___x_2088_ = v_a_2080_;
v_isShared_2089_ = v_isSharedCheck_2110_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_kind_2086_);
lean_inc(v_task_2085_);
lean_dec(v_a_2080_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2110_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v_registeredJobs_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; lean_object* v_job_2101_; 
v_registeredJobs_2090_ = lean_ctor_get(v___y_2069_, 3);
v___x_2091_ = lean_st_ref_take(v_registeredJobs_2090_);
v___x_2092_ = 1;
v___x_2093_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2072_, v___x_2092_);
v___x_2094_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2095_ = lean_string_append(v___x_2093_, v___x_2094_);
v___x_2096_ = l_Lake_Name_eraseHead(v_facet_2063_);
v___x_2097_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2096_, v___x_2092_);
v___x_2098_ = lean_string_append(v___x_2095_, v___x_2097_);
lean_dec_ref(v___x_2097_);
v___x_2099_ = 0;
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 2, v___x_2098_);
v_job_2101_ = v___x_2088_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_task_2085_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_kind_2086_);
lean_ctor_set(v_reuseFailAlloc_2109_, 2, v___x_2098_);
v_job_2101_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2107_; 
lean_ctor_set_uint8(v_job_2101_, sizeof(void*)*3, v___x_2099_);
lean_inc_ref(v_job_2101_);
v___x_2102_ = l_Lake_Job_toOpaque___redArg(v_job_2101_);
v___x_2103_ = lean_array_push(v___x_2091_, v___x_2102_);
v___x_2104_ = lean_st_ref_set(v_registeredJobs_2090_, v___x_2103_);
v___x_2105_ = l_Lake_Job_renew___redArg(v_job_2101_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2105_);
v___x_2107_ = v___x_2083_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_a_2081_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2072_);
lean_dec(v_facet_2063_);
return v___x_2079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object* v_what_2113_, lean_object* v_optFacet_2114_, lean_object* v___x_2115_, lean_object* v_facet_2116_, lean_object* v_pkg_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(v_what_2113_, v_optFacet_2114_, v___x_2115_, v_facet_2116_, v_pkg_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec(v___y_2119_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object* v_facet_2133_, lean_object* v_optFacet_2134_, lean_object* v_what_2135_){
_start:
{
lean_object* v___x_2136_; lean_object* v___f_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2136_ = l_Lake_instDataKindUnit;
v___f_2137_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2137_, 0, v_what_2135_);
lean_closure_set(v___f_2137_, 1, v_optFacet_2134_);
lean_closure_set(v___f_2137_, 2, v___x_2136_);
lean_closure_set(v___f_2137_, 3, v_facet_2133_);
v___x_2138_ = l_Lake_Package_keyword;
v___x_2139_ = 1;
v___x_2140_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2141_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2141_, 0, v___x_2138_);
lean_ctor_set(v___x_2141_, 1, v___f_2137_);
lean_ctor_set(v___x_2141_, 2, v___x_2136_);
lean_ctor_set(v___x_2141_, 3, v___x_2140_);
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*4, v___x_2139_);
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*4 + 1, v___x_2139_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* v_facet_2142_, lean_object* v_optFacet_2143_, lean_object* v_what_2144_, lean_object* v_inst_2145_, lean_object* v_inst_2146_){
_start:
{
lean_object* v___x_2147_; lean_object* v___f_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2147_ = l_Lake_instDataKindUnit;
v___f_2148_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2148_, 0, v_what_2144_);
lean_closure_set(v___f_2148_, 1, v_optFacet_2143_);
lean_closure_set(v___f_2148_, 2, v___x_2147_);
lean_closure_set(v___f_2148_, 3, v_facet_2142_);
v___x_2149_ = l_Lake_Package_keyword;
v___x_2150_ = 1;
v___x_2151_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2152_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2152_, 0, v___x_2149_);
lean_ctor_set(v___x_2152_, 1, v___f_2148_);
lean_ctor_set(v___x_2152_, 2, v___x_2147_);
lean_ctor_set(v___x_2152_, 3, v___x_2151_);
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*4, v___x_2150_);
lean_ctor_set_uint8(v___x_2152_, sizeof(void*)*4 + 1, v___x_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* v_baseName_2154_, lean_object* v___x_2155_, uint8_t v_success_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_a_2165_; lean_object* v_a_2166_; 
if (v_success_2156_ == 0)
{
lean_object* v_toBuildConfig_2186_; uint8_t v_verbosity_2187_; uint8_t v___x_2188_; uint8_t v___x_2189_; 
v_toBuildConfig_2186_ = lean_ctor_get(v___y_2161_, 0);
v_verbosity_2187_ = lean_ctor_get_uint8(v_toBuildConfig_2186_, sizeof(void*)*3 + 3);
v___x_2188_ = 2;
v___x_2189_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2187_, v___x_2188_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; 
lean_dec(v___x_2155_);
lean_dec(v_baseName_2154_);
v___x_2190_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2165_ = v___x_2190_;
v_a_2166_ = v___y_2162_;
goto v___jp_2164_;
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2191_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2192_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2154_, v___x_2189_);
v___x_2193_ = lean_string_append(v___x_2191_, v___x_2192_);
lean_dec_ref(v___x_2192_);
v___x_2194_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2195_ = lean_string_append(v___x_2193_, v___x_2194_);
v___x_2196_ = l_Lake_Name_eraseHead(v___x_2155_);
v___x_2197_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2196_, v___x_2189_);
v___x_2198_ = lean_string_append(v___x_2195_, v___x_2197_);
lean_dec_ref(v___x_2197_);
v___x_2199_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2200_ = lean_string_append(v___x_2198_, v___x_2199_);
v_a_2165_ = v___x_2200_;
v_a_2166_ = v___y_2162_;
goto v___jp_2164_;
}
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec(v___x_2155_);
lean_dec(v_baseName_2154_);
v___x_2201_ = lean_box(0);
v___x_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v___y_2162_);
return v___x_2202_;
}
v___jp_2164_:
{
lean_object* v_log_2167_; uint8_t v_action_2168_; uint8_t v_wantsRebuild_2169_; lean_object* v_trace_2170_; lean_object* v_buildTime_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2185_; 
v_log_2167_ = lean_ctor_get(v_a_2166_, 0);
v_action_2168_ = lean_ctor_get_uint8(v_a_2166_, sizeof(void*)*3);
v_wantsRebuild_2169_ = lean_ctor_get_uint8(v_a_2166_, sizeof(void*)*3 + 1);
v_trace_2170_ = lean_ctor_get(v_a_2166_, 1);
v_buildTime_2171_ = lean_ctor_get(v_a_2166_, 2);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_a_2166_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2173_ = v_a_2166_;
v_isShared_2174_ = v_isSharedCheck_2185_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_buildTime_2171_);
lean_inc(v_trace_2170_);
lean_inc(v_log_2167_);
lean_dec(v_a_2166_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2185_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2175_ = ((lean_object*)(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0));
v___x_2176_ = lean_string_append(v___x_2175_, v_a_2165_);
lean_dec_ref(v_a_2165_);
v___x_2177_ = 3;
v___x_2178_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2178_, 0, v___x_2176_);
lean_ctor_set_uint8(v___x_2178_, sizeof(void*)*1, v___x_2177_);
v___x_2179_ = lean_array_get_size(v_log_2167_);
v___x_2180_ = lean_array_push(v_log_2167_, v___x_2178_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2180_);
v___x_2182_ = v___x_2173_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_trace_2170_);
lean_ctor_set(v_reuseFailAlloc_2184_, 2, v_buildTime_2171_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, sizeof(void*)*3, v_action_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2184_, sizeof(void*)*3 + 1, v_wantsRebuild_2169_);
v___x_2182_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2179_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
return v___x_2183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object* v_baseName_2203_, lean_object* v___x_2204_, lean_object* v_success_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
uint8_t v_success_boxed_2213_; lean_object* v_res_2214_; 
v_success_boxed_2213_ = lean_unbox(v_success_2205_);
v_res_2214_ = l_Lake_Package_buildCacheFacetConfig___lam__1(v_baseName_2203_, v___x_2204_, v_success_boxed_2213_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* v___x_2215_, lean_object* v___x_2216_, lean_object* v___x_2217_, lean_object* v_pkg_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_baseName_2226_; lean_object* v_keyName_2227_; lean_object* v___f_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___f_2232_; lean_object* v___x_2233_; 
v_baseName_2226_ = lean_ctor_get(v_pkg_2218_, 1);
lean_inc_n(v_baseName_2226_, 2);
v_keyName_2227_ = lean_ctor_get(v_pkg_2218_, 2);
lean_inc(v___x_2215_);
v___f_2228_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2228_, 0, v_baseName_2226_);
lean_closure_set(v___f_2228_, 1, v___x_2215_);
lean_inc(v_keyName_2227_);
v___x_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_keyName_2227_);
v___x_2230_ = l_Lake_Package_keyword;
v___x_2231_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2229_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
lean_ctor_set(v___x_2231_, 2, v_pkg_2218_);
lean_ctor_set(v___x_2231_, 3, v___x_2215_);
lean_inc(v___x_2216_);
v___f_2232_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2232_, 0, v___x_2231_);
lean_closure_set(v___f_2232_, 1, v___x_2216_);
lean_closure_set(v___f_2232_, 2, v___f_2228_);
v___x_2233_ = l_Lake_ensureJob___redArg(v___x_2216_, v___f_2232_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2266_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
v_a_2235_ = lean_ctor_get(v___x_2233_, 1);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2237_ = v___x_2233_;
v_isShared_2238_ = v_isSharedCheck_2266_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_inc(v_a_2234_);
lean_dec(v___x_2233_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2266_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v_task_2239_; lean_object* v_kind_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2264_; 
v_task_2239_ = lean_ctor_get(v_a_2234_, 0);
v_kind_2240_ = lean_ctor_get(v_a_2234_, 1);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_a_2234_);
if (v_isSharedCheck_2264_ == 0)
{
lean_object* v_unused_2265_; 
v_unused_2265_ = lean_ctor_get(v_a_2234_, 2);
lean_dec(v_unused_2265_);
v___x_2242_ = v_a_2234_;
v_isShared_2243_ = v_isSharedCheck_2264_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_kind_2240_);
lean_inc(v_task_2239_);
lean_dec(v_a_2234_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2264_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v_registeredJobs_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; uint8_t v___x_2253_; lean_object* v_job_2255_; 
v_registeredJobs_2244_ = lean_ctor_get(v___y_2223_, 3);
v___x_2245_ = lean_st_ref_take(v_registeredJobs_2244_);
v___x_2246_ = 1;
v___x_2247_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2226_, v___x_2246_);
v___x_2248_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2249_ = lean_string_append(v___x_2247_, v___x_2248_);
v___x_2250_ = l_Lake_Name_eraseHead(v___x_2217_);
v___x_2251_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2250_, v___x_2246_);
v___x_2252_ = lean_string_append(v___x_2249_, v___x_2251_);
lean_dec_ref(v___x_2251_);
v___x_2253_ = 0;
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 2, v___x_2252_);
v_job_2255_ = v___x_2242_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_task_2239_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_kind_2240_);
lean_ctor_set(v_reuseFailAlloc_2263_, 2, v___x_2252_);
v_job_2255_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2261_; 
lean_ctor_set_uint8(v_job_2255_, sizeof(void*)*3, v___x_2253_);
lean_inc_ref(v_job_2255_);
v___x_2256_ = l_Lake_Job_toOpaque___redArg(v_job_2255_);
v___x_2257_ = lean_array_push(v___x_2245_, v___x_2256_);
v___x_2258_ = lean_st_ref_set(v_registeredJobs_2244_, v___x_2257_);
v___x_2259_ = l_Lake_Job_renew___redArg(v_job_2255_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 0, v___x_2259_);
v___x_2261_ = v___x_2237_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_a_2235_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2226_);
lean_dec(v___x_2217_);
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object* v___x_2267_, lean_object* v___x_2268_, lean_object* v___x_2269_, lean_object* v_pkg_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lake_Package_buildCacheFacetConfig___lam__2(v___x_2267_, v___x_2268_, v___x_2269_, v_pkg_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec(v___y_2272_);
return v_res_2278_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___f_2282_; 
v___x_2279_ = l_Lake_Package_buildCacheFacet;
v___x_2280_ = l_Lake_instDataKindUnit;
v___x_2281_ = l_Lake_Package_optBuildCacheFacet;
v___f_2282_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2282_, 0, v___x_2281_);
lean_closure_set(v___f_2282_, 1, v___x_2280_);
lean_closure_set(v___f_2282_, 2, v___x_2279_);
return v___f_2282_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___f_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___f_2283_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2284_ = 1;
v___x_2285_ = l_Lake_instDataKindUnit;
v___f_2286_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__0, &l_Lake_Package_buildCacheFacetConfig___closed__0_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__0);
v___x_2287_ = l_Lake_Package_keyword;
v___x_2288_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
lean_ctor_set(v___x_2288_, 1, v___f_2286_);
lean_ctor_set(v___x_2288_, 2, v___x_2285_);
lean_ctor_set(v___x_2288_, 3, v___f_2283_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*4, v___x_2284_);
lean_ctor_set_uint8(v___x_2288_, sizeof(void*)*4 + 1, v___x_2284_);
return v___x_2288_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig(void){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__1, &l_Lake_Package_buildCacheFacetConfig___closed__1_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__1);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* v_pkg_2291_, lean_object* v___x_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
uint8_t v_r_2301_; lean_object* v___y_2302_; lean_object* v_a_2306_; lean_object* v___x_2322_; 
lean_inc_ref(v_pkg_2291_);
v___x_2322_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_pkg_2291_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v_a_2324_; lean_object* v_dir_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
v_a_2324_ = lean_ctor_get(v___x_2322_, 1);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2322_, 2);
v_dir_2325_ = lean_ctor_get(v_pkg_2291_, 4);
v___x_2326_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_2325_);
v___x_2327_ = l_Lake_joinRelative(v_dir_2325_, v___x_2326_);
v___x_2328_ = ((lean_object*)(l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0));
v___x_2329_ = l_Lake_joinRelative(v___x_2327_, v___x_2328_);
v___x_2330_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2291_, v_a_2323_, v___x_2329_, v___x_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v_a_2324_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; uint8_t v___x_2332_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 1);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2330_, 2);
v___x_2332_ = 1;
v_r_2301_ = v___x_2332_;
v___y_2302_ = v_a_2331_;
goto v___jp_2300_;
}
else
{
lean_object* v_a_2333_; 
v_a_2333_ = lean_ctor_get(v___x_2330_, 1);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2330_, 2);
v_a_2306_ = v_a_2333_;
goto v___jp_2305_;
}
}
else
{
lean_object* v_a_2334_; 
lean_dec_ref(v_pkg_2291_);
v_a_2334_ = lean_ctor_get(v___x_2322_, 1);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2322_, 2);
v_a_2306_ = v_a_2334_;
goto v___jp_2305_;
}
v___jp_2300_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_box(v_r_2301_);
v___x_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
lean_ctor_set(v___x_2304_, 1, v___y_2302_);
return v___x_2304_;
}
v___jp_2305_:
{
lean_object* v_log_2307_; uint8_t v_action_2308_; uint8_t v_wantsRebuild_2309_; lean_object* v_trace_2310_; lean_object* v_buildTime_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2321_; 
v_log_2307_ = lean_ctor_get(v_a_2306_, 0);
v_action_2308_ = lean_ctor_get_uint8(v_a_2306_, sizeof(void*)*3);
v_wantsRebuild_2309_ = lean_ctor_get_uint8(v_a_2306_, sizeof(void*)*3 + 1);
v_trace_2310_ = lean_ctor_get(v_a_2306_, 1);
v_buildTime_2311_ = lean_ctor_get(v_a_2306_, 2);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_a_2306_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2313_ = v_a_2306_;
v_isShared_2314_ = v_isSharedCheck_2321_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_buildTime_2311_);
lean_inc(v_trace_2310_);
lean_inc(v_log_2307_);
lean_dec(v_a_2306_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2321_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
uint8_t v___x_2315_; uint8_t v___x_2316_; lean_object* v___x_2318_; 
v___x_2315_ = 4;
v___x_2316_ = l_Lake_JobAction_merge(v_action_2308_, v___x_2315_);
if (v_isShared_2314_ == 0)
{
v___x_2318_ = v___x_2313_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_log_2307_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_trace_2310_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_buildTime_2311_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*3 + 1, v_wantsRebuild_2309_);
v___x_2318_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
uint8_t v___x_2319_; 
lean_ctor_set_uint8(v___x_2318_, sizeof(void*)*3, v___x_2316_);
v___x_2319_ = 0;
v_r_2301_ = v___x_2319_;
v___y_2302_ = v___x_2318_;
goto v___jp_2300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* v_pkg_2335_, lean_object* v___x_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lake_Package_optBarrelFacetConfig___lam__0(v_pkg_2335_, v___x_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec_ref(v___x_2336_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* v___x_2345_, lean_object* v___f_2346_, lean_object* v___x_2347_, lean_object* v___x_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = l_Lake_Job_async___redArg(v___x_2345_, v___f_2346_, v___x_2347_, v___x_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
lean_ctor_set(v___x_2357_, 1, v___y_2354_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object* v___x_2358_, lean_object* v___f_2359_, lean_object* v___x_2360_, lean_object* v___x_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lake_Package_optBarrelFacetConfig___lam__1(v___x_2358_, v___f_2359_, v___x_2360_, v___x_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec(v___y_2363_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* v___x_2370_, lean_object* v___x_2371_, lean_object* v___x_2372_, lean_object* v_pkg_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___f_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___f_2384_; lean_object* v___x_2385_; 
lean_inc_ref(v_pkg_2373_);
v___f_2381_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2381_, 0, v_pkg_2373_);
lean_closure_set(v___f_2381_, 1, v___x_2370_);
v___x_2382_ = lean_unsigned_to_nat(0u);
v___x_2383_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2371_);
v___f_2384_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2384_, 0, v___x_2371_);
lean_closure_set(v___f_2384_, 1, v___f_2381_);
lean_closure_set(v___f_2384_, 2, v___x_2382_);
lean_closure_set(v___f_2384_, 3, v___x_2383_);
v___x_2385_ = l_Lake_ensureJob___redArg(v___x_2371_, v___f_2384_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2418_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_a_2387_ = lean_ctor_get(v___x_2385_, 1);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2389_ = v___x_2385_;
v_isShared_2390_ = v_isSharedCheck_2418_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2418_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v_task_2391_; lean_object* v_kind_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2416_; 
v_task_2391_ = lean_ctor_get(v_a_2386_, 0);
v_kind_2392_ = lean_ctor_get(v_a_2386_, 1);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_a_2386_);
if (v_isSharedCheck_2416_ == 0)
{
lean_object* v_unused_2417_; 
v_unused_2417_ = lean_ctor_get(v_a_2386_, 2);
lean_dec(v_unused_2417_);
v___x_2394_ = v_a_2386_;
v_isShared_2395_ = v_isSharedCheck_2416_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_kind_2392_);
lean_inc(v_task_2391_);
lean_dec(v_a_2386_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2416_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v_registeredJobs_2396_; lean_object* v___x_2397_; lean_object* v_baseName_2398_; uint8_t v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v_job_2407_; 
v_registeredJobs_2396_ = lean_ctor_get(v___y_2378_, 3);
v___x_2397_ = lean_st_ref_take(v_registeredJobs_2396_);
v_baseName_2398_ = lean_ctor_get(v_pkg_2373_, 1);
lean_inc(v_baseName_2398_);
lean_dec_ref(v_pkg_2373_);
v___x_2399_ = 1;
v___x_2400_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2398_, v___x_2399_);
v___x_2401_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2402_ = lean_string_append(v___x_2400_, v___x_2401_);
v___x_2403_ = l_Lake_Name_eraseHead(v___x_2372_);
v___x_2404_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2403_, v___x_2399_);
v___x_2405_ = lean_string_append(v___x_2402_, v___x_2404_);
lean_dec_ref(v___x_2404_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 2, v___x_2405_);
v_job_2407_ = v___x_2394_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_task_2391_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v_kind_2392_);
lean_ctor_set(v_reuseFailAlloc_2415_, 2, v___x_2405_);
v_job_2407_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2413_; 
lean_ctor_set_uint8(v_job_2407_, sizeof(void*)*3, v___x_2399_);
lean_inc_ref(v_job_2407_);
v___x_2408_ = l_Lake_Job_toOpaque___redArg(v_job_2407_);
v___x_2409_ = lean_array_push(v___x_2397_, v___x_2408_);
v___x_2410_ = lean_st_ref_set(v_registeredJobs_2396_, v___x_2409_);
v___x_2411_ = l_Lake_Job_renew___redArg(v_job_2407_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2411_);
v___x_2413_ = v___x_2389_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_a_2387_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_2373_);
lean_dec(v___x_2372_);
return v___x_2385_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object* v___x_2419_, lean_object* v___x_2420_, lean_object* v___x_2421_, lean_object* v_pkg_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lake_Package_optBarrelFacetConfig___lam__2(v___x_2419_, v___x_2420_, v___x_2421_, v_pkg_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec(v___y_2424_);
return v_res_2430_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___f_2434_; 
v___x_2431_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_2432_ = l_Lake_instDataKindBool;
v___x_2433_ = l_Lake_Reservoir_lakeHeaders;
v___f_2434_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2434_, 0, v___x_2433_);
lean_closure_set(v___f_2434_, 1, v___x_2432_);
lean_closure_set(v___f_2434_, 2, v___x_2431_);
return v___f_2434_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2435_; uint8_t v___x_2436_; lean_object* v___x_2437_; lean_object* v___f_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___f_2435_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_2436_ = 1;
v___x_2437_ = l_Lake_instDataKindBool;
v___f_2438_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__0, &l_Lake_Package_optBarrelFacetConfig___closed__0_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__0);
v___x_2439_ = l_Lake_Package_keyword;
v___x_2440_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
lean_ctor_set(v___x_2440_, 1, v___f_2438_);
lean_ctor_set(v___x_2440_, 2, v___x_2437_);
lean_ctor_set(v___x_2440_, 3, v___f_2435_);
lean_ctor_set_uint8(v___x_2440_, sizeof(void*)*4, v___x_2436_);
lean_ctor_set_uint8(v___x_2440_, sizeof(void*)*4 + 1, v___x_2436_);
return v___x_2440_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig(void){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__1, &l_Lake_Package_optBarrelFacetConfig___closed__1_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__1);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* v_baseName_2443_, lean_object* v___x_2444_, uint8_t v_success_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_a_2454_; lean_object* v_a_2455_; 
if (v_success_2445_ == 0)
{
lean_object* v_toBuildConfig_2475_; uint8_t v_verbosity_2476_; uint8_t v___x_2477_; uint8_t v___x_2478_; 
v_toBuildConfig_2475_ = lean_ctor_get(v___y_2450_, 0);
v_verbosity_2476_ = lean_ctor_get_uint8(v_toBuildConfig_2475_, sizeof(void*)*3 + 3);
v___x_2477_ = 2;
v___x_2478_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2476_, v___x_2477_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; 
lean_dec(v___x_2444_);
lean_dec(v_baseName_2443_);
v___x_2479_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2454_ = v___x_2479_;
v_a_2455_ = v___y_2451_;
goto v___jp_2453_;
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2480_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2481_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2443_, v___x_2478_);
v___x_2482_ = lean_string_append(v___x_2480_, v___x_2481_);
lean_dec_ref(v___x_2481_);
v___x_2483_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2484_ = lean_string_append(v___x_2482_, v___x_2483_);
v___x_2485_ = l_Lake_Name_eraseHead(v___x_2444_);
v___x_2486_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2485_, v___x_2478_);
v___x_2487_ = lean_string_append(v___x_2484_, v___x_2486_);
lean_dec_ref(v___x_2486_);
v___x_2488_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2489_ = lean_string_append(v___x_2487_, v___x_2488_);
v_a_2454_ = v___x_2489_;
v_a_2455_ = v___y_2451_;
goto v___jp_2453_;
}
}
else
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_dec(v___x_2444_);
lean_dec(v_baseName_2443_);
v___x_2490_ = lean_box(0);
v___x_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
lean_ctor_set(v___x_2491_, 1, v___y_2451_);
return v___x_2491_;
}
v___jp_2453_:
{
lean_object* v_log_2456_; uint8_t v_action_2457_; uint8_t v_wantsRebuild_2458_; lean_object* v_trace_2459_; lean_object* v_buildTime_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2474_; 
v_log_2456_ = lean_ctor_get(v_a_2455_, 0);
v_action_2457_ = lean_ctor_get_uint8(v_a_2455_, sizeof(void*)*3);
v_wantsRebuild_2458_ = lean_ctor_get_uint8(v_a_2455_, sizeof(void*)*3 + 1);
v_trace_2459_ = lean_ctor_get(v_a_2455_, 1);
v_buildTime_2460_ = lean_ctor_get(v_a_2455_, 2);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_a_2455_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2462_ = v_a_2455_;
v_isShared_2463_ = v_isSharedCheck_2474_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_buildTime_2460_);
lean_inc(v_trace_2459_);
lean_inc(v_log_2456_);
lean_dec(v_a_2455_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2474_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2464_ = ((lean_object*)(l_Lake_Package_barrelFacetConfig___lam__1___closed__0));
v___x_2465_ = lean_string_append(v___x_2464_, v_a_2454_);
lean_dec_ref(v_a_2454_);
v___x_2466_ = 3;
v___x_2467_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2467_, 0, v___x_2465_);
lean_ctor_set_uint8(v___x_2467_, sizeof(void*)*1, v___x_2466_);
v___x_2468_ = lean_array_get_size(v_log_2456_);
v___x_2469_ = lean_array_push(v_log_2456_, v___x_2467_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___x_2469_);
v___x_2471_ = v___x_2462_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_trace_2459_);
lean_ctor_set(v_reuseFailAlloc_2473_, 2, v_buildTime_2460_);
lean_ctor_set_uint8(v_reuseFailAlloc_2473_, sizeof(void*)*3, v_action_2457_);
lean_ctor_set_uint8(v_reuseFailAlloc_2473_, sizeof(void*)*3 + 1, v_wantsRebuild_2458_);
v___x_2471_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2468_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
return v___x_2472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object* v_baseName_2492_, lean_object* v___x_2493_, lean_object* v_success_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
uint8_t v_success_boxed_2502_; lean_object* v_res_2503_; 
v_success_boxed_2502_ = lean_unbox(v_success_2494_);
v_res_2503_ = l_Lake_Package_barrelFacetConfig___lam__1(v_baseName_2492_, v___x_2493_, v_success_boxed_2502_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* v___x_2504_, lean_object* v___x_2505_, lean_object* v___x_2506_, lean_object* v_pkg_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v_baseName_2515_; lean_object* v_keyName_2516_; lean_object* v___f_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___f_2521_; lean_object* v___x_2522_; 
v_baseName_2515_ = lean_ctor_get(v_pkg_2507_, 1);
lean_inc_n(v_baseName_2515_, 2);
v_keyName_2516_ = lean_ctor_get(v_pkg_2507_, 2);
lean_inc(v___x_2504_);
v___f_2517_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2517_, 0, v_baseName_2515_);
lean_closure_set(v___f_2517_, 1, v___x_2504_);
lean_inc(v_keyName_2516_);
v___x_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2518_, 0, v_keyName_2516_);
v___x_2519_ = l_Lake_Package_keyword;
v___x_2520_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
lean_ctor_set(v___x_2520_, 2, v_pkg_2507_);
lean_ctor_set(v___x_2520_, 3, v___x_2504_);
lean_inc(v___x_2505_);
v___f_2521_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2521_, 0, v___x_2520_);
lean_closure_set(v___f_2521_, 1, v___x_2505_);
lean_closure_set(v___f_2521_, 2, v___f_2517_);
v___x_2522_ = l_Lake_ensureJob___redArg(v___x_2505_, v___f_2521_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2555_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_a_2524_ = lean_ctor_get(v___x_2522_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2526_ = v___x_2522_;
v_isShared_2527_ = v_isSharedCheck_2555_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2555_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v_task_2528_; lean_object* v_kind_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2553_; 
v_task_2528_ = lean_ctor_get(v_a_2523_, 0);
v_kind_2529_ = lean_ctor_get(v_a_2523_, 1);
v_isSharedCheck_2553_ = !lean_is_exclusive(v_a_2523_);
if (v_isSharedCheck_2553_ == 0)
{
lean_object* v_unused_2554_; 
v_unused_2554_ = lean_ctor_get(v_a_2523_, 2);
lean_dec(v_unused_2554_);
v___x_2531_ = v_a_2523_;
v_isShared_2532_ = v_isSharedCheck_2553_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_kind_2529_);
lean_inc(v_task_2528_);
lean_dec(v_a_2523_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2553_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v_registeredJobs_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; lean_object* v_job_2544_; 
v_registeredJobs_2533_ = lean_ctor_get(v___y_2512_, 3);
v___x_2534_ = lean_st_ref_take(v_registeredJobs_2533_);
v___x_2535_ = 1;
v___x_2536_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2515_, v___x_2535_);
v___x_2537_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2538_ = lean_string_append(v___x_2536_, v___x_2537_);
v___x_2539_ = l_Lake_Name_eraseHead(v___x_2506_);
v___x_2540_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2539_, v___x_2535_);
v___x_2541_ = lean_string_append(v___x_2538_, v___x_2540_);
lean_dec_ref(v___x_2540_);
v___x_2542_ = 0;
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 2, v___x_2541_);
v_job_2544_ = v___x_2531_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_task_2528_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_kind_2529_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v___x_2541_);
v_job_2544_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2550_; 
lean_ctor_set_uint8(v_job_2544_, sizeof(void*)*3, v___x_2542_);
lean_inc_ref(v_job_2544_);
v___x_2545_ = l_Lake_Job_toOpaque___redArg(v_job_2544_);
v___x_2546_ = lean_array_push(v___x_2534_, v___x_2545_);
v___x_2547_ = lean_st_ref_set(v_registeredJobs_2533_, v___x_2546_);
v___x_2548_ = l_Lake_Job_renew___redArg(v_job_2544_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v___x_2548_);
v___x_2550_ = v___x_2526_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2548_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_a_2524_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2515_);
lean_dec(v___x_2506_);
return v___x_2522_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object* v___x_2556_, lean_object* v___x_2557_, lean_object* v___x_2558_, lean_object* v_pkg_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lake_Package_barrelFacetConfig___lam__2(v___x_2556_, v___x_2557_, v___x_2558_, v_pkg_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec(v___y_2561_);
return v_res_2567_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___f_2571_; 
v___x_2568_ = l_Lake_Package_reservoirBarrelFacet;
v___x_2569_ = l_Lake_instDataKindUnit;
v___x_2570_ = l_Lake_Package_optReservoirBarrelFacet;
v___f_2571_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2571_, 0, v___x_2570_);
lean_closure_set(v___f_2571_, 1, v___x_2569_);
lean_closure_set(v___f_2571_, 2, v___x_2568_);
return v___f_2571_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2572_; uint8_t v___x_2573_; lean_object* v___x_2574_; lean_object* v___f_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___f_2572_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2573_ = 1;
v___x_2574_ = l_Lake_instDataKindUnit;
v___f_2575_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__0, &l_Lake_Package_barrelFacetConfig___closed__0_once, _init_l_Lake_Package_barrelFacetConfig___closed__0);
v___x_2576_ = l_Lake_Package_keyword;
v___x_2577_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v___f_2575_);
lean_ctor_set(v___x_2577_, 2, v___x_2574_);
lean_ctor_set(v___x_2577_, 3, v___f_2572_);
lean_ctor_set_uint8(v___x_2577_, sizeof(void*)*4, v___x_2573_);
lean_ctor_set_uint8(v___x_2577_, sizeof(void*)*4 + 1, v___x_2573_);
return v___x_2577_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig(void){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__1, &l_Lake_Package_barrelFacetConfig___closed__1_once, _init_l_Lake_Package_barrelFacetConfig___closed__1);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object* v_pkg_2579_, lean_object* v___x_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
uint8_t v_r_2589_; lean_object* v___y_2590_; lean_object* v_a_2594_; lean_object* v___x_2610_; 
lean_inc_ref(v_pkg_2579_);
v___x_2610_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_pkg_2579_, v___y_2586_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v_a_2612_; lean_object* v_dir_2613_; lean_object* v_buildArchive_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
v_a_2612_ = lean_ctor_get(v___x_2610_, 1);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2610_, 2);
v_dir_2613_ = lean_ctor_get(v_pkg_2579_, 4);
v_buildArchive_2614_ = lean_ctor_get(v_pkg_2579_, 21);
v___x_2615_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_2613_);
v___x_2616_ = l_Lake_joinRelative(v_dir_2613_, v___x_2615_);
lean_inc_ref(v_buildArchive_2614_);
v___x_2617_ = l_Lake_joinRelative(v___x_2616_, v_buildArchive_2614_);
v___x_2618_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2579_, v_a_2611_, v___x_2617_, v___x_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v_a_2612_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; uint8_t v___x_2620_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 1);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 2);
v___x_2620_ = 1;
v_r_2589_ = v___x_2620_;
v___y_2590_ = v_a_2619_;
goto v___jp_2588_;
}
else
{
lean_object* v_a_2621_; 
v_a_2621_ = lean_ctor_get(v___x_2618_, 1);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2618_, 2);
v_a_2594_ = v_a_2621_;
goto v___jp_2593_;
}
}
else
{
lean_object* v_a_2622_; 
lean_dec_ref(v_pkg_2579_);
v_a_2622_ = lean_ctor_get(v___x_2610_, 1);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2610_, 2);
v_a_2594_ = v_a_2622_;
goto v___jp_2593_;
}
v___jp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_box(v_r_2589_);
v___x_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
lean_ctor_set(v___x_2592_, 1, v___y_2590_);
return v___x_2592_;
}
v___jp_2593_:
{
lean_object* v_log_2595_; uint8_t v_action_2596_; uint8_t v_wantsRebuild_2597_; lean_object* v_trace_2598_; lean_object* v_buildTime_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2609_; 
v_log_2595_ = lean_ctor_get(v_a_2594_, 0);
v_action_2596_ = lean_ctor_get_uint8(v_a_2594_, sizeof(void*)*3);
v_wantsRebuild_2597_ = lean_ctor_get_uint8(v_a_2594_, sizeof(void*)*3 + 1);
v_trace_2598_ = lean_ctor_get(v_a_2594_, 1);
v_buildTime_2599_ = lean_ctor_get(v_a_2594_, 2);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_a_2594_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2601_ = v_a_2594_;
v_isShared_2602_ = v_isSharedCheck_2609_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_buildTime_2599_);
lean_inc(v_trace_2598_);
lean_inc(v_log_2595_);
lean_dec(v_a_2594_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2609_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
uint8_t v___x_2603_; uint8_t v___x_2604_; lean_object* v___x_2606_; 
v___x_2603_ = 4;
v___x_2604_ = l_Lake_JobAction_merge(v_action_2596_, v___x_2603_);
if (v_isShared_2602_ == 0)
{
v___x_2606_ = v___x_2601_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_log_2595_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v_trace_2598_);
lean_ctor_set(v_reuseFailAlloc_2608_, 2, v_buildTime_2599_);
lean_ctor_set_uint8(v_reuseFailAlloc_2608_, sizeof(void*)*3 + 1, v_wantsRebuild_2597_);
v___x_2606_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
uint8_t v___x_2607_; 
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*3, v___x_2604_);
v___x_2607_ = 0;
v_r_2589_ = v___x_2607_;
v___y_2590_ = v___x_2606_;
goto v___jp_2588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object* v_pkg_2623_, lean_object* v___x_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(v_pkg_2623_, v___x_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec_ref(v___x_2624_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object* v___x_2633_, lean_object* v___x_2634_, lean_object* v___x_2635_, lean_object* v___x_2636_, lean_object* v_pkg_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v___f_2645_; lean_object* v___x_2646_; lean_object* v___f_2647_; lean_object* v___x_2648_; 
lean_inc_ref(v_pkg_2637_);
v___f_2645_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2645_, 0, v_pkg_2637_);
lean_closure_set(v___f_2645_, 1, v___x_2633_);
v___x_2646_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2634_);
v___f_2647_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2647_, 0, v___x_2634_);
lean_closure_set(v___f_2647_, 1, v___f_2645_);
lean_closure_set(v___f_2647_, 2, v___x_2635_);
lean_closure_set(v___f_2647_, 3, v___x_2646_);
v___x_2648_ = l_Lake_ensureJob___redArg(v___x_2634_, v___f_2647_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2681_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_a_2650_ = lean_ctor_get(v___x_2648_, 1);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2652_ = v___x_2648_;
v_isShared_2653_ = v_isSharedCheck_2681_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2681_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v_task_2654_; lean_object* v_kind_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2679_; 
v_task_2654_ = lean_ctor_get(v_a_2649_, 0);
v_kind_2655_ = lean_ctor_get(v_a_2649_, 1);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_a_2649_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; 
v_unused_2680_ = lean_ctor_get(v_a_2649_, 2);
lean_dec(v_unused_2680_);
v___x_2657_ = v_a_2649_;
v_isShared_2658_ = v_isSharedCheck_2679_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_kind_2655_);
lean_inc(v_task_2654_);
lean_dec(v_a_2649_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2679_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_registeredJobs_2659_; lean_object* v___x_2660_; lean_object* v_baseName_2661_; uint8_t v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v_job_2670_; 
v_registeredJobs_2659_ = lean_ctor_get(v___y_2642_, 3);
v___x_2660_ = lean_st_ref_take(v_registeredJobs_2659_);
v_baseName_2661_ = lean_ctor_get(v_pkg_2637_, 1);
lean_inc(v_baseName_2661_);
lean_dec_ref(v_pkg_2637_);
v___x_2662_ = 1;
v___x_2663_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2661_, v___x_2662_);
v___x_2664_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2665_ = lean_string_append(v___x_2663_, v___x_2664_);
v___x_2666_ = l_Lake_Name_eraseHead(v___x_2636_);
v___x_2667_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2666_, v___x_2662_);
v___x_2668_ = lean_string_append(v___x_2665_, v___x_2667_);
lean_dec_ref(v___x_2667_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 2, v___x_2668_);
v_job_2670_ = v___x_2657_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_task_2654_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_kind_2655_);
lean_ctor_set(v_reuseFailAlloc_2678_, 2, v___x_2668_);
v_job_2670_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
lean_ctor_set_uint8(v_job_2670_, sizeof(void*)*3, v___x_2662_);
lean_inc_ref(v_job_2670_);
v___x_2671_ = l_Lake_Job_toOpaque___redArg(v_job_2670_);
v___x_2672_ = lean_array_push(v___x_2660_, v___x_2671_);
v___x_2673_ = lean_st_ref_set(v_registeredJobs_2659_, v___x_2672_);
v___x_2674_ = l_Lake_Job_renew___redArg(v_job_2670_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2674_);
v___x_2676_ = v___x_2652_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_a_2650_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_2637_);
lean_dec(v___x_2636_);
return v___x_2648_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_2682_, lean_object* v___x_2683_, lean_object* v___x_2684_, lean_object* v___x_2685_, lean_object* v_pkg_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(v___x_2682_, v___x_2683_, v___x_2684_, v___x_2685_, v_pkg_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec(v___y_2688_);
return v_res_2694_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___f_2701_; 
v___x_2697_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_2698_ = lean_unsigned_to_nat(0u);
v___x_2699_ = l_Lake_instDataKindBool;
v___x_2700_ = ((lean_object*)(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0));
v___f_2701_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2701_, 0, v___x_2700_);
lean_closure_set(v___f_2701_, 1, v___x_2699_);
lean_closure_set(v___f_2701_, 2, v___x_2698_);
lean_closure_set(v___f_2701_, 3, v___x_2697_);
return v___f_2701_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2702_; uint8_t v___x_2703_; lean_object* v___x_2704_; lean_object* v___f_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___f_2702_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_2703_ = 1;
v___x_2704_ = l_Lake_instDataKindBool;
v___f_2705_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__1, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1);
v___x_2706_ = l_Lake_Package_keyword;
v___x_2707_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
lean_ctor_set(v___x_2707_, 1, v___f_2705_);
lean_ctor_set(v___x_2707_, 2, v___x_2704_);
lean_ctor_set(v___x_2707_, 3, v___f_2702_);
lean_ctor_set_uint8(v___x_2707_, sizeof(void*)*4, v___x_2703_);
lean_ctor_set_uint8(v___x_2707_, sizeof(void*)*4 + 1, v___x_2703_);
return v___x_2707_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__2, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* v_baseName_2710_, lean_object* v___x_2711_, uint8_t v_success_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_a_2721_; lean_object* v_a_2722_; 
if (v_success_2712_ == 0)
{
lean_object* v_toBuildConfig_2742_; uint8_t v_verbosity_2743_; uint8_t v___x_2744_; uint8_t v___x_2745_; 
v_toBuildConfig_2742_ = lean_ctor_get(v___y_2717_, 0);
v_verbosity_2743_ = lean_ctor_get_uint8(v_toBuildConfig_2742_, sizeof(void*)*3 + 3);
v___x_2744_ = 2;
v___x_2745_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2743_, v___x_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; 
lean_dec(v___x_2711_);
lean_dec(v_baseName_2710_);
v___x_2746_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2721_ = v___x_2746_;
v_a_2722_ = v___y_2718_;
goto v___jp_2720_;
}
else
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2747_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2748_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2710_, v___x_2745_);
v___x_2749_ = lean_string_append(v___x_2747_, v___x_2748_);
lean_dec_ref(v___x_2748_);
v___x_2750_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2751_ = lean_string_append(v___x_2749_, v___x_2750_);
v___x_2752_ = l_Lake_Name_eraseHead(v___x_2711_);
v___x_2753_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2752_, v___x_2745_);
v___x_2754_ = lean_string_append(v___x_2751_, v___x_2753_);
lean_dec_ref(v___x_2753_);
v___x_2755_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2756_ = lean_string_append(v___x_2754_, v___x_2755_);
v_a_2721_ = v___x_2756_;
v_a_2722_ = v___y_2718_;
goto v___jp_2720_;
}
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
lean_dec(v___x_2711_);
lean_dec(v_baseName_2710_);
v___x_2757_ = lean_box(0);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
lean_ctor_set(v___x_2758_, 1, v___y_2718_);
return v___x_2758_;
}
v___jp_2720_:
{
lean_object* v_log_2723_; uint8_t v_action_2724_; uint8_t v_wantsRebuild_2725_; lean_object* v_trace_2726_; lean_object* v_buildTime_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2741_; 
v_log_2723_ = lean_ctor_get(v_a_2722_, 0);
v_action_2724_ = lean_ctor_get_uint8(v_a_2722_, sizeof(void*)*3);
v_wantsRebuild_2725_ = lean_ctor_get_uint8(v_a_2722_, sizeof(void*)*3 + 1);
v_trace_2726_ = lean_ctor_get(v_a_2722_, 1);
v_buildTime_2727_ = lean_ctor_get(v_a_2722_, 2);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_a_2722_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2729_ = v_a_2722_;
v_isShared_2730_ = v_isSharedCheck_2741_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_buildTime_2727_);
lean_inc(v_trace_2726_);
lean_inc(v_log_2723_);
lean_dec(v_a_2722_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2741_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2731_ = ((lean_object*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0));
v___x_2732_ = lean_string_append(v___x_2731_, v_a_2721_);
lean_dec_ref(v_a_2721_);
v___x_2733_ = 3;
v___x_2734_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2734_, 0, v___x_2732_);
lean_ctor_set_uint8(v___x_2734_, sizeof(void*)*1, v___x_2733_);
v___x_2735_ = lean_array_get_size(v_log_2723_);
v___x_2736_ = lean_array_push(v_log_2723_, v___x_2734_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v___x_2736_);
v___x_2738_ = v___x_2729_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_trace_2726_);
lean_ctor_set(v_reuseFailAlloc_2740_, 2, v_buildTime_2727_);
lean_ctor_set_uint8(v_reuseFailAlloc_2740_, sizeof(void*)*3, v_action_2724_);
lean_ctor_set_uint8(v_reuseFailAlloc_2740_, sizeof(void*)*3 + 1, v_wantsRebuild_2725_);
v___x_2738_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; 
v___x_2739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2735_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
return v___x_2739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object* v_baseName_2759_, lean_object* v___x_2760_, lean_object* v_success_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
uint8_t v_success_boxed_2769_; lean_object* v_res_2770_; 
v_success_boxed_2769_ = lean_unbox(v_success_2761_);
v_res_2770_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(v_baseName_2759_, v___x_2760_, v_success_boxed_2769_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* v___x_2771_, lean_object* v___x_2772_, lean_object* v___x_2773_, lean_object* v_pkg_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_baseName_2782_; lean_object* v_keyName_2783_; lean_object* v___f_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___f_2788_; lean_object* v___x_2789_; 
v_baseName_2782_ = lean_ctor_get(v_pkg_2774_, 1);
lean_inc_n(v_baseName_2782_, 2);
v_keyName_2783_ = lean_ctor_get(v_pkg_2774_, 2);
lean_inc(v___x_2771_);
v___f_2784_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2784_, 0, v_baseName_2782_);
lean_closure_set(v___f_2784_, 1, v___x_2771_);
lean_inc(v_keyName_2783_);
v___x_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2785_, 0, v_keyName_2783_);
v___x_2786_ = l_Lake_Package_keyword;
v___x_2787_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2785_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
lean_ctor_set(v___x_2787_, 2, v_pkg_2774_);
lean_ctor_set(v___x_2787_, 3, v___x_2771_);
lean_inc(v___x_2772_);
v___f_2788_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2788_, 0, v___x_2787_);
lean_closure_set(v___f_2788_, 1, v___x_2772_);
lean_closure_set(v___f_2788_, 2, v___f_2784_);
v___x_2789_ = l_Lake_ensureJob___redArg(v___x_2772_, v___f_2788_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2822_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
v_a_2791_ = lean_ctor_get(v___x_2789_, 1);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2793_ = v___x_2789_;
v_isShared_2794_ = v_isSharedCheck_2822_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_inc(v_a_2790_);
lean_dec(v___x_2789_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2822_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_task_2795_; lean_object* v_kind_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2820_; 
v_task_2795_ = lean_ctor_get(v_a_2790_, 0);
v_kind_2796_ = lean_ctor_get(v_a_2790_, 1);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_a_2790_);
if (v_isSharedCheck_2820_ == 0)
{
lean_object* v_unused_2821_; 
v_unused_2821_ = lean_ctor_get(v_a_2790_, 2);
lean_dec(v_unused_2821_);
v___x_2798_ = v_a_2790_;
v_isShared_2799_ = v_isSharedCheck_2820_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_kind_2796_);
lean_inc(v_task_2795_);
lean_dec(v_a_2790_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2820_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v_registeredJobs_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; lean_object* v_job_2811_; 
v_registeredJobs_2800_ = lean_ctor_get(v___y_2779_, 3);
v___x_2801_ = lean_st_ref_take(v_registeredJobs_2800_);
v___x_2802_ = 1;
v___x_2803_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2782_, v___x_2802_);
v___x_2804_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2805_ = lean_string_append(v___x_2803_, v___x_2804_);
v___x_2806_ = l_Lake_Name_eraseHead(v___x_2773_);
v___x_2807_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2806_, v___x_2802_);
v___x_2808_ = lean_string_append(v___x_2805_, v___x_2807_);
lean_dec_ref(v___x_2807_);
v___x_2809_ = 0;
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 2, v___x_2808_);
v_job_2811_ = v___x_2798_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_task_2795_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_kind_2796_);
lean_ctor_set(v_reuseFailAlloc_2819_, 2, v___x_2808_);
v_job_2811_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2817_; 
lean_ctor_set_uint8(v_job_2811_, sizeof(void*)*3, v___x_2809_);
lean_inc_ref(v_job_2811_);
v___x_2812_ = l_Lake_Job_toOpaque___redArg(v_job_2811_);
v___x_2813_ = lean_array_push(v___x_2801_, v___x_2812_);
v___x_2814_ = lean_st_ref_set(v_registeredJobs_2800_, v___x_2813_);
v___x_2815_ = l_Lake_Job_renew___redArg(v_job_2811_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2815_);
v___x_2817_ = v___x_2793_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v_a_2791_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2782_);
lean_dec(v___x_2773_);
return v___x_2789_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_2823_, lean_object* v___x_2824_, lean_object* v___x_2825_, lean_object* v_pkg_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(v___x_2823_, v___x_2824_, v___x_2825_, v_pkg_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec(v___y_2828_);
return v_res_2834_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___f_2838_; 
v___x_2835_ = l_Lake_Package_gitHubReleaseFacet;
v___x_2836_ = l_Lake_instDataKindUnit;
v___x_2837_ = l_Lake_Package_optGitHubReleaseFacet;
v___f_2838_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2838_, 0, v___x_2837_);
lean_closure_set(v___f_2838_, 1, v___x_2836_);
lean_closure_set(v___f_2838_, 2, v___x_2835_);
return v___f_2838_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2839_; uint8_t v___x_2840_; lean_object* v___x_2841_; lean_object* v___f_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___f_2839_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2840_ = 1;
v___x_2841_ = l_Lake_instDataKindUnit;
v___f_2842_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__0, &l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0);
v___x_2843_ = l_Lake_Package_keyword;
v___x_2844_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set(v___x_2844_, 1, v___f_2842_);
lean_ctor_set(v___x_2844_, 2, v___x_2841_);
lean_ctor_set(v___x_2844_, 3, v___f_2839_);
lean_ctor_set_uint8(v___x_2844_, sizeof(void*)*4, v___x_2840_);
lean_ctor_set_uint8(v___x_2844_, sizeof(void*)*4 + 1, v___x_2840_);
return v___x_2844_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__1, &l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* v_build_2846_, uint8_t v_x_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v_log_2855_; uint8_t v_action_2856_; uint8_t v_wantsRebuild_2857_; lean_object* v_buildTime_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2867_; 
v_log_2855_ = lean_ctor_get(v___y_2853_, 0);
v_action_2856_ = lean_ctor_get_uint8(v___y_2853_, sizeof(void*)*3);
v_wantsRebuild_2857_ = lean_ctor_get_uint8(v___y_2853_, sizeof(void*)*3 + 1);
v_buildTime_2858_ = lean_ctor_get(v___y_2853_, 2);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___y_2853_);
if (v_isSharedCheck_2867_ == 0)
{
lean_object* v_unused_2868_; 
v_unused_2868_ = lean_ctor_get(v___y_2853_, 1);
lean_dec(v_unused_2868_);
v___x_2860_ = v___y_2853_;
v_isShared_2861_ = v_isSharedCheck_2867_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_buildTime_2858_);
lean_inc(v_log_2855_);
lean_dec(v___y_2853_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2867_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2862_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 1, v___x_2862_);
v___x_2864_ = v___x_2860_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_log_2855_);
lean_ctor_set(v_reuseFailAlloc_2866_, 1, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2866_, 2, v_buildTime_2858_);
lean_ctor_set_uint8(v_reuseFailAlloc_2866_, sizeof(void*)*3, v_action_2856_);
lean_ctor_set_uint8(v_reuseFailAlloc_2866_, sizeof(void*)*3 + 1, v_wantsRebuild_2857_);
v___x_2864_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2865_; 
lean_inc_ref(v___y_2852_);
lean_inc(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc(v___y_2849_);
v___x_2865_ = lean_apply_7(v_build_2846_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___x_2864_, lean_box(0));
return v___x_2865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* v_build_2869_, lean_object* v_x_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
uint8_t v_x_1923__boxed_2878_; lean_object* v_res_2879_; 
v_x_1923__boxed_2878_ = lean_unbox(v_x_2870_);
v_res_2879_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(v_build_2869_, v_x_1923__boxed_2878_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec(v___y_2872_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* v_self_2880_, lean_object* v_build_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_wsIdx_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; 
v_wsIdx_2889_ = lean_ctor_get(v_self_2880_, 0);
v___x_2890_ = lean_unsigned_to_nat(0u);
v___x_2891_ = lean_nat_dec_eq(v_wsIdx_2889_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; 
lean_inc_ref(v_a_2882_);
v___x_2892_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_2880_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2905_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
v_a_2894_ = lean_ctor_get(v___x_2892_, 1);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2896_ = v___x_2892_;
v_isShared_2897_ = v_isSharedCheck_2905_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_inc(v_a_2893_);
lean_dec(v___x_2892_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2905_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___f_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___f_2898_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_2898_, 0, v_build_2881_);
v___x_2899_ = lean_box(0);
v___x_2900_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2901_ = l_Lake_Job_bindM___redArg(v___x_2899_, v_a_2893_, v___f_2898_, v___x_2890_, v___x_2891_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v___x_2900_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2901_);
v___x_2903_ = v___x_2896_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2901_);
lean_ctor_set(v_reuseFailAlloc_2904_, 1, v_a_2894_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec_ref(v_a_2882_);
lean_dec_ref(v_build_2881_);
v_a_2906_ = lean_ctor_get(v___x_2892_, 0);
v_a_2907_ = lean_ctor_get(v___x_2892_, 1);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2892_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_inc(v_a_2906_);
lean_dec(v___x_2892_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2906_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
else
{
uint8_t v___x_2915_; uint8_t v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
lean_dec_ref(v_self_2880_);
v___x_2915_ = 0;
v___x_2916_ = 0;
v___x_2917_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2918_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2918_, 0, v_a_2887_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
lean_ctor_set(v___x_2918_, 2, v___x_2890_);
lean_ctor_set_uint8(v___x_2918_, sizeof(void*)*3, v___x_2915_);
lean_ctor_set_uint8(v___x_2918_, sizeof(void*)*3 + 1, v___x_2916_);
lean_inc_ref(v_a_2886_);
lean_inc(v_a_2885_);
lean_inc(v_a_2884_);
lean_inc(v_a_2883_);
v___x_2919_ = lean_apply_7(v_build_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v___x_2918_, lean_box(0));
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2929_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 1);
v_a_2921_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2923_ = v___x_2919_;
v_isShared_2924_ = v_isSharedCheck_2929_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2920_);
lean_inc(v_a_2921_);
lean_dec(v___x_2919_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2929_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v_log_2925_; lean_object* v___x_2927_; 
v_log_2925_ = lean_ctor_get(v_a_2920_, 0);
lean_inc_ref(v_log_2925_);
lean_dec(v_a_2920_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 1, v_log_2925_);
v___x_2927_ = v___x_2923_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2921_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_log_2925_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2939_; 
v_a_2930_ = lean_ctor_get(v___x_2919_, 1);
v_a_2931_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2933_ = v___x_2919_;
v_isShared_2934_ = v_isSharedCheck_2939_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2930_);
lean_inc(v_a_2931_);
lean_dec(v___x_2919_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2939_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v_log_2935_; lean_object* v___x_2937_; 
v_log_2935_ = lean_ctor_get(v_a_2930_, 0);
lean_inc_ref(v_log_2935_);
lean_dec(v_a_2930_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v_log_2935_);
v___x_2937_ = v___x_2933_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2931_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_log_2935_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___boxed(lean_object* v_self_2940_, lean_object* v_build_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_2940_, v_build_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec(v_a_2943_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* v_00_u03b1_2950_, lean_object* v_self_2951_, lean_object* v_build_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_2951_, v_build_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___boxed(lean_object* v_00_u03b1_2961_, lean_object* v_self_2962_, lean_object* v_build_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Lake_Package_afterBuildCacheAsync(v_00_u03b1_2961_, v_self_2962_, v_build_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
lean_dec_ref(v_a_2968_);
lean_dec(v_a_2967_);
lean_dec(v_a_2966_);
lean_dec(v_a_2965_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* v_build_2972_, uint8_t v_x_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v_log_2981_; uint8_t v_action_2982_; uint8_t v_wantsRebuild_2983_; lean_object* v_buildTime_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2993_; 
v_log_2981_ = lean_ctor_get(v___y_2979_, 0);
v_action_2982_ = lean_ctor_get_uint8(v___y_2979_, sizeof(void*)*3);
v_wantsRebuild_2983_ = lean_ctor_get_uint8(v___y_2979_, sizeof(void*)*3 + 1);
v_buildTime_2984_ = lean_ctor_get(v___y_2979_, 2);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___y_2979_);
if (v_isSharedCheck_2993_ == 0)
{
lean_object* v_unused_2994_; 
v_unused_2994_ = lean_ctor_get(v___y_2979_, 1);
lean_dec(v_unused_2994_);
v___x_2986_ = v___y_2979_;
v_isShared_2987_ = v_isSharedCheck_2993_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_buildTime_2984_);
lean_inc(v_log_2981_);
lean_dec(v___y_2979_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2993_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2988_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 1, v___x_2988_);
v___x_2990_ = v___x_2986_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_log_2981_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v_buildTime_2984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2992_, sizeof(void*)*3, v_action_2982_);
lean_ctor_set_uint8(v_reuseFailAlloc_2992_, sizeof(void*)*3 + 1, v_wantsRebuild_2983_);
v___x_2990_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
lean_object* v___x_2991_; 
lean_inc_ref(v___y_2978_);
lean_inc(v___y_2977_);
lean_inc(v___y_2976_);
lean_inc(v___y_2975_);
v___x_2991_ = lean_apply_7(v_build_2972_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___x_2990_, lean_box(0));
return v___x_2991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* v_build_2995_, lean_object* v_x_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_){
_start:
{
uint8_t v_x_1946__boxed_3004_; lean_object* v_res_3005_; 
v_x_1946__boxed_3004_ = lean_unbox(v_x_2996_);
v_res_3005_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(v_build_2995_, v_x_1946__boxed_3004_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
lean_dec_ref(v___y_3001_);
lean_dec(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* v_self_3006_, lean_object* v_build_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_wsIdx_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; 
v_wsIdx_3015_ = lean_ctor_get(v_self_3006_, 0);
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = lean_nat_dec_eq(v_wsIdx_3015_, v___x_3016_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; 
lean_inc_ref(v_a_3008_);
v___x_3018_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3006_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3031_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
v_a_3020_ = lean_ctor_get(v___x_3018_, 1);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3022_ = v___x_3018_;
v_isShared_3023_ = v_isSharedCheck_3031_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_inc(v_a_3019_);
lean_dec(v___x_3018_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3031_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___f_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3029_; 
v___f_3024_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3024_, 0, v_build_3007_);
v___x_3025_ = lean_box(0);
v___x_3026_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3027_ = l_Lake_Job_mapM___redArg(v___x_3025_, v_a_3019_, v___f_3024_, v___x_3016_, v___x_3017_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v___x_3026_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___x_3027_);
v___x_3029_ = v___x_3022_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v_a_3020_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec_ref(v_a_3008_);
lean_dec_ref(v_build_3007_);
v_a_3032_ = lean_ctor_get(v___x_3018_, 0);
v_a_3033_ = lean_ctor_get(v___x_3018_, 1);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3018_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_inc(v_a_3032_);
lean_dec(v___x_3018_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3032_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
else
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
lean_dec_ref(v_self_3006_);
v___x_3041_ = lean_box(0);
v___x_3042_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_3043_ = l_Lake_Job_async___redArg(v___x_3041_, v_build_3007_, v___x_3016_, v___x_3042_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
v___x_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
lean_ctor_set(v___x_3044_, 1, v_a_3013_);
return v___x_3044_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___boxed(lean_object* v_self_3045_, lean_object* v_build_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3045_, v_build_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec(v_a_3049_);
lean_dec(v_a_3048_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* v_00_u03b1_3055_, lean_object* v_self_3056_, lean_object* v_build_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3056_, v_build_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___boxed(lean_object* v_00_u03b1_3066_, lean_object* v_self_3067_, lean_object* v_build_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Lake_Package_afterBuildCacheSync(v_00_u03b1_3066_, v_self_3067_, v_build_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec(v_a_3071_);
lean_dec(v_a_3070_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(lean_object* v_k_3077_, lean_object* v_v_3078_, lean_object* v_t_3079_){
_start:
{
if (lean_obj_tag(v_t_3079_) == 0)
{
lean_object* v_size_3080_; lean_object* v_k_3081_; lean_object* v_v_3082_; lean_object* v_l_3083_; lean_object* v_r_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3364_; 
v_size_3080_ = lean_ctor_get(v_t_3079_, 0);
v_k_3081_ = lean_ctor_get(v_t_3079_, 1);
v_v_3082_ = lean_ctor_get(v_t_3079_, 2);
v_l_3083_ = lean_ctor_get(v_t_3079_, 3);
v_r_3084_ = lean_ctor_get(v_t_3079_, 4);
v_isSharedCheck_3364_ = !lean_is_exclusive(v_t_3079_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3086_ = v_t_3079_;
v_isShared_3087_ = v_isSharedCheck_3364_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_r_3084_);
lean_inc(v_l_3083_);
lean_inc(v_v_3082_);
lean_inc(v_k_3081_);
lean_inc(v_size_3080_);
lean_dec(v_t_3079_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3364_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
uint8_t v___x_3088_; 
v___x_3088_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3077_, v_k_3081_);
switch(v___x_3088_)
{
case 0:
{
lean_object* v_impl_3089_; lean_object* v___x_3090_; 
lean_dec(v_size_3080_);
v_impl_3089_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3077_, v_v_3078_, v_l_3083_);
v___x_3090_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3084_) == 0)
{
lean_object* v_size_3091_; lean_object* v_size_3092_; lean_object* v_k_3093_; lean_object* v_v_3094_; lean_object* v_l_3095_; lean_object* v_r_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v_size_3091_ = lean_ctor_get(v_r_3084_, 0);
v_size_3092_ = lean_ctor_get(v_impl_3089_, 0);
lean_inc(v_size_3092_);
v_k_3093_ = lean_ctor_get(v_impl_3089_, 1);
lean_inc(v_k_3093_);
v_v_3094_ = lean_ctor_get(v_impl_3089_, 2);
lean_inc(v_v_3094_);
v_l_3095_ = lean_ctor_get(v_impl_3089_, 3);
lean_inc(v_l_3095_);
v_r_3096_ = lean_ctor_get(v_impl_3089_, 4);
lean_inc(v_r_3096_);
v___x_3097_ = lean_unsigned_to_nat(3u);
v___x_3098_ = lean_nat_mul(v___x_3097_, v_size_3091_);
v___x_3099_ = lean_nat_dec_lt(v___x_3098_, v_size_3092_);
lean_dec(v___x_3098_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3103_; 
lean_dec(v_r_3096_);
lean_dec(v_l_3095_);
lean_dec(v_v_3094_);
lean_dec(v_k_3093_);
v___x_3100_ = lean_nat_add(v___x_3090_, v_size_3092_);
lean_dec(v_size_3092_);
v___x_3101_ = lean_nat_add(v___x_3100_, v_size_3091_);
lean_dec(v___x_3100_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 3, v_impl_3089_);
lean_ctor_set(v___x_3086_, 0, v___x_3101_);
v___x_3103_ = v___x_3086_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_k_3081_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_v_3082_);
lean_ctor_set(v_reuseFailAlloc_3104_, 3, v_impl_3089_);
lean_ctor_set(v_reuseFailAlloc_3104_, 4, v_r_3084_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
else
{
lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3170_; 
v_isSharedCheck_3170_ = !lean_is_exclusive(v_impl_3089_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; lean_object* v_unused_3172_; lean_object* v_unused_3173_; lean_object* v_unused_3174_; lean_object* v_unused_3175_; 
v_unused_3171_ = lean_ctor_get(v_impl_3089_, 4);
lean_dec(v_unused_3171_);
v_unused_3172_ = lean_ctor_get(v_impl_3089_, 3);
lean_dec(v_unused_3172_);
v_unused_3173_ = lean_ctor_get(v_impl_3089_, 2);
lean_dec(v_unused_3173_);
v_unused_3174_ = lean_ctor_get(v_impl_3089_, 1);
lean_dec(v_unused_3174_);
v_unused_3175_ = lean_ctor_get(v_impl_3089_, 0);
lean_dec(v_unused_3175_);
v___x_3106_ = v_impl_3089_;
v_isShared_3107_ = v_isSharedCheck_3170_;
goto v_resetjp_3105_;
}
else
{
lean_dec(v_impl_3089_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3170_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v_size_3108_; lean_object* v_size_3109_; lean_object* v_k_3110_; lean_object* v_v_3111_; lean_object* v_l_3112_; lean_object* v_r_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v_size_3108_ = lean_ctor_get(v_l_3095_, 0);
v_size_3109_ = lean_ctor_get(v_r_3096_, 0);
v_k_3110_ = lean_ctor_get(v_r_3096_, 1);
v_v_3111_ = lean_ctor_get(v_r_3096_, 2);
v_l_3112_ = lean_ctor_get(v_r_3096_, 3);
v_r_3113_ = lean_ctor_get(v_r_3096_, 4);
v___x_3114_ = lean_unsigned_to_nat(2u);
v___x_3115_ = lean_nat_mul(v___x_3114_, v_size_3108_);
v___x_3116_ = lean_nat_dec_lt(v_size_3109_, v___x_3115_);
lean_dec(v___x_3115_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3145_; 
lean_inc(v_r_3113_);
lean_inc(v_l_3112_);
lean_inc(v_v_3111_);
lean_inc(v_k_3110_);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_r_3096_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; lean_object* v_unused_3147_; lean_object* v_unused_3148_; lean_object* v_unused_3149_; lean_object* v_unused_3150_; 
v_unused_3146_ = lean_ctor_get(v_r_3096_, 4);
lean_dec(v_unused_3146_);
v_unused_3147_ = lean_ctor_get(v_r_3096_, 3);
lean_dec(v_unused_3147_);
v_unused_3148_ = lean_ctor_get(v_r_3096_, 2);
lean_dec(v_unused_3148_);
v_unused_3149_ = lean_ctor_get(v_r_3096_, 1);
lean_dec(v_unused_3149_);
v_unused_3150_ = lean_ctor_get(v_r_3096_, 0);
lean_dec(v_unused_3150_);
v___x_3118_ = v_r_3096_;
v_isShared_3119_ = v_isSharedCheck_3145_;
goto v_resetjp_3117_;
}
else
{
lean_dec(v_r_3096_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3145_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___x_3133_; lean_object* v___y_3135_; 
v___x_3120_ = lean_nat_add(v___x_3090_, v_size_3092_);
lean_dec(v_size_3092_);
v___x_3121_ = lean_nat_add(v___x_3120_, v_size_3091_);
lean_dec(v___x_3120_);
v___x_3133_ = lean_nat_add(v___x_3090_, v_size_3108_);
if (lean_obj_tag(v_l_3112_) == 0)
{
lean_object* v_size_3143_; 
v_size_3143_ = lean_ctor_get(v_l_3112_, 0);
lean_inc(v_size_3143_);
v___y_3135_ = v_size_3143_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3144_; 
v___x_3144_ = lean_unsigned_to_nat(0u);
v___y_3135_ = v___x_3144_;
goto v___jp_3134_;
}
v___jp_3122_:
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3126_ = lean_nat_add(v___y_3123_, v___y_3125_);
lean_dec(v___y_3125_);
lean_dec(v___y_3123_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 4, v_r_3084_);
lean_ctor_set(v___x_3118_, 3, v_r_3113_);
lean_ctor_set(v___x_3118_, 2, v_v_3082_);
lean_ctor_set(v___x_3118_, 1, v_k_3081_);
lean_ctor_set(v___x_3118_, 0, v___x_3126_);
v___x_3128_ = v___x_3118_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3126_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_k_3081_);
lean_ctor_set(v_reuseFailAlloc_3132_, 2, v_v_3082_);
lean_ctor_set(v_reuseFailAlloc_3132_, 3, v_r_3113_);
lean_ctor_set(v_reuseFailAlloc_3132_, 4, v_r_3084_);
v___x_3128_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3130_; 
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 4, v___x_3128_);
lean_ctor_set(v___x_3106_, 3, v___y_3124_);
lean_ctor_set(v___x_3106_, 2, v_v_3111_);
lean_ctor_set(v___x_3106_, 1, v_k_3110_);
lean_ctor_set(v___x_3106_, 0, v___x_3121_);
v___x_3130_ = v___x_3106_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3121_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_k_3110_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_v_3111_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v___y_3124_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
v___jp_3134_:
{
lean_object* v___x_3136_; lean_object* v___x_3138_; 
v___x_3136_ = lean_nat_add(v___x_3133_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec(v___x_3133_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 4, v_l_3112_);
lean_ctor_set(v___x_3086_, 3, v_l_3095_);
lean_ctor_set(v___x_3086_, 2, v_v_3094_);
lean_ctor_set(v___x_3086_, 1, v_k_3093_);
lean_ctor_set(v___x_3086_, 0, v___x_3136_);
v___x_3138_ = v___x_3086_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v_k_3093_);
lean_ctor_set(v_reuseFailAlloc_3142_, 2, v_v_3094_);
lean_ctor_set(v_reuseFailAlloc_3142_, 3, v_l_3095_);
lean_ctor_set(v_reuseFailAlloc_3142_, 4, v_l_3112_);
v___x_3138_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3139_; 
v___x_3139_ = lean_nat_add(v___x_3090_, v_size_3091_);
if (lean_obj_tag(v_r_3113_) == 0)
{
lean_object* v_size_3140_; 
v_size_3140_ = lean_ctor_get(v_r_3113_, 0);
lean_inc(v_size_3140_);
v___y_3123_ = v___x_3139_;
v___y_3124_ = v___x_3138_;
v___y_3125_ = v_size_3140_;
goto v___jp_3122_;
}
else
{
lean_object* v___x_3141_; 
v___x_3141_ = lean_unsigned_to_nat(0u);
v___y_3123_ = v___x_3139_;
v___y_3124_ = v___x_3138_;
v___y_3125_ = v___x_3141_;
goto v___jp_3122_;
}
}
}
}
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3156_; 
lean_del_object(v___x_3086_);
v___x_3151_ = lean_nat_add(v___x_3090_, v_size_3092_);
lean_dec(v_size_3092_);
v___x_3152_ = lean_nat_add(v___x_3151_, v_size_3091_);
lean_dec(v___x_3151_);
v___x_3153_ = lean_nat_add(v___x_3090_, v_size_3091_);
v___x_3154_ = lean_nat_add(v___x_3153_, v_size_3109_);
lean_dec(v___x_3153_);
lean_inc_ref(v_r_3084_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 4, v_r_3084_);
lean_ctor_set(v___x_3106_, 3, v_r_3096_);
lean_ctor_set(v___x_3106_, 2, v_v_3082_);
lean_ctor_set(v___x_3106_, 1, v_k_3081_);
lean_ctor_set(v___x_3106_, 0, v___x_3154_);
v___x_3156_ = v___x_3106_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3154_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_k_3081_);
lean_ctor_set(v_reuseFailAlloc_3169_, 2, v_v_3082_);
lean_ctor_set(v_reuseFailAlloc_3169_, 3, v_r_3096_);
lean_ctor_set(v_reuseFailAlloc_3169_, 4, v_r_3084_);
v___x_3156_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
v_isSharedCheck_3163_ = !lean_is_exclusive(v_r_3084_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; lean_object* v_unused_3165_; lean_object* v_unused_3166_; lean_object* v_unused_3167_; lean_object* v_unused_3168_; 
v_unused_3164_ = lean_ctor_get(v_r_3084_, 4);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_r_3084_, 3);
lean_dec(v_unused_3165_);
v_unused_3166_ = lean_ctor_get(v_r_3084_, 2);
lean_dec(v_unused_3166_);
v_unused_3167_ = lean_ctor_get(v_r_3084_, 1);
lean_dec(v_unused_3167_);
v_unused_3168_ = lean_ctor_get(v_r_3084_, 0);
lean_dec(v_unused_3168_);
v___x_3158_ = v_r_3084_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_dec(v_r_3084_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
lean_ctor_set(v___x_3158_, 4, v___x_3156_);
lean_ctor_set(v___x_3158_, 3, v_l_3095_);
lean_ctor_set(v___x_3158_, 2, v_v_3094_);
lean_ctor_set(v___x_3158_, 1, v_k_3093_);
lean_ctor_set(v___x_3158_, 0, v___x_3152_);
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_3152_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v_k_3093_);
lean_ctor_set(v_reuseFailAlloc_3162_, 2, v_v_3094_);
lean_ctor_set(v_reuseFailAlloc_3162_, 3, v_l_3095_);
lean_ctor_set(v_reuseFailAlloc_3162_, 4, v___x_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3176_; 
v_l_3176_ = lean_ctor_get(v_impl_3089_, 3);
lean_inc(v_l_3176_);
if (lean_obj_tag(v_l_3176_) == 0)
{
lean_object* v_r_3177_; lean_object* v_k_3178_; lean_object* v_v_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3190_; 
v_r_3177_ = lean_ctor_get(v_impl_3089_, 4);
v_k_3178_ = lean_ctor_get(v_impl_3089_, 1);
v_v_3179_ = lean_ctor_get(v_impl_3089_, 2);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_impl_3089_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; lean_object* v_unused_3192_; 
v_unused_3191_ = lean_ctor_get(v_impl_3089_, 3);
lean_dec(v_unused_3191_);
v_unused_3192_ = lean_ctor_get(v_impl_3089_, 0);
lean_dec(v_unused_3192_);
v___x_3181_ = v_impl_3089_;
v_isShared_3182_ = v_isSharedCheck_3190_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_r_3177_);
lean_inc(v_v_3179_);
lean_inc(v_k_3178_);
lean_dec(v_impl_3089_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3190_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3183_; lean_object* v___x_3185_; 
v___x_3183_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3177_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 3, v_r_3177_);
lean_ctor_set(v___x_3181_, 2, v_v_3082_);
lean_ctor_set(v___x_3181_, 1, v_k_3081_);
lean_ctor_set(v___x_3181_, 0, v___x_3090_);
v___x_3185_ = v___x_3181_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v_k_3081_);
lean_ctor_set(v_reuseFailAlloc_3189_, 2, v_v_3082_);
lean_ctor_set(v_reuseFailAlloc_3189_, 3, v_r_3177_);
lean_ctor_set(v_reuseFailAlloc_3189_, 4, v_r_3177_);
v___x_3185_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3187_; 
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 4, v___x_3185_);
lean_ctor_set(v___x_3086_, 3, v_l_3176_);
lean_ctor_set(v___x_3086_, 2, v_v_3179_);
lean_ctor_set(v___x_3086_, 1, v_k_3178_);
lean_ctor_set(v___x_3086_, 0, v___x_3183_);
v___x_3187_ = v___x_3086_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3183_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v_k_3178_);
lean_ctor_set(v_reuseFailAlloc_3188_, 2, v_v_3179_);
lean_ctor_set(v_reuseFailAlloc_3188_, 3, v_l_3176_);
lean_ctor_set(v_reuseFailAlloc_3188_, 4, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
else
{
lean_object* v_r_3193_; 
v_r_3193_ = lean_ctor_get(v_impl_3089_, 4);
lean_inc(v_r_3193_);
if (lean_obj_tag(v_r_3193_) == 0)
{
lean_object* v_k_3194_; lean_object* v_v_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3218_; 
v_k_3194_ = lean_ctor_get(v_impl_3089_, 1);
v_v_3195_ = lean_ctor_get(v_impl_3089_, 2);
v_isSharedCheck_3218_ = !lean_is_exclusive(v_impl_3089_);
if (v_isSharedCheck_3218_ == 0)
{
lean_object* v_unused_3219_; lean_object* v_unused_3220_; lean_object* v_unused_3221_; 
v_unused_3219_ = lean_ctor_get(v_impl_3089_, 4);
lean_dec(v_unused_3219_);
v_unused_3220_ = lean_ctor_get(v_impl_3089_, 3);
lean_dec(v_unused_3220_);
v_unused_3221_ = lean_ctor_get(v_impl_3089_, 0);
lean_dec(v_unused_3221_);
v___x_3197_ = v_impl_3089_;
v_isShared_3198_ = v_isSharedCheck_3218_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_v_3195_);
lean_inc(v_k_3194_);
lean_dec(v_impl_3089_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3218_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v_k_3199_; lean_object* v_v_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3214_; 
v_k_3199_ = lean_ctor_get(v_r_3193_, 1);
v_v_3200_ = lean_ctor_get(v_r_3193_, 2);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_r_3193_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; lean_object* v_unused_3216_; lean_object* v_unused_3217_; 
v_unused_3215_ = lean_ctor_get(v_r_3193_, 4);
lean_dec(v_unused_3215_);
v_unused_3216_ = lean_ctor_get(v_r_3193_, 3);
lean_dec(v_unused_3216_);
v_unused_3217_ = lean_ctor_get(v_r_3193_, 0);
lean_dec(v_unused_3217_);
v___x_3202_ = v_r_3193_;
v_isShared_3203_ = v_isSharedCheck_3214_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_v_3200_);
lean_inc(v_k_3199_);
lean_dec(v_r_3193_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3214_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; lean_object* v___x_3206_; 
v___x_3204_ = lean_unsigned_to_nat(3u);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 4, v_l_3176_);
lean_ctor_set(v___x_3202_, 3, v_l_3176_);
lean_ctor_set(v___x_3202_, 2, v_v_3195_);
lean_ctor_set(v___x_3202_, 1, v_k_3194_);
lean_ctor_set(v___x_3202_, 0, v___x_3090_);
v___x_3206_ = v___x_3202_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3213_, 1, v_k_3194_);
lean_ctor_set(v_reuseFailAlloc_3213_, 2, v_v_3195_);
lean_ctor_set(v_reuseFailAlloc_3213_, 3, v_l_3176_);
lean_ctor_set(v_reuseFailAlloc_3213_, 4, v_l_3176_);
v___x_3206_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3208_; 
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 4, v_l_3176_);
lean_ctor_set(v___x_3197_, 2, v_v_3082_);
lean_ctor_set(v___x_3197_, 1, v_k_3081_);
lean_ctor_set(v___x_3197_, 0, v___x_3090_);
v___x_3208_ = v___x_3197_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3090_);
lean_ctor_set(v_reuseFailAlloc_3212_, 1, v_k_3081_);
lean_ctor_set(v_reuseFailAlloc_3212_, 2, v_v_3082_);
lean_ctor_set(v_reuseFailAlloc_3212_, 3, v_l_3176_);
lean_ctor_set(v_reuseFailAlloc_3212_, 4, v_l_3176_);
v___x_3208_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3210_; 
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 4, v___x_3208_);
lean_ctor_set(v___x_3086_, 3, v___x_3206_);
lean_ctor_set(v___x_3086_, 2, v_v_3200_);
lean_ctor_set(v___x_3086_, 1, v_k_3199_);
lean_ctor_set(v___x_3086_, 0, v___x_3204_);
v___x_3210_ = v___x_3086_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v___x_3204_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_k_3199_);
lean_ctor_set(v_reuseFailAlloc_3211_, 2, v_v_3200_);
lean_ctor_set(v_reuseFailAlloc_3211_, 3, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3211_, 4, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
}
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3222_ = lean_unsigned_to_nat(2u);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 4, v_r_3193_);
lean_ctor_set(v___x_3086_, 3, v_impl_3089_);
lean_ctor_set(v___x_3086_, 0, v___x_3222_);
v___x_3224_ = v___x_3086_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_k_3081_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v_v_3082_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v_impl_3089_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v_r_3193_);
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
case 1:
{
lean_object* v___x_3227_; 
lean_dec(v_v_3082_);
lean_dec(v_k_3081_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 2, v_v_3078_);
lean_ctor_set(v___x_3086_, 1, v_k_3077_);
v___x_3227_ = v___x_3086_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_size_3080_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v_k_3077_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v_v_3078_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v_l_3083_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v_r_3084_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
default: 
{
lean_object* v_impl_3229_; lean_object* v___x_3230_; 
lean_dec(v_size_3080_);
v_impl_3229_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3077_, v_v_3078_, v_r_3084_);
v___x_3230_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3083_) == 0)
{
lean_object* v_size_3231_; lean_object* v_size_3232_; lean_object* v_k_3233_; lean_object* v_v_3234_; lean_object* v_l_3235_; lean_object* v_r_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; 
v_size_3231_ = lean_ctor_get(v_l_3083_, 0);
v_size_3232_ = lean_ctor_get(v_impl_3229_, 0);
lean_inc(v_size_3232_);
v_k_3233_ = lean_ctor_get(v_impl_3229_, 1);
lean_inc(v_k_3233_);
v_v_3234_ = lean_ctor_get(v_impl_3229_, 2);
lean_inc(v_v_3234_);
v_l_3235_ = lean_ctor_get(v_impl_3229_, 3);
lean_inc(v_l_3235_);
v_r_3236_ = lean_ctor_get(v_impl_3229_, 4);
lean_inc(v_r_3236_);
v___x_3237_ = lean_unsigned_to_nat(3u);
v___x_3238_ = lean_nat_mul(v___x_3237_, v_size_3231_);
v___x_3239_ = lean_nat_dec_lt(v___x_3238_, v_size_3232_);
lean_dec(v___x_3238_);
if (v___x_3239_ == 0)
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3243_; 
lean_dec(v_r_3236_);
lean_dec(v_l_3235_);
lean_dec(v_v_3234_);
lean_dec(v_k_3233_);
v___x_3240_ = lean_nat_add(v___x_3230_, v_size_3231_);
v___x_3241_ = lean_nat_add(v___x_3240_, v_size_3232_);
lean_dec(v_size_3232_);
lean_dec(v___x_3240_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 4, v_impl_3229_);
lean_ctor_set(v___x_3086_, 0, v___x_3241_);
v___x_3243_ = v___x_3086_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_k_3081_);
lean_ctor_set(v_reuseFailAlloc_3244_, 2, v_v_3082_);
lean_ctor_set(v_reuseFailAlloc_3244_, 3, v_l_3083_);
lean_ctor_set(v_reuseFailAlloc_3244_, 4, v_impl_3229_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
else
{
lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3308_; 
v_isSharedCheck_3308_ = !lean_is_exclusive(v_impl_3229_);
if (v_isSharedCheck_3308_ == 0)
{
lean_object* v_unused_3309_; lean_object* v_unused_3310_; lean_object* v_unused_3311_; lean_object* v_unused_3312_; lean_object* v_unused_3313_; 
v_unused_3309_ = lean_ctor_get(v_impl_3229_, 4);
lean_dec(v_unused_3309_);
v_unused_3310_ = lean_ctor_get(v_impl_3229_, 3);
lean_dec(v_unused_3310_);
v_unused_3311_ = lean_ctor_get(v_impl_3229_, 2);
lean_dec(v_unused_3311_);
v_unused_3312_ = lean_ctor_get(v_impl_3229_, 1);
lean_dec(v_unused_3312_);
v_unused_3313_ = lean_ctor_get(v_impl_3229_, 0);
lean_dec(v_unused_3313_);
v___x_3246_ = v_impl_3229_;
v_isShared_3247_ = v_isSharedCheck_3308_;
goto v_resetjp_3245_;
}
else
{
lean_dec(v_impl_3229_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3308_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v_size_3248_; lean_object* v_k_3249_; lean_object* v_v_3250_; lean_object* v_l_3251_; lean_object* v_r_3252_; lean_object* v_size_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
v_size_3248_ = lean_ctor_get(v_l_3235_, 0);
v_k_3249_ = lean_ctor_get(v_l_3235_, 1);
v_v_3250_ = lean_ctor_get(v_l_3235_, 2);
v_l_3251_ = lean_ctor_get(v_l_3235_, 3);
v_r_3252_ = lean_ctor_get(v_l_3235_, 4);
v_size_3253_ = lean_ctor_get(v_r_3236_, 0);
v___x_3254_ = lean_unsigned_to_nat(2u);
v___x_3255_ = lean_nat_mul(v___x_3254_, v_size_3253_);
v___x_3256_ = lean_nat_dec_lt(v_size_3248_, v___x_3255_);
lean_dec(v___x_3255_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3284_; 
lean_inc(v_r_3252_);
lean_inc(v_l_3251_);
lean_inc(v_v_3250_);
lean_inc(v_k_3249_);
v_isSharedCheck_3284_ = !lean_is_exclusive(v_l_3235_);
if (v_isSharedCheck_3284_ == 0)
{
lean_object* v_unused_3285_; lean_object* v_unused_3286_; lean_object* v_unused_3287_; lean_object* v_unused_3288_; lean_object* v_unused_3289_; 
v_unused_3285_ = lean_ctor_get(v_l_3235_, 4);
lean_dec(v_unused_3285_);
v_unused_3286_ = lean_ctor_get(v_l_3235_, 3);
lean_dec(v_unused_3286_);
v_unused_3287_ = lean_ctor_get(v_l_3235_, 2);
lean_dec(v_unused_3287_);
v_unused_3288_ = lean_ctor_get(v_l_3235_, 1);
lean_dec(v_unused_3288_);
v_unused_3289_ = lean_ctor_get(v_l_3235_, 0);
lean_dec(v_unused_3289_);
v___x_3258_ = v_l_3235_;
v_isShared_3259_ = v_isSharedCheck_3284_;
goto v_resetjp_3257_;
}
else
{
lean_dec(v_l_3235_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3284_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3274_; 
v___x_3260_ = lean_nat_add(v___x_3230_, v_size_3231_);
v___x_3261_ = lean_nat_add(v___x_3260_, v_size_3232_);
lean_dec(v_size_3232_);
if (lean_obj_tag(v_l_3251_) == 0)
{
lean_object* v_size_3282_; 
v_size_3282_ = lean_ctor_get(v_l_3251_, 0);
lean_inc(v_size_3282_);
v___y_3274_ = v_size_3282_;
goto v___jp_3273_;
}
else
{
lean_object* v___x_3283_; 
v___x_3283_ = lean_unsigned_to_nat(0u);
v___y_3274_ = v___x_3283_;
goto v___jp_3273_;
}
v___jp_3262_:
{
lean_object* v___x_3266_; lean_object* v___x_3268_; 
v___x_3266_ = lean_nat_add(v___y_3264_, v___y_3265_);
lean_dec(v___y_3265_);
lean_dec(v___y_3264_);
if (v_isShared_3259_ == 0)
{
lean_ctor_set(v___x_3258_, 4, v_r_3236_);
lean_ctor_set(v___x_3258_, 3, v_r_3252_);
lean_ctor_set(v___x_3258_, 2, v_v_3234_);
lean_ctor_set(v___x_3258_, 1, v_k_3233_);
lean_ctor_set(v___x_3258_, 0, v___x_3266_);
v___x_3268_ = v___x_3258_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v___x_3266_);
lean_ctor_set(v_reuseFailAlloc_3272_, 1, v_k_3233_);
lean_ctor_set(v_reuseFailAlloc_3272_, 2, v_v_3234_);
lean_ctor_set(v_reuseFailAlloc_3272_, 3, v_r_3252_);
lean_ctor_set(v_reuseFailAlloc_3272_, 4, v_r_3236_);
v___x_3268_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
lean_object* v___x_3270_; 
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 4, v___x_3268_);
lean_ctor_set(v___x_3246_, 3, v___y_3263_);
lean_ctor_set(v___x_3246_, 2, v_v_3250_);
lean_ctor_set(v___x_3246_, 1, v_k_3249_);
lean_ctor_set(v___x_3246_, 0, v___x_3261_);
v___x_3270_ = v___x_3246_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3261_);
lean_ctor_set(v_reuseFailAlloc_3271_, 1, v_k_3249_);
lean_ctor_set(v_reuseFailAlloc_3271_, 2, v_v_3250_);
lean_ctor_set(v_reuseFailAlloc_3271_, 3, v___y_3263_);
lean_ctor_set(v_reuseFailAlloc_3271_, 4, v___x_3268_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
v___jp_3273_:
{
lean_object* v___x_3275_; lean_object* v___x_3277_; 
v___x_3275_ = lean_nat_add(v___x_3260_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec(v___x_3260_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 4, v_l_3251_);
lean_ctor_set(v___x_3086_, 0, v___x_3275_);
v___x_3277_ = v___x_3086_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3275_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v_k_3081_);
lean_ctor_set(v_reuseFailAlloc_3281_, 2, v_v_3082_);
lean_ctor_set(v_reuseFailAlloc_3281_, 3, v_l_3083_);
lean_ctor_set(v_reuseFailAlloc_3281_, 4, v_l_3251_);
v___x_3277_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
lean_object* v___x_3278_; 
v___x_3278_ = lean_nat_add(v___x_3230_, v_size_3253_);
if (lean_obj_tag(v_r_3252_) == 0)
{
lean_object* v_size_3279_; 
v_size_3279_ = lean_ctor_get(v_r_3252_, 0);
lean_inc(v_size_3279_);
v___y_3263_ = v___x_3277_;
v___y_3264_ = v___x_3278_;
v___y_3265_ = v_size_3279_;
goto v___jp_3262_;
}
else
{
lean_object* v___x_3280_; 
v___x_3280_ = lean_unsigned_to_nat(0u);
v___y_3263_ = v___x_3277_;
v___y_3264_ = v___x_3278_;
v___y_3265_ = v___x_3280_;
goto v___jp_3262_;
}
}
}
}
}
else
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3294_; 
lean_del_object(v___x_3086_);
v___x_3290_ = lean_nat_add(v___x_3230_, v_size_3231_);
v___x_3291_ = lean_nat_add(v___x_3290_, v_size_3232_);
lean_dec(v_size_3232_);
v___x_3292_ = lean_nat_add(v___x_3290_, v_size_3248_);
lean_dec(v___x_3290_);
lean_inc_ref(v_l_3083_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 4, v_l_3235_);
lean_ctor_set(v___x_3246_, 3, v_l_3083_);
lean_ctor_set(v___x_3246_, 2, v_v_3082_);
lean_ctor_set(v___x_3246_, 1, v_k_3081_);
lean_ctor_set(v___x_3246_, 0, v___x_3292_);
v___x_3294_ = v___x_3246_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3292_);
lean_ctor_set(v_reuseFailAlloc_3307_, 1, v_k_3081_);
lean_ctor_set(v_reuseFailAlloc_3307_, 2, v_v_3082_);
lean_ctor_set(v_reuseFailAlloc_3307_, 3, v_l_3083_);
lean_ctor_set(v_reuseFailAlloc_3307_, 4, v_l_3235_);
v___x_3294_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
v_isSharedCheck_3301_ = !lean_is_exclusive(v_l_3083_);
if (v_isSharedCheck_3301_ == 0)
{
lean_object* v_unused_3302_; lean_object* v_unused_3303_; lean_object* v_unused_3304_; lean_object* v_unused_3305_; lean_object* v_unused_3306_; 
v_unused_3302_ = lean_ctor_get(v_l_3083_, 4);
lean_dec(v_unused_3302_);
v_unused_3303_ = lean_ctor_get(v_l_3083_, 3);
lean_dec(v_unused_3303_);
v_unused_3304_ = lean_ctor_get(v_l_3083_, 2);
lean_dec(v_unused_3304_);
v_unused_3305_ = lean_ctor_get(v_l_3083_, 1);
lean_dec(v_unused_3305_);
v_unused_3306_ = lean_ctor_get(v_l_3083_, 0);
lean_dec(v_unused_3306_);
v___x_3296_ = v_l_3083_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_dec(v_l_3083_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v_r_3236_);
lean_ctor_set(v___x_3296_, 3, v___x_3294_);
lean_ctor_set(v___x_3296_, 2, v_v_3234_);
lean_ctor_set(v___x_3296_, 1, v_k_3233_);
lean_ctor_set(v___x_3296_, 0, v___x_3291_);
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_k_3233_);
lean_ctor_set(v_reuseFailAlloc_3300_, 2, v_v_3234_);
lean_ctor_set(v_reuseFailAlloc_3300_, 3, v___x_3294_);
lean_ctor_set(v_reuseFailAlloc_3300_, 4, v_r_3236_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3314_; 
v_l_3314_ = lean_ctor_get(v_impl_3229_, 3);
lean_inc(v_l_3314_);
if (lean_obj_tag(v_l_3314_) == 0)
{
lean_object* v_r_3315_; lean_object* v_k_3316_; lean_object* v_v_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3340_; 
v_r_3315_ = lean_ctor_get(v_impl_3229_, 4);
v_k_3316_ = lean_ctor_get(v_impl_3229_, 1);
v_v_3317_ = lean_ctor_get(v_impl_3229_, 2);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_impl_3229_);
if (v_isSharedCheck_3340_ == 0)
{
lean_object* v_unused_3341_; lean_object* v_unused_3342_; 
v_unused_3341_ = lean_ctor_get(v_impl_3229_, 3);
lean_dec(v_unused_3341_);
v_unused_3342_ = lean_ctor_get(v_impl_3229_, 0);
lean_dec(v_unused_3342_);
v___x_3319_ = v_impl_3229_;
v_isShared_3320_ = v_isSharedCheck_3340_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_r_3315_);
lean_inc(v_v_3317_);
lean_inc(v_k_3316_);
lean_dec(v_impl_3229_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3340_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v_k_3321_; lean_object* v_v_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3336_; 
v_k_3321_ = lean_ctor_get(v_l_3314_, 1);
v_v_3322_ = lean_ctor_get(v_l_3314_, 2);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_l_3314_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; lean_object* v_unused_3338_; lean_object* v_unused_3339_; 
v_unused_3337_ = lean_ctor_get(v_l_3314_, 4);
lean_dec(v_unused_3337_);
v_unused_3338_ = lean_ctor_get(v_l_3314_, 3);
lean_dec(v_unused_3338_);
v_unused_3339_ = lean_ctor_get(v_l_3314_, 0);
lean_dec(v_unused_3339_);
v___x_3324_ = v_l_3314_;
v_isShared_3325_ = v_isSharedCheck_3336_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_v_3322_);
lean_inc(v_k_3321_);
lean_dec(v_l_3314_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3336_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; lean_object* v___x_3328_; 
v___x_3326_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3315_, 2);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 4, v_r_3315_);
lean_ctor_set(v___x_3324_, 3, v_r_3315_);
lean_ctor_set(v___x_3324_, 2, v_v_3082_);
lean_ctor_set(v___x_3324_, 1, v_k_3081_);
lean_ctor_set(v___x_3324_, 0, v___x_3230_);
v___x_3328_ = v___x_3324_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v_k_3081_);
lean_ctor_set(v_reuseFailAlloc_3335_, 2, v_v_3082_);
lean_ctor_set(v_reuseFailAlloc_3335_, 3, v_r_3315_);
lean_ctor_set(v_reuseFailAlloc_3335_, 4, v_r_3315_);
v___x_3328_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
lean_object* v___x_3330_; 
lean_inc(v_r_3315_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set(v___x_3319_, 3, v_r_3315_);
lean_ctor_set(v___x_3319_, 0, v___x_3230_);
v___x_3330_ = v___x_3319_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_k_3316_);
lean_ctor_set(v_reuseFailAlloc_3334_, 2, v_v_3317_);
lean_ctor_set(v_reuseFailAlloc_3334_, 3, v_r_3315_);
lean_ctor_set(v_reuseFailAlloc_3334_, 4, v_r_3315_);
v___x_3330_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
lean_object* v___x_3332_; 
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 4, v___x_3330_);
lean_ctor_set(v___x_3086_, 3, v___x_3328_);
lean_ctor_set(v___x_3086_, 2, v_v_3322_);
lean_ctor_set(v___x_3086_, 1, v_k_3321_);
lean_ctor_set(v___x_3086_, 0, v___x_3326_);
v___x_3332_ = v___x_3086_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3333_, 1, v_k_3321_);
lean_ctor_set(v_reuseFailAlloc_3333_, 2, v_v_3322_);
lean_ctor_set(v_reuseFailAlloc_3333_, 3, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3333_, 4, v___x_3330_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
}
}
else
{
lean_object* v_r_3343_; 
v_r_3343_ = lean_ctor_get(v_impl_3229_, 4);
lean_inc(v_r_3343_);
if (lean_obj_tag(v_r_3343_) == 0)
{
lean_object* v_k_3344_; lean_object* v_v_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3356_; 
v_k_3344_ = lean_ctor_get(v_impl_3229_, 1);
v_v_3345_ = lean_ctor_get(v_impl_3229_, 2);
v_isSharedCheck_3356_ = !lean_is_exclusive(v_impl_3229_);
if (v_isSharedCheck_3356_ == 0)
{
lean_object* v_unused_3357_; lean_object* v_unused_3358_; lean_object* v_unused_3359_; 
v_unused_3357_ = lean_ctor_get(v_impl_3229_, 4);
lean_dec(v_unused_3357_);
v_unused_3358_ = lean_ctor_get(v_impl_3229_, 3);
lean_dec(v_unused_3358_);
v_unused_3359_ = lean_ctor_get(v_impl_3229_, 0);
lean_dec(v_unused_3359_);
v___x_3347_ = v_impl_3229_;
v_isShared_3348_ = v_isSharedCheck_3356_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_v_3345_);
lean_inc(v_k_3344_);
lean_dec(v_impl_3229_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3356_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v___x_3351_; 
v___x_3349_ = lean_unsigned_to_nat(3u);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 4, v_l_3314_);
lean_ctor_set(v___x_3347_, 2, v_v_3082_);
lean_ctor_set(v___x_3347_, 1, v_k_3081_);
lean_ctor_set(v___x_3347_, 0, v___x_3230_);
v___x_3351_ = v___x_3347_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_k_3081_);
lean_ctor_set(v_reuseFailAlloc_3355_, 2, v_v_3082_);
lean_ctor_set(v_reuseFailAlloc_3355_, 3, v_l_3314_);
lean_ctor_set(v_reuseFailAlloc_3355_, 4, v_l_3314_);
v___x_3351_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
lean_object* v___x_3353_; 
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 4, v_r_3343_);
lean_ctor_set(v___x_3086_, 3, v___x_3351_);
lean_ctor_set(v___x_3086_, 2, v_v_3345_);
lean_ctor_set(v___x_3086_, 1, v_k_3344_);
lean_ctor_set(v___x_3086_, 0, v___x_3349_);
v___x_3353_ = v___x_3086_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3349_);
lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_k_3344_);
lean_ctor_set(v_reuseFailAlloc_3354_, 2, v_v_3345_);
lean_ctor_set(v_reuseFailAlloc_3354_, 3, v___x_3351_);
lean_ctor_set(v_reuseFailAlloc_3354_, 4, v_r_3343_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
else
{
lean_object* v___x_3360_; lean_object* v___x_3362_; 
v___x_3360_ = lean_unsigned_to_nat(2u);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 4, v_impl_3229_);
lean_ctor_set(v___x_3086_, 3, v_r_3343_);
lean_ctor_set(v___x_3086_, 0, v___x_3360_);
v___x_3362_ = v___x_3086_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_k_3081_);
lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_v_3082_);
lean_ctor_set(v_reuseFailAlloc_3363_, 3, v_r_3343_);
lean_ctor_set(v_reuseFailAlloc_3363_, 4, v_impl_3229_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
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
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = lean_unsigned_to_nat(1u);
v___x_3366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
lean_ctor_set(v___x_3366_, 1, v_k_3077_);
lean_ctor_set(v___x_3366_, 2, v_v_3078_);
lean_ctor_set(v___x_3366_, 3, v_t_3079_);
lean_ctor_set(v___x_3366_, 4, v_t_3079_);
return v___x_3366_;
}
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3367_ = lean_box(1);
v___x_3368_ = l_Lake_Package_depsFacetConfig;
v___x_3369_ = l_Lake_Package_depsFacet;
v___x_3370_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3369_, v___x_3368_, v___x_3367_);
return v___x_3370_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3371_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__0, &l_Lake_Package_initFacetConfigs___closed__0_once, _init_l_Lake_Package_initFacetConfigs___closed__0);
v___x_3372_ = l_Lake_Package_transDepsFacetConfig;
v___x_3373_ = l_Lake_Package_transDepsFacet;
v___x_3374_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3373_, v___x_3372_, v___x_3371_);
return v___x_3374_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3375_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__1, &l_Lake_Package_initFacetConfigs___closed__1_once, _init_l_Lake_Package_initFacetConfigs___closed__1);
v___x_3376_ = l_Lake_Package_extraDepFacetConfig;
v___x_3377_ = l_Lake_Package_extraDepFacet;
v___x_3378_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3377_, v___x_3376_, v___x_3375_);
return v___x_3378_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3379_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__2, &l_Lake_Package_initFacetConfigs___closed__2_once, _init_l_Lake_Package_initFacetConfigs___closed__2);
v___x_3380_ = l_Lake_Package_optBuildCacheFacetConfig;
v___x_3381_ = l_Lake_Package_optBuildCacheFacet;
v___x_3382_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3381_, v___x_3380_, v___x_3379_);
return v___x_3382_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3383_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__3, &l_Lake_Package_initFacetConfigs___closed__3_once, _init_l_Lake_Package_initFacetConfigs___closed__3);
v___x_3384_ = l_Lake_Package_buildCacheFacetConfig;
v___x_3385_ = l_Lake_Package_buildCacheFacet;
v___x_3386_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3385_, v___x_3384_, v___x_3383_);
return v___x_3386_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3387_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__4, &l_Lake_Package_initFacetConfigs___closed__4_once, _init_l_Lake_Package_initFacetConfigs___closed__4);
v___x_3388_ = l_Lake_Package_optBarrelFacetConfig;
v___x_3389_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3390_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3389_, v___x_3388_, v___x_3387_);
return v___x_3390_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3391_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__5, &l_Lake_Package_initFacetConfigs___closed__5_once, _init_l_Lake_Package_initFacetConfigs___closed__5);
v___x_3392_ = l_Lake_Package_barrelFacetConfig;
v___x_3393_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3394_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3393_, v___x_3392_, v___x_3391_);
return v___x_3394_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3395_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__6, &l_Lake_Package_initFacetConfigs___closed__6_once, _init_l_Lake_Package_initFacetConfigs___closed__6);
v___x_3396_ = l_Lake_Package_optGitHubReleaseFacetConfig;
v___x_3397_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3398_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3397_, v___x_3396_, v___x_3395_);
return v___x_3398_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3399_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__7, &l_Lake_Package_initFacetConfigs___closed__7_once, _init_l_Lake_Package_initFacetConfigs___closed__7);
v___x_3400_ = l_Lake_Package_gitHubReleaseFacetConfig;
v___x_3401_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3402_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3401_, v___x_3400_, v___x_3399_);
return v___x_3402_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs(void){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__8, &l_Lake_Package_initFacetConfigs___closed__8_once, _init_l_Lake_Package_initFacetConfigs___closed__8);
return v___x_3403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3404_, lean_object* v_k_3405_, lean_object* v_v_3406_, lean_object* v_t_3407_, lean_object* v_hl_3408_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3405_, v_v_3406_, v_t_3407_);
return v___x_3409_;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs(void){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Lake_Package_initFacetConfigs;
return v___x_3410_;
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
