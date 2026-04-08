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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lake_ensureJob___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lake_Job_toOpaque___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lake_Job_renew___redArg(lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
lean_object* l_Lake_Reservoir_pkgApiUrl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_uriEncode(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultLakeDir;
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
lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*);
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
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern lean_object* l_Lake_Package_transDepsFacet;
lean_object* l_Lake_Job_await___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = ": package not found for dependency '"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "' (this is likely a bug in Lake)"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__0_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__2 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3;
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0(lean_object* v___x_4_, lean_object* v_as_5_, size_t v_sz_6_, size_t v_i_7_, lean_object* v_b_8_){
_start:
{
uint8_t v___x_9_; 
v___x_9_ = lean_usize_dec_lt(v_i_7_, v_sz_6_);
if (v___x_9_ == 0)
{
lean_inc_ref(v_b_8_);
return v_b_8_;
}
else
{
lean_object* v_a_10_; lean_object* v_baseName_11_; lean_object* v___x_12_; uint8_t v___x_13_; 
v_a_10_ = lean_array_uget_borrowed(v_as_5_, v_i_7_);
v_baseName_11_ = lean_ctor_get(v_a_10_, 1);
v___x_12_ = lean_box(0);
v___x_13_ = lean_name_eq(v_baseName_11_, v___x_4_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; size_t v___x_15_; size_t v___x_16_; 
v___x_14_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___closed__0));
v___x_15_ = ((size_t)1ULL);
v___x_16_ = lean_usize_add(v_i_7_, v___x_15_);
v_i_7_ = v___x_16_;
v_b_8_ = v___x_14_;
goto _start;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
lean_inc(v_a_10_);
v___x_18_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_18_, 0, v_a_10_);
v___x_19_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
v___x_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___x_12_);
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___boxed(lean_object* v___x_21_, lean_object* v_as_22_, lean_object* v_sz_23_, lean_object* v_i_24_, lean_object* v_b_25_){
_start:
{
size_t v_sz_boxed_26_; size_t v_i_boxed_27_; lean_object* v_res_28_; 
v_sz_boxed_26_ = lean_unbox_usize(v_sz_23_);
lean_dec(v_sz_23_);
v_i_boxed_27_ = lean_unbox_usize(v_i_24_);
lean_dec(v_i_24_);
v_res_28_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0(v___x_21_, v_as_22_, v_sz_boxed_26_, v_i_boxed_27_, v_b_25_);
lean_dec_ref(v_b_25_);
lean_dec_ref(v_as_22_);
lean_dec(v___x_21_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg(lean_object* v_self_31_, size_t v_sz_32_, size_t v_i_33_, lean_object* v_bs_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
uint8_t v___x_38_; 
v___x_38_ = lean_usize_dec_lt(v_i_33_, v_sz_32_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; 
lean_dec_ref(v_self_31_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v_bs_34_);
lean_ctor_set(v___x_39_, 1, v___y_36_);
return v___x_39_;
}
else
{
lean_object* v_v_40_; lean_object* v_name_41_; lean_object* v_a_43_; lean_object* v_toContext_58_; lean_object* v_packages_59_; lean_object* v___x_60_; size_t v_sz_61_; size_t v___x_62_; lean_object* v___x_63_; lean_object* v_fst_64_; 
v_v_40_ = lean_array_uget_borrowed(v_bs_34_, v_i_33_);
v_name_41_ = lean_ctor_get(v_v_40_, 0);
v_toContext_58_ = lean_ctor_get(v___y_35_, 1);
v_packages_59_ = lean_ctor_get(v_toContext_58_, 5);
v___x_60_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___closed__0));
v_sz_61_ = lean_array_size(v_packages_59_);
v___x_62_ = ((size_t)0ULL);
v___x_63_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0(v_name_41_, v_packages_59_, v_sz_61_, v___x_62_, v___x_60_);
v_fst_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_fst_64_);
lean_dec_ref(v___x_63_);
if (lean_obj_tag(v_fst_64_) == 0)
{
lean_inc(v_name_41_);
lean_dec_ref(v_bs_34_);
v_a_43_ = v___y_36_;
goto v___jp_42_;
}
else
{
lean_object* v_val_65_; 
v_val_65_ = lean_ctor_get(v_fst_64_, 0);
lean_inc(v_val_65_);
lean_dec_ref(v_fst_64_);
if (lean_obj_tag(v_val_65_) == 1)
{
lean_object* v_val_66_; lean_object* v___x_67_; lean_object* v_bs_x27_68_; size_t v___x_69_; size_t v___x_70_; lean_object* v___x_71_; 
v_val_66_ = lean_ctor_get(v_val_65_, 0);
lean_inc(v_val_66_);
lean_dec_ref(v_val_65_);
v___x_67_ = lean_unsigned_to_nat(0u);
v_bs_x27_68_ = lean_array_uset(v_bs_34_, v_i_33_, v___x_67_);
v___x_69_ = ((size_t)1ULL);
v___x_70_ = lean_usize_add(v_i_33_, v___x_69_);
v___x_71_ = lean_array_uset(v_bs_x27_68_, v_i_33_, v_val_66_);
v_i_33_ = v___x_70_;
v_bs_34_ = v___x_71_;
goto _start;
}
else
{
lean_inc(v_name_41_);
lean_dec(v_val_65_);
lean_dec_ref(v_bs_34_);
v_a_43_ = v___y_36_;
goto v___jp_42_;
}
}
v___jp_42_:
{
lean_object* v_baseName_44_; uint8_t v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_baseName_44_ = lean_ctor_get(v_self_31_, 1);
lean_inc(v_baseName_44_);
lean_dec_ref(v_self_31_);
v___x_45_ = 0;
v___x_46_ = l_Lean_Name_toString(v_baseName_44_, v___x_45_);
v___x_47_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg___closed__0));
v___x_48_ = lean_string_append(v___x_46_, v___x_47_);
v___x_49_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_41_, v___x_38_);
v___x_50_ = lean_string_append(v___x_48_, v___x_49_);
lean_dec_ref(v___x_49_);
v___x_51_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg___closed__1));
v___x_52_ = lean_string_append(v___x_50_, v___x_51_);
v___x_53_ = 3;
v___x_54_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_54_, 0, v___x_52_);
lean_ctor_set_uint8(v___x_54_, sizeof(void*)*1, v___x_53_);
v___x_55_ = lean_array_get_size(v_a_43_);
v___x_56_ = lean_array_push(v_a_43_, v___x_54_);
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
return v___x_57_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg___boxed(lean_object* v_self_73_, lean_object* v_sz_74_, lean_object* v_i_75_, lean_object* v_bs_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
size_t v_sz_boxed_80_; size_t v_i_boxed_81_; lean_object* v_res_82_; 
v_sz_boxed_80_ = lean_unbox_usize(v_sz_74_);
lean_dec(v_sz_74_);
v_i_boxed_81_ = lean_unbox_usize(v_i_75_);
lean_dec(v_i_75_);
v_res_82_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg(v_self_73_, v_sz_boxed_80_, v_i_boxed_81_, v_bs_76_, v___y_77_, v___y_78_);
lean_dec_ref(v___y_77_);
return v_res_82_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__2));
v___x_88_ = l_Lake_BuildTrace_nil(v___x_87_);
return v___x_88_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__4(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3);
v___x_91_ = 0;
v___x_92_ = 0;
v___x_93_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__0));
v___x_94_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_90_);
lean_ctor_set(v___x_94_, 2, v___x_89_);
lean_ctor_set_uint8(v___x_94_, sizeof(void*)*3, v___x_92_);
lean_ctor_set_uint8(v___x_94_, sizeof(void*)*3 + 1, v___x_91_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0(lean_object* v_depConfigs_95_, lean_object* v_self_96_, lean_object* v___x_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
size_t v_sz_105_; size_t v___x_106_; lean_object* v___x_107_; 
v_sz_105_ = lean_array_size(v_depConfigs_95_);
v___x_106_ = ((size_t)0ULL);
v___x_107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg(v_self_96_, v_sz_105_, v___x_106_, v_depConfigs_95_, v___y_102_, v___y_103_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_122_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_a_109_ = lean_ctor_get(v___x_107_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_122_ == 0)
{
v___x_111_ = v___x_107_;
v_isShared_112_ = v_isSharedCheck_122_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_122_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_113_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1));
v___x_114_ = 0;
v___x_115_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__4);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 1, v___x_115_);
v___x_117_ = v___x_111_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_108_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v___x_115_);
v___x_117_ = v_reuseFailAlloc_121_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_task_pure(v___x_117_);
v___x_119_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_97_);
lean_ctor_set(v___x_119_, 2, v___x_113_);
lean_ctor_set_uint8(v___x_119_, sizeof(void*)*3, v___x_114_);
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v_a_109_);
return v___x_120_;
}
}
}
else
{
lean_object* v_a_123_; lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec(v___x_97_);
v_a_123_ = lean_ctor_get(v___x_107_, 0);
v_a_124_ = lean_ctor_get(v___x_107_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_107_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_inc(v_a_123_);
lean_dec(v___x_107_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_123_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___boxed(lean_object* v_depConfigs_132_, lean_object* v_self_133_, lean_object* v___x_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0(v_depConfigs_132_, v_self_133_, v___x_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps(lean_object* v_self_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_depConfigs_151_; lean_object* v___x_152_; lean_object* v___f_153_; lean_object* v___x_154_; 
v_depConfigs_151_ = lean_ctor_get(v_self_143_, 12);
lean_inc_ref(v_depConfigs_151_);
v___x_152_ = lean_box(0);
v___f_153_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___boxed), 10, 3);
lean_closure_set(v___f_153_, 0, v_depConfigs_151_);
lean_closure_set(v___f_153_, 1, v_self_143_);
lean_closure_set(v___f_153_, 2, v___x_152_);
v___x_154_ = l_Lake_ensureJob___redArg(v___x_152_, v___f_153_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___boxed(lean_object* v_self_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps(v_self_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec(v_a_158_);
lean_dec(v_a_157_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1(lean_object* v_self_164_, size_t v_sz_165_, size_t v_i_166_, lean_object* v_bs_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg(v_self_164_, v_sz_165_, v_i_166_, v_bs_167_, v___y_172_, v___y_173_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___boxed(lean_object* v_self_176_, lean_object* v_sz_177_, lean_object* v_i_178_, lean_object* v_bs_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
size_t v_sz_boxed_187_; size_t v_i_boxed_188_; lean_object* v_res_189_; 
v_sz_boxed_187_ = lean_unbox_usize(v_sz_177_);
lean_dec(v_sz_177_);
v_i_boxed_188_ = lean_unbox_usize(v_i_178_);
lean_dec(v_i_178_);
v_res_189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1(v_self_176_, v_sz_boxed_187_, v_i_boxed_188_, v_bs_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(size_t v_sz_190_, size_t v_i_191_, lean_object* v_bs_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = lean_usize_dec_lt(v_i_191_, v_sz_190_);
if (v___x_193_ == 0)
{
return v_bs_192_;
}
else
{
lean_object* v_v_194_; lean_object* v_keyName_195_; lean_object* v___x_196_; lean_object* v_bs_x27_197_; lean_object* v___x_198_; lean_object* v___x_199_; size_t v___x_200_; size_t v___x_201_; lean_object* v___x_202_; 
v_v_194_ = lean_array_uget_borrowed(v_bs_192_, v_i_191_);
v_keyName_195_ = lean_ctor_get(v_v_194_, 2);
lean_inc(v_keyName_195_);
v___x_196_ = lean_unsigned_to_nat(0u);
v_bs_x27_197_ = lean_array_uset(v_bs_192_, v_i_191_, v___x_196_);
v___x_198_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_keyName_195_, v___x_193_);
v___x_199_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
v___x_200_ = ((size_t)1ULL);
v___x_201_ = lean_usize_add(v_i_191_, v___x_200_);
v___x_202_ = lean_array_uset(v_bs_x27_197_, v_i_191_, v___x_199_);
v_i_191_ = v___x_201_;
v_bs_192_ = v___x_202_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1___boxed(lean_object* v_sz_204_, lean_object* v_i_205_, lean_object* v_bs_206_){
_start:
{
size_t v_sz_boxed_207_; size_t v_i_boxed_208_; lean_object* v_res_209_; 
v_sz_boxed_207_ = lean_unbox_usize(v_sz_204_);
lean_dec(v_sz_204_);
v_i_boxed_208_ = lean_unbox_usize(v_i_205_);
lean_dec(v_i_205_);
v_res_209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(v_sz_boxed_207_, v_i_boxed_208_, v_bs_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(lean_object* v_as_211_, size_t v_i_212_, size_t v_stop_213_, lean_object* v_b_214_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = lean_usize_dec_eq(v_i_212_, v_stop_213_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v_baseName_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; size_t v___x_222_; size_t v___x_223_; 
v___x_216_ = lean_array_uget_borrowed(v_as_211_, v_i_212_);
v_baseName_217_ = lean_ctor_get(v___x_216_, 1);
lean_inc(v_baseName_217_);
v___x_218_ = l_Lean_Name_toString(v_baseName_217_, v___x_215_);
v___x_219_ = lean_string_append(v_b_214_, v___x_218_);
lean_dec_ref(v___x_218_);
v___x_220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0));
v___x_221_ = lean_string_append(v___x_219_, v___x_220_);
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_add(v_i_212_, v___x_222_);
v_i_212_ = v___x_223_;
v_b_214_ = v___x_221_;
goto _start;
}
else
{
return v_b_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_225_, lean_object* v_i_226_, lean_object* v_stop_227_, lean_object* v_b_228_){
_start:
{
size_t v_i_boxed_229_; size_t v_stop_boxed_230_; lean_object* v_res_231_; 
v_i_boxed_229_ = lean_unbox_usize(v_i_226_);
lean_dec(v_i_226_);
v_stop_boxed_230_ = lean_unbox_usize(v_stop_227_);
lean_dec(v_stop_227_);
v_res_231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(v_as_225_, v_i_boxed_229_, v_stop_boxed_230_, v_b_228_);
lean_dec_ref(v_as_225_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0(uint8_t v_fmt_232_, lean_object* v_a_233_){
_start:
{
lean_object* v___y_235_; 
if (v_fmt_232_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_242_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1));
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = lean_array_get_size(v_a_233_);
v___x_245_ = lean_nat_dec_lt(v___x_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_dec_ref(v_a_233_);
v___y_235_ = v___x_242_;
goto v___jp_234_;
}
else
{
uint8_t v___x_246_; 
v___x_246_ = lean_nat_dec_le(v___x_244_, v___x_244_);
if (v___x_246_ == 0)
{
if (v___x_245_ == 0)
{
lean_dec_ref(v_a_233_);
v___y_235_ = v___x_242_;
goto v___jp_234_;
}
else
{
size_t v___x_247_; size_t v___x_248_; lean_object* v___x_249_; 
v___x_247_ = ((size_t)0ULL);
v___x_248_ = lean_usize_of_nat(v___x_244_);
v___x_249_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(v_a_233_, v___x_247_, v___x_248_, v___x_242_);
lean_dec_ref(v_a_233_);
v___y_235_ = v___x_249_;
goto v___jp_234_;
}
}
else
{
size_t v___x_250_; size_t v___x_251_; lean_object* v___x_252_; 
v___x_250_ = ((size_t)0ULL);
v___x_251_ = lean_usize_of_nat(v___x_244_);
v___x_252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0(v_a_233_, v___x_250_, v___x_251_, v___x_242_);
lean_dec_ref(v_a_233_);
v___y_235_ = v___x_252_;
goto v___jp_234_;
}
}
}
else
{
size_t v_sz_253_; size_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_sz_253_ = lean_array_size(v_a_233_);
v___x_254_ = ((size_t)0ULL);
v___x_255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__1(v_sz_253_, v___x_254_, v_a_233_);
v___x_256_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
v___x_257_ = l_Lean_Json_compress(v___x_256_);
return v___x_257_;
}
v___jp_234_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_string_utf8_byte_size(v___y_235_);
lean_inc_ref(v___y_235_);
v___x_239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_239_, 0, v___y_235_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
lean_ctor_set(v___x_239_, 2, v___x_238_);
v___x_240_ = l_String_Slice_Pos_prevn(v___x_239_, v___x_238_, v___x_236_);
lean_dec_ref(v___x_239_);
v___x_241_ = lean_string_utf8_extract(v___y_235_, v___x_237_, v___x_240_);
lean_dec(v___x_240_);
lean_dec_ref(v___y_235_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0___boxed(lean_object* v_fmt_258_, lean_object* v_a_259_){
_start:
{
uint8_t v_fmt_boxed_260_; lean_object* v_res_261_; 
v_fmt_boxed_260_ = lean_unbox(v_fmt_258_);
v_res_261_ = l_Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0(v_fmt_boxed_260_, v_a_259_);
return v_res_261_;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig___closed__2(void){
_start:
{
uint8_t v___x_264_; lean_object* v___f_265_; uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_264_ = 1;
v___f_265_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__0));
v___x_266_ = 0;
v___x_267_ = lean_box(0);
v___x_268_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__1));
v___x_269_ = l_Lake_Package_keyword;
v___x_270_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v___x_268_);
lean_ctor_set(v___x_270_, 2, v___x_267_);
lean_ctor_set(v___x_270_, 3, v___f_265_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*4, v___x_266_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*4 + 1, v___x_264_);
return v___x_270_;
}
}
static lean_object* _init_l_Lake_Package_depsFacetConfig(void){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_once(&l_Lake_Package_depsFacetConfig___closed__2, &l_Lake_Package_depsFacetConfig___closed__2_once, _init_l_Lake_Package_depsFacetConfig___closed__2);
return v___x_271_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_box(0);
v___x_273_ = lean_unsigned_to_nat(16u);
v___x_274_ = lean_mk_array(v___x_273_, v___x_272_);
return v___x_274_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__0);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = ((lean_object*)(l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__2));
v___x_281_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__1);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
return v___x_282_;
}
}
static lean_object* _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2(void){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_obj_once(&l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3, &l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3_once, _init_l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2___closed__3);
return v___x_283_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(lean_object* v_a_284_, lean_object* v_x_285_){
_start:
{
if (lean_obj_tag(v_x_285_) == 0)
{
uint8_t v___x_286_; 
v___x_286_ = 0;
return v___x_286_;
}
else
{
lean_object* v_key_287_; lean_object* v_tail_288_; lean_object* v_wsIdx_289_; lean_object* v_wsIdx_290_; uint8_t v___x_291_; 
v_key_287_ = lean_ctor_get(v_x_285_, 0);
v_tail_288_ = lean_ctor_get(v_x_285_, 2);
v_wsIdx_289_ = lean_ctor_get(v_key_287_, 0);
v_wsIdx_290_ = lean_ctor_get(v_a_284_, 0);
v___x_291_ = lean_nat_dec_eq(v_wsIdx_289_, v_wsIdx_290_);
if (v___x_291_ == 0)
{
v_x_285_ = v_tail_288_;
goto _start;
}
else
{
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_a_293_, lean_object* v_x_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_293_, v_x_294_);
lean_dec(v_x_294_);
lean_dec_ref(v_a_293_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_297_; uint64_t v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(1723u);
v___x_298_ = lean_uint64_of_nat(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(lean_object* v_m_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_buckets_301_; lean_object* v_keyName_302_; lean_object* v___x_303_; uint64_t v___y_305_; 
v_buckets_301_ = lean_ctor_get(v_m_299_, 1);
v_keyName_302_ = lean_ctor_get(v_a_300_, 2);
v___x_303_ = lean_array_get_size(v_buckets_301_);
if (lean_obj_tag(v_keyName_302_) == 0)
{
uint64_t v___x_319_; 
v___x_319_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0);
v___y_305_ = v___x_319_;
goto v___jp_304_;
}
else
{
uint64_t v_hash_320_; 
v_hash_320_ = lean_ctor_get_uint64(v_keyName_302_, sizeof(void*)*2);
v___y_305_ = v_hash_320_;
goto v___jp_304_;
}
v___jp_304_:
{
uint64_t v___x_306_; uint64_t v___x_307_; uint64_t v_fold_308_; uint64_t v___x_309_; uint64_t v___x_310_; uint64_t v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_306_ = 32ULL;
v___x_307_ = lean_uint64_shift_right(v___y_305_, v___x_306_);
v_fold_308_ = lean_uint64_xor(v___y_305_, v___x_307_);
v___x_309_ = 16ULL;
v___x_310_ = lean_uint64_shift_right(v_fold_308_, v___x_309_);
v___x_311_ = lean_uint64_xor(v_fold_308_, v___x_310_);
v___x_312_ = lean_uint64_to_usize(v___x_311_);
v___x_313_ = lean_usize_of_nat(v___x_303_);
v___x_314_ = ((size_t)1ULL);
v___x_315_ = lean_usize_sub(v___x_313_, v___x_314_);
v___x_316_ = lean_usize_land(v___x_312_, v___x_315_);
v___x_317_ = lean_array_uget_borrowed(v_buckets_301_, v___x_316_);
v___x_318_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_300_, v___x_317_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___boxed(lean_object* v_m_321_, lean_object* v_a_322_){
_start:
{
uint8_t v_res_323_; lean_object* v_r_324_; 
v_res_323_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_321_, v_a_322_);
lean_dec_ref(v_a_322_);
lean_dec_ref(v_m_321_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
return v_x_325_;
}
else
{
lean_object* v_key_327_; lean_object* v_value_328_; lean_object* v_tail_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_356_; 
v_key_327_ = lean_ctor_get(v_x_326_, 0);
v_value_328_ = lean_ctor_get(v_x_326_, 1);
v_tail_329_ = lean_ctor_get(v_x_326_, 2);
v_isSharedCheck_356_ = !lean_is_exclusive(v_x_326_);
if (v_isSharedCheck_356_ == 0)
{
v___x_331_ = v_x_326_;
v_isShared_332_ = v_isSharedCheck_356_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_tail_329_);
lean_inc(v_value_328_);
lean_inc(v_key_327_);
lean_dec(v_x_326_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_356_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v_keyName_333_; lean_object* v___x_334_; uint64_t v___y_336_; 
v_keyName_333_ = lean_ctor_get(v_key_327_, 2);
v___x_334_ = lean_array_get_size(v_x_325_);
if (lean_obj_tag(v_keyName_333_) == 0)
{
uint64_t v___x_354_; 
v___x_354_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0);
v___y_336_ = v___x_354_;
goto v___jp_335_;
}
else
{
uint64_t v_hash_355_; 
v_hash_355_ = lean_ctor_get_uint64(v_keyName_333_, sizeof(void*)*2);
v___y_336_ = v_hash_355_;
goto v___jp_335_;
}
v___jp_335_:
{
uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v_fold_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_337_ = 32ULL;
v___x_338_ = lean_uint64_shift_right(v___y_336_, v___x_337_);
v_fold_339_ = lean_uint64_xor(v___y_336_, v___x_338_);
v___x_340_ = 16ULL;
v___x_341_ = lean_uint64_shift_right(v_fold_339_, v___x_340_);
v___x_342_ = lean_uint64_xor(v_fold_339_, v___x_341_);
v___x_343_ = lean_uint64_to_usize(v___x_342_);
v___x_344_ = lean_usize_of_nat(v___x_334_);
v___x_345_ = ((size_t)1ULL);
v___x_346_ = lean_usize_sub(v___x_344_, v___x_345_);
v___x_347_ = lean_usize_land(v___x_343_, v___x_346_);
v___x_348_ = lean_array_uget_borrowed(v_x_325_, v___x_347_);
lean_inc(v___x_348_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 2, v___x_348_);
v___x_350_ = v___x_331_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_key_327_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_value_328_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v___x_348_);
v___x_350_ = v_reuseFailAlloc_353_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; 
v___x_351_ = lean_array_uset(v_x_325_, v___x_347_, v___x_350_);
v_x_325_ = v___x_351_;
v_x_326_ = v_tail_329_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_i_357_, lean_object* v_source_358_, lean_object* v_target_359_){
_start:
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = lean_array_get_size(v_source_358_);
v___x_361_ = lean_nat_dec_lt(v_i_357_, v___x_360_);
if (v___x_361_ == 0)
{
lean_dec_ref(v_source_358_);
lean_dec(v_i_357_);
return v_target_359_;
}
else
{
lean_object* v_es_362_; lean_object* v___x_363_; lean_object* v_source_364_; lean_object* v_target_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_es_362_ = lean_array_fget(v_source_358_, v_i_357_);
v___x_363_ = lean_box(0);
v_source_364_ = lean_array_fset(v_source_358_, v_i_357_, v___x_363_);
v_target_365_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(v_target_359_, v_es_362_);
v___x_366_ = lean_unsigned_to_nat(1u);
v___x_367_ = lean_nat_add(v_i_357_, v___x_366_);
lean_dec(v_i_357_);
v_i_357_ = v___x_367_;
v_source_358_ = v_source_364_;
v_target_359_ = v_target_365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(lean_object* v_data_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_nbuckets_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_370_ = lean_array_get_size(v_data_369_);
v___x_371_ = lean_unsigned_to_nat(2u);
v_nbuckets_372_ = lean_nat_mul(v___x_370_, v___x_371_);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_box(0);
v___x_375_ = lean_mk_array(v_nbuckets_372_, v___x_374_);
v___x_376_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v___x_373_, v_data_369_, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(lean_object* v_m_377_, lean_object* v_a_378_, lean_object* v_b_379_){
_start:
{
lean_object* v_size_380_; lean_object* v_buckets_381_; lean_object* v_keyName_382_; lean_object* v___x_383_; uint64_t v___y_385_; 
v_size_380_ = lean_ctor_get(v_m_377_, 0);
v_buckets_381_ = lean_ctor_get(v_m_377_, 1);
v_keyName_382_ = lean_ctor_get(v_a_378_, 2);
v___x_383_ = lean_array_get_size(v_buckets_381_);
if (lean_obj_tag(v_keyName_382_) == 0)
{
uint64_t v___x_422_; 
v___x_422_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg___closed__0);
v___y_385_ = v___x_422_;
goto v___jp_384_;
}
else
{
uint64_t v_hash_423_; 
v_hash_423_ = lean_ctor_get_uint64(v_keyName_382_, sizeof(void*)*2);
v___y_385_ = v_hash_423_;
goto v___jp_384_;
}
v___jp_384_:
{
uint64_t v___x_386_; uint64_t v___x_387_; uint64_t v_fold_388_; uint64_t v___x_389_; uint64_t v___x_390_; uint64_t v___x_391_; size_t v___x_392_; size_t v___x_393_; size_t v___x_394_; size_t v___x_395_; size_t v___x_396_; lean_object* v_bkt_397_; uint8_t v___x_398_; 
v___x_386_ = 32ULL;
v___x_387_ = lean_uint64_shift_right(v___y_385_, v___x_386_);
v_fold_388_ = lean_uint64_xor(v___y_385_, v___x_387_);
v___x_389_ = 16ULL;
v___x_390_ = lean_uint64_shift_right(v_fold_388_, v___x_389_);
v___x_391_ = lean_uint64_xor(v_fold_388_, v___x_390_);
v___x_392_ = lean_uint64_to_usize(v___x_391_);
v___x_393_ = lean_usize_of_nat(v___x_383_);
v___x_394_ = ((size_t)1ULL);
v___x_395_ = lean_usize_sub(v___x_393_, v___x_394_);
v___x_396_ = lean_usize_land(v___x_392_, v___x_395_);
v_bkt_397_ = lean_array_uget_borrowed(v_buckets_381_, v___x_396_);
v___x_398_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_378_, v_bkt_397_);
if (v___x_398_ == 0)
{
lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_419_; 
lean_inc_ref(v_buckets_381_);
lean_inc(v_size_380_);
v_isSharedCheck_419_ = !lean_is_exclusive(v_m_377_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; lean_object* v_unused_421_; 
v_unused_420_ = lean_ctor_get(v_m_377_, 1);
lean_dec(v_unused_420_);
v_unused_421_ = lean_ctor_get(v_m_377_, 0);
lean_dec(v_unused_421_);
v___x_400_ = v_m_377_;
v_isShared_401_ = v_isSharedCheck_419_;
goto v_resetjp_399_;
}
else
{
lean_dec(v_m_377_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_419_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v_size_x27_403_; lean_object* v___x_404_; lean_object* v_buckets_x27_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_402_ = lean_unsigned_to_nat(1u);
v_size_x27_403_ = lean_nat_add(v_size_380_, v___x_402_);
lean_dec(v_size_380_);
lean_inc(v_bkt_397_);
v___x_404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_404_, 0, v_a_378_);
lean_ctor_set(v___x_404_, 1, v_b_379_);
lean_ctor_set(v___x_404_, 2, v_bkt_397_);
v_buckets_x27_405_ = lean_array_uset(v_buckets_381_, v___x_396_, v___x_404_);
v___x_406_ = lean_unsigned_to_nat(4u);
v___x_407_ = lean_nat_mul(v_size_x27_403_, v___x_406_);
v___x_408_ = lean_unsigned_to_nat(3u);
v___x_409_ = lean_nat_div(v___x_407_, v___x_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_array_get_size(v_buckets_x27_405_);
v___x_411_ = lean_nat_dec_le(v___x_409_, v___x_410_);
lean_dec(v___x_409_);
if (v___x_411_ == 0)
{
lean_object* v_val_412_; lean_object* v___x_414_; 
v_val_412_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_buckets_x27_405_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v_val_412_);
lean_ctor_set(v___x_400_, 0, v_size_x27_403_);
v___x_414_ = v___x_400_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_size_x27_403_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_val_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
else
{
lean_object* v___x_417_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v_buckets_x27_405_);
lean_ctor_set(v___x_400_, 0, v_size_x27_403_);
v___x_417_ = v___x_400_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_size_x27_403_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_buckets_x27_405_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_dec(v_b_379_);
lean_dec_ref(v_a_378_);
return v_m_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(lean_object* v_self_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_toHashSet_426_; lean_object* v_toArray_427_; uint8_t v___x_428_; 
v_toHashSet_426_ = lean_ctor_get(v_self_424_, 0);
v_toArray_427_ = lean_ctor_get(v_self_424_, 1);
v___x_428_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_toHashSet_426_, v_a_425_);
if (v___x_428_ == 0)
{
lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_438_; 
lean_inc_ref(v_toArray_427_);
lean_inc_ref(v_toHashSet_426_);
v_isSharedCheck_438_ = !lean_is_exclusive(v_self_424_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; lean_object* v_unused_440_; 
v_unused_439_ = lean_ctor_get(v_self_424_, 1);
lean_dec(v_unused_439_);
v_unused_440_ = lean_ctor_get(v_self_424_, 0);
lean_dec(v_unused_440_);
v___x_430_ = v_self_424_;
v_isShared_431_ = v_isSharedCheck_438_;
goto v_resetjp_429_;
}
else
{
lean_dec(v_self_424_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_438_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_432_ = lean_box(0);
lean_inc_ref(v_a_425_);
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_toHashSet_426_, v_a_425_, v___x_432_);
v___x_434_ = lean_array_push(v_toArray_427_, v_a_425_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v___x_434_);
lean_ctor_set(v___x_430_, 0, v___x_433_);
v___x_436_ = v___x_430_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
else
{
lean_dec_ref(v_a_425_);
return v_self_424_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(lean_object* v_as_441_, size_t v_i_442_, size_t v_stop_443_, lean_object* v_b_444_){
_start:
{
uint8_t v___x_445_; 
v___x_445_ = lean_usize_dec_eq(v_i_442_, v_stop_443_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; lean_object* v___x_447_; size_t v___x_448_; size_t v___x_449_; 
v___x_446_ = lean_array_uget_borrowed(v_as_441_, v_i_442_);
lean_inc(v___x_446_);
v___x_447_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v_b_444_, v___x_446_);
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_add(v_i_442_, v___x_448_);
v_i_442_ = v___x_449_;
v_b_444_ = v___x_447_;
goto _start;
}
else
{
return v_b_444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1___boxed(lean_object* v_as_451_, lean_object* v_i_452_, lean_object* v_stop_453_, lean_object* v_b_454_){
_start:
{
size_t v_i_boxed_455_; size_t v_stop_boxed_456_; lean_object* v_res_457_; 
v_i_boxed_455_ = lean_unbox_usize(v_i_452_);
lean_dec(v_i_452_);
v_stop_boxed_456_ = lean_unbox_usize(v_stop_453_);
lean_dec(v_stop_453_);
v_res_457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_as_451_, v_i_boxed_455_, v_stop_boxed_456_, v_b_454_);
lean_dec_ref(v_as_451_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(lean_object* v_self_458_, lean_object* v_as_459_, size_t v_i_460_, size_t v_stop_461_, lean_object* v_b_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
uint8_t v___x_470_; 
v___x_470_ = lean_usize_dec_eq(v_i_460_, v_stop_461_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v_name_472_; lean_object* v_a_474_; lean_object* v_toContext_489_; lean_object* v_packages_490_; lean_object* v___x_491_; size_t v_sz_492_; size_t v___x_493_; lean_object* v___x_494_; lean_object* v_fst_495_; 
v___x_471_ = lean_array_uget_borrowed(v_as_459_, v_i_460_);
v_name_472_ = lean_ctor_get(v___x_471_, 0);
v_toContext_489_ = lean_ctor_get(v___y_467_, 1);
v_packages_490_ = lean_ctor_get(v_toContext_489_, 5);
v___x_491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0___closed__0));
v_sz_492_ = lean_array_size(v_packages_490_);
v___x_493_ = ((size_t)0ULL);
v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__0(v_name_472_, v_packages_490_, v_sz_492_, v___x_493_, v___x_491_);
v_fst_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_fst_495_);
lean_dec_ref(v___x_494_);
if (lean_obj_tag(v_fst_495_) == 0)
{
lean_dec_ref(v___y_463_);
lean_dec_ref(v_b_462_);
v_a_474_ = v___y_468_;
goto v___jp_473_;
}
else
{
lean_object* v_val_496_; 
v_val_496_ = lean_ctor_get(v_fst_495_, 0);
lean_inc(v_val_496_);
lean_dec_ref(v_fst_495_);
if (lean_obj_tag(v_val_496_) == 1)
{
lean_object* v_val_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_546_; 
v_val_497_ = lean_ctor_get(v_val_496_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v_val_496_);
if (v_isSharedCheck_546_ == 0)
{
v___x_499_ = v_val_496_;
v_isShared_500_ = v_isSharedCheck_546_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_val_497_);
lean_dec(v_val_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_546_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_keyName_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v_keyName_501_ = lean_ctor_get(v_val_497_, 2);
v___x_502_ = l_Lake_Package_transDepsFacet;
lean_inc(v_keyName_501_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v_keyName_501_);
v___x_504_ = v___x_499_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_keyName_501_);
v___x_504_ = v_reuseFailAlloc_545_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = l_Lake_Package_keyword;
lean_inc(v_val_497_);
v___x_506_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
lean_ctor_set(v___x_506_, 2, v_val_497_);
lean_ctor_set(v___x_506_, 3, v___x_502_);
lean_inc_ref(v___y_463_);
lean_inc_ref(v___y_467_);
lean_inc(v___y_466_);
lean_inc(v___y_465_);
lean_inc(v___y_464_);
v___x_507_ = lean_apply_7(v___y_463_, v___x_506_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, lean_box(0));
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v_a_509_; lean_object* v___x_510_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
v_a_509_ = lean_ctor_get(v___x_507_, 1);
lean_inc(v_a_509_);
lean_dec_ref(v___x_507_);
v___x_510_ = l_Lake_Job_await___redArg(v_a_508_, v_a_509_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v_a_512_; lean_object* v___y_514_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
v_a_512_ = lean_ctor_get(v___x_510_, 1);
lean_inc(v_a_512_);
lean_dec_ref(v___x_510_);
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = lean_array_get_size(v_a_511_);
v___x_521_ = lean_nat_dec_lt(v___x_519_, v___x_520_);
if (v___x_521_ == 0)
{
lean_dec(v_a_511_);
v___y_514_ = v_b_462_;
goto v___jp_513_;
}
else
{
uint8_t v___x_522_; 
v___x_522_ = lean_nat_dec_le(v___x_520_, v___x_520_);
if (v___x_522_ == 0)
{
if (v___x_521_ == 0)
{
lean_dec(v_a_511_);
v___y_514_ = v_b_462_;
goto v___jp_513_;
}
else
{
size_t v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_usize_of_nat(v___x_520_);
v___x_524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_511_, v___x_493_, v___x_523_, v_b_462_);
lean_dec(v_a_511_);
v___y_514_ = v___x_524_;
goto v___jp_513_;
}
}
else
{
size_t v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_usize_of_nat(v___x_520_);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_511_, v___x_493_, v___x_525_, v_b_462_);
lean_dec(v_a_511_);
v___y_514_ = v___x_526_;
goto v___jp_513_;
}
}
v___jp_513_:
{
lean_object* v___x_515_; size_t v___x_516_; size_t v___x_517_; 
v___x_515_ = l_Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0(v___y_514_, v_val_497_);
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_add(v_i_460_, v___x_516_);
v_i_460_ = v___x_517_;
v_b_462_ = v___x_515_;
v___y_468_ = v_a_512_;
goto _start;
}
}
else
{
lean_object* v_a_527_; lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec(v_val_497_);
lean_dec_ref(v___y_463_);
lean_dec_ref(v_b_462_);
lean_dec_ref(v_self_458_);
v_a_527_ = lean_ctor_get(v___x_510_, 0);
v_a_528_ = lean_ctor_get(v___x_510_, 1);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_510_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_inc(v_a_527_);
lean_dec(v___x_510_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_527_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
else
{
lean_object* v_a_536_; lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec(v_val_497_);
lean_dec_ref(v___y_463_);
lean_dec_ref(v_b_462_);
lean_dec_ref(v_self_458_);
v_a_536_ = lean_ctor_get(v___x_507_, 0);
v_a_537_ = lean_ctor_get(v___x_507_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_507_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_inc(v_a_536_);
lean_dec(v___x_507_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_536_);
lean_ctor_set(v_reuseFailAlloc_543_, 1, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
else
{
lean_dec(v_val_496_);
lean_dec_ref(v___y_463_);
lean_dec_ref(v_b_462_);
v_a_474_ = v___y_468_;
goto v___jp_473_;
}
}
v___jp_473_:
{
lean_object* v_baseName_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_baseName_475_ = lean_ctor_get(v_self_458_, 1);
lean_inc(v_baseName_475_);
lean_dec_ref(v_self_458_);
v___x_476_ = l_Lean_Name_toString(v_baseName_475_, v___x_470_);
v___x_477_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg___closed__0));
v___x_478_ = lean_string_append(v___x_476_, v___x_477_);
v___x_479_ = 1;
lean_inc(v_name_472_);
v___x_480_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_472_, v___x_479_);
v___x_481_ = lean_string_append(v___x_478_, v___x_480_);
lean_dec_ref(v___x_480_);
v___x_482_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Build_Package_0__Lake_Package_recFetchDeps_spec__1___redArg___closed__1));
v___x_483_ = lean_string_append(v___x_481_, v___x_482_);
v___x_484_ = 3;
v___x_485_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set_uint8(v___x_485_, sizeof(void*)*1, v___x_484_);
v___x_486_ = lean_array_get_size(v_a_474_);
v___x_487_ = lean_array_push(v_a_474_, v___x_485_);
v___x_488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
return v___x_488_;
}
}
else
{
lean_object* v___x_547_; 
lean_dec_ref(v___y_463_);
lean_dec_ref(v_self_458_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v_b_462_);
lean_ctor_set(v___x_547_, 1, v___y_468_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3___boxed(lean_object* v_self_548_, lean_object* v_as_549_, lean_object* v_i_550_, lean_object* v_stop_551_, lean_object* v_b_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
size_t v_i_boxed_560_; size_t v_stop_boxed_561_; lean_object* v_res_562_; 
v_i_boxed_560_ = lean_unbox_usize(v_i_550_);
lean_dec(v_i_550_);
v_stop_boxed_561_ = lean_unbox_usize(v_stop_551_);
lean_dec(v_stop_551_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_self_548_, v_as_549_, v_i_boxed_560_, v_stop_boxed_561_, v_b_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v_as_549_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(lean_object* v___x_563_, lean_object* v___x_564_, lean_object* v___x_565_, lean_object* v___x_566_, lean_object* v_self_567_, lean_object* v_depConfigs_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_a_577_; lean_object* v_a_578_; lean_object* v___y_598_; uint8_t v___x_610_; 
v___x_610_ = lean_nat_dec_lt(v___x_563_, v___x_565_);
if (v___x_610_ == 0)
{
lean_dec_ref(v___y_569_);
lean_dec_ref(v_self_567_);
v_a_577_ = v___x_566_;
v_a_578_ = v___y_574_;
goto v___jp_576_;
}
else
{
uint8_t v___x_611_; 
v___x_611_ = lean_nat_dec_le(v___x_565_, v___x_565_);
if (v___x_611_ == 0)
{
if (v___x_610_ == 0)
{
lean_dec_ref(v___y_569_);
lean_dec_ref(v_self_567_);
v_a_577_ = v___x_566_;
v_a_578_ = v___y_574_;
goto v___jp_576_;
}
else
{
size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; 
v___x_612_ = ((size_t)0ULL);
v___x_613_ = lean_usize_of_nat(v___x_565_);
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_self_567_, v_depConfigs_568_, v___x_612_, v___x_613_, v___x_566_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
v___y_598_ = v___x_614_;
goto v___jp_597_;
}
}
else
{
size_t v___x_615_; size_t v___x_616_; lean_object* v___x_617_; 
v___x_615_ = ((size_t)0ULL);
v___x_616_ = lean_usize_of_nat(v___x_565_);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_self_567_, v_depConfigs_568_, v___x_615_, v___x_616_, v___x_566_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
v___y_598_ = v___x_617_;
goto v___jp_597_;
}
}
v___jp_576_:
{
lean_object* v_toArray_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_595_; 
v_toArray_579_ = lean_ctor_get(v_a_577_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v_a_577_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v_a_577_, 0);
lean_dec(v_unused_596_);
v___x_581_ = v_a_577_;
v_isShared_582_ = v_isSharedCheck_595_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_toArray_579_);
lean_dec(v_a_577_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_595_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v___x_583_ = lean_mk_empty_array_with_capacity(v___x_563_);
v___x_584_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1));
v___x_585_ = 0;
v___x_586_ = 0;
v___x_587_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3);
v___x_588_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_588_, 0, v___x_583_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
lean_ctor_set(v___x_588_, 2, v___x_563_);
lean_ctor_set_uint8(v___x_588_, sizeof(void*)*3, v___x_585_);
lean_ctor_set_uint8(v___x_588_, sizeof(void*)*3 + 1, v___x_586_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v___x_588_);
lean_ctor_set(v___x_581_, 0, v_toArray_579_);
v___x_590_ = v___x_581_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_toArray_579_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___x_588_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_task_pure(v___x_590_);
v___x_592_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___x_564_);
lean_ctor_set(v___x_592_, 2, v___x_584_);
lean_ctor_set_uint8(v___x_592_, sizeof(void*)*3, v___x_586_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v_a_578_);
return v___x_593_;
}
}
}
v___jp_597_:
{
if (lean_obj_tag(v___y_598_) == 0)
{
lean_object* v_a_599_; lean_object* v_a_600_; 
v_a_599_ = lean_ctor_get(v___y_598_, 0);
lean_inc(v_a_599_);
v_a_600_ = lean_ctor_get(v___y_598_, 1);
lean_inc(v_a_600_);
lean_dec_ref(v___y_598_);
v_a_577_ = v_a_599_;
v_a_578_ = v_a_600_;
goto v___jp_576_;
}
else
{
lean_object* v_a_601_; lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec(v___x_564_);
lean_dec(v___x_563_);
v_a_601_ = lean_ctor_get(v___y_598_, 0);
v_a_602_ = lean_ctor_get(v___y_598_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v___y_598_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___y_598_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_inc(v_a_601_);
lean_dec(v___y_598_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_601_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed(lean_object* v___x_618_, lean_object* v___x_619_, lean_object* v___x_620_, lean_object* v___x_621_, lean_object* v_self_622_, lean_object* v_depConfigs_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(v___x_618_, v___x_619_, v___x_620_, v___x_621_, v_self_622_, v_depConfigs_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v_depConfigs_623_);
lean_dec(v___x_620_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(lean_object* v_self_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_depConfigs_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___f_645_; lean_object* v___x_646_; 
v_depConfigs_640_ = lean_ctor_get(v_self_632_, 12);
lean_inc_ref(v_depConfigs_640_);
v___x_641_ = lean_box(0);
v___x_642_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2;
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_array_get_size(v_depConfigs_640_);
v___f_645_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed), 13, 6);
lean_closure_set(v___f_645_, 0, v___x_643_);
lean_closure_set(v___f_645_, 1, v___x_641_);
lean_closure_set(v___f_645_, 2, v___x_644_);
lean_closure_set(v___f_645_, 3, v___x_642_);
lean_closure_set(v___f_645_, 4, v_self_632_);
lean_closure_set(v___f_645_, 5, v_depConfigs_640_);
v___x_646_ = l_Lake_ensureJob___redArg(v___x_641_, v___f_645_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___boxed(lean_object* v_self_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(v_self_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec(v_a_650_);
lean_dec(v_a_649_);
return v_res_655_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object* v_00_u03b2_656_, lean_object* v_m_657_, lean_object* v_a_658_){
_start:
{
uint8_t v___x_659_; 
v___x_659_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_657_, v_a_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_660_, lean_object* v_m_661_, lean_object* v_a_662_){
_start:
{
uint8_t v_res_663_; lean_object* v_r_664_; 
v_res_663_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(v_00_u03b2_660_, v_m_661_, v_a_662_);
lean_dec_ref(v_a_662_);
lean_dec_ref(v_m_661_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1(lean_object* v_00_u03b2_665_, lean_object* v_m_666_, lean_object* v_a_667_, lean_object* v_b_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_m_666_, v_a_667_, v_b_668_);
return v___x_669_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_670_, lean_object* v_a_671_, lean_object* v_x_672_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_671_, v_x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_674_, lean_object* v_a_675_, lean_object* v_x_676_){
_start:
{
uint8_t v_res_677_; lean_object* v_r_678_; 
v_res_677_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(v_00_u03b2_674_, v_a_675_, v_x_676_);
lean_dec(v_x_676_);
lean_dec_ref(v_a_675_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_679_, lean_object* v_data_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_data_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_682_, lean_object* v_i_683_, lean_object* v_source_684_, lean_object* v_target_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v_i_683_, v_source_684_, v_target_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_687_, lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(v_x_688_, v_x_689_);
return v___x_690_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_692_; lean_object* v___f_693_; uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_692_ = 1;
v___f_693_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__0));
v___x_694_ = 0;
v___x_695_ = lean_box(0);
v___x_696_ = ((lean_object*)(l_Lake_Package_transDepsFacetConfig___closed__0));
v___x_697_ = l_Lake_Package_keyword;
v___x_698_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_696_);
lean_ctor_set(v___x_698_, 2, v___x_695_);
lean_ctor_set(v___x_698_, 3, v___f_693_);
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*4, v___x_694_);
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*4 + 1, v___x_692_);
return v___x_698_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig(void){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = lean_obj_once(&l_Lake_Package_transDepsFacetConfig___closed__1, &l_Lake_Package_transDepsFacetConfig___closed__1_once, _init_l_Lake_Package_transDepsFacetConfig___closed__1);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object* v_self_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_config_708_; uint8_t v_preferReleaseBuild_709_; 
v_config_708_ = lean_ctor_get(v_self_700_, 6);
v_preferReleaseBuild_709_ = lean_ctor_get_uint8(v_config_708_, sizeof(void*)*26 + 2);
if (v_preferReleaseBuild_709_ == 0)
{
lean_object* v_keyName_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_keyName_710_ = lean_ctor_get(v_self_700_, 2);
v___x_711_ = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(v_keyName_710_);
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v_keyName_710_);
v___x_713_ = l_Lake_Package_keyword;
v___x_714_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
lean_ctor_set(v___x_714_, 2, v_self_700_);
lean_ctor_set(v___x_714_, 3, v___x_711_);
lean_inc_ref(v_a_705_);
lean_inc(v_a_704_);
lean_inc(v_a_703_);
lean_inc(v_a_702_);
v___x_715_ = lean_apply_7(v_a_701_, v___x_714_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, lean_box(0));
return v___x_715_;
}
else
{
lean_object* v_keyName_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_keyName_716_ = lean_ctor_get(v_self_700_, 2);
v___x_717_ = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(v_keyName_716_);
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v_keyName_716_);
v___x_719_ = l_Lake_Package_keyword;
v___x_720_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
lean_ctor_set(v___x_720_, 2, v_self_700_);
lean_ctor_set(v___x_720_, 3, v___x_717_);
lean_inc_ref(v_a_705_);
lean_inc(v_a_704_);
lean_inc(v_a_703_);
lean_inc(v_a_702_);
v___x_721_ = lean_apply_7(v_a_701_, v___x_720_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, lean_box(0));
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___boxed(lean_object* v_self_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(v_self_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
lean_dec_ref(v_a_727_);
lean_dec(v_a_726_);
lean_dec(v_a_725_);
lean_dec(v_a_724_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t v_fmt_733_, uint8_t v_a_734_){
_start:
{
if (v_fmt_733_ == 0)
{
if (v_a_734_ == 0)
{
lean_object* v___x_735_; 
v___x_735_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0));
return v___x_735_;
}
else
{
lean_object* v___x_736_; 
v___x_736_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1));
return v___x_736_;
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_737_, 0, v_a_734_);
v___x_738_ = l_Lean_Json_compress(v___x_737_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object* v_fmt_739_, lean_object* v_a_740_){
_start:
{
uint8_t v_fmt_boxed_741_; uint8_t v_a_boxed_742_; lean_object* v_res_743_; 
v_fmt_boxed_741_ = lean_unbox(v_fmt_739_);
v_a_boxed_742_ = lean_unbox(v_a_740_);
v_res_743_ = l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(v_fmt_boxed_741_, v_a_boxed_742_);
return v_res_743_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___f_746_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_747_ = 1;
v___x_748_ = l_Lake_instDataKindBool;
v___f_749_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__0));
v___x_750_ = l_Lake_Package_keyword;
v___x_751_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___f_749_);
lean_ctor_set(v___x_751_, 2, v___x_748_);
lean_ctor_set(v___x_751_, 3, v___f_746_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*4, v___x_747_);
lean_ctor_set_uint8(v___x_751_, sizeof(void*)*4 + 1, v___x_747_);
return v___x_751_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig(void){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_obj_once(&l_Lake_Package_optBuildCacheFacetConfig___closed__2, &l_Lake_Package_optBuildCacheFacetConfig___closed__2_once, _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(lean_object* v_self_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___y_764_; uint8_t v___y_765_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_788_; lean_object* v___y_789_; uint8_t v___y_790_; lean_object* v___y_791_; uint8_t v___y_792_; lean_object* v_toContext_796_; lean_object* v_lakeEnv_797_; uint8_t v_noCache_798_; lean_object* v_toolchain_799_; uint8_t v_a_801_; lean_object* v_a_802_; 
v_toContext_796_ = lean_ctor_get(v_a_760_, 1);
v_lakeEnv_797_ = lean_ctor_get(v_toContext_796_, 1);
v_noCache_798_ = lean_ctor_get_uint8(v_lakeEnv_797_, sizeof(void*)*19);
v_toolchain_799_ = lean_ctor_get(v_lakeEnv_797_, 18);
if (v_noCache_798_ == 0)
{
uint8_t v___x_817_; 
v___x_817_ = 1;
v_a_801_ = v___x_817_;
v_a_802_ = v_a_761_;
goto v___jp_800_;
}
else
{
uint8_t v___x_818_; 
v___x_818_ = 0;
v_a_801_ = v___x_818_;
v_a_802_ = v_a_761_;
goto v___jp_800_;
}
v___jp_763_:
{
uint8_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_766_ = 1;
v___x_767_ = lean_box(0);
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__0));
v___x_770_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1));
v___x_771_ = 0;
v___x_772_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3);
v___x_773_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_773_, 0, v___x_769_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
lean_ctor_set(v___x_773_, 2, v___x_768_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*3, v___x_771_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*3 + 1, v___y_765_);
v___x_774_ = lean_box(v___x_766_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v___x_773_);
v___x_776_ = lean_task_pure(v___x_775_);
v___x_777_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v___x_767_);
lean_ctor_set(v___x_777_, 2, v___x_770_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*3, v___y_765_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v___y_764_);
return v___x_778_;
}
v___jp_779_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_782_ = l_Lake_Package_optBuildCacheFacet;
v___x_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_783_, 0, v___y_780_);
v___x_784_ = l_Lake_Package_keyword;
v___x_785_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
lean_ctor_set(v___x_785_, 2, v_self_755_);
lean_ctor_set(v___x_785_, 3, v___x_782_);
lean_inc_ref(v_a_760_);
lean_inc(v_a_759_);
lean_inc(v_a_758_);
lean_inc(v_a_757_);
v___x_786_ = lean_apply_7(v_a_756_, v___x_785_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v___y_781_, lean_box(0));
return v___x_786_;
}
v___jp_787_:
{
if (v___y_792_ == 0)
{
lean_dec(v___y_789_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_self_755_);
v___y_764_ = v___y_791_;
v___y_765_ = v___y_792_;
goto v___jp_763_;
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_793_ = lean_string_utf8_byte_size(v___y_788_);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_nat_dec_eq(v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
v___y_780_ = v___y_789_;
v___y_781_ = v___y_791_;
goto v___jp_779_;
}
else
{
lean_dec(v___y_789_);
lean_dec_ref(v_a_756_);
lean_dec_ref(v_self_755_);
v___y_764_ = v___y_791_;
v___y_765_ = v___y_790_;
goto v___jp_763_;
}
}
}
v___jp_800_:
{
lean_object* v_config_803_; lean_object* v_keyName_804_; lean_object* v_dir_805_; lean_object* v_scope_806_; lean_object* v_buildDir_807_; uint8_t v_preferReleaseBuild_808_; lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v_config_803_ = lean_ctor_get(v_self_755_, 6);
v_keyName_804_ = lean_ctor_get(v_self_755_, 2);
v_dir_805_ = lean_ctor_get(v_self_755_, 4);
v_scope_806_ = lean_ctor_get(v_self_755_, 10);
v_buildDir_807_ = lean_ctor_get(v_config_803_, 5);
v_preferReleaseBuild_808_ = lean_ctor_get_uint8(v_config_803_, sizeof(void*)*26 + 2);
lean_inc_ref(v_buildDir_807_);
v___x_809_ = l_System_FilePath_normalize(v_buildDir_807_);
lean_inc_ref(v_dir_805_);
v___x_810_ = l_Lake_joinRelative(v_dir_805_, v___x_809_);
v___x_811_ = l_System_FilePath_pathExists(v___x_810_);
lean_dec_ref(v___x_810_);
if (v_a_801_ == 0)
{
lean_dec_ref(v_a_756_);
lean_dec_ref(v_self_755_);
v___y_764_ = v_a_802_;
v___y_765_ = v_a_801_;
goto v___jp_763_;
}
else
{
if (v___x_811_ == 0)
{
if (v_preferReleaseBuild_808_ == 0)
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0));
v___x_813_ = lean_string_dec_eq(v_scope_806_, v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1));
v___x_815_ = lean_string_dec_eq(v_scope_806_, v___x_814_);
lean_inc(v_keyName_804_);
v___y_788_ = v_toolchain_799_;
v___y_789_ = v_keyName_804_;
v___y_790_ = v_preferReleaseBuild_808_;
v___y_791_ = v_a_802_;
v___y_792_ = v___x_815_;
goto v___jp_787_;
}
else
{
lean_inc(v_keyName_804_);
v___y_788_ = v_toolchain_799_;
v___y_789_ = v_keyName_804_;
v___y_790_ = v_preferReleaseBuild_808_;
v___y_791_ = v_a_802_;
v___y_792_ = v___x_813_;
goto v___jp_787_;
}
}
else
{
lean_inc(v_keyName_804_);
v___y_780_ = v_keyName_804_;
v___y_781_ = v_a_802_;
goto v___jp_779_;
}
}
else
{
uint8_t v___x_816_; 
lean_dec_ref(v_a_756_);
lean_dec_ref(v_self_755_);
v___x_816_ = 0;
v___y_764_ = v_a_802_;
v___y_765_ = v___x_816_;
goto v___jp_763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___boxed(lean_object* v_self_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec(v_a_822_);
lean_dec(v_a_821_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object* v_self_832_, lean_object* v_facet_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_toBuildConfig_837_; uint8_t v_verbosity_838_; uint8_t v___x_839_; uint8_t v___x_840_; 
v_toBuildConfig_837_ = lean_ctor_get(v_a_834_, 0);
v_verbosity_838_ = lean_ctor_get_uint8(v_toBuildConfig_837_, sizeof(void*)*2 + 3);
v___x_839_ = 2;
v___x_840_ = l_Lake_instDecidableEqVerbosity(v_verbosity_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec(v_facet_833_);
lean_dec_ref(v_self_832_);
v___x_841_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v_a_835_);
return v___x_842_;
}
else
{
lean_object* v_baseName_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_baseName_843_ = lean_ctor_get(v_self_832_, 1);
lean_inc(v_baseName_843_);
lean_dec_ref(v_self_832_);
v___x_844_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_845_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_843_, v___x_840_);
v___x_846_ = lean_string_append(v___x_844_, v___x_845_);
lean_dec_ref(v___x_845_);
v___x_847_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_848_ = lean_string_append(v___x_846_, v___x_847_);
v___x_849_ = l_Lake_Name_eraseHead(v_facet_833_);
v___x_850_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_849_, v___x_840_);
v___x_851_ = lean_string_append(v___x_848_, v___x_850_);
lean_dec_ref(v___x_850_);
v___x_852_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_853_ = lean_string_append(v___x_851_, v___x_852_);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v_a_835_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* v_self_855_, lean_object* v_facet_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(v_self_855_, v_facet_856_, v_a_857_, v_a_858_);
lean_dec_ref(v_a_857_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* v_self_861_, lean_object* v_facet_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_toBuildConfig_870_; uint8_t v_verbosity_871_; uint8_t v___x_872_; uint8_t v___x_873_; 
v_toBuildConfig_870_ = lean_ctor_get(v_a_867_, 0);
v_verbosity_871_ = lean_ctor_get_uint8(v_toBuildConfig_870_, sizeof(void*)*2 + 3);
v___x_872_ = 2;
v___x_873_ = l_Lake_instDecidableEqVerbosity(v_verbosity_871_, v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; 
lean_dec(v_facet_862_);
lean_dec_ref(v_self_861_);
v___x_874_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v_a_868_);
return v___x_875_;
}
else
{
lean_object* v_baseName_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_baseName_876_ = lean_ctor_get(v_self_861_, 1);
lean_inc(v_baseName_876_);
lean_dec_ref(v_self_861_);
v___x_877_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_878_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_876_, v___x_873_);
v___x_879_ = lean_string_append(v___x_877_, v___x_878_);
lean_dec_ref(v___x_878_);
v___x_880_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_881_ = lean_string_append(v___x_879_, v___x_880_);
v___x_882_ = l_Lake_Name_eraseHead(v_facet_862_);
v___x_883_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_882_, v___x_873_);
v___x_884_ = lean_string_append(v___x_881_, v___x_883_);
lean_dec_ref(v___x_883_);
v___x_885_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_886_ = lean_string_append(v___x_884_, v___x_885_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v_a_868_);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* v_self_888_, lean_object* v_facet_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(v_self_888_, v_facet_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
return v_res_897_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_901_ = l_Lake_Name_eraseHead(v___x_900_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_903_ = l_Lake_Name_eraseHead(v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(lean_object* v_self_904_, uint8_t v_success_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_a_914_; lean_object* v_a_915_; lean_object* v_a_936_; lean_object* v_a_937_; 
if (v_success_905_ == 0)
{
lean_object* v_config_957_; uint8_t v_preferReleaseBuild_958_; 
v_config_957_ = lean_ctor_get(v_self_904_, 6);
v_preferReleaseBuild_958_ = lean_ctor_get_uint8(v_config_957_, sizeof(void*)*26 + 2);
if (v_preferReleaseBuild_958_ == 0)
{
lean_object* v_toBuildConfig_959_; lean_object* v_baseName_960_; uint8_t v_verbosity_961_; uint8_t v___x_962_; uint8_t v___x_963_; 
v_toBuildConfig_959_ = lean_ctor_get(v___y_910_, 0);
v_baseName_960_ = lean_ctor_get(v_self_904_, 1);
lean_inc(v_baseName_960_);
lean_dec_ref(v_self_904_);
v_verbosity_961_ = lean_ctor_get_uint8(v_toBuildConfig_959_, sizeof(void*)*2 + 3);
v___x_962_ = 2;
v___x_963_ = l_Lake_instDecidableEqVerbosity(v_verbosity_961_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
lean_dec(v_baseName_960_);
v___x_964_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_914_ = v___x_964_;
v_a_915_ = v___y_911_;
goto v___jp_913_;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_965_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_966_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_960_, v___x_963_);
v___x_967_ = lean_string_append(v___x_965_, v___x_966_);
lean_dec_ref(v___x_966_);
v___x_968_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_969_ = lean_string_append(v___x_967_, v___x_968_);
v___x_970_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2);
v___x_971_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_970_, v___x_963_);
v___x_972_ = lean_string_append(v___x_969_, v___x_971_);
lean_dec_ref(v___x_971_);
v___x_973_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_974_ = lean_string_append(v___x_972_, v___x_973_);
v_a_914_ = v___x_974_;
v_a_915_ = v___y_911_;
goto v___jp_913_;
}
}
else
{
lean_object* v_toBuildConfig_975_; lean_object* v_baseName_976_; uint8_t v_verbosity_977_; uint8_t v___x_978_; uint8_t v___x_979_; 
v_toBuildConfig_975_ = lean_ctor_get(v___y_910_, 0);
v_baseName_976_ = lean_ctor_get(v_self_904_, 1);
lean_inc(v_baseName_976_);
lean_dec_ref(v_self_904_);
v_verbosity_977_ = lean_ctor_get_uint8(v_toBuildConfig_975_, sizeof(void*)*2 + 3);
v___x_978_ = 2;
v___x_979_ = l_Lake_instDecidableEqVerbosity(v_verbosity_977_, v___x_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
lean_dec(v_baseName_976_);
v___x_980_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_936_ = v___x_980_;
v_a_937_ = v___y_911_;
goto v___jp_935_;
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_981_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_982_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_976_, v___x_979_);
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
lean_dec_ref(v___x_982_);
v___x_984_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
v___x_986_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
v___x_987_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_986_, v___x_979_);
v___x_988_ = lean_string_append(v___x_985_, v___x_987_);
lean_dec_ref(v___x_987_);
v___x_989_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_990_ = lean_string_append(v___x_988_, v___x_989_);
v_a_936_ = v___x_990_;
v_a_937_ = v___y_911_;
goto v___jp_935_;
}
}
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; 
lean_dec_ref(v_self_904_);
v___x_991_ = lean_box(0);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___y_911_);
return v___x_992_;
}
v___jp_913_:
{
lean_object* v_log_916_; uint8_t v_action_917_; uint8_t v_wantsRebuild_918_; lean_object* v_trace_919_; lean_object* v_buildTime_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_934_; 
v_log_916_ = lean_ctor_get(v_a_915_, 0);
v_action_917_ = lean_ctor_get_uint8(v_a_915_, sizeof(void*)*3);
v_wantsRebuild_918_ = lean_ctor_get_uint8(v_a_915_, sizeof(void*)*3 + 1);
v_trace_919_ = lean_ctor_get(v_a_915_, 1);
v_buildTime_920_ = lean_ctor_get(v_a_915_, 2);
v_isSharedCheck_934_ = !lean_is_exclusive(v_a_915_);
if (v_isSharedCheck_934_ == 0)
{
v___x_922_ = v_a_915_;
v_isShared_923_ = v_isSharedCheck_934_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_buildTime_920_);
lean_inc(v_trace_919_);
lean_inc(v_log_916_);
lean_dec(v_a_915_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_934_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_924_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0));
v___x_925_ = lean_string_append(v___x_924_, v_a_914_);
lean_dec_ref(v_a_914_);
v___x_926_ = 0;
v___x_927_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set_uint8(v___x_927_, sizeof(void*)*1, v___x_926_);
v___x_928_ = lean_box(0);
v___x_929_ = lean_array_push(v_log_916_, v___x_927_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_929_);
v___x_931_ = v___x_922_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_trace_919_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_buildTime_920_);
lean_ctor_set_uint8(v_reuseFailAlloc_933_, sizeof(void*)*3, v_action_917_);
lean_ctor_set_uint8(v_reuseFailAlloc_933_, sizeof(void*)*3 + 1, v_wantsRebuild_918_);
v___x_931_ = v_reuseFailAlloc_933_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_928_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
return v___x_932_;
}
}
}
v___jp_935_:
{
lean_object* v_log_938_; uint8_t v_action_939_; uint8_t v_wantsRebuild_940_; lean_object* v_trace_941_; lean_object* v_buildTime_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_956_; 
v_log_938_ = lean_ctor_get(v_a_937_, 0);
v_action_939_ = lean_ctor_get_uint8(v_a_937_, sizeof(void*)*3);
v_wantsRebuild_940_ = lean_ctor_get_uint8(v_a_937_, sizeof(void*)*3 + 1);
v_trace_941_ = lean_ctor_get(v_a_937_, 1);
v_buildTime_942_ = lean_ctor_get(v_a_937_, 2);
v_isSharedCheck_956_ = !lean_is_exclusive(v_a_937_);
if (v_isSharedCheck_956_ == 0)
{
v___x_944_ = v_a_937_;
v_isShared_945_ = v_isSharedCheck_956_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_buildTime_942_);
lean_inc(v_trace_941_);
lean_inc(v_log_938_);
lean_dec(v_a_937_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_956_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_946_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1));
v___x_947_ = lean_string_append(v___x_946_, v_a_936_);
lean_dec_ref(v_a_936_);
v___x_948_ = 2;
v___x_949_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*1, v___x_948_);
v___x_950_ = lean_box(0);
v___x_951_ = lean_array_push(v_log_938_, v___x_949_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_951_);
v___x_953_ = v___x_944_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_trace_941_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_buildTime_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, sizeof(void*)*3, v_action_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_955_, sizeof(void*)*3 + 1, v_wantsRebuild_940_);
v___x_953_ = v_reuseFailAlloc_955_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_954_; 
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_950_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
return v___x_954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* v_self_993_, lean_object* v_success_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
uint8_t v_success_boxed_1002_; lean_object* v_res_1003_; 
v_success_boxed_1002_ = lean_unbox(v_success_994_);
v_res_1003_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(v_self_993_, v_success_boxed_1002_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* v_self_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___x_1012_; 
lean_inc_ref(v_a_1005_);
lean_inc_ref(v_self_1004_);
v___x_1012_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1027_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_a_1014_ = lean_ctor_get(v___x_1012_, 1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1016_ = v___x_1012_;
v_isShared_1017_ = v_isSharedCheck_1027_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1027_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___f_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___f_1018_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(v___f_1018_, 0, v_self_1004_);
v___x_1019_ = l_Lake_instDataKindUnit;
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1021_ = 0;
v___x_1022_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3);
v___x_1023_ = l_Lake_Job_mapM___redArg(v___x_1019_, v_a_1013_, v___f_1018_, v___x_1020_, v___x_1021_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v___x_1022_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1023_);
v___x_1025_ = v___x_1016_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_a_1014_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v_a_1005_);
lean_dec_ref(v_self_1004_);
v_a_1028_ = lean_ctor_get(v___x_1012_, 0);
v_a_1029_ = lean_ctor_get(v___x_1012_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1012_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_inc(v_a_1028_);
lean_dec(v___x_1012_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1028_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(lean_object* v_self_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec(v_a_1039_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* v_self_1046_, lean_object* v_as_1047_, size_t v_sz_1048_, size_t v_i_1049_, lean_object* v_b_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
uint8_t v___x_1058_; 
v___x_1058_ = lean_usize_dec_lt(v_i_1049_, v_sz_1048_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_dec_ref(v___y_1051_);
lean_dec_ref(v_self_1046_);
v___x_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1059_, 0, v_b_1050_);
lean_ctor_set(v___x_1059_, 1, v___y_1056_);
return v___x_1059_;
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1061_; 
v_a_1060_ = lean_array_uget_borrowed(v_as_1047_, v_i_1049_);
lean_inc_ref(v___y_1051_);
lean_inc(v_a_1060_);
lean_inc_ref(v_self_1046_);
v___x_1061_ = l_Lake_Package_fetchTargetJob(v_self_1046_, v_a_1060_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v_a_1063_; lean_object* v___x_1064_; size_t v___x_1065_; size_t v___x_1066_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
v_a_1063_ = lean_ctor_get(v___x_1061_, 1);
lean_inc(v_a_1063_);
lean_dec_ref(v___x_1061_);
v___x_1064_ = l_Lake_Job_mix___redArg(v_b_1050_, v_a_1062_);
v___x_1065_ = ((size_t)1ULL);
v___x_1066_ = lean_usize_add(v_i_1049_, v___x_1065_);
v_i_1049_ = v___x_1066_;
v_b_1050_ = v___x_1064_;
v___y_1056_ = v_a_1063_;
goto _start;
}
else
{
lean_object* v_a_1068_; lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec_ref(v___y_1051_);
lean_dec_ref(v_b_1050_);
lean_dec_ref(v_self_1046_);
v_a_1068_ = lean_ctor_get(v___x_1061_, 0);
v_a_1069_ = lean_ctor_get(v___x_1061_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1061_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_inc(v_a_1068_);
lean_dec(v___x_1061_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1068_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* v_self_1077_, lean_object* v_as_1078_, lean_object* v_sz_1079_, lean_object* v_i_1080_, lean_object* v_b_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
size_t v_sz_boxed_1089_; size_t v_i_boxed_1090_; lean_object* v_res_1091_; 
v_sz_boxed_1089_ = lean_unbox_usize(v_sz_1079_);
lean_dec(v_sz_1079_);
v_i_boxed_1090_ = lean_unbox_usize(v_i_1080_);
lean_dec(v_i_1080_);
v_res_1091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1077_, v_as_1078_, v_sz_boxed_1089_, v_i_boxed_1090_, v_b_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v_as_1078_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object* v_config_1092_, lean_object* v_self_1093_, lean_object* v_____r_1094_, lean_object* v_job_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_extraDepTargets_1103_; size_t v_sz_1104_; size_t v___x_1105_; lean_object* v___x_1106_; 
v_extraDepTargets_1103_ = lean_ctor_get(v_config_1092_, 2);
v_sz_1104_ = lean_array_size(v_extraDepTargets_1103_);
v___x_1105_ = ((size_t)0ULL);
v___x_1106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1093_, v_extraDepTargets_1103_, v_sz_1104_, v___x_1105_, v_job_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object* v_config_1107_, lean_object* v_self_1108_, lean_object* v_____r_1109_, lean_object* v_job_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(v_config_1107_, v_self_1108_, v_____r_1109_, v_job_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v_config_1107_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(uint8_t v___x_1119_, lean_object* v_self_1120_, lean_object* v_job_1121_, lean_object* v___f_1122_, lean_object* v___x_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
if (v___x_1119_ == 0)
{
lean_object* v___x_1131_; 
lean_inc_ref(v___y_1124_);
v___x_1131_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1120_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v_a_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
v_a_1133_ = lean_ctor_get(v___x_1131_, 1);
lean_inc(v_a_1133_);
lean_dec_ref(v___x_1131_);
v___x_1134_ = l_Lake_Job_add___redArg(v_job_1121_, v_a_1132_);
lean_inc_ref(v___y_1128_);
lean_inc(v___y_1127_);
lean_inc(v___y_1126_);
lean_inc(v___y_1125_);
v___x_1135_ = lean_apply_9(v___f_1122_, v___x_1123_, v___x_1134_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v_a_1133_, lean_box(0));
return v___x_1135_;
}
else
{
lean_dec_ref(v___y_1124_);
lean_dec_ref(v___f_1122_);
lean_dec_ref(v_job_1121_);
return v___x_1131_;
}
}
else
{
lean_object* v___x_1136_; 
lean_dec_ref(v_self_1120_);
lean_inc_ref(v___y_1128_);
lean_inc(v___y_1127_);
lean_inc(v___y_1126_);
lean_inc(v___y_1125_);
v___x_1136_ = lean_apply_9(v___f_1122_, v___x_1123_, v_job_1121_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, lean_box(0));
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* v___x_1137_, lean_object* v_self_1138_, lean_object* v_job_1139_, lean_object* v___f_1140_, lean_object* v___x_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
uint8_t v___x_4161__boxed_1149_; lean_object* v_res_1150_; 
v___x_4161__boxed_1149_ = lean_unbox(v___x_1137_);
v_res_1150_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(v___x_4161__boxed_1149_, v_self_1138_, v_job_1139_, v___f_1140_, v___x_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec(v___y_1143_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object* v_self_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_){
_start:
{
lean_object* v_wsIdx_1161_; lean_object* v_baseName_1162_; lean_object* v_config_1163_; lean_object* v___f_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; uint8_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v_job_1183_; uint8_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___y_1186_; lean_object* v___x_1187_; 
v_wsIdx_1161_ = lean_ctor_get(v_self_1153_, 0);
v_baseName_1162_ = lean_ctor_get(v_self_1153_, 1);
v_config_1163_ = lean_ctor_get(v_self_1153_, 6);
lean_inc_ref(v_self_1153_);
lean_inc_ref(v_config_1163_);
v___f_1164_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1164_, 0, v_config_1163_);
lean_closure_set(v___f_1164_, 1, v_self_1153_);
v___x_1165_ = l_Lake_instDataKindUnit;
v___x_1166_ = 1;
lean_inc(v_baseName_1162_);
v___x_1167_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1162_, v___x_1166_);
v___x_1168_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0));
v___x_1169_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1));
v___x_1170_ = lean_string_append(v___x_1169_, v___x_1167_);
v___x_1171_ = lean_string_append(v___x_1170_, v___x_1168_);
v___x_1172_ = lean_box(0);
v___x_1173_ = lean_box(0);
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__0));
v___x_1176_ = 0;
v___x_1177_ = 0;
v___x_1178_ = l_Lake_BuildTrace_nil(v___x_1171_);
v___x_1179_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1179_, 0, v___x_1175_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
lean_ctor_set(v___x_1179_, 2, v___x_1174_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*3, v___x_1176_);
lean_ctor_set_uint8(v___x_1179_, sizeof(void*)*3 + 1, v___x_1177_);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1172_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = lean_task_pure(v___x_1180_);
v___x_1182_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1));
v_job_1183_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_1183_, 0, v___x_1181_);
lean_ctor_set(v_job_1183_, 1, v___x_1173_);
lean_ctor_set(v_job_1183_, 2, v___x_1182_);
lean_ctor_set_uint8(v_job_1183_, sizeof(void*)*3, v___x_1177_);
v___x_1184_ = lean_nat_dec_eq(v_wsIdx_1161_, v___x_1174_);
v___x_1185_ = lean_box(v___x_1184_);
v___y_1186_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 12, 5);
lean_closure_set(v___y_1186_, 0, v___x_1185_);
lean_closure_set(v___y_1186_, 1, v_self_1153_);
lean_closure_set(v___y_1186_, 2, v_job_1183_);
lean_closure_set(v___y_1186_, 3, v___f_1164_);
lean_closure_set(v___y_1186_, 4, v___x_1172_);
v___x_1187_ = l_Lake_ensureJob___redArg(v___x_1165_, v___y_1186_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1213_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
v_a_1189_ = lean_ctor_get(v___x_1187_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1191_ = v___x_1187_;
v_isShared_1192_ = v_isSharedCheck_1213_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_inc(v_a_1188_);
lean_dec(v___x_1187_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1213_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v_task_1193_; lean_object* v_kind_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1211_; 
v_task_1193_ = lean_ctor_get(v_a_1188_, 0);
v_kind_1194_ = lean_ctor_get(v_a_1188_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_a_1188_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; 
v_unused_1212_ = lean_ctor_get(v_a_1188_, 2);
lean_dec(v_unused_1212_);
v___x_1196_ = v_a_1188_;
v_isShared_1197_ = v_isSharedCheck_1211_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_kind_1194_);
lean_inc(v_task_1193_);
lean_dec(v_a_1188_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1211_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v_registeredJobs_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v_job_1202_; 
v_registeredJobs_1198_ = lean_ctor_get(v_a_1158_, 3);
v___x_1199_ = lean_st_ref_take(v_registeredJobs_1198_);
v___x_1200_ = lean_string_append(v___x_1167_, v___x_1168_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 2, v___x_1200_);
v_job_1202_ = v___x_1196_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_task_1193_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_kind_1194_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v___x_1200_);
v_job_1202_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
lean_ctor_set_uint8(v_job_1202_, sizeof(void*)*3, v___x_1177_);
lean_inc_ref(v_job_1202_);
v___x_1203_ = l_Lake_Job_toOpaque___redArg(v_job_1202_);
v___x_1204_ = lean_array_push(v___x_1199_, v___x_1203_);
v___x_1205_ = lean_st_ref_set(v_registeredJobs_1198_, v___x_1204_);
v___x_1206_ = l_Lake_Job_renew___redArg(v_job_1202_);
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1206_);
v___x_1208_ = v___x_1191_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_a_1189_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1167_);
return v___x_1187_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(lean_object* v_self_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(v_self_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec(v_a_1216_);
return v_res_1222_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_box(0);
v___x_1224_ = l_Lean_Json_compress(v___x_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t v_fmt_1225_){
_start:
{
if (v_fmt_1225_ == 0)
{
lean_object* v___x_1226_; 
v___x_1226_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1));
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
return v___x_1227_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_1228_){
_start:
{
uint8_t v_fmt_boxed_1229_; lean_object* v_res_1230_; 
v_fmt_boxed_1229_ = lean_unbox(v_fmt_1228_);
v_res_1230_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_boxed_1229_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(uint8_t v_fmt_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_1231_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object* v_fmt_1234_, lean_object* v_a_1235_){
_start:
{
uint8_t v_fmt_boxed_1236_; lean_object* v_res_1237_; 
v_fmt_boxed_1236_ = lean_unbox(v_fmt_1234_);
v_res_1237_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(v_fmt_boxed_1236_, v_a_1235_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v___y_1238_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
uint8_t v___y_67__boxed_1243_; lean_object* v_res_1244_; 
v___y_67__boxed_1243_ = lean_unbox(v___y_1241_);
v_res_1244_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_67__boxed_1243_, v___y_1242_);
return v_res_1244_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___f_1247_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_1248_ = 1;
v___x_1249_ = l_Lake_instDataKindUnit;
v___x_1250_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__1));
v___x_1251_ = l_Lake_Package_keyword;
v___x_1252_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v___x_1250_);
lean_ctor_set(v___x_1252_, 2, v___x_1249_);
lean_ctor_set(v___x_1252_, 3, v___f_1247_);
lean_ctor_set_uint8(v___x_1252_, sizeof(void*)*4, v___x_1248_);
lean_ctor_set_uint8(v___x_1252_, sizeof(void*)*4 + 1, v___x_1248_);
return v___x_1252_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_obj_once(&l_Lake_Package_extraDepFacetConfig___closed__2, &l_Lake_Package_extraDepFacetConfig___closed__2_once, _init_l_Lake_Package_extraDepFacetConfig___closed__2);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object* v_self_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v_origName_1273_; lean_object* v_dir_1274_; lean_object* v_scope_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v_origName_1273_ = lean_ctor_get(v_self_1269_, 3);
lean_inc(v_origName_1273_);
v_dir_1274_ = lean_ctor_get(v_self_1269_, 4);
lean_inc_ref(v_dir_1274_);
v_scope_1275_ = lean_ctor_get(v_self_1269_, 10);
lean_inc_ref(v_scope_1275_);
lean_dec_ref(v_self_1269_);
v___x_1276_ = lean_string_utf8_byte_size(v_scope_1275_);
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = lean_nat_dec_eq(v___x_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
v___x_1280_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1279_, v_dir_1274_);
if (lean_obj_tag(v___x_1280_) == 1)
{
lean_object* v_toContext_1281_; lean_object* v_lakeEnv_1282_; lean_object* v_log_1283_; uint8_t v_action_1284_; uint8_t v_wantsRebuild_1285_; lean_object* v_trace_1286_; lean_object* v_buildTime_1287_; lean_object* v_val_1288_; lean_object* v_toolchain_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_toContext_1281_ = lean_ctor_get(v_a_1270_, 1);
v_lakeEnv_1282_ = lean_ctor_get(v_toContext_1281_, 1);
v_log_1283_ = lean_ctor_get(v_a_1271_, 0);
v_action_1284_ = lean_ctor_get_uint8(v_a_1271_, sizeof(void*)*3);
v_wantsRebuild_1285_ = lean_ctor_get_uint8(v_a_1271_, sizeof(void*)*3 + 1);
v_trace_1286_ = lean_ctor_get(v_a_1271_, 1);
v_buildTime_1287_ = lean_ctor_get(v_a_1271_, 2);
v_val_1288_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_val_1288_);
lean_dec_ref(v___x_1280_);
v_toolchain_1289_ = lean_ctor_get(v_lakeEnv_1282_, 18);
v___x_1290_ = lean_string_utf8_byte_size(v_toolchain_1289_);
v___x_1291_ = lean_nat_dec_eq(v___x_1290_, v___x_1277_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1292_ = l_Lean_Name_toString(v_origName_1273_, v___x_1278_);
lean_inc_ref(v_lakeEnv_1282_);
v___x_1293_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_1282_, v_scope_1275_, v___x_1292_);
v___x_1294_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1));
v___x_1295_ = lean_string_append(v___x_1293_, v___x_1294_);
v___x_1296_ = lean_string_append(v___x_1295_, v_val_1288_);
lean_dec(v_val_1288_);
v___x_1297_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2));
v___x_1298_ = lean_string_append(v___x_1296_, v___x_1297_);
v___x_1299_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1));
lean_inc_ref(v_toolchain_1289_);
v___x_1300_ = l_Lake_uriEncode(v_toolchain_1289_, v___x_1299_);
v___x_1301_ = lean_string_append(v___x_1298_, v___x_1300_);
lean_dec_ref(v___x_1300_);
v___x_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v_a_1271_);
return v___x_1302_;
}
else
{
lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1313_; 
lean_inc(v_buildTime_1287_);
lean_inc_ref(v_trace_1286_);
lean_inc_ref(v_log_1283_);
lean_dec(v_val_1288_);
lean_dec_ref(v_scope_1275_);
lean_dec(v_origName_1273_);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_a_1271_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; lean_object* v_unused_1315_; lean_object* v_unused_1316_; 
v_unused_1314_ = lean_ctor_get(v_a_1271_, 2);
lean_dec(v_unused_1314_);
v_unused_1315_ = lean_ctor_get(v_a_1271_, 1);
lean_dec(v_unused_1315_);
v_unused_1316_ = lean_ctor_get(v_a_1271_, 0);
lean_dec(v_unused_1316_);
v___x_1304_ = v_a_1271_;
v_isShared_1305_ = v_isSharedCheck_1313_;
goto v_resetjp_1303_;
}
else
{
lean_dec(v_a_1271_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1313_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1306_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4));
v___x_1307_ = lean_array_get_size(v_log_1283_);
v___x_1308_ = lean_array_push(v_log_1283_, v___x_1306_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1308_);
v___x_1310_ = v___x_1304_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_trace_1286_);
lean_ctor_set(v_reuseFailAlloc_1312_, 2, v_buildTime_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1312_, sizeof(void*)*3, v_action_1284_);
lean_ctor_set_uint8(v_reuseFailAlloc_1312_, sizeof(void*)*3 + 1, v_wantsRebuild_1285_);
v___x_1310_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1311_; 
v___x_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1307_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
return v___x_1311_;
}
}
}
}
else
{
lean_object* v_log_1317_; uint8_t v_action_1318_; uint8_t v_wantsRebuild_1319_; lean_object* v_trace_1320_; lean_object* v_buildTime_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v___x_1280_);
lean_dec_ref(v_scope_1275_);
lean_dec(v_origName_1273_);
v_log_1317_ = lean_ctor_get(v_a_1271_, 0);
v_action_1318_ = lean_ctor_get_uint8(v_a_1271_, sizeof(void*)*3);
v_wantsRebuild_1319_ = lean_ctor_get_uint8(v_a_1271_, sizeof(void*)*3 + 1);
v_trace_1320_ = lean_ctor_get(v_a_1271_, 1);
v_buildTime_1321_ = lean_ctor_get(v_a_1271_, 2);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_a_1271_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1323_ = v_a_1271_;
v_isShared_1324_ = v_isSharedCheck_1332_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_buildTime_1321_);
lean_inc(v_trace_1320_);
lean_inc(v_log_1317_);
lean_dec(v_a_1271_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1332_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1325_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6));
v___x_1326_ = lean_array_get_size(v_log_1317_);
v___x_1327_ = lean_array_push(v_log_1317_, v___x_1325_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1327_);
v___x_1329_ = v___x_1323_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_trace_1320_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_buildTime_1321_);
lean_ctor_set_uint8(v_reuseFailAlloc_1331_, sizeof(void*)*3, v_action_1318_);
lean_ctor_set_uint8(v_reuseFailAlloc_1331_, sizeof(void*)*3 + 1, v_wantsRebuild_1319_);
v___x_1329_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1326_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
return v___x_1330_;
}
}
}
}
else
{
lean_object* v_log_1333_; uint8_t v_action_1334_; uint8_t v_wantsRebuild_1335_; lean_object* v_trace_1336_; lean_object* v_buildTime_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_scope_1275_);
lean_dec_ref(v_dir_1274_);
lean_dec(v_origName_1273_);
v_log_1333_ = lean_ctor_get(v_a_1271_, 0);
v_action_1334_ = lean_ctor_get_uint8(v_a_1271_, sizeof(void*)*3);
v_wantsRebuild_1335_ = lean_ctor_get_uint8(v_a_1271_, sizeof(void*)*3 + 1);
v_trace_1336_ = lean_ctor_get(v_a_1271_, 1);
v_buildTime_1337_ = lean_ctor_get(v_a_1271_, 2);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_a_1271_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1339_ = v_a_1271_;
v_isShared_1340_ = v_isSharedCheck_1348_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_buildTime_1337_);
lean_inc(v_trace_1336_);
lean_inc(v_log_1333_);
lean_dec(v_a_1271_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1348_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1341_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8));
v___x_1342_ = lean_array_get_size(v_log_1333_);
v___x_1343_ = lean_array_push(v_log_1333_, v___x_1341_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1343_);
v___x_1345_ = v___x_1339_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_trace_1336_);
lean_ctor_set(v_reuseFailAlloc_1347_, 2, v_buildTime_1337_);
lean_ctor_set_uint8(v_reuseFailAlloc_1347_, sizeof(void*)*3, v_action_1334_);
lean_ctor_set_uint8(v_reuseFailAlloc_1347_, sizeof(void*)*3 + 1, v_wantsRebuild_1335_);
v___x_1345_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1342_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___boxed(lean_object* v_self_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1349_, v_a_1350_, v_a_1351_);
lean_dec_ref(v_a_1350_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object* v_self_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1354_, v_a_1359_, v_a_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object* v_self_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(v_self_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object* v_self_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_rev_1385_; lean_object* v_log_1386_; uint8_t v_action_1387_; uint8_t v_wantsRebuild_1388_; lean_object* v_trace_1389_; lean_object* v_buildTime_1390_; lean_object* v_dir_1399_; lean_object* v_config_1400_; lean_object* v_remoteUrl_1401_; lean_object* v_buildArchive_1402_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; uint8_t v___y_1407_; uint8_t v___y_1408_; lean_object* v_val_1409_; lean_object* v___y_1429_; lean_object* v_releaseRepo_1460_; 
v_dir_1399_ = lean_ctor_get(v_self_1381_, 4);
lean_inc_ref(v_dir_1399_);
v_config_1400_ = lean_ctor_get(v_self_1381_, 6);
lean_inc_ref(v_config_1400_);
v_remoteUrl_1401_ = lean_ctor_get(v_self_1381_, 11);
lean_inc_ref(v_remoteUrl_1401_);
v_buildArchive_1402_ = lean_ctor_get(v_self_1381_, 19);
lean_inc_ref(v_buildArchive_1402_);
lean_dec_ref(v_self_1381_);
v_releaseRepo_1460_ = lean_ctor_get(v_config_1400_, 10);
lean_inc(v_releaseRepo_1460_);
lean_dec_ref(v_config_1400_);
if (lean_obj_tag(v_releaseRepo_1460_) == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1461_ = lean_string_utf8_byte_size(v_remoteUrl_1401_);
v___x_1462_ = lean_unsigned_to_nat(0u);
v___x_1463_ = lean_nat_dec_eq(v___x_1461_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_dec_ref(v_remoteUrl_1401_);
v___y_1429_ = v_releaseRepo_1460_;
goto v___jp_1428_;
}
else
{
lean_object* v___x_1464_; 
v___x_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_remoteUrl_1401_);
v___y_1429_ = v___x_1464_;
goto v___jp_1428_;
}
}
else
{
lean_dec_ref(v_remoteUrl_1401_);
v___y_1429_ = v_releaseRepo_1460_;
goto v___jp_1428_;
}
v___jp_1384_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1391_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0));
v___x_1392_ = lean_string_append(v___x_1391_, v_rev_1385_);
lean_dec_ref(v_rev_1385_);
v___x_1393_ = 3;
v___x_1394_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*1, v___x_1393_);
v___x_1395_ = lean_array_get_size(v_log_1386_);
v___x_1396_ = lean_array_push(v_log_1386_, v___x_1394_);
v___x_1397_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v_trace_1389_);
lean_ctor_set(v___x_1397_, 2, v_buildTime_1390_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*3, v_action_1387_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*3 + 1, v_wantsRebuild_1388_);
v___x_1398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1395_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
return v___x_1398_;
}
v___jp_1403_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
lean_inc_ref(v_dir_1399_);
v___x_1411_ = l_Lake_GitRepo_findTag_x3f(v___x_1410_, v_dir_1399_);
if (lean_obj_tag(v___x_1411_) == 1)
{
lean_object* v_val_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_dec_ref(v_dir_1399_);
v_val_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_val_1412_);
lean_dec_ref(v___x_1411_);
v___x_1413_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1413_, 0, v___y_1404_);
lean_ctor_set(v___x_1413_, 1, v___y_1405_);
lean_ctor_set(v___x_1413_, 2, v___y_1406_);
lean_ctor_set_uint8(v___x_1413_, sizeof(void*)*3, v___y_1407_);
lean_ctor_set_uint8(v___x_1413_, sizeof(void*)*3 + 1, v___y_1408_);
v___x_1414_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1));
v___x_1415_ = lean_string_append(v_val_1409_, v___x_1414_);
v___x_1416_ = lean_string_append(v___x_1415_, v_val_1412_);
lean_dec(v_val_1412_);
v___x_1417_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2));
v___x_1418_ = lean_string_append(v___x_1416_, v___x_1417_);
v___x_1419_ = lean_string_append(v___x_1418_, v_buildArchive_1402_);
lean_dec_ref(v_buildArchive_1402_);
v___x_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
lean_ctor_set(v___x_1420_, 1, v___x_1413_);
return v___x_1420_;
}
else
{
lean_object* v___x_1421_; 
lean_dec(v___x_1411_);
lean_dec_ref(v_val_1409_);
lean_dec_ref(v_buildArchive_1402_);
v___x_1421_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1410_, v_dir_1399_);
if (lean_obj_tag(v___x_1421_) == 1)
{
lean_object* v_val_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v_val_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_val_1422_);
lean_dec_ref(v___x_1421_);
v___x_1423_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3));
v___x_1424_ = lean_string_append(v___x_1423_, v_val_1422_);
lean_dec(v_val_1422_);
v___x_1425_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4));
v___x_1426_ = lean_string_append(v___x_1424_, v___x_1425_);
v_rev_1385_ = v___x_1426_;
v_log_1386_ = v___y_1404_;
v_action_1387_ = v___y_1407_;
v_wantsRebuild_1388_ = v___y_1408_;
v_trace_1389_ = v___y_1405_;
v_buildTime_1390_ = v___y_1406_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1427_; 
lean_dec(v___x_1421_);
v___x_1427_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1));
v_rev_1385_ = v___x_1427_;
v_log_1386_ = v___y_1404_;
v_action_1387_ = v___y_1407_;
v_wantsRebuild_1388_ = v___y_1408_;
v_trace_1389_ = v___y_1405_;
v_buildTime_1390_ = v___y_1406_;
goto v___jp_1384_;
}
}
}
v___jp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_dir_1399_);
v___x_1431_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v___x_1430_, v_dir_1399_);
if (lean_obj_tag(v___y_1429_) == 0)
{
if (lean_obj_tag(v___x_1431_) == 1)
{
lean_object* v_log_1432_; uint8_t v_action_1433_; uint8_t v_wantsRebuild_1434_; lean_object* v_trace_1435_; lean_object* v_buildTime_1436_; lean_object* v_val_1437_; 
v_log_1432_ = lean_ctor_get(v_a_1382_, 0);
lean_inc_ref(v_log_1432_);
v_action_1433_ = lean_ctor_get_uint8(v_a_1382_, sizeof(void*)*3);
v_wantsRebuild_1434_ = lean_ctor_get_uint8(v_a_1382_, sizeof(void*)*3 + 1);
v_trace_1435_ = lean_ctor_get(v_a_1382_, 1);
lean_inc_ref(v_trace_1435_);
v_buildTime_1436_ = lean_ctor_get(v_a_1382_, 2);
lean_inc(v_buildTime_1436_);
lean_dec_ref(v_a_1382_);
v_val_1437_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_val_1437_);
lean_dec_ref(v___x_1431_);
v___y_1404_ = v_log_1432_;
v___y_1405_ = v_trace_1435_;
v___y_1406_ = v_buildTime_1436_;
v___y_1407_ = v_action_1433_;
v___y_1408_ = v_wantsRebuild_1434_;
v_val_1409_ = v_val_1437_;
goto v___jp_1403_;
}
else
{
lean_object* v_log_1438_; uint8_t v_action_1439_; uint8_t v_wantsRebuild_1440_; lean_object* v_trace_1441_; lean_object* v_buildTime_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1453_; 
lean_dec(v___x_1431_);
lean_dec_ref(v_buildArchive_1402_);
lean_dec_ref(v_dir_1399_);
v_log_1438_ = lean_ctor_get(v_a_1382_, 0);
v_action_1439_ = lean_ctor_get_uint8(v_a_1382_, sizeof(void*)*3);
v_wantsRebuild_1440_ = lean_ctor_get_uint8(v_a_1382_, sizeof(void*)*3 + 1);
v_trace_1441_ = lean_ctor_get(v_a_1382_, 1);
v_buildTime_1442_ = lean_ctor_get(v_a_1382_, 2);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_a_1382_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1444_ = v_a_1382_;
v_isShared_1445_ = v_isSharedCheck_1453_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_buildTime_1442_);
lean_inc(v_trace_1441_);
lean_inc(v_log_1438_);
lean_dec(v_a_1382_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1453_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1446_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6));
v___x_1447_ = lean_array_get_size(v_log_1438_);
v___x_1448_ = lean_array_push(v_log_1438_, v___x_1446_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1448_);
v___x_1450_ = v___x_1444_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_trace_1441_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_buildTime_1442_);
lean_ctor_set_uint8(v_reuseFailAlloc_1452_, sizeof(void*)*3, v_action_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1452_, sizeof(void*)*3 + 1, v_wantsRebuild_1440_);
v___x_1450_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1447_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
return v___x_1451_;
}
}
}
}
else
{
lean_object* v_log_1454_; uint8_t v_action_1455_; uint8_t v_wantsRebuild_1456_; lean_object* v_trace_1457_; lean_object* v_buildTime_1458_; lean_object* v_val_1459_; 
lean_dec(v___x_1431_);
v_log_1454_ = lean_ctor_get(v_a_1382_, 0);
lean_inc_ref(v_log_1454_);
v_action_1455_ = lean_ctor_get_uint8(v_a_1382_, sizeof(void*)*3);
v_wantsRebuild_1456_ = lean_ctor_get_uint8(v_a_1382_, sizeof(void*)*3 + 1);
v_trace_1457_ = lean_ctor_get(v_a_1382_, 1);
lean_inc_ref(v_trace_1457_);
v_buildTime_1458_ = lean_ctor_get(v_a_1382_, 2);
lean_inc(v_buildTime_1458_);
lean_dec_ref(v_a_1382_);
v_val_1459_ = lean_ctor_get(v___y_1429_, 0);
lean_inc(v_val_1459_);
lean_dec_ref(v___y_1429_);
v___y_1404_ = v_log_1454_;
v___y_1405_ = v_trace_1457_;
v___y_1406_ = v_buildTime_1458_;
v___y_1407_ = v_action_1455_;
v___y_1408_ = v_wantsRebuild_1456_;
v_val_1409_ = v_val_1459_;
goto v___jp_1403_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(lean_object* v_self_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1465_, v_a_1466_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object* v_self_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1469_, v_a_1475_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object* v_self_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(v_self_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_);
lean_dec_ref(v_a_1483_);
lean_dec(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(lean_object* v_val_1487_, lean_object* v_a_x3f_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1491_; lean_object* v_log_1492_; uint8_t v_action_1493_; uint8_t v_wantsRebuild_1494_; lean_object* v_trace_1495_; lean_object* v_buildTime_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1507_; 
v___x_1491_ = lean_io_mono_ms_now();
v_log_1492_ = lean_ctor_get(v___y_1489_, 0);
v_action_1493_ = lean_ctor_get_uint8(v___y_1489_, sizeof(void*)*3);
v_wantsRebuild_1494_ = lean_ctor_get_uint8(v___y_1489_, sizeof(void*)*3 + 1);
v_trace_1495_ = lean_ctor_get(v___y_1489_, 1);
v_buildTime_1496_ = lean_ctor_get(v___y_1489_, 2);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___y_1489_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1498_ = v___y_1489_;
v_isShared_1499_ = v_isSharedCheck_1507_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_buildTime_1496_);
lean_inc(v_trace_1495_);
lean_inc(v_log_1492_);
lean_dec(v___y_1489_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1507_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1500_ = lean_nat_sub(v___x_1491_, v_val_1487_);
lean_dec(v___x_1491_);
v___x_1501_ = lean_box(0);
v___x_1502_ = lean_nat_add(v_buildTime_1496_, v___x_1500_);
lean_dec(v___x_1500_);
lean_dec(v_buildTime_1496_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 2, v___x_1502_);
v___x_1504_ = v___x_1498_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_log_1492_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_trace_1495_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v___x_1502_);
lean_ctor_set_uint8(v_reuseFailAlloc_1506_, sizeof(void*)*3, v_action_1493_);
lean_ctor_set_uint8(v_reuseFailAlloc_1506_, sizeof(void*)*3 + 1, v_wantsRebuild_1494_);
v___x_1504_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1501_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
return v___x_1505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0___boxed(lean_object* v_val_1508_, lean_object* v_a_x3f_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v_val_1508_, v_a_x3f_1509_, v___y_1510_);
lean_dec(v_a_x3f_1509_);
lean_dec(v_val_1508_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(lean_object* v_url_1518_, lean_object* v_archiveFile_1519_, lean_object* v_headers_1520_, lean_object* v_depTrace_1521_, lean_object* v_traceFile_1522_, uint8_t v_action_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_a_1528_; lean_object* v_a_1529_; lean_object* v_log_1532_; uint8_t v_action_1533_; uint8_t v_wantsRebuild_1534_; lean_object* v_trace_1535_; lean_object* v_buildTime_1536_; lean_object* v_toBuildConfig_1542_; lean_object* v_log_1543_; uint8_t v_action_1544_; uint8_t v_wantsRebuild_1545_; lean_object* v_trace_1546_; lean_object* v_buildTime_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1637_; 
v_toBuildConfig_1542_ = lean_ctor_get(v_a_1524_, 0);
v_log_1543_ = lean_ctor_get(v_a_1525_, 0);
v_action_1544_ = lean_ctor_get_uint8(v_a_1525_, sizeof(void*)*3);
v_wantsRebuild_1545_ = lean_ctor_get_uint8(v_a_1525_, sizeof(void*)*3 + 1);
v_trace_1546_ = lean_ctor_get(v_a_1525_, 1);
v_buildTime_1547_ = lean_ctor_get(v_a_1525_, 2);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_a_1525_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1549_ = v_a_1525_;
v_isShared_1550_ = v_isSharedCheck_1637_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_buildTime_1547_);
lean_inc(v_trace_1546_);
lean_inc(v_log_1543_);
lean_dec(v_a_1525_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1637_;
goto v_resetjp_1548_;
}
v___jp_1527_:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1530_, 0, v_a_1528_);
lean_ctor_set(v___x_1530_, 1, v_a_1529_);
return v___x_1530_;
}
v___jp_1531_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1537_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1));
v___x_1538_ = lean_array_get_size(v_log_1532_);
v___x_1539_ = lean_array_push(v_log_1532_, v___x_1537_);
v___x_1540_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v_trace_1535_);
lean_ctor_set(v___x_1540_, 2, v_buildTime_1536_);
lean_ctor_set_uint8(v___x_1540_, sizeof(void*)*3, v_action_1533_);
lean_ctor_set_uint8(v___x_1540_, sizeof(void*)*3 + 1, v_wantsRebuild_1534_);
v___x_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1538_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
return v___x_1541_;
}
v_resetjp_1548_:
{
uint8_t v_noBuild_1551_; uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v_noBuild_1551_ = lean_ctor_get_uint8(v_toBuildConfig_1542_, sizeof(void*)*2 + 2);
v___x_1552_ = l_Lake_JobAction_merge(v_action_1544_, v_action_1523_);
v___x_1553_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2));
lean_inc_ref(v_traceFile_1522_);
v___x_1554_ = l_System_FilePath_addExtension(v_traceFile_1522_, v___x_1553_);
if (v_noBuild_1551_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v_a_1558_; lean_object* v_a_1559_; 
v___x_1555_ = lean_io_mono_ms_now();
lean_inc_ref(v_log_1543_);
v___x_1556_ = l_Lake_download(v_url_1518_, v_archiveFile_1519_, v_headers_1520_, v_log_1543_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1563_; lean_object* v_a_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_a_1563_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1563_);
v_a_1564_ = lean_ctor_get(v___x_1556_, 1);
lean_inc(v_a_1564_);
lean_dec_ref(v___x_1556_);
v___x_1565_ = lean_array_get_size(v_log_1543_);
lean_dec_ref(v_log_1543_);
v___x_1566_ = lean_array_get_size(v_a_1564_);
v___x_1567_ = l_Array_extract___redArg(v_a_1564_, v___x_1565_, v___x_1566_);
v___x_1568_ = lean_box(0);
v___x_1569_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1521_, v___x_1568_, v___x_1567_);
v___x_1570_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1522_, v___x_1569_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1607_; 
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1607_ == 0)
{
lean_object* v_unused_1608_; 
v_unused_1608_ = lean_ctor_get(v___x_1570_, 0);
lean_dec(v_unused_1608_);
v___x_1572_ = v___x_1570_;
v_isShared_1573_ = v_isSharedCheck_1607_;
goto v_resetjp_1571_;
}
else
{
lean_dec(v___x_1570_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1607_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lake_removeFileIfExists(v___x_1554_);
lean_dec_ref(v___x_1554_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1597_; 
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; 
v_unused_1598_ = lean_ctor_get(v___x_1574_, 0);
lean_dec(v_unused_1598_);
v___x_1576_ = v___x_1574_;
v_isShared_1577_ = v_isSharedCheck_1597_;
goto v_resetjp_1575_;
}
else
{
lean_dec(v___x_1574_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1597_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v_a_1564_);
v___x_1579_ = v___x_1549_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1564_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_trace_1546_);
lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_buildTime_1547_);
lean_ctor_set_uint8(v_reuseFailAlloc_1596_, sizeof(void*)*3 + 1, v_wantsRebuild_1545_);
v___x_1579_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1581_; 
lean_ctor_set_uint8(v___x_1579_, sizeof(void*)*3, v___x_1552_);
lean_inc(v_a_1563_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v_a_1563_);
v___x_1581_ = v___x_1576_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1563_);
v___x_1581_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1573_ == 0)
{
lean_ctor_set_tag(v___x_1572_, 1);
lean_ctor_set(v___x_1572_, 0, v___x_1581_);
v___x_1583_ = v___x_1572_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
lean_object* v___x_1584_; lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
v___x_1584_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1555_, v___x_1583_, v___x_1579_);
lean_dec_ref(v___x_1583_);
lean_dec(v___x_1555_);
v_a_1585_ = lean_ctor_get(v___x_1584_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v___x_1584_, 0);
lean_dec(v_unused_1593_);
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_a_1563_);
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1563_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
lean_del_object(v___x_1572_);
lean_dec(v_a_1563_);
v_a_1599_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1574_);
v___x_1600_ = lean_io_error_to_string(v_a_1599_);
v___x_1601_ = 3;
v___x_1602_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1602_, 0, v___x_1600_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*1, v___x_1601_);
v___x_1603_ = lean_array_push(v_a_1564_, v___x_1602_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1603_);
v___x_1605_ = v___x_1549_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_trace_1546_);
lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_buildTime_1547_);
lean_ctor_set_uint8(v_reuseFailAlloc_1606_, sizeof(void*)*3 + 1, v_wantsRebuild_1545_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_ctor_set_uint8(v___x_1605_, sizeof(void*)*3, v___x_1552_);
v_a_1558_ = v___x_1566_;
v_a_1559_ = v___x_1605_;
goto v___jp_1557_;
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1615_; 
lean_dec(v_a_1563_);
lean_dec_ref(v___x_1554_);
v_a_1609_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1609_);
lean_dec_ref(v___x_1570_);
v___x_1610_ = lean_io_error_to_string(v_a_1609_);
v___x_1611_ = 3;
v___x_1612_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set_uint8(v___x_1612_, sizeof(void*)*1, v___x_1611_);
v___x_1613_ = lean_array_push(v_a_1564_, v___x_1612_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1613_);
v___x_1615_ = v___x_1549_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1616_, 1, v_trace_1546_);
lean_ctor_set(v_reuseFailAlloc_1616_, 2, v_buildTime_1547_);
lean_ctor_set_uint8(v_reuseFailAlloc_1616_, sizeof(void*)*3 + 1, v_wantsRebuild_1545_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_ctor_set_uint8(v___x_1615_, sizeof(void*)*3, v___x_1552_);
v_a_1558_ = v___x_1566_;
v_a_1559_ = v___x_1615_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v_a_1618_; lean_object* v___x_1620_; 
lean_dec_ref(v___x_1554_);
lean_dec_ref(v_log_1543_);
lean_dec_ref(v_traceFile_1522_);
v_a_1617_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1617_);
v_a_1618_ = lean_ctor_get(v___x_1556_, 1);
lean_inc(v_a_1618_);
lean_dec_ref(v___x_1556_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v_a_1618_);
v___x_1620_ = v___x_1549_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1618_);
lean_ctor_set(v_reuseFailAlloc_1621_, 1, v_trace_1546_);
lean_ctor_set(v_reuseFailAlloc_1621_, 2, v_buildTime_1547_);
lean_ctor_set_uint8(v_reuseFailAlloc_1621_, sizeof(void*)*3 + 1, v_wantsRebuild_1545_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3, v___x_1552_);
v_a_1558_ = v_a_1617_;
v_a_1559_ = v___x_1620_;
goto v___jp_1557_;
}
}
v___jp_1557_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v_a_1562_; 
v___x_1560_ = lean_box(0);
v___x_1561_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1555_, v___x_1560_, v_a_1559_);
lean_dec(v___x_1555_);
v_a_1562_ = lean_ctor_get(v___x_1561_, 1);
lean_inc(v_a_1562_);
lean_dec_ref(v___x_1561_);
v_a_1528_ = v_a_1558_;
v_a_1529_ = v_a_1562_;
goto v___jp_1527_;
}
}
else
{
uint8_t v___x_1622_; 
lean_dec_ref(v_archiveFile_1519_);
lean_dec_ref(v_url_1518_);
v___x_1622_ = l_System_FilePath_pathExists(v_traceFile_1522_);
lean_dec_ref(v_traceFile_1522_);
if (v___x_1622_ == 0)
{
lean_dec_ref(v___x_1554_);
lean_del_object(v___x_1549_);
v_log_1532_ = v_log_1543_;
v_action_1533_ = v___x_1552_;
v_wantsRebuild_1534_ = v_noBuild_1551_;
v_trace_1535_ = v_trace_1546_;
v_buildTime_1536_ = v_buildTime_1547_;
goto v___jp_1531_;
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1623_ = lean_box(0);
v___x_1624_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__0));
v___x_1625_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1521_, v___x_1623_, v___x_1624_);
v___x_1626_ = l_Lake_BuildMetadata_writeFile(v___x_1554_, v___x_1625_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_dec_ref(v___x_1626_);
lean_del_object(v___x_1549_);
v_log_1532_ = v_log_1543_;
v_action_1533_ = v___x_1552_;
v_wantsRebuild_1534_ = v_noBuild_1551_;
v_trace_1535_ = v_trace_1546_;
v_buildTime_1536_ = v_buildTime_1547_;
goto v___jp_1531_;
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref(v___x_1626_);
v___x_1628_ = lean_io_error_to_string(v_a_1627_);
v___x_1629_ = 3;
v___x_1630_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1630_, 0, v___x_1628_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*1, v___x_1629_);
v___x_1631_ = lean_array_get_size(v_log_1543_);
v___x_1632_ = lean_array_push(v_log_1543_, v___x_1630_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1632_);
v___x_1634_ = v___x_1549_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_trace_1546_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_buildTime_1547_);
v___x_1634_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; 
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3, v___x_1552_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 1, v_noBuild_1551_);
v___x_1635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1631_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
return v___x_1635_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___boxed(lean_object* v_url_1638_, lean_object* v_archiveFile_1639_, lean_object* v_headers_1640_, lean_object* v_depTrace_1641_, lean_object* v_traceFile_1642_, lean_object* v_action_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
uint8_t v_action_boxed_1647_; lean_object* v_res_1648_; 
v_action_boxed_1647_ = lean_unbox(v_action_1643_);
v_res_1648_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1638_, v_archiveFile_1639_, v_headers_1640_, v_depTrace_1641_, v_traceFile_1642_, v_action_boxed_1647_, v_a_1644_, v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec_ref(v_depTrace_1641_);
lean_dec_ref(v_headers_1640_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(lean_object* v_url_1649_, lean_object* v_archiveFile_1650_, lean_object* v_headers_1651_, lean_object* v_a_1652_, lean_object* v_depTrace_1653_, lean_object* v_traceFile_1654_, uint8_t v_action_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1649_, v_archiveFile_1650_, v_headers_1651_, v_depTrace_1653_, v_traceFile_1654_, v_action_1655_, v_a_1659_, v_a_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___boxed(lean_object* v_url_1663_, lean_object* v_archiveFile_1664_, lean_object* v_headers_1665_, lean_object* v_a_1666_, lean_object* v_depTrace_1667_, lean_object* v_traceFile_1668_, lean_object* v_action_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
uint8_t v_action_boxed_1676_; lean_object* v_res_1677_; 
v_action_boxed_1676_ = lean_unbox(v_action_1669_);
v_res_1677_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(v_url_1663_, v_archiveFile_1664_, v_headers_1665_, v_a_1666_, v_depTrace_1667_, v_traceFile_1668_, v_action_boxed_1676_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_depTrace_1667_);
lean_dec_ref(v_a_1666_);
lean_dec_ref(v_headers_1665_);
return v_res_1677_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(lean_object* v_x_1678_, lean_object* v_x_1679_){
_start:
{
if (lean_obj_tag(v_x_1678_) == 0)
{
if (lean_obj_tag(v_x_1679_) == 0)
{
uint8_t v___x_1680_; 
v___x_1680_ = 1;
return v___x_1680_;
}
else
{
uint8_t v___x_1681_; 
v___x_1681_ = 0;
return v___x_1681_;
}
}
else
{
if (lean_obj_tag(v_x_1679_) == 0)
{
uint8_t v___x_1682_; 
v___x_1682_ = 0;
return v___x_1682_;
}
else
{
lean_object* v_val_1683_; lean_object* v_val_1684_; uint64_t v___x_1685_; uint64_t v___x_1686_; uint8_t v___x_1687_; 
v_val_1683_ = lean_ctor_get(v_x_1678_, 0);
v_val_1684_ = lean_ctor_get(v_x_1679_, 0);
v___x_1685_ = lean_unbox_uint64(v_val_1683_);
v___x_1686_ = lean_unbox_uint64(v_val_1684_);
v___x_1687_ = lean_uint64_dec_eq(v___x_1685_, v___x_1686_);
return v___x_1687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(lean_object* v_x_1688_, lean_object* v_x_1689_){
_start:
{
uint8_t v_res_1690_; lean_object* v_r_1691_; 
v_res_1690_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v_x_1688_, v_x_1689_);
lean_dec(v_x_1689_);
lean_dec(v_x_1688_);
v_r_1691_ = lean_box(v_res_1690_);
return v_r_1691_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object* v_info_1692_, lean_object* v_self_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_io_metadata(v_info_1692_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v_modified_1697_; uint8_t v___x_1698_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref(v___x_1695_);
v_modified_1697_ = lean_ctor_get(v_a_1696_, 1);
lean_inc_ref(v_modified_1697_);
lean_dec(v_a_1696_);
v___x_1698_ = l_IO_FS_instOrdSystemTime_ord(v_self_1693_, v_modified_1697_);
lean_dec_ref(v_modified_1697_);
if (v___x_1698_ == 0)
{
uint8_t v___x_1699_; 
v___x_1699_ = 1;
return v___x_1699_;
}
else
{
uint8_t v___x_1700_; 
v___x_1700_ = 0;
return v___x_1700_;
}
}
else
{
uint8_t v___x_1701_; 
lean_dec_ref(v___x_1695_);
v___x_1701_ = 0;
return v___x_1701_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object* v_info_1702_, lean_object* v_self_1703_, lean_object* v_a_1704_){
_start:
{
uint8_t v_res_1705_; lean_object* v_r_1706_; 
v_res_1705_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1702_, v_self_1703_);
lean_dec_ref(v_self_1703_);
lean_dec_ref(v_info_1702_);
v_r_1706_ = lean_box(v_res_1705_);
return v_r_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(lean_object* v_info_1707_, lean_object* v_depTrace_1708_, lean_object* v_depHash_1709_, lean_object* v_oldTrace_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
uint64_t v_hash_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_hash_1714_ = lean_ctor_get_uint64(v_depTrace_1708_, sizeof(void*)*3);
v___x_1715_ = lean_box_uint64(v_hash_1714_);
v___x_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
v___x_1717_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v___x_1716_, v_depHash_1709_);
lean_dec_ref(v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v_toBuildConfig_1718_; uint8_t v_oldMode_1719_; 
v_toBuildConfig_1718_ = lean_ctor_get(v_a_1711_, 0);
v_oldMode_1719_ = lean_ctor_get_uint8(v_toBuildConfig_1718_, sizeof(void*)*2);
if (v_oldMode_1719_ == 0)
{
uint8_t v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = 0;
v___x_1721_ = lean_box(v___x_1720_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v_a_1712_);
return v___x_1722_;
}
else
{
uint8_t v___x_1723_; 
v___x_1723_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1707_, v_oldTrace_1710_);
if (v___x_1723_ == 0)
{
uint8_t v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = 0;
v___x_1725_ = lean_box(v___x_1724_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
lean_ctor_set(v___x_1726_, 1, v_a_1712_);
return v___x_1726_;
}
else
{
uint8_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = 1;
v___x_1728_ = lean_box(v___x_1727_);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
lean_ctor_set(v___x_1729_, 1, v_a_1712_);
return v___x_1729_;
}
}
}
else
{
uint8_t v___x_1730_; 
v___x_1730_ = l_System_FilePath_pathExists(v_info_1707_);
if (v___x_1730_ == 0)
{
uint8_t v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1731_ = 0;
v___x_1732_ = lean_box(v___x_1731_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v_a_1712_);
return v___x_1733_;
}
else
{
uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = 2;
v___x_1735_ = lean_box(v___x_1734_);
v___x_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
lean_ctor_set(v___x_1736_, 1, v_a_1712_);
return v___x_1736_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(lean_object* v_info_1737_, lean_object* v_depTrace_1738_, lean_object* v_depHash_1739_, lean_object* v_oldTrace_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1737_, v_depTrace_1738_, v_depHash_1739_, v_oldTrace_1740_, v_a_1741_, v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec_ref(v_oldTrace_1740_);
lean_dec(v_depHash_1739_);
lean_dec_ref(v_depTrace_1738_);
lean_dec_ref(v_info_1737_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(lean_object* v_a_1745_, lean_object* v_info_1746_, lean_object* v_depTrace_1747_, lean_object* v_savedTrace_1748_, lean_object* v_oldTrace_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
if (lean_obj_tag(v_savedTrace_1748_) == 2)
{
lean_object* v_data_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1806_; 
v_data_1756_ = lean_ctor_get(v_savedTrace_1748_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_savedTrace_1748_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1758_ = v_savedTrace_1748_;
v_isShared_1759_ = v_isSharedCheck_1806_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_data_1756_);
lean_dec(v_savedTrace_1748_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1806_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
uint64_t v_depHash_1760_; lean_object* v_log_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v_depHash_1760_ = lean_ctor_get_uint64(v_data_1756_, sizeof(void*)*3);
v_log_1761_ = lean_ctor_get(v_data_1756_, 2);
lean_inc_ref(v_log_1761_);
lean_dec_ref(v_data_1756_);
v___x_1762_ = lean_box_uint64(v_depHash_1760_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set_tag(v___x_1758_, 1);
lean_ctor_set(v___x_1758_, 0, v___x_1762_);
v___x_1764_ = v___x_1758_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1765_; lean_object* v_a_1766_; lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1804_; 
v___x_1765_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1746_, v_depTrace_1747_, v___x_1764_, v_oldTrace_1749_, v_a_1753_, v_a_1754_);
lean_dec_ref(v___x_1764_);
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_a_1767_ = lean_ctor_get(v___x_1765_, 1);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1769_ = v___x_1765_;
v_isShared_1770_ = v_isSharedCheck_1804_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1804_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___y_1772_; uint8_t v___x_1776_; uint8_t v___x_1777_; uint8_t v___x_1778_; 
v___x_1776_ = 0;
v___x_1777_ = lean_unbox(v_a_1766_);
v___x_1778_ = l_Lake_instDecidableEqOutputStatus(v___x_1777_, v___x_1776_);
if (v___x_1778_ == 0)
{
lean_object* v_log_1779_; uint8_t v_action_1780_; uint8_t v_wantsRebuild_1781_; lean_object* v_trace_1782_; lean_object* v_buildTime_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1803_; 
v_log_1779_ = lean_ctor_get(v_a_1767_, 0);
v_action_1780_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*3);
v_wantsRebuild_1781_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*3 + 1);
v_trace_1782_ = lean_ctor_get(v_a_1767_, 1);
v_buildTime_1783_ = lean_ctor_get(v_a_1767_, 2);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_a_1767_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1785_ = v_a_1767_;
v_isShared_1786_ = v_isSharedCheck_1803_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_buildTime_1783_);
lean_inc(v_trace_1782_);
lean_inc(v_log_1779_);
lean_dec(v_a_1767_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1803_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
uint8_t v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1790_; 
v___x_1787_ = 1;
v___x_1788_ = l_Lake_JobAction_merge(v_action_1780_, v___x_1787_);
if (v_isShared_1786_ == 0)
{
v___x_1790_ = v___x_1785_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_log_1779_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_trace_1782_);
lean_ctor_set(v_reuseFailAlloc_1802_, 2, v_buildTime_1783_);
lean_ctor_set_uint8(v_reuseFailAlloc_1802_, sizeof(void*)*3 + 1, v_wantsRebuild_1781_);
v___x_1790_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1791_; 
lean_ctor_set_uint8(v___x_1790_, sizeof(void*)*3, v___x_1788_);
v___x_1791_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_1761_, v_a_1745_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v___x_1790_);
lean_dec_ref(v_log_1761_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 1);
lean_inc(v_a_1792_);
lean_dec_ref(v___x_1791_);
v___y_1772_ = v_a_1792_;
goto v___jp_1771_;
}
else
{
lean_object* v_a_1793_; lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_del_object(v___x_1769_);
lean_dec(v_a_1766_);
v_a_1793_ = lean_ctor_get(v___x_1791_, 0);
v_a_1794_ = lean_ctor_get(v___x_1791_, 1);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1791_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_inc(v_a_1793_);
lean_dec(v___x_1791_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1793_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_a_1794_);
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
}
}
else
{
lean_dec_ref(v_log_1761_);
v___y_1772_ = v_a_1767_;
goto v___jp_1771_;
}
v___jp_1771_:
{
lean_object* v___x_1774_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 1, v___y_1772_);
v___x_1774_ = v___x_1769_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1766_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v___y_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_1807_; uint8_t v_oldMode_1808_; 
lean_dec(v_savedTrace_1748_);
v_toBuildConfig_1807_ = lean_ctor_get(v_a_1753_, 0);
v_oldMode_1808_ = lean_ctor_get_uint8(v_toBuildConfig_1807_, sizeof(void*)*2);
if (v_oldMode_1808_ == 0)
{
uint8_t v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = 0;
v___x_1810_ = lean_box(v___x_1809_);
v___x_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
lean_ctor_set(v___x_1811_, 1, v_a_1754_);
return v___x_1811_;
}
else
{
uint8_t v___x_1812_; 
v___x_1812_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_1746_, v_oldTrace_1749_);
if (v___x_1812_ == 0)
{
uint8_t v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = 0;
v___x_1814_ = lean_box(v___x_1813_);
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v_a_1754_);
return v___x_1815_;
}
else
{
uint8_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = 1;
v___x_1817_ = lean_box(v___x_1816_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
lean_ctor_set(v___x_1818_, 1, v_a_1754_);
return v___x_1818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object* v_a_1819_, lean_object* v_info_1820_, lean_object* v_depTrace_1821_, lean_object* v_savedTrace_1822_, lean_object* v_oldTrace_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_1819_, v_info_1820_, v_depTrace_1821_, v_savedTrace_1822_, v_oldTrace_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
lean_dec_ref(v_a_1827_);
lean_dec(v_a_1826_);
lean_dec(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec_ref(v_oldTrace_1823_);
lean_dec_ref(v_depTrace_1821_);
lean_dec_ref(v_info_1820_);
lean_dec_ref(v_a_1819_);
return v_res_1830_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_unsigned_to_nat(0u);
v___x_1836_ = lean_nat_to_int(v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4(void){
_start:
{
uint32_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = 0;
v___x_1838_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3);
v___x_1839_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set_uint32(v___x_1839_, sizeof(void*)*1, v___x_1837_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(lean_object* v_self_1840_, lean_object* v_url_1841_, lean_object* v_archiveFile_1842_, lean_object* v_headers_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_a_1852_; lean_object* v_a_1853_; lean_object* v_log_1855_; uint8_t v_action_1856_; uint8_t v_wantsRebuild_1857_; lean_object* v_trace_1858_; lean_object* v_buildTime_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1955_; 
v_log_1855_ = lean_ctor_get(v_a_1849_, 0);
v_action_1856_ = lean_ctor_get_uint8(v_a_1849_, sizeof(void*)*3);
v_wantsRebuild_1857_ = lean_ctor_get_uint8(v_a_1849_, sizeof(void*)*3 + 1);
v_trace_1858_ = lean_ctor_get(v_a_1849_, 1);
v_buildTime_1859_ = lean_ctor_get(v_a_1849_, 2);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_a_1849_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1861_ = v_a_1849_;
v_isShared_1862_ = v_isSharedCheck_1955_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_buildTime_1859_);
lean_inc(v_trace_1858_);
lean_inc(v_log_1855_);
lean_dec(v_a_1849_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1955_;
goto v_resetjp_1860_;
}
v___jp_1851_:
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1854_, 0, v_a_1852_);
lean_ctor_set(v___x_1854_, 1, v_a_1853_);
return v___x_1854_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v_traceFile_1864_; lean_object* v___x_1865_; 
v___x_1863_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0));
lean_inc_ref(v_archiveFile_1842_);
v_traceFile_1864_ = l_System_FilePath_addExtension(v_archiveFile_1842_, v___x_1863_);
lean_inc_ref(v_traceFile_1864_);
v___x_1865_ = l_Lake_readTraceFile(v_traceFile_1864_, v_log_1855_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v_a_1867_; lean_object* v___x_1868_; uint64_t v___x_1869_; uint64_t v___x_1870_; uint64_t v_depTrace_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1876_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
v_a_1867_ = lean_ctor_get(v___x_1865_, 1);
lean_inc(v_a_1867_);
lean_dec_ref(v___x_1865_);
v___x_1868_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1));
v___x_1869_ = l_Lake_Hash_nil;
v___x_1870_ = lean_string_hash(v_url_1841_);
v_depTrace_1871_ = lean_uint64_mix_hash(v___x_1869_, v___x_1870_);
v___x_1872_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2));
v___x_1873_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
v___x_1874_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1868_);
lean_ctor_set(v___x_1874_, 2, v___x_1873_);
lean_ctor_set_uint64(v___x_1874_, sizeof(void*)*3, v_depTrace_1871_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v_a_1867_);
v___x_1876_ = v___x_1861_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1867_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_trace_1858_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_buildTime_1859_);
lean_ctor_set_uint8(v_reuseFailAlloc_1949_, sizeof(void*)*3, v_action_1856_);
lean_ctor_set_uint8(v_reuseFailAlloc_1949_, sizeof(void*)*3 + 1, v_wantsRebuild_1857_);
v___x_1876_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_1844_, v_archiveFile_1842_, v___x_1874_, v_a_1866_, v___x_1873_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v___x_1876_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1946_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
v_a_1879_ = lean_ctor_get(v___x_1877_, 1);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1881_ = v___x_1877_;
v_isShared_1882_ = v_isSharedCheck_1946_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_inc(v_a_1878_);
lean_dec(v___x_1877_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1946_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
uint8_t v___x_1883_; uint8_t v___y_1885_; uint8_t v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; uint8_t v_a_1915_; lean_object* v_a_1916_; uint8_t v___x_1937_; uint8_t v___x_1938_; uint8_t v___x_1939_; 
v___x_1883_ = 2;
v___x_1937_ = 0;
v___x_1938_ = lean_unbox(v_a_1878_);
lean_dec(v_a_1878_);
v___x_1939_ = l_Lake_instDecidableEqOutputStatus(v___x_1938_, v___x_1937_);
if (v___x_1939_ == 0)
{
uint8_t v___x_1940_; 
lean_dec_ref(v___x_1874_);
lean_dec_ref(v_traceFile_1864_);
lean_dec_ref(v_url_1841_);
v___x_1940_ = 1;
v_a_1915_ = v___x_1940_;
v_a_1916_ = v_a_1879_;
goto v___jp_1914_;
}
else
{
lean_object* v___x_1941_; 
lean_inc_ref(v_archiveFile_1842_);
v___x_1941_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_1841_, v_archiveFile_1842_, v_headers_1843_, v___x_1874_, v_traceFile_1864_, v___x_1883_, v_a_1848_, v_a_1879_);
lean_dec_ref(v___x_1874_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; uint8_t v___x_1943_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 1);
lean_inc(v_a_1942_);
lean_dec_ref(v___x_1941_);
v___x_1943_ = 0;
v_a_1915_ = v___x_1943_;
v_a_1916_ = v_a_1942_;
goto v___jp_1914_;
}
else
{
lean_object* v_a_1944_; lean_object* v_a_1945_; 
lean_del_object(v___x_1881_);
lean_dec_ref(v_archiveFile_1842_);
lean_dec_ref(v_self_1840_);
v_a_1944_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1944_);
v_a_1945_ = lean_ctor_get(v___x_1941_, 1);
lean_inc(v_a_1945_);
lean_dec_ref(v___x_1941_);
v_a_1852_ = v_a_1944_;
v_a_1853_ = v_a_1945_;
goto v___jp_1851_;
}
}
v___jp_1884_:
{
uint8_t v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1891_ = 1;
v___x_1892_ = l_Lake_untar(v_archiveFile_1842_, v___y_1888_, v___x_1891_, v___y_1889_);
v___x_1893_ = l_Lake_JobAction_merge(v___y_1886_, v___x_1883_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1894_; lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1903_; 
v_a_1894_ = lean_ctor_get(v___x_1892_, 0);
v_a_1895_ = lean_ctor_get(v___x_1892_, 1);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1897_ = v___x_1892_;
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_inc(v_a_1894_);
lean_dec(v___x_1892_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1899_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1899_, 0, v_a_1895_);
lean_ctor_set(v___x_1899_, 1, v___y_1887_);
lean_ctor_set(v___x_1899_, 2, v___y_1890_);
lean_ctor_set_uint8(v___x_1899_, sizeof(void*)*3, v___x_1893_);
lean_ctor_set_uint8(v___x_1899_, sizeof(void*)*3 + 1, v___y_1885_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 1, v___x_1899_);
v___x_1901_ = v___x_1897_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1894_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1913_; 
v_a_1904_ = lean_ctor_get(v___x_1892_, 0);
v_a_1905_ = lean_ctor_get(v___x_1892_, 1);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1907_ = v___x_1892_;
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_inc(v_a_1904_);
lean_dec(v___x_1892_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1913_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1909_, 0, v_a_1905_);
lean_ctor_set(v___x_1909_, 1, v___y_1887_);
lean_ctor_set(v___x_1909_, 2, v___y_1890_);
lean_ctor_set_uint8(v___x_1909_, sizeof(void*)*3, v___x_1893_);
lean_ctor_set_uint8(v___x_1909_, sizeof(void*)*3 + 1, v___y_1885_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 1, v___x_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1904_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v___x_1909_);
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
v___jp_1914_:
{
lean_object* v_config_1917_; lean_object* v_dir_1918_; lean_object* v_buildDir_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v_config_1917_ = lean_ctor_get(v_self_1840_, 6);
lean_inc_ref(v_config_1917_);
v_dir_1918_ = lean_ctor_get(v_self_1840_, 4);
lean_inc_ref(v_dir_1918_);
lean_dec_ref(v_self_1840_);
v_buildDir_1919_ = lean_ctor_get(v_config_1917_, 5);
lean_inc_ref(v_buildDir_1919_);
lean_dec_ref(v_config_1917_);
v___x_1920_ = l_System_FilePath_normalize(v_buildDir_1919_);
v___x_1921_ = l_Lake_joinRelative(v_dir_1918_, v___x_1920_);
v___x_1922_ = l_System_FilePath_pathExists(v___x_1921_);
if (v_a_1915_ == 0)
{
lean_object* v_log_1923_; uint8_t v_action_1924_; uint8_t v_wantsRebuild_1925_; lean_object* v_trace_1926_; lean_object* v_buildTime_1927_; 
lean_del_object(v___x_1881_);
v_log_1923_ = lean_ctor_get(v_a_1916_, 0);
lean_inc_ref(v_log_1923_);
v_action_1924_ = lean_ctor_get_uint8(v_a_1916_, sizeof(void*)*3);
v_wantsRebuild_1925_ = lean_ctor_get_uint8(v_a_1916_, sizeof(void*)*3 + 1);
v_trace_1926_ = lean_ctor_get(v_a_1916_, 1);
lean_inc_ref(v_trace_1926_);
v_buildTime_1927_ = lean_ctor_get(v_a_1916_, 2);
lean_inc(v_buildTime_1927_);
lean_dec_ref(v_a_1916_);
v___y_1885_ = v_wantsRebuild_1925_;
v___y_1886_ = v_action_1924_;
v___y_1887_ = v_trace_1926_;
v___y_1888_ = v___x_1921_;
v___y_1889_ = v_log_1923_;
v___y_1890_ = v_buildTime_1927_;
goto v___jp_1884_;
}
else
{
if (v___x_1922_ == 0)
{
lean_object* v_log_1928_; uint8_t v_action_1929_; uint8_t v_wantsRebuild_1930_; lean_object* v_trace_1931_; lean_object* v_buildTime_1932_; 
lean_del_object(v___x_1881_);
v_log_1928_ = lean_ctor_get(v_a_1916_, 0);
lean_inc_ref(v_log_1928_);
v_action_1929_ = lean_ctor_get_uint8(v_a_1916_, sizeof(void*)*3);
v_wantsRebuild_1930_ = lean_ctor_get_uint8(v_a_1916_, sizeof(void*)*3 + 1);
v_trace_1931_ = lean_ctor_get(v_a_1916_, 1);
lean_inc_ref(v_trace_1931_);
v_buildTime_1932_ = lean_ctor_get(v_a_1916_, 2);
lean_inc(v_buildTime_1932_);
lean_dec_ref(v_a_1916_);
v___y_1885_ = v_wantsRebuild_1930_;
v___y_1886_ = v_action_1929_;
v___y_1887_ = v_trace_1931_;
v___y_1888_ = v___x_1921_;
v___y_1889_ = v_log_1928_;
v___y_1890_ = v_buildTime_1932_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
lean_dec_ref(v___x_1921_);
lean_dec_ref(v_archiveFile_1842_);
v___x_1933_ = lean_box(0);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 1, v_a_1916_);
lean_ctor_set(v___x_1881_, 0, v___x_1933_);
v___x_1935_ = v___x_1881_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_a_1916_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v_a_1948_; 
lean_dec_ref(v___x_1874_);
lean_dec_ref(v_traceFile_1864_);
lean_dec_ref(v_archiveFile_1842_);
lean_dec_ref(v_url_1841_);
lean_dec_ref(v_self_1840_);
v_a_1947_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1947_);
v_a_1948_ = lean_ctor_get(v___x_1877_, 1);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1877_);
v_a_1852_ = v_a_1947_;
v_a_1853_ = v_a_1948_;
goto v___jp_1851_;
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v_a_1951_; lean_object* v___x_1953_; 
lean_dec_ref(v_traceFile_1864_);
lean_dec_ref(v_archiveFile_1842_);
lean_dec_ref(v_url_1841_);
lean_dec_ref(v_self_1840_);
v_a_1950_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1950_);
v_a_1951_ = lean_ctor_get(v___x_1865_, 1);
lean_inc(v_a_1951_);
lean_dec_ref(v___x_1865_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v_a_1951_);
v___x_1953_ = v___x_1861_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1951_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_trace_1858_);
lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_buildTime_1859_);
lean_ctor_set_uint8(v_reuseFailAlloc_1954_, sizeof(void*)*3, v_action_1856_);
lean_ctor_set_uint8(v_reuseFailAlloc_1954_, sizeof(void*)*3 + 1, v_wantsRebuild_1857_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
v_a_1852_ = v_a_1950_;
v_a_1853_ = v___x_1953_;
goto v___jp_1851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object* v_self_1956_, lean_object* v_url_1957_, lean_object* v_archiveFile_1958_, lean_object* v_headers_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_self_1956_, v_url_1957_, v_archiveFile_1958_, v_headers_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec_ref(v_headers_1959_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object* v_a_1968_, lean_object* v_info_1969_, lean_object* v_depTrace_1970_, lean_object* v_depHash_1971_, lean_object* v_oldTrace_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_1969_, v_depTrace_1970_, v_depHash_1971_, v_oldTrace_1972_, v_a_1976_, v_a_1977_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object* v_a_1980_, lean_object* v_info_1981_, lean_object* v_depTrace_1982_, lean_object* v_depHash_1983_, lean_object* v_oldTrace_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_1980_, v_info_1981_, v_depTrace_1982_, v_depHash_1983_, v_oldTrace_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
lean_dec_ref(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_oldTrace_1984_);
lean_dec(v_depHash_1983_);
lean_dec_ref(v_depTrace_1982_);
lean_dec_ref(v_info_1981_);
lean_dec_ref(v_a_1980_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_getUrl_1992_, lean_object* v_pkg_1993_, lean_object* v_archiveFile_1994_, lean_object* v_headers_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
uint8_t v_r_2004_; lean_object* v___y_2005_; lean_object* v_a_2009_; lean_object* v___x_2025_; 
lean_inc_ref(v___y_2000_);
lean_inc(v___y_1999_);
lean_inc(v___y_1998_);
lean_inc(v___y_1997_);
lean_inc_ref(v___y_1996_);
lean_inc_ref(v_pkg_1993_);
v___x_2025_ = lean_apply_8(v_getUrl_1992_, v_pkg_1993_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, lean_box(0));
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v_a_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
v_a_2027_ = lean_ctor_get(v___x_2025_, 1);
lean_inc(v_a_2027_);
lean_dec_ref(v___x_2025_);
lean_inc_ref(v_pkg_1993_);
v___x_2028_ = lean_apply_1(v_archiveFile_1994_, v_pkg_1993_);
v___x_2029_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_1993_, v_a_2026_, v___x_2028_, v_headers_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v_a_2027_);
lean_dec_ref(v___y_1996_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; uint8_t v___x_2031_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 1);
lean_inc(v_a_2030_);
lean_dec_ref(v___x_2029_);
v___x_2031_ = 1;
v_r_2004_ = v___x_2031_;
v___y_2005_ = v_a_2030_;
goto v___jp_2003_;
}
else
{
lean_object* v_a_2032_; 
v_a_2032_ = lean_ctor_get(v___x_2029_, 1);
lean_inc(v_a_2032_);
lean_dec_ref(v___x_2029_);
v_a_2009_ = v_a_2032_;
goto v___jp_2008_;
}
}
else
{
lean_object* v_a_2033_; 
lean_dec_ref(v___y_1996_);
lean_dec_ref(v_archiveFile_1994_);
lean_dec_ref(v_pkg_1993_);
v_a_2033_ = lean_ctor_get(v___x_2025_, 1);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2025_);
v_a_2009_ = v_a_2033_;
goto v___jp_2008_;
}
v___jp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_box(v_r_2004_);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
lean_ctor_set(v___x_2007_, 1, v___y_2005_);
return v___x_2007_;
}
v___jp_2008_:
{
lean_object* v_log_2010_; uint8_t v_action_2011_; uint8_t v_wantsRebuild_2012_; lean_object* v_trace_2013_; lean_object* v_buildTime_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2024_; 
v_log_2010_ = lean_ctor_get(v_a_2009_, 0);
v_action_2011_ = lean_ctor_get_uint8(v_a_2009_, sizeof(void*)*3);
v_wantsRebuild_2012_ = lean_ctor_get_uint8(v_a_2009_, sizeof(void*)*3 + 1);
v_trace_2013_ = lean_ctor_get(v_a_2009_, 1);
v_buildTime_2014_ = lean_ctor_get(v_a_2009_, 2);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_a_2009_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2016_ = v_a_2009_;
v_isShared_2017_ = v_isSharedCheck_2024_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_buildTime_2014_);
lean_inc(v_trace_2013_);
lean_inc(v_log_2010_);
lean_dec(v_a_2009_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2024_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
uint8_t v___x_2018_; uint8_t v___x_2019_; lean_object* v___x_2021_; 
v___x_2018_ = 2;
v___x_2019_ = l_Lake_JobAction_merge(v_action_2011_, v___x_2018_);
if (v_isShared_2017_ == 0)
{
v___x_2021_ = v___x_2016_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_log_2010_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_trace_2013_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_buildTime_2014_);
lean_ctor_set_uint8(v_reuseFailAlloc_2023_, sizeof(void*)*3 + 1, v_wantsRebuild_2012_);
v___x_2021_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
uint8_t v___x_2022_; 
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*3, v___x_2019_);
v___x_2022_ = 0;
v_r_2004_ = v___x_2022_;
v___y_2005_ = v___x_2021_;
goto v___jp_2003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_getUrl_2034_, lean_object* v_pkg_2035_, lean_object* v_archiveFile_2036_, lean_object* v_headers_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(v_getUrl_2034_, v_pkg_2035_, v_archiveFile_2036_, v_headers_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v_headers_2037_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* v_getUrl_2046_, lean_object* v_archiveFile_2047_, lean_object* v_headers_2048_, lean_object* v___x_2049_, lean_object* v_facet_2050_, lean_object* v_pkg_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
lean_object* v___f_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_inc_ref(v_pkg_2051_);
v___f_2059_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2059_, 0, v_getUrl_2046_);
lean_closure_set(v___f_2059_, 1, v_pkg_2051_);
lean_closure_set(v___f_2059_, 2, v_archiveFile_2047_);
lean_closure_set(v___f_2059_, 3, v_headers_2048_);
v___x_2060_ = lean_unsigned_to_nat(0u);
v___x_2061_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1));
lean_inc(v___x_2049_);
v___x_2062_ = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(v___x_2062_, 0, lean_box(0));
lean_closure_set(v___x_2062_, 1, v___x_2049_);
lean_closure_set(v___x_2062_, 2, v___f_2059_);
lean_closure_set(v___x_2062_, 3, v___x_2060_);
lean_closure_set(v___x_2062_, 4, v___x_2061_);
v___x_2063_ = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM___boxed), 9, 2);
lean_closure_set(v___x_2063_, 0, lean_box(0));
lean_closure_set(v___x_2063_, 1, v___x_2062_);
v___x_2064_ = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM___boxed), 9, 2);
lean_closure_set(v___x_2064_, 0, lean_box(0));
lean_closure_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = l_Lake_ensureJob___redArg(v___x_2049_, v___x_2064_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2098_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
v_a_2067_ = lean_ctor_get(v___x_2065_, 1);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2069_ = v___x_2065_;
v_isShared_2070_ = v_isSharedCheck_2098_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_inc(v_a_2066_);
lean_dec(v___x_2065_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2098_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v_task_2071_; lean_object* v_kind_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2096_; 
v_task_2071_ = lean_ctor_get(v_a_2066_, 0);
v_kind_2072_ = lean_ctor_get(v_a_2066_, 1);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_a_2066_);
if (v_isSharedCheck_2096_ == 0)
{
lean_object* v_unused_2097_; 
v_unused_2097_ = lean_ctor_get(v_a_2066_, 2);
lean_dec(v_unused_2097_);
v___x_2074_ = v_a_2066_;
v_isShared_2075_ = v_isSharedCheck_2096_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_kind_2072_);
lean_inc(v_task_2071_);
lean_dec(v_a_2066_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2096_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v_registeredJobs_2076_; lean_object* v___x_2077_; lean_object* v_baseName_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v_job_2087_; 
v_registeredJobs_2076_ = lean_ctor_get(v___y_2056_, 3);
v___x_2077_ = lean_st_ref_take(v_registeredJobs_2076_);
v_baseName_2078_ = lean_ctor_get(v_pkg_2051_, 1);
lean_inc(v_baseName_2078_);
lean_dec_ref(v_pkg_2051_);
v___x_2079_ = 1;
v___x_2080_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2078_, v___x_2079_);
v___x_2081_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2082_ = lean_string_append(v___x_2080_, v___x_2081_);
v___x_2083_ = l_Lake_Name_eraseHead(v_facet_2050_);
v___x_2084_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2083_, v___x_2079_);
v___x_2085_ = lean_string_append(v___x_2082_, v___x_2084_);
lean_dec_ref(v___x_2084_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 2, v___x_2085_);
v_job_2087_ = v___x_2074_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_task_2071_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_kind_2072_);
lean_ctor_set(v_reuseFailAlloc_2095_, 2, v___x_2085_);
v_job_2087_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2093_; 
lean_ctor_set_uint8(v_job_2087_, sizeof(void*)*3, v___x_2079_);
lean_inc_ref(v_job_2087_);
v___x_2088_ = l_Lake_Job_toOpaque___redArg(v_job_2087_);
v___x_2089_ = lean_array_push(v___x_2077_, v___x_2088_);
v___x_2090_ = lean_st_ref_set(v_registeredJobs_2076_, v___x_2089_);
v___x_2091_ = l_Lake_Job_renew___redArg(v_job_2087_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2091_);
v___x_2093_ = v___x_2069_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2094_, 1, v_a_2067_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_2051_);
lean_dec(v_facet_2050_);
return v___x_2065_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v_getUrl_2099_, lean_object* v_archiveFile_2100_, lean_object* v_headers_2101_, lean_object* v___x_2102_, lean_object* v_facet_2103_, lean_object* v_pkg_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_2099_, v_archiveFile_2100_, v_headers_2101_, v___x_2102_, v_facet_2103_, v_pkg_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec(v___y_2106_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object* v_facet_2120_, lean_object* v_archiveFile_2121_, lean_object* v_getUrl_2122_, lean_object* v_headers_2123_){
_start:
{
lean_object* v___x_2124_; lean_object* v___f_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2124_ = l_Lake_instDataKindBool;
v___f_2125_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2125_, 0, v_getUrl_2122_);
lean_closure_set(v___f_2125_, 1, v_archiveFile_2121_);
lean_closure_set(v___f_2125_, 2, v_headers_2123_);
lean_closure_set(v___f_2125_, 3, v___x_2124_);
lean_closure_set(v___f_2125_, 4, v_facet_2120_);
v___x_2126_ = l_Lake_Package_keyword;
v___x_2127_ = 1;
v___x_2128_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_2129_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2129_, 0, v___x_2126_);
lean_ctor_set(v___x_2129_, 1, v___f_2125_);
lean_ctor_set(v___x_2129_, 2, v___x_2124_);
lean_ctor_set(v___x_2129_, 3, v___x_2128_);
lean_ctor_set_uint8(v___x_2129_, sizeof(void*)*4, v___x_2127_);
lean_ctor_set_uint8(v___x_2129_, sizeof(void*)*4 + 1, v___x_2127_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* v_facet_2130_, lean_object* v_archiveFile_2131_, lean_object* v_getUrl_2132_, lean_object* v_headers_2133_, lean_object* v_inst_2134_){
_start:
{
lean_object* v___x_2135_; lean_object* v___f_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2135_ = l_Lake_instDataKindBool;
v___f_2136_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2136_, 0, v_getUrl_2132_);
lean_closure_set(v___f_2136_, 1, v_archiveFile_2131_);
lean_closure_set(v___f_2136_, 2, v_headers_2133_);
lean_closure_set(v___f_2136_, 3, v___x_2135_);
lean_closure_set(v___f_2136_, 4, v_facet_2130_);
v___x_2137_ = l_Lake_Package_keyword;
v___x_2138_ = 1;
v___x_2139_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_2140_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2140_, 0, v___x_2137_);
lean_ctor_set(v___x_2140_, 1, v___f_2136_);
lean_ctor_set(v___x_2140_, 2, v___x_2135_);
lean_ctor_set(v___x_2140_, 3, v___x_2139_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*4, v___x_2138_);
lean_ctor_set_uint8(v___x_2140_, sizeof(void*)*4 + 1, v___x_2138_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_what_2142_, lean_object* v_baseName_2143_, lean_object* v_optFacet_2144_, uint8_t v_success_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_a_2154_; lean_object* v_a_2155_; 
if (v_success_2145_ == 0)
{
lean_object* v_toBuildConfig_2176_; uint8_t v_verbosity_2177_; uint8_t v___x_2178_; uint8_t v___x_2179_; 
v_toBuildConfig_2176_ = lean_ctor_get(v___y_2150_, 0);
v_verbosity_2177_ = lean_ctor_get_uint8(v_toBuildConfig_2176_, sizeof(void*)*2 + 3);
v___x_2178_ = 2;
v___x_2179_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2177_, v___x_2178_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; 
lean_dec(v_optFacet_2144_);
lean_dec(v_baseName_2143_);
v___x_2180_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2154_ = v___x_2180_;
v_a_2155_ = v___y_2151_;
goto v___jp_2153_;
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2181_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2182_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2143_, v___x_2179_);
v___x_2183_ = lean_string_append(v___x_2181_, v___x_2182_);
lean_dec_ref(v___x_2182_);
v___x_2184_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2185_ = lean_string_append(v___x_2183_, v___x_2184_);
v___x_2186_ = l_Lake_Name_eraseHead(v_optFacet_2144_);
v___x_2187_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2186_, v___x_2179_);
v___x_2188_ = lean_string_append(v___x_2185_, v___x_2187_);
lean_dec_ref(v___x_2187_);
v___x_2189_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2190_ = lean_string_append(v___x_2188_, v___x_2189_);
v_a_2154_ = v___x_2190_;
v_a_2155_ = v___y_2151_;
goto v___jp_2153_;
}
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec(v_optFacet_2144_);
lean_dec(v_baseName_2143_);
v___x_2191_ = lean_box(0);
v___x_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set(v___x_2192_, 1, v___y_2151_);
return v___x_2192_;
}
v___jp_2153_:
{
lean_object* v_log_2156_; uint8_t v_action_2157_; uint8_t v_wantsRebuild_2158_; lean_object* v_trace_2159_; lean_object* v_buildTime_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2175_; 
v_log_2156_ = lean_ctor_get(v_a_2155_, 0);
v_action_2157_ = lean_ctor_get_uint8(v_a_2155_, sizeof(void*)*3);
v_wantsRebuild_2158_ = lean_ctor_get_uint8(v_a_2155_, sizeof(void*)*3 + 1);
v_trace_2159_ = lean_ctor_get(v_a_2155_, 1);
v_buildTime_2160_ = lean_ctor_get(v_a_2155_, 2);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_a_2155_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2162_ = v_a_2155_;
v_isShared_2163_ = v_isSharedCheck_2175_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_buildTime_2160_);
lean_inc(v_trace_2159_);
lean_inc(v_log_2156_);
lean_dec(v_a_2155_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2175_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2164_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0));
v___x_2165_ = lean_string_append(v___x_2164_, v_what_2142_);
v___x_2166_ = lean_string_append(v___x_2165_, v_a_2154_);
lean_dec_ref(v_a_2154_);
v___x_2167_ = 3;
v___x_2168_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*1, v___x_2167_);
v___x_2169_ = lean_array_get_size(v_log_2156_);
v___x_2170_ = lean_array_push(v_log_2156_, v___x_2168_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2170_);
v___x_2172_ = v___x_2162_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2170_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_trace_2159_);
lean_ctor_set(v_reuseFailAlloc_2174_, 2, v_buildTime_2160_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*3, v_action_2157_);
lean_ctor_set_uint8(v_reuseFailAlloc_2174_, sizeof(void*)*3 + 1, v_wantsRebuild_2158_);
v___x_2172_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2173_; 
v___x_2173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2169_);
lean_ctor_set(v___x_2173_, 1, v___x_2172_);
return v___x_2173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_what_2193_, lean_object* v_baseName_2194_, lean_object* v_optFacet_2195_, lean_object* v_success_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
uint8_t v_success_boxed_2204_; lean_object* v_res_2205_; 
v_success_boxed_2204_ = lean_unbox(v_success_2196_);
v_res_2205_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(v_what_2193_, v_baseName_2194_, v_optFacet_2195_, v_success_boxed_2204_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec_ref(v_what_2193_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object* v___x_2206_, lean_object* v___x_2207_, lean_object* v___f_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; 
lean_inc_ref(v___y_2209_);
lean_inc_ref(v___y_2213_);
lean_inc(v___y_2212_);
lean_inc(v___y_2211_);
lean_inc(v___y_2210_);
v___x_2216_ = lean_apply_7(v___y_2209_, v___x_2206_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, lean_box(0));
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2229_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_a_2218_ = lean_ctor_get(v___x_2216_, 1);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2220_ = v___x_2216_;
v_isShared_2221_ = v_isSharedCheck_2229_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2229_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2222_; uint8_t v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2222_ = lean_unsigned_to_nat(0u);
v___x_2223_ = 0;
v___x_2224_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3);
v___x_2225_ = l_Lake_Job_mapM___redArg(v___x_2207_, v_a_2217_, v___f_2208_, v___x_2222_, v___x_2223_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___x_2224_);
if (v_isShared_2221_ == 0)
{
lean_ctor_set(v___x_2220_, 0, v___x_2225_);
v___x_2227_ = v___x_2220_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_a_2218_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v___y_2209_);
lean_dec_ref(v___f_2208_);
lean_dec(v___x_2207_);
v_a_2230_ = lean_ctor_get(v___x_2216_, 0);
v_a_2231_ = lean_ctor_get(v___x_2216_, 1);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2216_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_inc(v_a_2230_);
lean_dec(v___x_2216_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2230_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v___x_2239_, lean_object* v___x_2240_, lean_object* v___f_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(v___x_2239_, v___x_2240_, v___f_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec(v___y_2243_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object* v_what_2250_, lean_object* v_optFacet_2251_, lean_object* v___x_2252_, lean_object* v_facet_2253_, lean_object* v_pkg_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v_baseName_2262_; lean_object* v_keyName_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___f_2268_; lean_object* v___x_2269_; 
v_baseName_2262_ = lean_ctor_get(v_pkg_2254_, 1);
lean_inc_n(v_baseName_2262_, 2);
v_keyName_2263_ = lean_ctor_get(v_pkg_2254_, 2);
lean_inc(v_optFacet_2251_);
v___f_2264_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2264_, 0, v_what_2250_);
lean_closure_set(v___f_2264_, 1, v_baseName_2262_);
lean_closure_set(v___f_2264_, 2, v_optFacet_2251_);
lean_inc(v_keyName_2263_);
v___x_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2265_, 0, v_keyName_2263_);
v___x_2266_ = l_Lake_Package_keyword;
v___x_2267_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2265_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
lean_ctor_set(v___x_2267_, 2, v_pkg_2254_);
lean_ctor_set(v___x_2267_, 3, v_optFacet_2251_);
lean_inc(v___x_2252_);
v___f_2268_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2268_, 0, v___x_2267_);
lean_closure_set(v___f_2268_, 1, v___x_2252_);
lean_closure_set(v___f_2268_, 2, v___f_2264_);
v___x_2269_ = l_Lake_ensureJob___redArg(v___x_2252_, v___f_2268_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2302_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_a_2271_ = lean_ctor_get(v___x_2269_, 1);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2273_ = v___x_2269_;
v_isShared_2274_ = v_isSharedCheck_2302_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2302_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v_task_2275_; lean_object* v_kind_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2300_; 
v_task_2275_ = lean_ctor_get(v_a_2270_, 0);
v_kind_2276_ = lean_ctor_get(v_a_2270_, 1);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_a_2270_);
if (v_isSharedCheck_2300_ == 0)
{
lean_object* v_unused_2301_; 
v_unused_2301_ = lean_ctor_get(v_a_2270_, 2);
lean_dec(v_unused_2301_);
v___x_2278_ = v_a_2270_;
v_isShared_2279_ = v_isSharedCheck_2300_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_kind_2276_);
lean_inc(v_task_2275_);
lean_dec(v_a_2270_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2300_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v_registeredJobs_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; lean_object* v_job_2291_; 
v_registeredJobs_2280_ = lean_ctor_get(v___y_2259_, 3);
v___x_2281_ = lean_st_ref_take(v_registeredJobs_2280_);
v___x_2282_ = 1;
v___x_2283_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2262_, v___x_2282_);
v___x_2284_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2285_ = lean_string_append(v___x_2283_, v___x_2284_);
v___x_2286_ = l_Lake_Name_eraseHead(v_facet_2253_);
v___x_2287_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2286_, v___x_2282_);
v___x_2288_ = lean_string_append(v___x_2285_, v___x_2287_);
lean_dec_ref(v___x_2287_);
v___x_2289_ = 0;
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 2, v___x_2288_);
v_job_2291_ = v___x_2278_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_task_2275_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_kind_2276_);
lean_ctor_set(v_reuseFailAlloc_2299_, 2, v___x_2288_);
v_job_2291_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
lean_ctor_set_uint8(v_job_2291_, sizeof(void*)*3, v___x_2289_);
lean_inc_ref(v_job_2291_);
v___x_2292_ = l_Lake_Job_toOpaque___redArg(v_job_2291_);
v___x_2293_ = lean_array_push(v___x_2281_, v___x_2292_);
v___x_2294_ = lean_st_ref_set(v_registeredJobs_2280_, v___x_2293_);
v___x_2295_ = l_Lake_Job_renew___redArg(v_job_2291_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2295_);
v___x_2297_ = v___x_2273_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_a_2271_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2262_);
lean_dec(v_facet_2253_);
return v___x_2269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object* v_what_2303_, lean_object* v_optFacet_2304_, lean_object* v___x_2305_, lean_object* v_facet_2306_, lean_object* v_pkg_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(v_what_2303_, v_optFacet_2304_, v___x_2305_, v_facet_2306_, v_pkg_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec(v___y_2309_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object* v_facet_2323_, lean_object* v_optFacet_2324_, lean_object* v_what_2325_){
_start:
{
lean_object* v___x_2326_; lean_object* v___f_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2326_ = l_Lake_instDataKindUnit;
v___f_2327_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2327_, 0, v_what_2325_);
lean_closure_set(v___f_2327_, 1, v_optFacet_2324_);
lean_closure_set(v___f_2327_, 2, v___x_2326_);
lean_closure_set(v___f_2327_, 3, v_facet_2323_);
v___x_2328_ = l_Lake_Package_keyword;
v___x_2329_ = 1;
v___x_2330_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2331_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2331_, 0, v___x_2328_);
lean_ctor_set(v___x_2331_, 1, v___f_2327_);
lean_ctor_set(v___x_2331_, 2, v___x_2326_);
lean_ctor_set(v___x_2331_, 3, v___x_2330_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*4, v___x_2329_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*4 + 1, v___x_2329_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* v_facet_2332_, lean_object* v_optFacet_2333_, lean_object* v_what_2334_, lean_object* v_inst_2335_, lean_object* v_inst_2336_){
_start:
{
lean_object* v___x_2337_; lean_object* v___f_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2337_ = l_Lake_instDataKindUnit;
v___f_2338_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2338_, 0, v_what_2334_);
lean_closure_set(v___f_2338_, 1, v_optFacet_2333_);
lean_closure_set(v___f_2338_, 2, v___x_2337_);
lean_closure_set(v___f_2338_, 3, v_facet_2332_);
v___x_2339_ = l_Lake_Package_keyword;
v___x_2340_ = 1;
v___x_2341_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2342_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2342_, 0, v___x_2339_);
lean_ctor_set(v___x_2342_, 1, v___f_2338_);
lean_ctor_set(v___x_2342_, 2, v___x_2337_);
lean_ctor_set(v___x_2342_, 3, v___x_2341_);
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*4, v___x_2340_);
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*4 + 1, v___x_2340_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* v_baseName_2344_, lean_object* v___x_2345_, uint8_t v_success_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_a_2355_; lean_object* v_a_2356_; 
if (v_success_2346_ == 0)
{
lean_object* v_toBuildConfig_2376_; uint8_t v_verbosity_2377_; uint8_t v___x_2378_; uint8_t v___x_2379_; 
v_toBuildConfig_2376_ = lean_ctor_get(v___y_2351_, 0);
v_verbosity_2377_ = lean_ctor_get_uint8(v_toBuildConfig_2376_, sizeof(void*)*2 + 3);
v___x_2378_ = 2;
v___x_2379_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2377_, v___x_2378_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; 
lean_dec(v___x_2345_);
lean_dec(v_baseName_2344_);
v___x_2380_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2355_ = v___x_2380_;
v_a_2356_ = v___y_2352_;
goto v___jp_2354_;
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2381_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2382_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2344_, v___x_2379_);
v___x_2383_ = lean_string_append(v___x_2381_, v___x_2382_);
lean_dec_ref(v___x_2382_);
v___x_2384_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2385_ = lean_string_append(v___x_2383_, v___x_2384_);
v___x_2386_ = l_Lake_Name_eraseHead(v___x_2345_);
v___x_2387_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2386_, v___x_2379_);
v___x_2388_ = lean_string_append(v___x_2385_, v___x_2387_);
lean_dec_ref(v___x_2387_);
v___x_2389_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2390_ = lean_string_append(v___x_2388_, v___x_2389_);
v_a_2355_ = v___x_2390_;
v_a_2356_ = v___y_2352_;
goto v___jp_2354_;
}
}
else
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
lean_dec(v___x_2345_);
lean_dec(v_baseName_2344_);
v___x_2391_ = lean_box(0);
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
lean_ctor_set(v___x_2392_, 1, v___y_2352_);
return v___x_2392_;
}
v___jp_2354_:
{
lean_object* v_log_2357_; uint8_t v_action_2358_; uint8_t v_wantsRebuild_2359_; lean_object* v_trace_2360_; lean_object* v_buildTime_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2375_; 
v_log_2357_ = lean_ctor_get(v_a_2356_, 0);
v_action_2358_ = lean_ctor_get_uint8(v_a_2356_, sizeof(void*)*3);
v_wantsRebuild_2359_ = lean_ctor_get_uint8(v_a_2356_, sizeof(void*)*3 + 1);
v_trace_2360_ = lean_ctor_get(v_a_2356_, 1);
v_buildTime_2361_ = lean_ctor_get(v_a_2356_, 2);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_a_2356_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2363_ = v_a_2356_;
v_isShared_2364_ = v_isSharedCheck_2375_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_buildTime_2361_);
lean_inc(v_trace_2360_);
lean_inc(v_log_2357_);
lean_dec(v_a_2356_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2375_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; uint8_t v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2372_; 
v___x_2365_ = ((lean_object*)(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0));
v___x_2366_ = lean_string_append(v___x_2365_, v_a_2355_);
lean_dec_ref(v_a_2355_);
v___x_2367_ = 3;
v___x_2368_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2368_, 0, v___x_2366_);
lean_ctor_set_uint8(v___x_2368_, sizeof(void*)*1, v___x_2367_);
v___x_2369_ = lean_array_get_size(v_log_2357_);
v___x_2370_ = lean_array_push(v_log_2357_, v___x_2368_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 0, v___x_2370_);
v___x_2372_ = v___x_2363_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_trace_2360_);
lean_ctor_set(v_reuseFailAlloc_2374_, 2, v_buildTime_2361_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*3, v_action_2358_);
lean_ctor_set_uint8(v_reuseFailAlloc_2374_, sizeof(void*)*3 + 1, v_wantsRebuild_2359_);
v___x_2372_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2373_; 
v___x_2373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2369_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
return v___x_2373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object* v_baseName_2393_, lean_object* v___x_2394_, lean_object* v_success_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
uint8_t v_success_boxed_2403_; lean_object* v_res_2404_; 
v_success_boxed_2403_ = lean_unbox(v_success_2395_);
v_res_2404_ = l_Lake_Package_buildCacheFacetConfig___lam__1(v_baseName_2393_, v___x_2394_, v_success_boxed_2403_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* v___x_2405_, lean_object* v___x_2406_, lean_object* v___x_2407_, lean_object* v_pkg_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_baseName_2416_; lean_object* v_keyName_2417_; lean_object* v___f_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___f_2422_; lean_object* v___x_2423_; 
v_baseName_2416_ = lean_ctor_get(v_pkg_2408_, 1);
lean_inc_n(v_baseName_2416_, 2);
v_keyName_2417_ = lean_ctor_get(v_pkg_2408_, 2);
lean_inc(v___x_2405_);
v___f_2418_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2418_, 0, v_baseName_2416_);
lean_closure_set(v___f_2418_, 1, v___x_2405_);
lean_inc(v_keyName_2417_);
v___x_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2419_, 0, v_keyName_2417_);
v___x_2420_ = l_Lake_Package_keyword;
v___x_2421_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2419_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
lean_ctor_set(v___x_2421_, 2, v_pkg_2408_);
lean_ctor_set(v___x_2421_, 3, v___x_2405_);
lean_inc(v___x_2406_);
v___f_2422_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2422_, 0, v___x_2421_);
lean_closure_set(v___f_2422_, 1, v___x_2406_);
lean_closure_set(v___f_2422_, 2, v___f_2418_);
v___x_2423_ = l_Lake_ensureJob___redArg(v___x_2406_, v___f_2422_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2456_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
v_a_2425_ = lean_ctor_get(v___x_2423_, 1);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2427_ = v___x_2423_;
v_isShared_2428_ = v_isSharedCheck_2456_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_inc(v_a_2424_);
lean_dec(v___x_2423_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2456_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v_task_2429_; lean_object* v_kind_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2454_; 
v_task_2429_ = lean_ctor_get(v_a_2424_, 0);
v_kind_2430_ = lean_ctor_get(v_a_2424_, 1);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_a_2424_);
if (v_isSharedCheck_2454_ == 0)
{
lean_object* v_unused_2455_; 
v_unused_2455_ = lean_ctor_get(v_a_2424_, 2);
lean_dec(v_unused_2455_);
v___x_2432_ = v_a_2424_;
v_isShared_2433_ = v_isSharedCheck_2454_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_kind_2430_);
lean_inc(v_task_2429_);
lean_dec(v_a_2424_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2454_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v_registeredJobs_2434_; lean_object* v___x_2435_; uint8_t v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; lean_object* v_job_2445_; 
v_registeredJobs_2434_ = lean_ctor_get(v___y_2413_, 3);
v___x_2435_ = lean_st_ref_take(v_registeredJobs_2434_);
v___x_2436_ = 1;
v___x_2437_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2416_, v___x_2436_);
v___x_2438_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2439_ = lean_string_append(v___x_2437_, v___x_2438_);
v___x_2440_ = l_Lake_Name_eraseHead(v___x_2407_);
v___x_2441_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2440_, v___x_2436_);
v___x_2442_ = lean_string_append(v___x_2439_, v___x_2441_);
lean_dec_ref(v___x_2441_);
v___x_2443_ = 0;
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 2, v___x_2442_);
v_job_2445_ = v___x_2432_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_task_2429_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_kind_2430_);
lean_ctor_set(v_reuseFailAlloc_2453_, 2, v___x_2442_);
v_job_2445_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2451_; 
lean_ctor_set_uint8(v_job_2445_, sizeof(void*)*3, v___x_2443_);
lean_inc_ref(v_job_2445_);
v___x_2446_ = l_Lake_Job_toOpaque___redArg(v_job_2445_);
v___x_2447_ = lean_array_push(v___x_2435_, v___x_2446_);
v___x_2448_ = lean_st_ref_set(v_registeredJobs_2434_, v___x_2447_);
v___x_2449_ = l_Lake_Job_renew___redArg(v_job_2445_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2449_);
v___x_2451_ = v___x_2427_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_a_2425_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2416_);
lean_dec(v___x_2407_);
return v___x_2423_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object* v___x_2457_, lean_object* v___x_2458_, lean_object* v___x_2459_, lean_object* v_pkg_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Lake_Package_buildCacheFacetConfig___lam__2(v___x_2457_, v___x_2458_, v___x_2459_, v_pkg_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec(v___y_2462_);
return v_res_2468_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___f_2472_; 
v___x_2469_ = l_Lake_Package_buildCacheFacet;
v___x_2470_ = l_Lake_instDataKindUnit;
v___x_2471_ = l_Lake_Package_optBuildCacheFacet;
v___f_2472_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2472_, 0, v___x_2471_);
lean_closure_set(v___f_2472_, 1, v___x_2470_);
lean_closure_set(v___f_2472_, 2, v___x_2469_);
return v___f_2472_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2473_; uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___f_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___f_2473_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2474_ = 1;
v___x_2475_ = l_Lake_instDataKindUnit;
v___f_2476_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__0, &l_Lake_Package_buildCacheFacetConfig___closed__0_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__0);
v___x_2477_ = l_Lake_Package_keyword;
v___x_2478_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
lean_ctor_set(v___x_2478_, 1, v___f_2476_);
lean_ctor_set(v___x_2478_, 2, v___x_2475_);
lean_ctor_set(v___x_2478_, 3, v___f_2473_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*4, v___x_2474_);
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*4 + 1, v___x_2474_);
return v___x_2478_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig(void){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__1, &l_Lake_Package_buildCacheFacetConfig___closed__1_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__1);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* v_pkg_2481_, lean_object* v___x_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
uint8_t v_r_2491_; lean_object* v___y_2492_; lean_object* v_a_2496_; lean_object* v___x_2512_; 
lean_inc_ref(v_pkg_2481_);
v___x_2512_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_pkg_2481_, v___y_2487_, v___y_2488_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v_a_2514_; lean_object* v_dir_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
v_a_2514_ = lean_ctor_get(v___x_2512_, 1);
lean_inc(v_a_2514_);
lean_dec_ref(v___x_2512_);
v_dir_2515_ = lean_ctor_get(v_pkg_2481_, 4);
v___x_2516_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_2515_);
v___x_2517_ = l_Lake_joinRelative(v_dir_2515_, v___x_2516_);
v___x_2518_ = ((lean_object*)(l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0));
v___x_2519_ = l_Lake_joinRelative(v___x_2517_, v___x_2518_);
v___x_2520_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2481_, v_a_2513_, v___x_2519_, v___x_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v_a_2514_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; uint8_t v___x_2522_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 1);
lean_inc(v_a_2521_);
lean_dec_ref(v___x_2520_);
v___x_2522_ = 1;
v_r_2491_ = v___x_2522_;
v___y_2492_ = v_a_2521_;
goto v___jp_2490_;
}
else
{
lean_object* v_a_2523_; 
v_a_2523_ = lean_ctor_get(v___x_2520_, 1);
lean_inc(v_a_2523_);
lean_dec_ref(v___x_2520_);
v_a_2496_ = v_a_2523_;
goto v___jp_2495_;
}
}
else
{
lean_object* v_a_2524_; 
lean_dec_ref(v_pkg_2481_);
v_a_2524_ = lean_ctor_get(v___x_2512_, 1);
lean_inc(v_a_2524_);
lean_dec_ref(v___x_2512_);
v_a_2496_ = v_a_2524_;
goto v___jp_2495_;
}
v___jp_2490_:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2493_ = lean_box(v_r_2491_);
v___x_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
lean_ctor_set(v___x_2494_, 1, v___y_2492_);
return v___x_2494_;
}
v___jp_2495_:
{
lean_object* v_log_2497_; uint8_t v_action_2498_; uint8_t v_wantsRebuild_2499_; lean_object* v_trace_2500_; lean_object* v_buildTime_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2511_; 
v_log_2497_ = lean_ctor_get(v_a_2496_, 0);
v_action_2498_ = lean_ctor_get_uint8(v_a_2496_, sizeof(void*)*3);
v_wantsRebuild_2499_ = lean_ctor_get_uint8(v_a_2496_, sizeof(void*)*3 + 1);
v_trace_2500_ = lean_ctor_get(v_a_2496_, 1);
v_buildTime_2501_ = lean_ctor_get(v_a_2496_, 2);
v_isSharedCheck_2511_ = !lean_is_exclusive(v_a_2496_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2503_ = v_a_2496_;
v_isShared_2504_ = v_isSharedCheck_2511_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_buildTime_2501_);
lean_inc(v_trace_2500_);
lean_inc(v_log_2497_);
lean_dec(v_a_2496_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2511_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
uint8_t v___x_2505_; uint8_t v___x_2506_; lean_object* v___x_2508_; 
v___x_2505_ = 2;
v___x_2506_ = l_Lake_JobAction_merge(v_action_2498_, v___x_2505_);
if (v_isShared_2504_ == 0)
{
v___x_2508_ = v___x_2503_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_log_2497_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_trace_2500_);
lean_ctor_set(v_reuseFailAlloc_2510_, 2, v_buildTime_2501_);
lean_ctor_set_uint8(v_reuseFailAlloc_2510_, sizeof(void*)*3 + 1, v_wantsRebuild_2499_);
v___x_2508_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
uint8_t v___x_2509_; 
lean_ctor_set_uint8(v___x_2508_, sizeof(void*)*3, v___x_2506_);
v___x_2509_ = 0;
v_r_2491_ = v___x_2509_;
v___y_2492_ = v___x_2508_;
goto v___jp_2490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* v_pkg_2525_, lean_object* v___x_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lake_Package_optBarrelFacetConfig___lam__0(v_pkg_2525_, v___x_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec_ref(v___x_2526_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* v___x_2535_, lean_object* v___f_2536_, lean_object* v___x_2537_, lean_object* v___x_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = l_Lake_Job_async___redArg(v___x_2535_, v___f_2536_, v___x_2537_, v___x_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
lean_ctor_set(v___x_2547_, 1, v___y_2544_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object* v___x_2548_, lean_object* v___f_2549_, lean_object* v___x_2550_, lean_object* v___x_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lake_Package_optBarrelFacetConfig___lam__1(v___x_2548_, v___f_2549_, v___x_2550_, v___x_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec(v___y_2554_);
lean_dec(v___y_2553_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* v___x_2560_, lean_object* v___x_2561_, lean_object* v___x_2562_, lean_object* v_pkg_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v___f_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___f_2574_; lean_object* v___x_2575_; 
lean_inc_ref(v_pkg_2563_);
v___f_2571_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2571_, 0, v_pkg_2563_);
lean_closure_set(v___f_2571_, 1, v___x_2560_);
v___x_2572_ = lean_unsigned_to_nat(0u);
v___x_2573_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1));
lean_inc(v___x_2561_);
v___f_2574_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2574_, 0, v___x_2561_);
lean_closure_set(v___f_2574_, 1, v___f_2571_);
lean_closure_set(v___f_2574_, 2, v___x_2572_);
lean_closure_set(v___f_2574_, 3, v___x_2573_);
v___x_2575_ = l_Lake_ensureJob___redArg(v___x_2561_, v___f_2574_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2608_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
v_a_2577_ = lean_ctor_get(v___x_2575_, 1);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2579_ = v___x_2575_;
v_isShared_2580_ = v_isSharedCheck_2608_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_inc(v_a_2576_);
lean_dec(v___x_2575_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2608_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v_task_2581_; lean_object* v_kind_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2606_; 
v_task_2581_ = lean_ctor_get(v_a_2576_, 0);
v_kind_2582_ = lean_ctor_get(v_a_2576_, 1);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_a_2576_);
if (v_isSharedCheck_2606_ == 0)
{
lean_object* v_unused_2607_; 
v_unused_2607_ = lean_ctor_get(v_a_2576_, 2);
lean_dec(v_unused_2607_);
v___x_2584_ = v_a_2576_;
v_isShared_2585_ = v_isSharedCheck_2606_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_kind_2582_);
lean_inc(v_task_2581_);
lean_dec(v_a_2576_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2606_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v_registeredJobs_2586_; lean_object* v___x_2587_; lean_object* v_baseName_2588_; uint8_t v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v_job_2597_; 
v_registeredJobs_2586_ = lean_ctor_get(v___y_2568_, 3);
v___x_2587_ = lean_st_ref_take(v_registeredJobs_2586_);
v_baseName_2588_ = lean_ctor_get(v_pkg_2563_, 1);
lean_inc(v_baseName_2588_);
lean_dec_ref(v_pkg_2563_);
v___x_2589_ = 1;
v___x_2590_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2588_, v___x_2589_);
v___x_2591_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2592_ = lean_string_append(v___x_2590_, v___x_2591_);
v___x_2593_ = l_Lake_Name_eraseHead(v___x_2562_);
v___x_2594_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2593_, v___x_2589_);
v___x_2595_ = lean_string_append(v___x_2592_, v___x_2594_);
lean_dec_ref(v___x_2594_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 2, v___x_2595_);
v_job_2597_ = v___x_2584_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_task_2581_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_kind_2582_);
lean_ctor_set(v_reuseFailAlloc_2605_, 2, v___x_2595_);
v_job_2597_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
lean_ctor_set_uint8(v_job_2597_, sizeof(void*)*3, v___x_2589_);
lean_inc_ref(v_job_2597_);
v___x_2598_ = l_Lake_Job_toOpaque___redArg(v_job_2597_);
v___x_2599_ = lean_array_push(v___x_2587_, v___x_2598_);
v___x_2600_ = lean_st_ref_set(v_registeredJobs_2586_, v___x_2599_);
v___x_2601_ = l_Lake_Job_renew___redArg(v_job_2597_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v___x_2601_);
v___x_2603_ = v___x_2579_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v_a_2577_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_2563_);
lean_dec(v___x_2562_);
return v___x_2575_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object* v___x_2609_, lean_object* v___x_2610_, lean_object* v___x_2611_, lean_object* v_pkg_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Lake_Package_optBarrelFacetConfig___lam__2(v___x_2609_, v___x_2610_, v___x_2611_, v_pkg_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec(v___y_2614_);
return v_res_2620_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___f_2624_; 
v___x_2621_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_2622_ = l_Lake_instDataKindBool;
v___x_2623_ = l_Lake_Reservoir_lakeHeaders;
v___f_2624_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2624_, 0, v___x_2623_);
lean_closure_set(v___f_2624_, 1, v___x_2622_);
lean_closure_set(v___f_2624_, 2, v___x_2621_);
return v___f_2624_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2625_; uint8_t v___x_2626_; lean_object* v___x_2627_; lean_object* v___f_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___f_2625_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_2626_ = 1;
v___x_2627_ = l_Lake_instDataKindBool;
v___f_2628_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__0, &l_Lake_Package_optBarrelFacetConfig___closed__0_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__0);
v___x_2629_ = l_Lake_Package_keyword;
v___x_2630_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
lean_ctor_set(v___x_2630_, 1, v___f_2628_);
lean_ctor_set(v___x_2630_, 2, v___x_2627_);
lean_ctor_set(v___x_2630_, 3, v___f_2625_);
lean_ctor_set_uint8(v___x_2630_, sizeof(void*)*4, v___x_2626_);
lean_ctor_set_uint8(v___x_2630_, sizeof(void*)*4 + 1, v___x_2626_);
return v___x_2630_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig(void){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__1, &l_Lake_Package_optBarrelFacetConfig___closed__1_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__1);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* v_baseName_2633_, lean_object* v___x_2634_, uint8_t v_success_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v_a_2644_; lean_object* v_a_2645_; 
if (v_success_2635_ == 0)
{
lean_object* v_toBuildConfig_2665_; uint8_t v_verbosity_2666_; uint8_t v___x_2667_; uint8_t v___x_2668_; 
v_toBuildConfig_2665_ = lean_ctor_get(v___y_2640_, 0);
v_verbosity_2666_ = lean_ctor_get_uint8(v_toBuildConfig_2665_, sizeof(void*)*2 + 3);
v___x_2667_ = 2;
v___x_2668_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2666_, v___x_2667_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; 
lean_dec(v___x_2634_);
lean_dec(v_baseName_2633_);
v___x_2669_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2644_ = v___x_2669_;
v_a_2645_ = v___y_2641_;
goto v___jp_2643_;
}
else
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2670_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2671_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2633_, v___x_2668_);
v___x_2672_ = lean_string_append(v___x_2670_, v___x_2671_);
lean_dec_ref(v___x_2671_);
v___x_2673_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2674_ = lean_string_append(v___x_2672_, v___x_2673_);
v___x_2675_ = l_Lake_Name_eraseHead(v___x_2634_);
v___x_2676_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2675_, v___x_2668_);
v___x_2677_ = lean_string_append(v___x_2674_, v___x_2676_);
lean_dec_ref(v___x_2676_);
v___x_2678_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2679_ = lean_string_append(v___x_2677_, v___x_2678_);
v_a_2644_ = v___x_2679_;
v_a_2645_ = v___y_2641_;
goto v___jp_2643_;
}
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; 
lean_dec(v___x_2634_);
lean_dec(v_baseName_2633_);
v___x_2680_ = lean_box(0);
v___x_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2680_);
lean_ctor_set(v___x_2681_, 1, v___y_2641_);
return v___x_2681_;
}
v___jp_2643_:
{
lean_object* v_log_2646_; uint8_t v_action_2647_; uint8_t v_wantsRebuild_2648_; lean_object* v_trace_2649_; lean_object* v_buildTime_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2664_; 
v_log_2646_ = lean_ctor_get(v_a_2645_, 0);
v_action_2647_ = lean_ctor_get_uint8(v_a_2645_, sizeof(void*)*3);
v_wantsRebuild_2648_ = lean_ctor_get_uint8(v_a_2645_, sizeof(void*)*3 + 1);
v_trace_2649_ = lean_ctor_get(v_a_2645_, 1);
v_buildTime_2650_ = lean_ctor_get(v_a_2645_, 2);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_a_2645_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2652_ = v_a_2645_;
v_isShared_2653_ = v_isSharedCheck_2664_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_buildTime_2650_);
lean_inc(v_trace_2649_);
lean_inc(v_log_2646_);
lean_dec(v_a_2645_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2664_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2654_ = ((lean_object*)(l_Lake_Package_barrelFacetConfig___lam__1___closed__0));
v___x_2655_ = lean_string_append(v___x_2654_, v_a_2644_);
lean_dec_ref(v_a_2644_);
v___x_2656_ = 3;
v___x_2657_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2657_, 0, v___x_2655_);
lean_ctor_set_uint8(v___x_2657_, sizeof(void*)*1, v___x_2656_);
v___x_2658_ = lean_array_get_size(v_log_2646_);
v___x_2659_ = lean_array_push(v_log_2646_, v___x_2657_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2659_);
v___x_2661_ = v___x_2652_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_trace_2649_);
lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_buildTime_2650_);
lean_ctor_set_uint8(v_reuseFailAlloc_2663_, sizeof(void*)*3, v_action_2647_);
lean_ctor_set_uint8(v_reuseFailAlloc_2663_, sizeof(void*)*3 + 1, v_wantsRebuild_2648_);
v___x_2661_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2658_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
return v___x_2662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object* v_baseName_2682_, lean_object* v___x_2683_, lean_object* v_success_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
uint8_t v_success_boxed_2692_; lean_object* v_res_2693_; 
v_success_boxed_2692_ = lean_unbox(v_success_2684_);
v_res_2693_ = l_Lake_Package_barrelFacetConfig___lam__1(v_baseName_2682_, v___x_2683_, v_success_boxed_2692_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* v___x_2694_, lean_object* v___x_2695_, lean_object* v___x_2696_, lean_object* v_pkg_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_baseName_2705_; lean_object* v_keyName_2706_; lean_object* v___f_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___f_2711_; lean_object* v___x_2712_; 
v_baseName_2705_ = lean_ctor_get(v_pkg_2697_, 1);
lean_inc_n(v_baseName_2705_, 2);
v_keyName_2706_ = lean_ctor_get(v_pkg_2697_, 2);
lean_inc(v___x_2694_);
v___f_2707_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2707_, 0, v_baseName_2705_);
lean_closure_set(v___f_2707_, 1, v___x_2694_);
lean_inc(v_keyName_2706_);
v___x_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2708_, 0, v_keyName_2706_);
v___x_2709_ = l_Lake_Package_keyword;
v___x_2710_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2708_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
lean_ctor_set(v___x_2710_, 2, v_pkg_2697_);
lean_ctor_set(v___x_2710_, 3, v___x_2694_);
lean_inc(v___x_2695_);
v___f_2711_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2711_, 0, v___x_2710_);
lean_closure_set(v___f_2711_, 1, v___x_2695_);
lean_closure_set(v___f_2711_, 2, v___f_2707_);
v___x_2712_ = l_Lake_ensureJob___redArg(v___x_2695_, v___f_2711_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2745_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
v_a_2714_ = lean_ctor_get(v___x_2712_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2716_ = v___x_2712_;
v_isShared_2717_ = v_isSharedCheck_2745_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_inc(v_a_2713_);
lean_dec(v___x_2712_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2745_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v_task_2718_; lean_object* v_kind_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2743_; 
v_task_2718_ = lean_ctor_get(v_a_2713_, 0);
v_kind_2719_ = lean_ctor_get(v_a_2713_, 1);
v_isSharedCheck_2743_ = !lean_is_exclusive(v_a_2713_);
if (v_isSharedCheck_2743_ == 0)
{
lean_object* v_unused_2744_; 
v_unused_2744_ = lean_ctor_get(v_a_2713_, 2);
lean_dec(v_unused_2744_);
v___x_2721_ = v_a_2713_;
v_isShared_2722_ = v_isSharedCheck_2743_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_kind_2719_);
lean_inc(v_task_2718_);
lean_dec(v_a_2713_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2743_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v_registeredJobs_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; lean_object* v_job_2734_; 
v_registeredJobs_2723_ = lean_ctor_get(v___y_2702_, 3);
v___x_2724_ = lean_st_ref_take(v_registeredJobs_2723_);
v___x_2725_ = 1;
v___x_2726_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2705_, v___x_2725_);
v___x_2727_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2728_ = lean_string_append(v___x_2726_, v___x_2727_);
v___x_2729_ = l_Lake_Name_eraseHead(v___x_2696_);
v___x_2730_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2729_, v___x_2725_);
v___x_2731_ = lean_string_append(v___x_2728_, v___x_2730_);
lean_dec_ref(v___x_2730_);
v___x_2732_ = 0;
if (v_isShared_2722_ == 0)
{
lean_ctor_set(v___x_2721_, 2, v___x_2731_);
v_job_2734_ = v___x_2721_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_task_2718_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_kind_2719_);
lean_ctor_set(v_reuseFailAlloc_2742_, 2, v___x_2731_);
v_job_2734_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2740_; 
lean_ctor_set_uint8(v_job_2734_, sizeof(void*)*3, v___x_2732_);
lean_inc_ref(v_job_2734_);
v___x_2735_ = l_Lake_Job_toOpaque___redArg(v_job_2734_);
v___x_2736_ = lean_array_push(v___x_2724_, v___x_2735_);
v___x_2737_ = lean_st_ref_set(v_registeredJobs_2723_, v___x_2736_);
v___x_2738_ = l_Lake_Job_renew___redArg(v_job_2734_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v___x_2738_);
v___x_2740_ = v___x_2716_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_a_2714_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2705_);
lean_dec(v___x_2696_);
return v___x_2712_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object* v___x_2746_, lean_object* v___x_2747_, lean_object* v___x_2748_, lean_object* v_pkg_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lake_Package_barrelFacetConfig___lam__2(v___x_2746_, v___x_2747_, v___x_2748_, v_pkg_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec(v___y_2751_);
return v_res_2757_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___f_2761_; 
v___x_2758_ = l_Lake_Package_reservoirBarrelFacet;
v___x_2759_ = l_Lake_instDataKindUnit;
v___x_2760_ = l_Lake_Package_optReservoirBarrelFacet;
v___f_2761_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2761_, 0, v___x_2760_);
lean_closure_set(v___f_2761_, 1, v___x_2759_);
lean_closure_set(v___f_2761_, 2, v___x_2758_);
return v___f_2761_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2762_; uint8_t v___x_2763_; lean_object* v___x_2764_; lean_object* v___f_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___f_2762_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2763_ = 1;
v___x_2764_ = l_Lake_instDataKindUnit;
v___f_2765_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__0, &l_Lake_Package_barrelFacetConfig___closed__0_once, _init_l_Lake_Package_barrelFacetConfig___closed__0);
v___x_2766_ = l_Lake_Package_keyword;
v___x_2767_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v___f_2765_);
lean_ctor_set(v___x_2767_, 2, v___x_2764_);
lean_ctor_set(v___x_2767_, 3, v___f_2762_);
lean_ctor_set_uint8(v___x_2767_, sizeof(void*)*4, v___x_2763_);
lean_ctor_set_uint8(v___x_2767_, sizeof(void*)*4 + 1, v___x_2763_);
return v___x_2767_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig(void){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__1, &l_Lake_Package_barrelFacetConfig___closed__1_once, _init_l_Lake_Package_barrelFacetConfig___closed__1);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object* v_pkg_2769_, lean_object* v___x_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
uint8_t v_r_2779_; lean_object* v___y_2780_; lean_object* v_a_2784_; lean_object* v___x_2800_; 
lean_inc_ref(v_pkg_2769_);
v___x_2800_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_pkg_2769_, v___y_2776_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v_a_2802_; lean_object* v_dir_2803_; lean_object* v_buildArchive_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
v_a_2802_ = lean_ctor_get(v___x_2800_, 1);
lean_inc(v_a_2802_);
lean_dec_ref(v___x_2800_);
v_dir_2803_ = lean_ctor_get(v_pkg_2769_, 4);
v_buildArchive_2804_ = lean_ctor_get(v_pkg_2769_, 19);
v___x_2805_ = l_Lake_defaultLakeDir;
lean_inc_ref(v_dir_2803_);
v___x_2806_ = l_Lake_joinRelative(v_dir_2803_, v___x_2805_);
lean_inc_ref(v_buildArchive_2804_);
v___x_2807_ = l_Lake_joinRelative(v___x_2806_, v_buildArchive_2804_);
v___x_2808_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2769_, v_a_2801_, v___x_2807_, v___x_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v_a_2802_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; uint8_t v___x_2810_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 1);
lean_inc(v_a_2809_);
lean_dec_ref(v___x_2808_);
v___x_2810_ = 1;
v_r_2779_ = v___x_2810_;
v___y_2780_ = v_a_2809_;
goto v___jp_2778_;
}
else
{
lean_object* v_a_2811_; 
v_a_2811_ = lean_ctor_get(v___x_2808_, 1);
lean_inc(v_a_2811_);
lean_dec_ref(v___x_2808_);
v_a_2784_ = v_a_2811_;
goto v___jp_2783_;
}
}
else
{
lean_object* v_a_2812_; 
lean_dec_ref(v_pkg_2769_);
v_a_2812_ = lean_ctor_get(v___x_2800_, 1);
lean_inc(v_a_2812_);
lean_dec_ref(v___x_2800_);
v_a_2784_ = v_a_2812_;
goto v___jp_2783_;
}
v___jp_2778_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_box(v_r_2779_);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
lean_ctor_set(v___x_2782_, 1, v___y_2780_);
return v___x_2782_;
}
v___jp_2783_:
{
lean_object* v_log_2785_; uint8_t v_action_2786_; uint8_t v_wantsRebuild_2787_; lean_object* v_trace_2788_; lean_object* v_buildTime_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2799_; 
v_log_2785_ = lean_ctor_get(v_a_2784_, 0);
v_action_2786_ = lean_ctor_get_uint8(v_a_2784_, sizeof(void*)*3);
v_wantsRebuild_2787_ = lean_ctor_get_uint8(v_a_2784_, sizeof(void*)*3 + 1);
v_trace_2788_ = lean_ctor_get(v_a_2784_, 1);
v_buildTime_2789_ = lean_ctor_get(v_a_2784_, 2);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_a_2784_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2791_ = v_a_2784_;
v_isShared_2792_ = v_isSharedCheck_2799_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_buildTime_2789_);
lean_inc(v_trace_2788_);
lean_inc(v_log_2785_);
lean_dec(v_a_2784_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2799_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
uint8_t v___x_2793_; uint8_t v___x_2794_; lean_object* v___x_2796_; 
v___x_2793_ = 2;
v___x_2794_ = l_Lake_JobAction_merge(v_action_2786_, v___x_2793_);
if (v_isShared_2792_ == 0)
{
v___x_2796_ = v___x_2791_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_log_2785_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_trace_2788_);
lean_ctor_set(v_reuseFailAlloc_2798_, 2, v_buildTime_2789_);
lean_ctor_set_uint8(v_reuseFailAlloc_2798_, sizeof(void*)*3 + 1, v_wantsRebuild_2787_);
v___x_2796_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
uint8_t v___x_2797_; 
lean_ctor_set_uint8(v___x_2796_, sizeof(void*)*3, v___x_2794_);
v___x_2797_ = 0;
v_r_2779_ = v___x_2797_;
v___y_2780_ = v___x_2796_;
goto v___jp_2778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object* v_pkg_2813_, lean_object* v___x_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(v_pkg_2813_, v___x_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec_ref(v___x_2814_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object* v___x_2823_, lean_object* v___x_2824_, lean_object* v___x_2825_, lean_object* v___x_2826_, lean_object* v_pkg_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___f_2835_; lean_object* v___x_2836_; lean_object* v___f_2837_; lean_object* v___x_2838_; 
lean_inc_ref(v_pkg_2827_);
v___f_2835_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2835_, 0, v_pkg_2827_);
lean_closure_set(v___f_2835_, 1, v___x_2823_);
v___x_2836_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1));
lean_inc(v___x_2824_);
v___f_2837_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2837_, 0, v___x_2824_);
lean_closure_set(v___f_2837_, 1, v___f_2835_);
lean_closure_set(v___f_2837_, 2, v___x_2825_);
lean_closure_set(v___f_2837_, 3, v___x_2836_);
v___x_2838_ = l_Lake_ensureJob___redArg(v___x_2824_, v___f_2837_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2871_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_a_2840_ = lean_ctor_get(v___x_2838_, 1);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2842_ = v___x_2838_;
v_isShared_2843_ = v_isSharedCheck_2871_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2871_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v_task_2844_; lean_object* v_kind_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2869_; 
v_task_2844_ = lean_ctor_get(v_a_2839_, 0);
v_kind_2845_ = lean_ctor_get(v_a_2839_, 1);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_a_2839_);
if (v_isSharedCheck_2869_ == 0)
{
lean_object* v_unused_2870_; 
v_unused_2870_ = lean_ctor_get(v_a_2839_, 2);
lean_dec(v_unused_2870_);
v___x_2847_ = v_a_2839_;
v_isShared_2848_ = v_isSharedCheck_2869_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_kind_2845_);
lean_inc(v_task_2844_);
lean_dec(v_a_2839_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2869_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v_registeredJobs_2849_; lean_object* v___x_2850_; lean_object* v_baseName_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v_job_2860_; 
v_registeredJobs_2849_ = lean_ctor_get(v___y_2832_, 3);
v___x_2850_ = lean_st_ref_take(v_registeredJobs_2849_);
v_baseName_2851_ = lean_ctor_get(v_pkg_2827_, 1);
lean_inc(v_baseName_2851_);
lean_dec_ref(v_pkg_2827_);
v___x_2852_ = 1;
v___x_2853_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2851_, v___x_2852_);
v___x_2854_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2855_ = lean_string_append(v___x_2853_, v___x_2854_);
v___x_2856_ = l_Lake_Name_eraseHead(v___x_2826_);
v___x_2857_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2856_, v___x_2852_);
v___x_2858_ = lean_string_append(v___x_2855_, v___x_2857_);
lean_dec_ref(v___x_2857_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 2, v___x_2858_);
v_job_2860_ = v___x_2847_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_task_2844_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v_kind_2845_);
lean_ctor_set(v_reuseFailAlloc_2868_, 2, v___x_2858_);
v_job_2860_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
lean_ctor_set_uint8(v_job_2860_, sizeof(void*)*3, v___x_2852_);
lean_inc_ref(v_job_2860_);
v___x_2861_ = l_Lake_Job_toOpaque___redArg(v_job_2860_);
v___x_2862_ = lean_array_push(v___x_2850_, v___x_2861_);
v___x_2863_ = lean_st_ref_set(v_registeredJobs_2849_, v___x_2862_);
v___x_2864_ = l_Lake_Job_renew___redArg(v_job_2860_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2864_);
v___x_2866_ = v___x_2842_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2864_);
lean_ctor_set(v_reuseFailAlloc_2867_, 1, v_a_2840_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
else
{
lean_dec_ref(v_pkg_2827_);
lean_dec(v___x_2826_);
return v___x_2838_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_2872_, lean_object* v___x_2873_, lean_object* v___x_2874_, lean_object* v___x_2875_, lean_object* v_pkg_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(v___x_2872_, v___x_2873_, v___x_2874_, v___x_2875_, v_pkg_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec(v___y_2878_);
return v_res_2884_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___f_2891_; 
v___x_2887_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_2888_ = lean_unsigned_to_nat(0u);
v___x_2889_ = l_Lake_instDataKindBool;
v___x_2890_ = ((lean_object*)(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0));
v___f_2891_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2891_, 0, v___x_2890_);
lean_closure_set(v___f_2891_, 1, v___x_2889_);
lean_closure_set(v___f_2891_, 2, v___x_2888_);
lean_closure_set(v___f_2891_, 3, v___x_2887_);
return v___f_2891_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_2892_; uint8_t v___x_2893_; lean_object* v___x_2894_; lean_object* v___f_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___f_2892_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_2893_ = 1;
v___x_2894_ = l_Lake_instDataKindBool;
v___f_2895_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__1, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1);
v___x_2896_ = l_Lake_Package_keyword;
v___x_2897_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
lean_ctor_set(v___x_2897_, 1, v___f_2895_);
lean_ctor_set(v___x_2897_, 2, v___x_2894_);
lean_ctor_set(v___x_2897_, 3, v___f_2892_);
lean_ctor_set_uint8(v___x_2897_, sizeof(void*)*4, v___x_2893_);
lean_ctor_set_uint8(v___x_2897_, sizeof(void*)*4 + 1, v___x_2893_);
return v___x_2897_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__2, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* v_baseName_2900_, lean_object* v___x_2901_, uint8_t v_success_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_a_2911_; lean_object* v_a_2912_; 
if (v_success_2902_ == 0)
{
lean_object* v_toBuildConfig_2932_; uint8_t v_verbosity_2933_; uint8_t v___x_2934_; uint8_t v___x_2935_; 
v_toBuildConfig_2932_ = lean_ctor_get(v___y_2907_, 0);
v_verbosity_2933_ = lean_ctor_get_uint8(v_toBuildConfig_2932_, sizeof(void*)*2 + 3);
v___x_2934_ = 2;
v___x_2935_ = l_Lake_instDecidableEqVerbosity(v_verbosity_2933_, v___x_2934_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; 
lean_dec(v___x_2901_);
lean_dec(v_baseName_2900_);
v___x_2936_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2911_ = v___x_2936_;
v_a_2912_ = v___y_2908_;
goto v___jp_2910_;
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2937_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2938_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2900_, v___x_2935_);
v___x_2939_ = lean_string_append(v___x_2937_, v___x_2938_);
lean_dec_ref(v___x_2938_);
v___x_2940_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2941_ = lean_string_append(v___x_2939_, v___x_2940_);
v___x_2942_ = l_Lake_Name_eraseHead(v___x_2901_);
v___x_2943_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2942_, v___x_2935_);
v___x_2944_ = lean_string_append(v___x_2941_, v___x_2943_);
lean_dec_ref(v___x_2943_);
v___x_2945_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2946_ = lean_string_append(v___x_2944_, v___x_2945_);
v_a_2911_ = v___x_2946_;
v_a_2912_ = v___y_2908_;
goto v___jp_2910_;
}
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
lean_dec(v___x_2901_);
lean_dec(v_baseName_2900_);
v___x_2947_ = lean_box(0);
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
lean_ctor_set(v___x_2948_, 1, v___y_2908_);
return v___x_2948_;
}
v___jp_2910_:
{
lean_object* v_log_2913_; uint8_t v_action_2914_; uint8_t v_wantsRebuild_2915_; lean_object* v_trace_2916_; lean_object* v_buildTime_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2931_; 
v_log_2913_ = lean_ctor_get(v_a_2912_, 0);
v_action_2914_ = lean_ctor_get_uint8(v_a_2912_, sizeof(void*)*3);
v_wantsRebuild_2915_ = lean_ctor_get_uint8(v_a_2912_, sizeof(void*)*3 + 1);
v_trace_2916_ = lean_ctor_get(v_a_2912_, 1);
v_buildTime_2917_ = lean_ctor_get(v_a_2912_, 2);
v_isSharedCheck_2931_ = !lean_is_exclusive(v_a_2912_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2919_ = v_a_2912_;
v_isShared_2920_ = v_isSharedCheck_2931_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_buildTime_2917_);
lean_inc(v_trace_2916_);
lean_inc(v_log_2913_);
lean_dec(v_a_2912_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2931_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2921_ = ((lean_object*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0));
v___x_2922_ = lean_string_append(v___x_2921_, v_a_2911_);
lean_dec_ref(v_a_2911_);
v___x_2923_ = 3;
v___x_2924_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2924_, 0, v___x_2922_);
lean_ctor_set_uint8(v___x_2924_, sizeof(void*)*1, v___x_2923_);
v___x_2925_ = lean_array_get_size(v_log_2913_);
v___x_2926_ = lean_array_push(v_log_2913_, v___x_2924_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 0, v___x_2926_);
v___x_2928_ = v___x_2919_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2926_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_trace_2916_);
lean_ctor_set(v_reuseFailAlloc_2930_, 2, v_buildTime_2917_);
lean_ctor_set_uint8(v_reuseFailAlloc_2930_, sizeof(void*)*3, v_action_2914_);
lean_ctor_set_uint8(v_reuseFailAlloc_2930_, sizeof(void*)*3 + 1, v_wantsRebuild_2915_);
v___x_2928_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2925_);
lean_ctor_set(v___x_2929_, 1, v___x_2928_);
return v___x_2929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object* v_baseName_2949_, lean_object* v___x_2950_, lean_object* v_success_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
uint8_t v_success_boxed_2959_; lean_object* v_res_2960_; 
v_success_boxed_2959_ = lean_unbox(v_success_2951_);
v_res_2960_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(v_baseName_2949_, v___x_2950_, v_success_boxed_2959_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* v___x_2961_, lean_object* v___x_2962_, lean_object* v___x_2963_, lean_object* v_pkg_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_baseName_2972_; lean_object* v_keyName_2973_; lean_object* v___f_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___f_2978_; lean_object* v___x_2979_; 
v_baseName_2972_ = lean_ctor_get(v_pkg_2964_, 1);
lean_inc_n(v_baseName_2972_, 2);
v_keyName_2973_ = lean_ctor_get(v_pkg_2964_, 2);
lean_inc(v___x_2961_);
v___f_2974_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2974_, 0, v_baseName_2972_);
lean_closure_set(v___f_2974_, 1, v___x_2961_);
lean_inc(v_keyName_2973_);
v___x_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2975_, 0, v_keyName_2973_);
v___x_2976_ = l_Lake_Package_keyword;
v___x_2977_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2975_);
lean_ctor_set(v___x_2977_, 1, v___x_2976_);
lean_ctor_set(v___x_2977_, 2, v_pkg_2964_);
lean_ctor_set(v___x_2977_, 3, v___x_2961_);
lean_inc(v___x_2962_);
v___f_2978_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2978_, 0, v___x_2977_);
lean_closure_set(v___f_2978_, 1, v___x_2962_);
lean_closure_set(v___f_2978_, 2, v___f_2974_);
v___x_2979_ = l_Lake_ensureJob___redArg(v___x_2962_, v___f_2978_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3012_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
v_a_2981_ = lean_ctor_get(v___x_2979_, 1);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2983_ = v___x_2979_;
v_isShared_2984_ = v_isSharedCheck_3012_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_inc(v_a_2980_);
lean_dec(v___x_2979_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3012_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v_task_2985_; lean_object* v_kind_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3010_; 
v_task_2985_ = lean_ctor_get(v_a_2980_, 0);
v_kind_2986_ = lean_ctor_get(v_a_2980_, 1);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_a_2980_);
if (v_isSharedCheck_3010_ == 0)
{
lean_object* v_unused_3011_; 
v_unused_3011_ = lean_ctor_get(v_a_2980_, 2);
lean_dec(v_unused_3011_);
v___x_2988_ = v_a_2980_;
v_isShared_2989_ = v_isSharedCheck_3010_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_kind_2986_);
lean_inc(v_task_2985_);
lean_dec(v_a_2980_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3010_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v_registeredJobs_2990_; lean_object* v___x_2991_; uint8_t v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; lean_object* v_job_3001_; 
v_registeredJobs_2990_ = lean_ctor_get(v___y_2969_, 3);
v___x_2991_ = lean_st_ref_take(v_registeredJobs_2990_);
v___x_2992_ = 1;
v___x_2993_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2972_, v___x_2992_);
v___x_2994_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2995_ = lean_string_append(v___x_2993_, v___x_2994_);
v___x_2996_ = l_Lake_Name_eraseHead(v___x_2963_);
v___x_2997_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2996_, v___x_2992_);
v___x_2998_ = lean_string_append(v___x_2995_, v___x_2997_);
lean_dec_ref(v___x_2997_);
v___x_2999_ = 0;
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 2, v___x_2998_);
v_job_3001_ = v___x_2988_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_task_2985_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v_kind_2986_);
lean_ctor_set(v_reuseFailAlloc_3009_, 2, v___x_2998_);
v_job_3001_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
lean_ctor_set_uint8(v_job_3001_, sizeof(void*)*3, v___x_2999_);
lean_inc_ref(v_job_3001_);
v___x_3002_ = l_Lake_Job_toOpaque___redArg(v_job_3001_);
v___x_3003_ = lean_array_push(v___x_2991_, v___x_3002_);
v___x_3004_ = lean_st_ref_set(v_registeredJobs_2990_, v___x_3003_);
v___x_3005_ = l_Lake_Job_renew___redArg(v_job_3001_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 0, v___x_3005_);
v___x_3007_ = v___x_2983_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_a_2981_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
else
{
lean_dec(v_baseName_2972_);
lean_dec(v___x_2963_);
return v___x_2979_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_3013_, lean_object* v___x_3014_, lean_object* v___x_3015_, lean_object* v_pkg_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(v___x_3013_, v___x_3014_, v___x_3015_, v_pkg_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec(v___y_3018_);
return v_res_3024_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___f_3028_; 
v___x_3025_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3026_ = l_Lake_instDataKindUnit;
v___x_3027_ = l_Lake_Package_optGitHubReleaseFacet;
v___f_3028_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3028_, 0, v___x_3027_);
lean_closure_set(v___f_3028_, 1, v___x_3026_);
lean_closure_set(v___f_3028_, 2, v___x_3025_);
return v___f_3028_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3029_; uint8_t v___x_3030_; lean_object* v___x_3031_; lean_object* v___f_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___f_3029_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3030_ = 1;
v___x_3031_ = l_Lake_instDataKindUnit;
v___f_3032_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__0, &l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0);
v___x_3033_ = l_Lake_Package_keyword;
v___x_3034_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
lean_ctor_set(v___x_3034_, 1, v___f_3032_);
lean_ctor_set(v___x_3034_, 2, v___x_3031_);
lean_ctor_set(v___x_3034_, 3, v___f_3029_);
lean_ctor_set_uint8(v___x_3034_, sizeof(void*)*4, v___x_3030_);
lean_ctor_set_uint8(v___x_3034_, sizeof(void*)*4 + 1, v___x_3030_);
return v___x_3034_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__1, &l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* v_build_3036_, uint8_t v_x_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_log_3045_; uint8_t v_action_3046_; uint8_t v_wantsRebuild_3047_; lean_object* v_buildTime_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3057_; 
v_log_3045_ = lean_ctor_get(v___y_3043_, 0);
v_action_3046_ = lean_ctor_get_uint8(v___y_3043_, sizeof(void*)*3);
v_wantsRebuild_3047_ = lean_ctor_get_uint8(v___y_3043_, sizeof(void*)*3 + 1);
v_buildTime_3048_ = lean_ctor_get(v___y_3043_, 2);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___y_3043_);
if (v_isSharedCheck_3057_ == 0)
{
lean_object* v_unused_3058_; 
v_unused_3058_ = lean_ctor_get(v___y_3043_, 1);
lean_dec(v_unused_3058_);
v___x_3050_ = v___y_3043_;
v_isShared_3051_ = v_isSharedCheck_3057_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_buildTime_3048_);
lean_inc(v_log_3045_);
lean_dec(v___y_3043_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3057_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3052_; lean_object* v___x_3054_; 
v___x_3052_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 1, v___x_3052_);
v___x_3054_ = v___x_3050_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_log_3045_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v___x_3052_);
lean_ctor_set(v_reuseFailAlloc_3056_, 2, v_buildTime_3048_);
lean_ctor_set_uint8(v_reuseFailAlloc_3056_, sizeof(void*)*3, v_action_3046_);
lean_ctor_set_uint8(v_reuseFailAlloc_3056_, sizeof(void*)*3 + 1, v_wantsRebuild_3047_);
v___x_3054_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3055_; 
lean_inc_ref(v___y_3042_);
lean_inc(v___y_3041_);
lean_inc(v___y_3040_);
lean_inc(v___y_3039_);
v___x_3055_ = lean_apply_7(v_build_3036_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___x_3054_, lean_box(0));
return v___x_3055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* v_build_3059_, lean_object* v_x_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
uint8_t v_x_1923__boxed_3068_; lean_object* v_res_3069_; 
v_x_1923__boxed_3068_ = lean_unbox(v_x_3060_);
v_res_3069_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(v_build_3059_, v_x_1923__boxed_3068_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec(v___y_3062_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* v_self_3070_, lean_object* v_build_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v_wsIdx_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v_wsIdx_3079_ = lean_ctor_get(v_self_3070_, 0);
v___x_3080_ = lean_unsigned_to_nat(0u);
v___x_3081_ = lean_nat_dec_eq(v_wsIdx_3079_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; 
lean_inc_ref(v_a_3072_);
v___x_3082_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3070_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3095_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
v_a_3084_ = lean_ctor_get(v___x_3082_, 1);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3086_ = v___x_3082_;
v_isShared_3087_ = v_isSharedCheck_3095_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_inc(v_a_3083_);
lean_dec(v___x_3082_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3095_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___f_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___f_3088_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3088_, 0, v_build_3071_);
v___x_3089_ = lean_box(0);
v___x_3090_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3);
v___x_3091_ = l_Lake_Job_bindM___redArg(v___x_3089_, v_a_3083_, v___f_3088_, v___x_3080_, v___x_3081_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v___x_3090_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v___x_3091_);
v___x_3093_ = v___x_3086_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v_a_3084_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec_ref(v_a_3072_);
lean_dec_ref(v_build_3071_);
v_a_3096_ = lean_ctor_get(v___x_3082_, 0);
v_a_3097_ = lean_ctor_get(v___x_3082_, 1);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3082_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_inc(v_a_3096_);
lean_dec(v___x_3082_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3096_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
else
{
uint8_t v___x_3105_; uint8_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_dec_ref(v_self_3070_);
v___x_3105_ = 0;
v___x_3106_ = 0;
v___x_3107_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3);
v___x_3108_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3108_, 0, v_a_3077_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
lean_ctor_set(v___x_3108_, 2, v___x_3080_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*3, v___x_3105_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*3 + 1, v___x_3106_);
lean_inc_ref(v_a_3076_);
lean_inc(v_a_3075_);
lean_inc(v_a_3074_);
lean_inc(v_a_3073_);
v___x_3109_ = lean_apply_7(v_build_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v___x_3108_, lean_box(0));
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3119_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 1);
v_a_3111_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3113_ = v___x_3109_;
v_isShared_3114_ = v_isSharedCheck_3119_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3110_);
lean_inc(v_a_3111_);
lean_dec(v___x_3109_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3119_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v_log_3115_; lean_object* v___x_3117_; 
v_log_3115_ = lean_ctor_get(v_a_3110_, 0);
lean_inc_ref(v_log_3115_);
lean_dec(v_a_3110_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 1, v_log_3115_);
v___x_3117_ = v___x_3113_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3111_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v_log_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3129_; 
v_a_3120_ = lean_ctor_get(v___x_3109_, 1);
v_a_3121_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3123_ = v___x_3109_;
v_isShared_3124_ = v_isSharedCheck_3129_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3120_);
lean_inc(v_a_3121_);
lean_dec(v___x_3109_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3129_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v_log_3125_; lean_object* v___x_3127_; 
v_log_3125_ = lean_ctor_get(v_a_3120_, 0);
lean_inc_ref(v_log_3125_);
lean_dec(v_a_3120_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 1, v_log_3125_);
v___x_3127_ = v___x_3123_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3121_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_log_3125_);
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
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___boxed(lean_object* v_self_3130_, lean_object* v_build_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3130_, v_build_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec(v_a_3135_);
lean_dec(v_a_3134_);
lean_dec(v_a_3133_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* v_00_u03b1_3140_, lean_object* v_self_3141_, lean_object* v_build_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3141_, v_build_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___boxed(lean_object* v_00_u03b1_3151_, lean_object* v_self_3152_, lean_object* v_build_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lake_Package_afterBuildCacheAsync(v_00_u03b1_3151_, v_self_3152_, v_build_3153_, v_a_3154_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec(v_a_3156_);
lean_dec(v_a_3155_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* v_build_3162_, uint8_t v_x_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_log_3171_; uint8_t v_action_3172_; uint8_t v_wantsRebuild_3173_; lean_object* v_buildTime_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3183_; 
v_log_3171_ = lean_ctor_get(v___y_3169_, 0);
v_action_3172_ = lean_ctor_get_uint8(v___y_3169_, sizeof(void*)*3);
v_wantsRebuild_3173_ = lean_ctor_get_uint8(v___y_3169_, sizeof(void*)*3 + 1);
v_buildTime_3174_ = lean_ctor_get(v___y_3169_, 2);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___y_3169_);
if (v_isSharedCheck_3183_ == 0)
{
lean_object* v_unused_3184_; 
v_unused_3184_ = lean_ctor_get(v___y_3169_, 1);
lean_dec(v_unused_3184_);
v___x_3176_ = v___y_3169_;
v_isShared_3177_ = v_isSharedCheck_3183_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_buildTime_3174_);
lean_inc(v_log_3171_);
lean_dec(v___y_3169_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3183_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3178_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3);
if (v_isShared_3177_ == 0)
{
lean_ctor_set(v___x_3176_, 1, v___x_3178_);
v___x_3180_ = v___x_3176_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_log_3171_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3182_, 2, v_buildTime_3174_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, sizeof(void*)*3, v_action_3172_);
lean_ctor_set_uint8(v_reuseFailAlloc_3182_, sizeof(void*)*3 + 1, v_wantsRebuild_3173_);
v___x_3180_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3181_; 
lean_inc_ref(v___y_3168_);
lean_inc(v___y_3167_);
lean_inc(v___y_3166_);
lean_inc(v___y_3165_);
v___x_3181_ = lean_apply_7(v_build_3162_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___x_3180_, lean_box(0));
return v___x_3181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* v_build_3185_, lean_object* v_x_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
uint8_t v_x_1946__boxed_3194_; lean_object* v_res_3195_; 
v_x_1946__boxed_3194_ = lean_unbox(v_x_3186_);
v_res_3195_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(v_build_3185_, v_x_1946__boxed_3194_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec(v___y_3188_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* v_self_3196_, lean_object* v_build_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v_wsIdx_3205_; lean_object* v___x_3206_; uint8_t v___x_3207_; 
v_wsIdx_3205_ = lean_ctor_get(v_self_3196_, 0);
v___x_3206_ = lean_unsigned_to_nat(0u);
v___x_3207_ = lean_nat_dec_eq(v_wsIdx_3205_, v___x_3206_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; 
lean_inc_ref(v_a_3198_);
v___x_3208_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3196_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3221_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_a_3210_ = lean_ctor_get(v___x_3208_, 1);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3212_ = v___x_3208_;
v_isShared_3213_ = v_isSharedCheck_3221_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3221_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___f_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___f_3214_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3214_, 0, v_build_3197_);
v___x_3215_ = lean_box(0);
v___x_3216_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__3);
v___x_3217_ = l_Lake_Job_mapM___redArg(v___x_3215_, v_a_3209_, v___f_3214_, v___x_3206_, v___x_3207_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v___x_3216_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v___x_3217_);
v___x_3219_ = v___x_3212_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_a_3210_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
else
{
lean_object* v_a_3222_; lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3230_; 
lean_dec_ref(v_a_3198_);
lean_dec_ref(v_build_3197_);
v_a_3222_ = lean_ctor_get(v___x_3208_, 0);
v_a_3223_ = lean_ctor_get(v___x_3208_, 1);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3225_ = v___x_3208_;
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_inc(v_a_3222_);
lean_dec(v___x_3208_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3230_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3228_; 
if (v_isShared_3226_ == 0)
{
v___x_3228_ = v___x_3225_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3222_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_a_3223_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
else
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
lean_dec_ref(v_self_3196_);
v___x_3231_ = lean_box(0);
v___x_3232_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___lam__0___closed__1));
v___x_3233_ = l_Lake_Job_async___redArg(v___x_3231_, v_build_3197_, v___x_3206_, v___x_3232_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_);
v___x_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
lean_ctor_set(v___x_3234_, 1, v_a_3203_);
return v___x_3234_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___boxed(lean_object* v_self_3235_, lean_object* v_build_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3235_, v_build_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_);
lean_dec_ref(v_a_3241_);
lean_dec(v_a_3240_);
lean_dec(v_a_3239_);
lean_dec(v_a_3238_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* v_00_u03b1_3245_, lean_object* v_self_3246_, lean_object* v_build_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3246_, v_build_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___boxed(lean_object* v_00_u03b1_3256_, lean_object* v_self_3257_, lean_object* v_build_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Lake_Package_afterBuildCacheSync(v_00_u03b1_3256_, v_self_3257_, v_build_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_);
lean_dec_ref(v_a_3263_);
lean_dec(v_a_3262_);
lean_dec(v_a_3261_);
lean_dec(v_a_3260_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(lean_object* v_k_3267_, lean_object* v_v_3268_, lean_object* v_t_3269_){
_start:
{
if (lean_obj_tag(v_t_3269_) == 0)
{
lean_object* v_size_3270_; lean_object* v_k_3271_; lean_object* v_v_3272_; lean_object* v_l_3273_; lean_object* v_r_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3554_; 
v_size_3270_ = lean_ctor_get(v_t_3269_, 0);
v_k_3271_ = lean_ctor_get(v_t_3269_, 1);
v_v_3272_ = lean_ctor_get(v_t_3269_, 2);
v_l_3273_ = lean_ctor_get(v_t_3269_, 3);
v_r_3274_ = lean_ctor_get(v_t_3269_, 4);
v_isSharedCheck_3554_ = !lean_is_exclusive(v_t_3269_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3276_ = v_t_3269_;
v_isShared_3277_ = v_isSharedCheck_3554_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_r_3274_);
lean_inc(v_l_3273_);
lean_inc(v_v_3272_);
lean_inc(v_k_3271_);
lean_inc(v_size_3270_);
lean_dec(v_t_3269_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3554_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
uint8_t v___x_3278_; 
v___x_3278_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3267_, v_k_3271_);
switch(v___x_3278_)
{
case 0:
{
lean_object* v_impl_3279_; lean_object* v___x_3280_; 
lean_dec(v_size_3270_);
v_impl_3279_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3267_, v_v_3268_, v_l_3273_);
v___x_3280_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3274_) == 0)
{
lean_object* v_size_3281_; lean_object* v_size_3282_; lean_object* v_k_3283_; lean_object* v_v_3284_; lean_object* v_l_3285_; lean_object* v_r_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; uint8_t v___x_3289_; 
v_size_3281_ = lean_ctor_get(v_r_3274_, 0);
v_size_3282_ = lean_ctor_get(v_impl_3279_, 0);
lean_inc(v_size_3282_);
v_k_3283_ = lean_ctor_get(v_impl_3279_, 1);
lean_inc(v_k_3283_);
v_v_3284_ = lean_ctor_get(v_impl_3279_, 2);
lean_inc(v_v_3284_);
v_l_3285_ = lean_ctor_get(v_impl_3279_, 3);
lean_inc(v_l_3285_);
v_r_3286_ = lean_ctor_get(v_impl_3279_, 4);
lean_inc(v_r_3286_);
v___x_3287_ = lean_unsigned_to_nat(3u);
v___x_3288_ = lean_nat_mul(v___x_3287_, v_size_3281_);
v___x_3289_ = lean_nat_dec_lt(v___x_3288_, v_size_3282_);
lean_dec(v___x_3288_);
if (v___x_3289_ == 0)
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3293_; 
lean_dec(v_r_3286_);
lean_dec(v_l_3285_);
lean_dec(v_v_3284_);
lean_dec(v_k_3283_);
v___x_3290_ = lean_nat_add(v___x_3280_, v_size_3282_);
lean_dec(v_size_3282_);
v___x_3291_ = lean_nat_add(v___x_3290_, v_size_3281_);
lean_dec(v___x_3290_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 3, v_impl_3279_);
lean_ctor_set(v___x_3276_, 0, v___x_3291_);
v___x_3293_ = v___x_3276_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_k_3271_);
lean_ctor_set(v_reuseFailAlloc_3294_, 2, v_v_3272_);
lean_ctor_set(v_reuseFailAlloc_3294_, 3, v_impl_3279_);
lean_ctor_set(v_reuseFailAlloc_3294_, 4, v_r_3274_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
else
{
lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3360_; 
v_isSharedCheck_3360_ = !lean_is_exclusive(v_impl_3279_);
if (v_isSharedCheck_3360_ == 0)
{
lean_object* v_unused_3361_; lean_object* v_unused_3362_; lean_object* v_unused_3363_; lean_object* v_unused_3364_; lean_object* v_unused_3365_; 
v_unused_3361_ = lean_ctor_get(v_impl_3279_, 4);
lean_dec(v_unused_3361_);
v_unused_3362_ = lean_ctor_get(v_impl_3279_, 3);
lean_dec(v_unused_3362_);
v_unused_3363_ = lean_ctor_get(v_impl_3279_, 2);
lean_dec(v_unused_3363_);
v_unused_3364_ = lean_ctor_get(v_impl_3279_, 1);
lean_dec(v_unused_3364_);
v_unused_3365_ = lean_ctor_get(v_impl_3279_, 0);
lean_dec(v_unused_3365_);
v___x_3296_ = v_impl_3279_;
v_isShared_3297_ = v_isSharedCheck_3360_;
goto v_resetjp_3295_;
}
else
{
lean_dec(v_impl_3279_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3360_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v_size_3298_; lean_object* v_size_3299_; lean_object* v_k_3300_; lean_object* v_v_3301_; lean_object* v_l_3302_; lean_object* v_r_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; 
v_size_3298_ = lean_ctor_get(v_l_3285_, 0);
v_size_3299_ = lean_ctor_get(v_r_3286_, 0);
v_k_3300_ = lean_ctor_get(v_r_3286_, 1);
v_v_3301_ = lean_ctor_get(v_r_3286_, 2);
v_l_3302_ = lean_ctor_get(v_r_3286_, 3);
v_r_3303_ = lean_ctor_get(v_r_3286_, 4);
v___x_3304_ = lean_unsigned_to_nat(2u);
v___x_3305_ = lean_nat_mul(v___x_3304_, v_size_3298_);
v___x_3306_ = lean_nat_dec_lt(v_size_3299_, v___x_3305_);
lean_dec(v___x_3305_);
if (v___x_3306_ == 0)
{
lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3335_; 
lean_inc(v_r_3303_);
lean_inc(v_l_3302_);
lean_inc(v_v_3301_);
lean_inc(v_k_3300_);
v_isSharedCheck_3335_ = !lean_is_exclusive(v_r_3286_);
if (v_isSharedCheck_3335_ == 0)
{
lean_object* v_unused_3336_; lean_object* v_unused_3337_; lean_object* v_unused_3338_; lean_object* v_unused_3339_; lean_object* v_unused_3340_; 
v_unused_3336_ = lean_ctor_get(v_r_3286_, 4);
lean_dec(v_unused_3336_);
v_unused_3337_ = lean_ctor_get(v_r_3286_, 3);
lean_dec(v_unused_3337_);
v_unused_3338_ = lean_ctor_get(v_r_3286_, 2);
lean_dec(v_unused_3338_);
v_unused_3339_ = lean_ctor_get(v_r_3286_, 1);
lean_dec(v_unused_3339_);
v_unused_3340_ = lean_ctor_get(v_r_3286_, 0);
lean_dec(v_unused_3340_);
v___x_3308_ = v_r_3286_;
v_isShared_3309_ = v_isSharedCheck_3335_;
goto v_resetjp_3307_;
}
else
{
lean_dec(v_r_3286_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3335_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___x_3323_; lean_object* v___y_3325_; 
v___x_3310_ = lean_nat_add(v___x_3280_, v_size_3282_);
lean_dec(v_size_3282_);
v___x_3311_ = lean_nat_add(v___x_3310_, v_size_3281_);
lean_dec(v___x_3310_);
v___x_3323_ = lean_nat_add(v___x_3280_, v_size_3298_);
if (lean_obj_tag(v_l_3302_) == 0)
{
lean_object* v_size_3333_; 
v_size_3333_ = lean_ctor_get(v_l_3302_, 0);
lean_inc(v_size_3333_);
v___y_3325_ = v_size_3333_;
goto v___jp_3324_;
}
else
{
lean_object* v___x_3334_; 
v___x_3334_ = lean_unsigned_to_nat(0u);
v___y_3325_ = v___x_3334_;
goto v___jp_3324_;
}
v___jp_3312_:
{
lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3316_ = lean_nat_add(v___y_3313_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec(v___y_3313_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 4, v_r_3274_);
lean_ctor_set(v___x_3308_, 3, v_r_3303_);
lean_ctor_set(v___x_3308_, 2, v_v_3272_);
lean_ctor_set(v___x_3308_, 1, v_k_3271_);
lean_ctor_set(v___x_3308_, 0, v___x_3316_);
v___x_3318_ = v___x_3308_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3322_, 1, v_k_3271_);
lean_ctor_set(v_reuseFailAlloc_3322_, 2, v_v_3272_);
lean_ctor_set(v_reuseFailAlloc_3322_, 3, v_r_3303_);
lean_ctor_set(v_reuseFailAlloc_3322_, 4, v_r_3274_);
v___x_3318_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
lean_object* v___x_3320_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v___x_3318_);
lean_ctor_set(v___x_3296_, 3, v___y_3314_);
lean_ctor_set(v___x_3296_, 2, v_v_3301_);
lean_ctor_set(v___x_3296_, 1, v_k_3300_);
lean_ctor_set(v___x_3296_, 0, v___x_3311_);
v___x_3320_ = v___x_3296_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v_k_3300_);
lean_ctor_set(v_reuseFailAlloc_3321_, 2, v_v_3301_);
lean_ctor_set(v_reuseFailAlloc_3321_, 3, v___y_3314_);
lean_ctor_set(v_reuseFailAlloc_3321_, 4, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
v___jp_3324_:
{
lean_object* v___x_3326_; lean_object* v___x_3328_; 
v___x_3326_ = lean_nat_add(v___x_3323_, v___y_3325_);
lean_dec(v___y_3325_);
lean_dec(v___x_3323_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 4, v_l_3302_);
lean_ctor_set(v___x_3276_, 3, v_l_3285_);
lean_ctor_set(v___x_3276_, 2, v_v_3284_);
lean_ctor_set(v___x_3276_, 1, v_k_3283_);
lean_ctor_set(v___x_3276_, 0, v___x_3326_);
v___x_3328_ = v___x_3276_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3332_, 1, v_k_3283_);
lean_ctor_set(v_reuseFailAlloc_3332_, 2, v_v_3284_);
lean_ctor_set(v_reuseFailAlloc_3332_, 3, v_l_3285_);
lean_ctor_set(v_reuseFailAlloc_3332_, 4, v_l_3302_);
v___x_3328_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
lean_object* v___x_3329_; 
v___x_3329_ = lean_nat_add(v___x_3280_, v_size_3281_);
if (lean_obj_tag(v_r_3303_) == 0)
{
lean_object* v_size_3330_; 
v_size_3330_ = lean_ctor_get(v_r_3303_, 0);
lean_inc(v_size_3330_);
v___y_3313_ = v___x_3329_;
v___y_3314_ = v___x_3328_;
v___y_3315_ = v_size_3330_;
goto v___jp_3312_;
}
else
{
lean_object* v___x_3331_; 
v___x_3331_ = lean_unsigned_to_nat(0u);
v___y_3313_ = v___x_3329_;
v___y_3314_ = v___x_3328_;
v___y_3315_ = v___x_3331_;
goto v___jp_3312_;
}
}
}
}
}
else
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3346_; 
lean_del_object(v___x_3276_);
v___x_3341_ = lean_nat_add(v___x_3280_, v_size_3282_);
lean_dec(v_size_3282_);
v___x_3342_ = lean_nat_add(v___x_3341_, v_size_3281_);
lean_dec(v___x_3341_);
v___x_3343_ = lean_nat_add(v___x_3280_, v_size_3281_);
v___x_3344_ = lean_nat_add(v___x_3343_, v_size_3299_);
lean_dec(v___x_3343_);
lean_inc_ref(v_r_3274_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 4, v_r_3274_);
lean_ctor_set(v___x_3296_, 3, v_r_3286_);
lean_ctor_set(v___x_3296_, 2, v_v_3272_);
lean_ctor_set(v___x_3296_, 1, v_k_3271_);
lean_ctor_set(v___x_3296_, 0, v___x_3344_);
v___x_3346_ = v___x_3296_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3344_);
lean_ctor_set(v_reuseFailAlloc_3359_, 1, v_k_3271_);
lean_ctor_set(v_reuseFailAlloc_3359_, 2, v_v_3272_);
lean_ctor_set(v_reuseFailAlloc_3359_, 3, v_r_3286_);
lean_ctor_set(v_reuseFailAlloc_3359_, 4, v_r_3274_);
v___x_3346_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
v_isSharedCheck_3353_ = !lean_is_exclusive(v_r_3274_);
if (v_isSharedCheck_3353_ == 0)
{
lean_object* v_unused_3354_; lean_object* v_unused_3355_; lean_object* v_unused_3356_; lean_object* v_unused_3357_; lean_object* v_unused_3358_; 
v_unused_3354_ = lean_ctor_get(v_r_3274_, 4);
lean_dec(v_unused_3354_);
v_unused_3355_ = lean_ctor_get(v_r_3274_, 3);
lean_dec(v_unused_3355_);
v_unused_3356_ = lean_ctor_get(v_r_3274_, 2);
lean_dec(v_unused_3356_);
v_unused_3357_ = lean_ctor_get(v_r_3274_, 1);
lean_dec(v_unused_3357_);
v_unused_3358_ = lean_ctor_get(v_r_3274_, 0);
lean_dec(v_unused_3358_);
v___x_3348_ = v_r_3274_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_dec(v_r_3274_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 4, v___x_3346_);
lean_ctor_set(v___x_3348_, 3, v_l_3285_);
lean_ctor_set(v___x_3348_, 2, v_v_3284_);
lean_ctor_set(v___x_3348_, 1, v_k_3283_);
lean_ctor_set(v___x_3348_, 0, v___x_3342_);
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_k_3283_);
lean_ctor_set(v_reuseFailAlloc_3352_, 2, v_v_3284_);
lean_ctor_set(v_reuseFailAlloc_3352_, 3, v_l_3285_);
lean_ctor_set(v_reuseFailAlloc_3352_, 4, v___x_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3366_; 
v_l_3366_ = lean_ctor_get(v_impl_3279_, 3);
lean_inc(v_l_3366_);
if (lean_obj_tag(v_l_3366_) == 0)
{
lean_object* v_r_3367_; lean_object* v_k_3368_; lean_object* v_v_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3380_; 
v_r_3367_ = lean_ctor_get(v_impl_3279_, 4);
v_k_3368_ = lean_ctor_get(v_impl_3279_, 1);
v_v_3369_ = lean_ctor_get(v_impl_3279_, 2);
v_isSharedCheck_3380_ = !lean_is_exclusive(v_impl_3279_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; lean_object* v_unused_3382_; 
v_unused_3381_ = lean_ctor_get(v_impl_3279_, 3);
lean_dec(v_unused_3381_);
v_unused_3382_ = lean_ctor_get(v_impl_3279_, 0);
lean_dec(v_unused_3382_);
v___x_3371_ = v_impl_3279_;
v_isShared_3372_ = v_isSharedCheck_3380_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_r_3367_);
lean_inc(v_v_3369_);
lean_inc(v_k_3368_);
lean_dec(v_impl_3279_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3380_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3373_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3367_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 3, v_r_3367_);
lean_ctor_set(v___x_3371_, 2, v_v_3272_);
lean_ctor_set(v___x_3371_, 1, v_k_3271_);
lean_ctor_set(v___x_3371_, 0, v___x_3280_);
v___x_3375_ = v___x_3371_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_k_3271_);
lean_ctor_set(v_reuseFailAlloc_3379_, 2, v_v_3272_);
lean_ctor_set(v_reuseFailAlloc_3379_, 3, v_r_3367_);
lean_ctor_set(v_reuseFailAlloc_3379_, 4, v_r_3367_);
v___x_3375_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 4, v___x_3375_);
lean_ctor_set(v___x_3276_, 3, v_l_3366_);
lean_ctor_set(v___x_3276_, 2, v_v_3369_);
lean_ctor_set(v___x_3276_, 1, v_k_3368_);
lean_ctor_set(v___x_3276_, 0, v___x_3373_);
v___x_3377_ = v___x_3276_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3373_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v_k_3368_);
lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_v_3369_);
lean_ctor_set(v_reuseFailAlloc_3378_, 3, v_l_3366_);
lean_ctor_set(v_reuseFailAlloc_3378_, 4, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
else
{
lean_object* v_r_3383_; 
v_r_3383_ = lean_ctor_get(v_impl_3279_, 4);
lean_inc(v_r_3383_);
if (lean_obj_tag(v_r_3383_) == 0)
{
lean_object* v_k_3384_; lean_object* v_v_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3408_; 
v_k_3384_ = lean_ctor_get(v_impl_3279_, 1);
v_v_3385_ = lean_ctor_get(v_impl_3279_, 2);
v_isSharedCheck_3408_ = !lean_is_exclusive(v_impl_3279_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; lean_object* v_unused_3410_; lean_object* v_unused_3411_; 
v_unused_3409_ = lean_ctor_get(v_impl_3279_, 4);
lean_dec(v_unused_3409_);
v_unused_3410_ = lean_ctor_get(v_impl_3279_, 3);
lean_dec(v_unused_3410_);
v_unused_3411_ = lean_ctor_get(v_impl_3279_, 0);
lean_dec(v_unused_3411_);
v___x_3387_ = v_impl_3279_;
v_isShared_3388_ = v_isSharedCheck_3408_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_v_3385_);
lean_inc(v_k_3384_);
lean_dec(v_impl_3279_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3408_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v_k_3389_; lean_object* v_v_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3404_; 
v_k_3389_ = lean_ctor_get(v_r_3383_, 1);
v_v_3390_ = lean_ctor_get(v_r_3383_, 2);
v_isSharedCheck_3404_ = !lean_is_exclusive(v_r_3383_);
if (v_isSharedCheck_3404_ == 0)
{
lean_object* v_unused_3405_; lean_object* v_unused_3406_; lean_object* v_unused_3407_; 
v_unused_3405_ = lean_ctor_get(v_r_3383_, 4);
lean_dec(v_unused_3405_);
v_unused_3406_ = lean_ctor_get(v_r_3383_, 3);
lean_dec(v_unused_3406_);
v_unused_3407_ = lean_ctor_get(v_r_3383_, 0);
lean_dec(v_unused_3407_);
v___x_3392_ = v_r_3383_;
v_isShared_3393_ = v_isSharedCheck_3404_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_v_3390_);
lean_inc(v_k_3389_);
lean_dec(v_r_3383_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3404_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3394_; lean_object* v___x_3396_; 
v___x_3394_ = lean_unsigned_to_nat(3u);
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 4, v_l_3366_);
lean_ctor_set(v___x_3392_, 3, v_l_3366_);
lean_ctor_set(v___x_3392_, 2, v_v_3385_);
lean_ctor_set(v___x_3392_, 1, v_k_3384_);
lean_ctor_set(v___x_3392_, 0, v___x_3280_);
v___x_3396_ = v___x_3392_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3403_, 1, v_k_3384_);
lean_ctor_set(v_reuseFailAlloc_3403_, 2, v_v_3385_);
lean_ctor_set(v_reuseFailAlloc_3403_, 3, v_l_3366_);
lean_ctor_set(v_reuseFailAlloc_3403_, 4, v_l_3366_);
v___x_3396_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
lean_object* v___x_3398_; 
if (v_isShared_3388_ == 0)
{
lean_ctor_set(v___x_3387_, 4, v_l_3366_);
lean_ctor_set(v___x_3387_, 2, v_v_3272_);
lean_ctor_set(v___x_3387_, 1, v_k_3271_);
lean_ctor_set(v___x_3387_, 0, v___x_3280_);
v___x_3398_ = v___x_3387_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3402_, 1, v_k_3271_);
lean_ctor_set(v_reuseFailAlloc_3402_, 2, v_v_3272_);
lean_ctor_set(v_reuseFailAlloc_3402_, 3, v_l_3366_);
lean_ctor_set(v_reuseFailAlloc_3402_, 4, v_l_3366_);
v___x_3398_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3400_; 
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 4, v___x_3398_);
lean_ctor_set(v___x_3276_, 3, v___x_3396_);
lean_ctor_set(v___x_3276_, 2, v_v_3390_);
lean_ctor_set(v___x_3276_, 1, v_k_3389_);
lean_ctor_set(v___x_3276_, 0, v___x_3394_);
v___x_3400_ = v___x_3276_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v___x_3394_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v_k_3389_);
lean_ctor_set(v_reuseFailAlloc_3401_, 2, v_v_3390_);
lean_ctor_set(v_reuseFailAlloc_3401_, 3, v___x_3396_);
lean_ctor_set(v_reuseFailAlloc_3401_, 4, v___x_3398_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
}
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3414_; 
v___x_3412_ = lean_unsigned_to_nat(2u);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 4, v_r_3383_);
lean_ctor_set(v___x_3276_, 3, v_impl_3279_);
lean_ctor_set(v___x_3276_, 0, v___x_3412_);
v___x_3414_ = v___x_3276_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3412_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_k_3271_);
lean_ctor_set(v_reuseFailAlloc_3415_, 2, v_v_3272_);
lean_ctor_set(v_reuseFailAlloc_3415_, 3, v_impl_3279_);
lean_ctor_set(v_reuseFailAlloc_3415_, 4, v_r_3383_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3417_; 
lean_dec(v_v_3272_);
lean_dec(v_k_3271_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 2, v_v_3268_);
lean_ctor_set(v___x_3276_, 1, v_k_3267_);
v___x_3417_ = v___x_3276_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_size_3270_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v_k_3267_);
lean_ctor_set(v_reuseFailAlloc_3418_, 2, v_v_3268_);
lean_ctor_set(v_reuseFailAlloc_3418_, 3, v_l_3273_);
lean_ctor_set(v_reuseFailAlloc_3418_, 4, v_r_3274_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
default: 
{
lean_object* v_impl_3419_; lean_object* v___x_3420_; 
lean_dec(v_size_3270_);
v_impl_3419_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3267_, v_v_3268_, v_r_3274_);
v___x_3420_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3273_) == 0)
{
lean_object* v_size_3421_; lean_object* v_size_3422_; lean_object* v_k_3423_; lean_object* v_v_3424_; lean_object* v_l_3425_; lean_object* v_r_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
v_size_3421_ = lean_ctor_get(v_l_3273_, 0);
v_size_3422_ = lean_ctor_get(v_impl_3419_, 0);
lean_inc(v_size_3422_);
v_k_3423_ = lean_ctor_get(v_impl_3419_, 1);
lean_inc(v_k_3423_);
v_v_3424_ = lean_ctor_get(v_impl_3419_, 2);
lean_inc(v_v_3424_);
v_l_3425_ = lean_ctor_get(v_impl_3419_, 3);
lean_inc(v_l_3425_);
v_r_3426_ = lean_ctor_get(v_impl_3419_, 4);
lean_inc(v_r_3426_);
v___x_3427_ = lean_unsigned_to_nat(3u);
v___x_3428_ = lean_nat_mul(v___x_3427_, v_size_3421_);
v___x_3429_ = lean_nat_dec_lt(v___x_3428_, v_size_3422_);
lean_dec(v___x_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3433_; 
lean_dec(v_r_3426_);
lean_dec(v_l_3425_);
lean_dec(v_v_3424_);
lean_dec(v_k_3423_);
v___x_3430_ = lean_nat_add(v___x_3420_, v_size_3421_);
v___x_3431_ = lean_nat_add(v___x_3430_, v_size_3422_);
lean_dec(v_size_3422_);
lean_dec(v___x_3430_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 4, v_impl_3419_);
lean_ctor_set(v___x_3276_, 0, v___x_3431_);
v___x_3433_ = v___x_3276_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_k_3271_);
lean_ctor_set(v_reuseFailAlloc_3434_, 2, v_v_3272_);
lean_ctor_set(v_reuseFailAlloc_3434_, 3, v_l_3273_);
lean_ctor_set(v_reuseFailAlloc_3434_, 4, v_impl_3419_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
else
{
lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3498_; 
v_isSharedCheck_3498_ = !lean_is_exclusive(v_impl_3419_);
if (v_isSharedCheck_3498_ == 0)
{
lean_object* v_unused_3499_; lean_object* v_unused_3500_; lean_object* v_unused_3501_; lean_object* v_unused_3502_; lean_object* v_unused_3503_; 
v_unused_3499_ = lean_ctor_get(v_impl_3419_, 4);
lean_dec(v_unused_3499_);
v_unused_3500_ = lean_ctor_get(v_impl_3419_, 3);
lean_dec(v_unused_3500_);
v_unused_3501_ = lean_ctor_get(v_impl_3419_, 2);
lean_dec(v_unused_3501_);
v_unused_3502_ = lean_ctor_get(v_impl_3419_, 1);
lean_dec(v_unused_3502_);
v_unused_3503_ = lean_ctor_get(v_impl_3419_, 0);
lean_dec(v_unused_3503_);
v___x_3436_ = v_impl_3419_;
v_isShared_3437_ = v_isSharedCheck_3498_;
goto v_resetjp_3435_;
}
else
{
lean_dec(v_impl_3419_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3498_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v_size_3438_; lean_object* v_k_3439_; lean_object* v_v_3440_; lean_object* v_l_3441_; lean_object* v_r_3442_; lean_object* v_size_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v_size_3438_ = lean_ctor_get(v_l_3425_, 0);
v_k_3439_ = lean_ctor_get(v_l_3425_, 1);
v_v_3440_ = lean_ctor_get(v_l_3425_, 2);
v_l_3441_ = lean_ctor_get(v_l_3425_, 3);
v_r_3442_ = lean_ctor_get(v_l_3425_, 4);
v_size_3443_ = lean_ctor_get(v_r_3426_, 0);
v___x_3444_ = lean_unsigned_to_nat(2u);
v___x_3445_ = lean_nat_mul(v___x_3444_, v_size_3443_);
v___x_3446_ = lean_nat_dec_lt(v_size_3438_, v___x_3445_);
lean_dec(v___x_3445_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3474_; 
lean_inc(v_r_3442_);
lean_inc(v_l_3441_);
lean_inc(v_v_3440_);
lean_inc(v_k_3439_);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_l_3425_);
if (v_isSharedCheck_3474_ == 0)
{
lean_object* v_unused_3475_; lean_object* v_unused_3476_; lean_object* v_unused_3477_; lean_object* v_unused_3478_; lean_object* v_unused_3479_; 
v_unused_3475_ = lean_ctor_get(v_l_3425_, 4);
lean_dec(v_unused_3475_);
v_unused_3476_ = lean_ctor_get(v_l_3425_, 3);
lean_dec(v_unused_3476_);
v_unused_3477_ = lean_ctor_get(v_l_3425_, 2);
lean_dec(v_unused_3477_);
v_unused_3478_ = lean_ctor_get(v_l_3425_, 1);
lean_dec(v_unused_3478_);
v_unused_3479_ = lean_ctor_get(v_l_3425_, 0);
lean_dec(v_unused_3479_);
v___x_3448_ = v_l_3425_;
v_isShared_3449_ = v_isSharedCheck_3474_;
goto v_resetjp_3447_;
}
else
{
lean_dec(v_l_3425_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3474_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3464_; 
v___x_3450_ = lean_nat_add(v___x_3420_, v_size_3421_);
v___x_3451_ = lean_nat_add(v___x_3450_, v_size_3422_);
lean_dec(v_size_3422_);
if (lean_obj_tag(v_l_3441_) == 0)
{
lean_object* v_size_3472_; 
v_size_3472_ = lean_ctor_get(v_l_3441_, 0);
lean_inc(v_size_3472_);
v___y_3464_ = v_size_3472_;
goto v___jp_3463_;
}
else
{
lean_object* v___x_3473_; 
v___x_3473_ = lean_unsigned_to_nat(0u);
v___y_3464_ = v___x_3473_;
goto v___jp_3463_;
}
v___jp_3452_:
{
lean_object* v___x_3456_; lean_object* v___x_3458_; 
v___x_3456_ = lean_nat_add(v___y_3454_, v___y_3455_);
lean_dec(v___y_3455_);
lean_dec(v___y_3454_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 4, v_r_3426_);
lean_ctor_set(v___x_3448_, 3, v_r_3442_);
lean_ctor_set(v___x_3448_, 2, v_v_3424_);
lean_ctor_set(v___x_3448_, 1, v_k_3423_);
lean_ctor_set(v___x_3448_, 0, v___x_3456_);
v___x_3458_ = v___x_3448_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3462_, 1, v_k_3423_);
lean_ctor_set(v_reuseFailAlloc_3462_, 2, v_v_3424_);
lean_ctor_set(v_reuseFailAlloc_3462_, 3, v_r_3442_);
lean_ctor_set(v_reuseFailAlloc_3462_, 4, v_r_3426_);
v___x_3458_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3460_; 
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v___x_3458_);
lean_ctor_set(v___x_3436_, 3, v___y_3453_);
lean_ctor_set(v___x_3436_, 2, v_v_3440_);
lean_ctor_set(v___x_3436_, 1, v_k_3439_);
lean_ctor_set(v___x_3436_, 0, v___x_3451_);
v___x_3460_ = v___x_3436_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_k_3439_);
lean_ctor_set(v_reuseFailAlloc_3461_, 2, v_v_3440_);
lean_ctor_set(v_reuseFailAlloc_3461_, 3, v___y_3453_);
lean_ctor_set(v_reuseFailAlloc_3461_, 4, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
v___jp_3463_:
{
lean_object* v___x_3465_; lean_object* v___x_3467_; 
v___x_3465_ = lean_nat_add(v___x_3450_, v___y_3464_);
lean_dec(v___y_3464_);
lean_dec(v___x_3450_);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 4, v_l_3441_);
lean_ctor_set(v___x_3276_, 0, v___x_3465_);
v___x_3467_ = v___x_3276_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3465_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_k_3271_);
lean_ctor_set(v_reuseFailAlloc_3471_, 2, v_v_3272_);
lean_ctor_set(v_reuseFailAlloc_3471_, 3, v_l_3273_);
lean_ctor_set(v_reuseFailAlloc_3471_, 4, v_l_3441_);
v___x_3467_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
lean_object* v___x_3468_; 
v___x_3468_ = lean_nat_add(v___x_3420_, v_size_3443_);
if (lean_obj_tag(v_r_3442_) == 0)
{
lean_object* v_size_3469_; 
v_size_3469_ = lean_ctor_get(v_r_3442_, 0);
lean_inc(v_size_3469_);
v___y_3453_ = v___x_3467_;
v___y_3454_ = v___x_3468_;
v___y_3455_ = v_size_3469_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3470_; 
v___x_3470_ = lean_unsigned_to_nat(0u);
v___y_3453_ = v___x_3467_;
v___y_3454_ = v___x_3468_;
v___y_3455_ = v___x_3470_;
goto v___jp_3452_;
}
}
}
}
}
else
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3484_; 
lean_del_object(v___x_3276_);
v___x_3480_ = lean_nat_add(v___x_3420_, v_size_3421_);
v___x_3481_ = lean_nat_add(v___x_3480_, v_size_3422_);
lean_dec(v_size_3422_);
v___x_3482_ = lean_nat_add(v___x_3480_, v_size_3438_);
lean_dec(v___x_3480_);
lean_inc_ref(v_l_3273_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 4, v_l_3425_);
lean_ctor_set(v___x_3436_, 3, v_l_3273_);
lean_ctor_set(v___x_3436_, 2, v_v_3272_);
lean_ctor_set(v___x_3436_, 1, v_k_3271_);
lean_ctor_set(v___x_3436_, 0, v___x_3482_);
v___x_3484_ = v___x_3436_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3482_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_k_3271_);
lean_ctor_set(v_reuseFailAlloc_3497_, 2, v_v_3272_);
lean_ctor_set(v_reuseFailAlloc_3497_, 3, v_l_3273_);
lean_ctor_set(v_reuseFailAlloc_3497_, 4, v_l_3425_);
v___x_3484_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
v_isSharedCheck_3491_ = !lean_is_exclusive(v_l_3273_);
if (v_isSharedCheck_3491_ == 0)
{
lean_object* v_unused_3492_; lean_object* v_unused_3493_; lean_object* v_unused_3494_; lean_object* v_unused_3495_; lean_object* v_unused_3496_; 
v_unused_3492_ = lean_ctor_get(v_l_3273_, 4);
lean_dec(v_unused_3492_);
v_unused_3493_ = lean_ctor_get(v_l_3273_, 3);
lean_dec(v_unused_3493_);
v_unused_3494_ = lean_ctor_get(v_l_3273_, 2);
lean_dec(v_unused_3494_);
v_unused_3495_ = lean_ctor_get(v_l_3273_, 1);
lean_dec(v_unused_3495_);
v_unused_3496_ = lean_ctor_get(v_l_3273_, 0);
lean_dec(v_unused_3496_);
v___x_3486_ = v_l_3273_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_dec(v_l_3273_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
lean_ctor_set(v___x_3486_, 4, v_r_3426_);
lean_ctor_set(v___x_3486_, 3, v___x_3484_);
lean_ctor_set(v___x_3486_, 2, v_v_3424_);
lean_ctor_set(v___x_3486_, 1, v_k_3423_);
lean_ctor_set(v___x_3486_, 0, v___x_3481_);
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3481_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_k_3423_);
lean_ctor_set(v_reuseFailAlloc_3490_, 2, v_v_3424_);
lean_ctor_set(v_reuseFailAlloc_3490_, 3, v___x_3484_);
lean_ctor_set(v_reuseFailAlloc_3490_, 4, v_r_3426_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3504_; 
v_l_3504_ = lean_ctor_get(v_impl_3419_, 3);
lean_inc(v_l_3504_);
if (lean_obj_tag(v_l_3504_) == 0)
{
lean_object* v_r_3505_; lean_object* v_k_3506_; lean_object* v_v_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3530_; 
v_r_3505_ = lean_ctor_get(v_impl_3419_, 4);
v_k_3506_ = lean_ctor_get(v_impl_3419_, 1);
v_v_3507_ = lean_ctor_get(v_impl_3419_, 2);
v_isSharedCheck_3530_ = !lean_is_exclusive(v_impl_3419_);
if (v_isSharedCheck_3530_ == 0)
{
lean_object* v_unused_3531_; lean_object* v_unused_3532_; 
v_unused_3531_ = lean_ctor_get(v_impl_3419_, 3);
lean_dec(v_unused_3531_);
v_unused_3532_ = lean_ctor_get(v_impl_3419_, 0);
lean_dec(v_unused_3532_);
v___x_3509_ = v_impl_3419_;
v_isShared_3510_ = v_isSharedCheck_3530_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_r_3505_);
lean_inc(v_v_3507_);
lean_inc(v_k_3506_);
lean_dec(v_impl_3419_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3530_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v_k_3511_; lean_object* v_v_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3526_; 
v_k_3511_ = lean_ctor_get(v_l_3504_, 1);
v_v_3512_ = lean_ctor_get(v_l_3504_, 2);
v_isSharedCheck_3526_ = !lean_is_exclusive(v_l_3504_);
if (v_isSharedCheck_3526_ == 0)
{
lean_object* v_unused_3527_; lean_object* v_unused_3528_; lean_object* v_unused_3529_; 
v_unused_3527_ = lean_ctor_get(v_l_3504_, 4);
lean_dec(v_unused_3527_);
v_unused_3528_ = lean_ctor_get(v_l_3504_, 3);
lean_dec(v_unused_3528_);
v_unused_3529_ = lean_ctor_get(v_l_3504_, 0);
lean_dec(v_unused_3529_);
v___x_3514_ = v_l_3504_;
v_isShared_3515_ = v_isSharedCheck_3526_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_v_3512_);
lean_inc(v_k_3511_);
lean_dec(v_l_3504_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3526_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3516_; lean_object* v___x_3518_; 
v___x_3516_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3505_, 2);
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 4, v_r_3505_);
lean_ctor_set(v___x_3514_, 3, v_r_3505_);
lean_ctor_set(v___x_3514_, 2, v_v_3272_);
lean_ctor_set(v___x_3514_, 1, v_k_3271_);
lean_ctor_set(v___x_3514_, 0, v___x_3420_);
v___x_3518_ = v___x_3514_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v_k_3271_);
lean_ctor_set(v_reuseFailAlloc_3525_, 2, v_v_3272_);
lean_ctor_set(v_reuseFailAlloc_3525_, 3, v_r_3505_);
lean_ctor_set(v_reuseFailAlloc_3525_, 4, v_r_3505_);
v___x_3518_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3520_; 
lean_inc(v_r_3505_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 3, v_r_3505_);
lean_ctor_set(v___x_3509_, 0, v___x_3420_);
v___x_3520_ = v___x_3509_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v_k_3506_);
lean_ctor_set(v_reuseFailAlloc_3524_, 2, v_v_3507_);
lean_ctor_set(v_reuseFailAlloc_3524_, 3, v_r_3505_);
lean_ctor_set(v_reuseFailAlloc_3524_, 4, v_r_3505_);
v___x_3520_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3522_; 
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 4, v___x_3520_);
lean_ctor_set(v___x_3276_, 3, v___x_3518_);
lean_ctor_set(v___x_3276_, 2, v_v_3512_);
lean_ctor_set(v___x_3276_, 1, v_k_3511_);
lean_ctor_set(v___x_3276_, 0, v___x_3516_);
v___x_3522_ = v___x_3276_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3516_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_k_3511_);
lean_ctor_set(v_reuseFailAlloc_3523_, 2, v_v_3512_);
lean_ctor_set(v_reuseFailAlloc_3523_, 3, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3523_, 4, v___x_3520_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
}
}
else
{
lean_object* v_r_3533_; 
v_r_3533_ = lean_ctor_get(v_impl_3419_, 4);
lean_inc(v_r_3533_);
if (lean_obj_tag(v_r_3533_) == 0)
{
lean_object* v_k_3534_; lean_object* v_v_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3546_; 
v_k_3534_ = lean_ctor_get(v_impl_3419_, 1);
v_v_3535_ = lean_ctor_get(v_impl_3419_, 2);
v_isSharedCheck_3546_ = !lean_is_exclusive(v_impl_3419_);
if (v_isSharedCheck_3546_ == 0)
{
lean_object* v_unused_3547_; lean_object* v_unused_3548_; lean_object* v_unused_3549_; 
v_unused_3547_ = lean_ctor_get(v_impl_3419_, 4);
lean_dec(v_unused_3547_);
v_unused_3548_ = lean_ctor_get(v_impl_3419_, 3);
lean_dec(v_unused_3548_);
v_unused_3549_ = lean_ctor_get(v_impl_3419_, 0);
lean_dec(v_unused_3549_);
v___x_3537_ = v_impl_3419_;
v_isShared_3538_ = v_isSharedCheck_3546_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_v_3535_);
lean_inc(v_k_3534_);
lean_dec(v_impl_3419_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3546_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___x_3541_; 
v___x_3539_ = lean_unsigned_to_nat(3u);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 4, v_l_3504_);
lean_ctor_set(v___x_3537_, 2, v_v_3272_);
lean_ctor_set(v___x_3537_, 1, v_k_3271_);
lean_ctor_set(v___x_3537_, 0, v___x_3420_);
v___x_3541_ = v___x_3537_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v_k_3271_);
lean_ctor_set(v_reuseFailAlloc_3545_, 2, v_v_3272_);
lean_ctor_set(v_reuseFailAlloc_3545_, 3, v_l_3504_);
lean_ctor_set(v_reuseFailAlloc_3545_, 4, v_l_3504_);
v___x_3541_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
lean_object* v___x_3543_; 
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 4, v_r_3533_);
lean_ctor_set(v___x_3276_, 3, v___x_3541_);
lean_ctor_set(v___x_3276_, 2, v_v_3535_);
lean_ctor_set(v___x_3276_, 1, v_k_3534_);
lean_ctor_set(v___x_3276_, 0, v___x_3539_);
v___x_3543_ = v___x_3276_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3539_);
lean_ctor_set(v_reuseFailAlloc_3544_, 1, v_k_3534_);
lean_ctor_set(v_reuseFailAlloc_3544_, 2, v_v_3535_);
lean_ctor_set(v_reuseFailAlloc_3544_, 3, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3544_, 4, v_r_3533_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
else
{
lean_object* v___x_3550_; lean_object* v___x_3552_; 
v___x_3550_ = lean_unsigned_to_nat(2u);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 4, v_impl_3419_);
lean_ctor_set(v___x_3276_, 3, v_r_3533_);
lean_ctor_set(v___x_3276_, 0, v___x_3550_);
v___x_3552_ = v___x_3276_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3550_);
lean_ctor_set(v_reuseFailAlloc_3553_, 1, v_k_3271_);
lean_ctor_set(v_reuseFailAlloc_3553_, 2, v_v_3272_);
lean_ctor_set(v_reuseFailAlloc_3553_, 3, v_r_3533_);
lean_ctor_set(v_reuseFailAlloc_3553_, 4, v_impl_3419_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
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
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = lean_unsigned_to_nat(1u);
v___x_3556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3555_);
lean_ctor_set(v___x_3556_, 1, v_k_3267_);
lean_ctor_set(v___x_3556_, 2, v_v_3268_);
lean_ctor_set(v___x_3556_, 3, v_t_3269_);
lean_ctor_set(v___x_3556_, 4, v_t_3269_);
return v___x_3556_;
}
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3557_ = lean_box(1);
v___x_3558_ = l_Lake_Package_depsFacetConfig;
v___x_3559_ = l_Lake_Package_depsFacet;
v___x_3560_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3559_, v___x_3558_, v___x_3557_);
return v___x_3560_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3561_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__0, &l_Lake_Package_initFacetConfigs___closed__0_once, _init_l_Lake_Package_initFacetConfigs___closed__0);
v___x_3562_ = l_Lake_Package_transDepsFacetConfig;
v___x_3563_ = l_Lake_Package_transDepsFacet;
v___x_3564_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3563_, v___x_3562_, v___x_3561_);
return v___x_3564_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3565_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__1, &l_Lake_Package_initFacetConfigs___closed__1_once, _init_l_Lake_Package_initFacetConfigs___closed__1);
v___x_3566_ = l_Lake_Package_extraDepFacetConfig;
v___x_3567_ = l_Lake_Package_extraDepFacet;
v___x_3568_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3567_, v___x_3566_, v___x_3565_);
return v___x_3568_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3569_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__2, &l_Lake_Package_initFacetConfigs___closed__2_once, _init_l_Lake_Package_initFacetConfigs___closed__2);
v___x_3570_ = l_Lake_Package_optBuildCacheFacetConfig;
v___x_3571_ = l_Lake_Package_optBuildCacheFacet;
v___x_3572_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3571_, v___x_3570_, v___x_3569_);
return v___x_3572_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3573_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__3, &l_Lake_Package_initFacetConfigs___closed__3_once, _init_l_Lake_Package_initFacetConfigs___closed__3);
v___x_3574_ = l_Lake_Package_buildCacheFacetConfig;
v___x_3575_ = l_Lake_Package_buildCacheFacet;
v___x_3576_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3575_, v___x_3574_, v___x_3573_);
return v___x_3576_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3577_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__4, &l_Lake_Package_initFacetConfigs___closed__4_once, _init_l_Lake_Package_initFacetConfigs___closed__4);
v___x_3578_ = l_Lake_Package_optBarrelFacetConfig;
v___x_3579_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3580_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3579_, v___x_3578_, v___x_3577_);
return v___x_3580_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3581_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__5, &l_Lake_Package_initFacetConfigs___closed__5_once, _init_l_Lake_Package_initFacetConfigs___closed__5);
v___x_3582_ = l_Lake_Package_barrelFacetConfig;
v___x_3583_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3584_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3583_, v___x_3582_, v___x_3581_);
return v___x_3584_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3585_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__6, &l_Lake_Package_initFacetConfigs___closed__6_once, _init_l_Lake_Package_initFacetConfigs___closed__6);
v___x_3586_ = l_Lake_Package_optGitHubReleaseFacetConfig;
v___x_3587_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3588_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3587_, v___x_3586_, v___x_3585_);
return v___x_3588_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3589_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__7, &l_Lake_Package_initFacetConfigs___closed__7_once, _init_l_Lake_Package_initFacetConfigs___closed__7);
v___x_3590_ = l_Lake_Package_gitHubReleaseFacetConfig;
v___x_3591_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3592_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3591_, v___x_3590_, v___x_3589_);
return v___x_3592_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs(void){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__8, &l_Lake_Package_initFacetConfigs___closed__8_once, _init_l_Lake_Package_initFacetConfigs___closed__8);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3594_, lean_object* v_k_3595_, lean_object* v_v_3596_, lean_object* v_t_3597_, lean_object* v_hl_3598_){
_start:
{
lean_object* v___x_3599_; 
v___x_3599_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3595_, v_v_3596_, v_t_3597_);
return v___x_3599_;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs(void){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Lake_Package_initFacetConfigs;
return v___x_3600_;
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
