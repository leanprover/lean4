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
v___x_407_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_407_, 0, v___x_402_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
lean_ctor_set(v___x_407_, 2, v___x_383_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*3, v___x_404_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*3 + 1, v___x_405_);
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
v___x_857_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_857_, 0, v___x_852_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
lean_ctor_set(v___x_857_, 2, v___x_833_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*3, v___x_854_);
lean_ctor_set_uint8(v___x_857_, sizeof(void*)*3 + 1, v___x_855_);
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
size_t v_sz_boxed_892_; size_t v___x_15369__boxed_893_; lean_object* v_res_894_; 
v_sz_boxed_892_ = lean_unbox_usize(v_sz_880_);
lean_dec(v_sz_880_);
v___x_15369__boxed_893_ = lean_unbox_usize(v___x_881_);
lean_dec(v___x_881_);
v_res_894_ = l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0(v_self_878_, v_defaultTargets_879_, v_sz_boxed_892_, v___x_15369__boxed_893_, v___x_882_, v___x_883_, v___x_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
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
v___x_1155_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1155_, 0, v___x_1151_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
lean_ctor_set(v___x_1155_, 2, v___x_1150_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3, v___x_1153_);
lean_ctor_set_uint8(v___x_1155_, sizeof(void*)*3 + 1, v___y_1147_);
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
v___x_1174_ = lean_string_utf8_byte_size(v___y_1172_);
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = lean_nat_dec_eq(v___x_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
v___y_1162_ = v___y_1170_;
v___y_1163_ = v___y_1173_;
goto v___jp_1161_;
}
else
{
lean_dec(v___y_1173_);
lean_dec_ref(v_a_1138_);
lean_dec_ref(v_self_1137_);
v___y_1146_ = v___y_1170_;
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
v___y_1170_ = v_a_1183_;
v___y_1171_ = v_preferReleaseBuild_1189_;
v___y_1172_ = v_toolchain_1180_;
v___y_1173_ = v_keyName_1185_;
goto v___jp_1169_;
}
}
else
{
lean_inc(v_keyName_1185_);
v___y_1170_ = v_a_1183_;
v___y_1171_ = v_preferReleaseBuild_1189_;
v___y_1172_ = v_toolchain_1180_;
v___y_1173_ = v_keyName_1185_;
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
v_verbosity_1221_ = lean_ctor_get_uint8(v_toBuildConfig_1220_, sizeof(void*)*4 + 4);
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
v_verbosity_1255_ = lean_ctor_get_uint8(v_toBuildConfig_1254_, sizeof(void*)*4 + 4);
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
lean_object* v_a_1299_; lean_object* v_a_1300_; lean_object* v_a_1321_; lean_object* v_a_1322_; 
if (v_success_1290_ == 0)
{
lean_object* v_config_1342_; uint8_t v_preferReleaseBuild_1343_; 
v_config_1342_ = lean_ctor_get(v_self_1289_, 6);
v_preferReleaseBuild_1343_ = lean_ctor_get_uint8(v_config_1342_, sizeof(void*)*28 + 2);
if (v_preferReleaseBuild_1343_ == 0)
{
lean_object* v_toBuildConfig_1344_; lean_object* v_baseName_1345_; uint8_t v_verbosity_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v_toBuildConfig_1344_ = lean_ctor_get(v___y_1295_, 0);
v_baseName_1345_ = lean_ctor_get(v_self_1289_, 1);
lean_inc(v_baseName_1345_);
lean_dec_ref(v_self_1289_);
v_verbosity_1346_ = lean_ctor_get_uint8(v_toBuildConfig_1344_, sizeof(void*)*4 + 4);
v___x_1347_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1346_);
v___x_1348_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_1349_ = lean_nat_dec_eq(v___x_1347_, v___x_1348_);
lean_dec(v___x_1347_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_dec(v_baseName_1345_);
v___x_1350_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_1299_ = v___x_1350_;
v_a_1300_ = v___y_1296_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1351_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1352_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1345_, v___x_1349_);
v___x_1353_ = lean_string_append(v___x_1351_, v___x_1352_);
lean_dec_ref(v___x_1352_);
v___x_1354_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1355_ = lean_string_append(v___x_1353_, v___x_1354_);
v___x_1356_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2);
v___x_1357_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1356_, v___x_1349_);
v___x_1358_ = lean_string_append(v___x_1355_, v___x_1357_);
lean_dec_ref(v___x_1357_);
v___x_1359_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_1360_ = lean_string_append(v___x_1358_, v___x_1359_);
v_a_1299_ = v___x_1360_;
v_a_1300_ = v___y_1296_;
goto v___jp_1298_;
}
}
else
{
lean_object* v_toBuildConfig_1361_; lean_object* v_baseName_1362_; uint8_t v_verbosity_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; uint8_t v___x_1366_; 
v_toBuildConfig_1361_ = lean_ctor_get(v___y_1295_, 0);
v_baseName_1362_ = lean_ctor_get(v_self_1289_, 1);
lean_inc(v_baseName_1362_);
lean_dec_ref(v_self_1289_);
v_verbosity_1363_ = lean_ctor_get_uint8(v_toBuildConfig_1361_, sizeof(void*)*4 + 4);
v___x_1364_ = l_Lake_Verbosity_ctorIdx(v_verbosity_1363_);
v___x_1365_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_1366_ = lean_nat_dec_eq(v___x_1364_, v___x_1365_);
lean_dec(v___x_1364_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
lean_dec(v_baseName_1362_);
v___x_1367_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_1321_ = v___x_1367_;
v_a_1322_ = v___y_1296_;
goto v___jp_1320_;
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1368_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1369_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1362_, v___x_1366_);
v___x_1370_ = lean_string_append(v___x_1368_, v___x_1369_);
lean_dec_ref(v___x_1369_);
v___x_1371_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1372_ = lean_string_append(v___x_1370_, v___x_1371_);
v___x_1373_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
v___x_1374_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1373_, v___x_1366_);
v___x_1375_ = lean_string_append(v___x_1372_, v___x_1374_);
lean_dec_ref(v___x_1374_);
v___x_1376_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_1377_ = lean_string_append(v___x_1375_, v___x_1376_);
v_a_1321_ = v___x_1377_;
v_a_1322_ = v___y_1296_;
goto v___jp_1320_;
}
}
}
else
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_dec_ref(v_self_1289_);
v___x_1378_ = lean_box(0);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
lean_ctor_set(v___x_1379_, 1, v___y_1296_);
return v___x_1379_;
}
v___jp_1298_:
{
lean_object* v_log_1301_; uint8_t v_action_1302_; uint8_t v_wantsRebuild_1303_; lean_object* v_trace_1304_; lean_object* v_buildTime_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1319_; 
v_log_1301_ = lean_ctor_get(v_a_1300_, 0);
v_action_1302_ = lean_ctor_get_uint8(v_a_1300_, sizeof(void*)*3);
v_wantsRebuild_1303_ = lean_ctor_get_uint8(v_a_1300_, sizeof(void*)*3 + 1);
v_trace_1304_ = lean_ctor_get(v_a_1300_, 1);
v_buildTime_1305_ = lean_ctor_get(v_a_1300_, 2);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_a_1300_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1307_ = v_a_1300_;
v_isShared_1308_ = v_isSharedCheck_1319_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_buildTime_1305_);
lean_inc(v_trace_1304_);
lean_inc(v_log_1301_);
lean_dec(v_a_1300_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1319_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1309_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0));
v___x_1310_ = lean_string_append(v___x_1309_, v_a_1299_);
lean_dec_ref(v_a_1299_);
v___x_1311_ = 0;
v___x_1312_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set_uint8(v___x_1312_, sizeof(void*)*1, v___x_1311_);
v___x_1313_ = lean_box(0);
v___x_1314_ = lean_array_push(v_log_1301_, v___x_1312_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1314_);
v___x_1316_ = v___x_1307_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_trace_1304_);
lean_ctor_set(v_reuseFailAlloc_1318_, 2, v_buildTime_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*3, v_action_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1318_, sizeof(void*)*3 + 1, v_wantsRebuild_1303_);
v___x_1316_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1313_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
return v___x_1317_;
}
}
}
v___jp_1320_:
{
lean_object* v_log_1323_; uint8_t v_action_1324_; uint8_t v_wantsRebuild_1325_; lean_object* v_trace_1326_; lean_object* v_buildTime_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1341_; 
v_log_1323_ = lean_ctor_get(v_a_1322_, 0);
v_action_1324_ = lean_ctor_get_uint8(v_a_1322_, sizeof(void*)*3);
v_wantsRebuild_1325_ = lean_ctor_get_uint8(v_a_1322_, sizeof(void*)*3 + 1);
v_trace_1326_ = lean_ctor_get(v_a_1322_, 1);
v_buildTime_1327_ = lean_ctor_get(v_a_1322_, 2);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_a_1322_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1329_ = v_a_1322_;
v_isShared_1330_ = v_isSharedCheck_1341_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_buildTime_1327_);
lean_inc(v_trace_1326_);
lean_inc(v_log_1323_);
lean_dec(v_a_1322_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1341_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1331_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1));
v___x_1332_ = lean_string_append(v___x_1331_, v_a_1321_);
lean_dec_ref(v_a_1321_);
v___x_1333_ = 2;
v___x_1334_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1334_, 0, v___x_1332_);
lean_ctor_set_uint8(v___x_1334_, sizeof(void*)*1, v___x_1333_);
v___x_1335_ = lean_box(0);
v___x_1336_ = lean_array_push(v_log_1323_, v___x_1334_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v___x_1336_);
v___x_1338_ = v___x_1329_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_trace_1326_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_buildTime_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*3, v_action_1324_);
lean_ctor_set_uint8(v_reuseFailAlloc_1340_, sizeof(void*)*3 + 1, v_wantsRebuild_1325_);
v___x_1338_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1335_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
return v___x_1339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* v_self_1380_, lean_object* v_success_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
uint8_t v_success_boxed_1389_; lean_object* v_res_1390_; 
v_success_boxed_1389_ = lean_unbox(v_success_1381_);
v_res_1390_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(v_self_1380_, v_success_boxed_1389_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* v_self_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v___f_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
lean_inc_ref(v_self_1391_);
v___f_1399_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(v___f_1399_, 0, v_self_1391_);
v___x_1400_ = l_Lake_instDataKindUnit;
lean_inc_ref(v_a_1392_);
v___x_1401_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1414_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_a_1403_ = lean_ctor_get(v___x_1401_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1405_ = v___x_1401_;
v_isShared_1406_ = v_isSharedCheck_1414_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1414_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; uint8_t v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1407_ = lean_unsigned_to_nat(0u);
v___x_1408_ = 0;
v___x_1409_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_1410_ = l_Lake_Job_mapM___redArg(v___x_1400_, v_a_1402_, v___f_1399_, v___x_1407_, v___x_1408_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v___x_1409_);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1410_);
v___x_1412_ = v___x_1405_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_a_1403_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v___f_1399_);
lean_dec_ref(v_a_1392_);
v_a_1415_ = lean_ctor_get(v___x_1401_, 0);
v_a_1416_ = lean_ctor_get(v___x_1401_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1401_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_inc(v_a_1415_);
lean_dec(v___x_1401_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1415_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(lean_object* v_self_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec(v_a_1427_);
lean_dec(v_a_1426_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* v_self_1433_, lean_object* v_as_1434_, size_t v_sz_1435_, size_t v_i_1436_, lean_object* v_b_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
uint8_t v___x_1445_; 
v___x_1445_ = lean_usize_dec_lt(v_i_1436_, v_sz_1435_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; 
lean_dec_ref(v___y_1438_);
lean_dec_ref(v_self_1433_);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v_b_1437_);
lean_ctor_set(v___x_1446_, 1, v___y_1443_);
return v___x_1446_;
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1448_; 
v_a_1447_ = lean_array_uget_borrowed(v_as_1434_, v_i_1436_);
lean_inc_ref(v___y_1438_);
lean_inc(v_a_1447_);
lean_inc_ref(v_self_1433_);
v___x_1448_ = l_Lake_Package_fetchTargetJob(v_self_1433_, v_a_1447_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v_a_1450_; lean_object* v___x_1451_; size_t v___x_1452_; size_t v___x_1453_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
v_a_1450_ = lean_ctor_get(v___x_1448_, 1);
lean_inc(v_a_1450_);
lean_dec_ref_known(v___x_1448_, 2);
v___x_1451_ = l_Lake_Job_mix___redArg(v_b_1437_, v_a_1449_);
v___x_1452_ = ((size_t)1ULL);
v___x_1453_ = lean_usize_add(v_i_1436_, v___x_1452_);
v_i_1436_ = v___x_1453_;
v_b_1437_ = v___x_1451_;
v___y_1443_ = v_a_1450_;
goto _start;
}
else
{
lean_object* v_a_1455_; lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec_ref(v___y_1438_);
lean_dec_ref(v_b_1437_);
lean_dec_ref(v_self_1433_);
v_a_1455_ = lean_ctor_get(v___x_1448_, 0);
v_a_1456_ = lean_ctor_get(v___x_1448_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1448_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_inc(v_a_1455_);
lean_dec(v___x_1448_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1455_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* v_self_1464_, lean_object* v_as_1465_, lean_object* v_sz_1466_, lean_object* v_i_1467_, lean_object* v_b_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
size_t v_sz_boxed_1476_; size_t v_i_boxed_1477_; lean_object* v_res_1478_; 
v_sz_boxed_1476_ = lean_unbox_usize(v_sz_1466_);
lean_dec(v_sz_1466_);
v_i_boxed_1477_ = lean_unbox_usize(v_i_1467_);
lean_dec(v_i_1467_);
v_res_1478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1464_, v_as_1465_, v_sz_boxed_1476_, v_i_boxed_1477_, v_b_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v_as_1465_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object* v_config_1479_, lean_object* v_self_1480_, lean_object* v_____r_1481_, lean_object* v_job_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_extraDepTargets_1490_; size_t v_sz_1491_; size_t v___x_1492_; lean_object* v___x_1493_; 
v_extraDepTargets_1490_ = lean_ctor_get(v_config_1479_, 2);
v_sz_1491_ = lean_array_size(v_extraDepTargets_1490_);
v___x_1492_ = ((size_t)0ULL);
v___x_1493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1480_, v_extraDepTargets_1490_, v_sz_1491_, v___x_1492_, v_job_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object* v_config_1494_, lean_object* v_self_1495_, lean_object* v_____r_1496_, lean_object* v_job_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(v_config_1494_, v_self_1495_, v_____r_1496_, v_job_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v_config_1494_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(uint8_t v___x_1506_, lean_object* v_self_1507_, lean_object* v_job_1508_, lean_object* v___f_1509_, lean_object* v___x_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
if (v___x_1506_ == 0)
{
lean_object* v___x_1518_; 
lean_inc_ref(v___y_1511_);
v___x_1518_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1507_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v_a_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
v_a_1520_ = lean_ctor_get(v___x_1518_, 1);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1518_, 2);
v___x_1521_ = l_Lake_Job_add___redArg(v_job_1508_, v_a_1519_);
lean_inc_ref(v___y_1515_);
lean_inc(v___y_1514_);
lean_inc(v___y_1513_);
lean_inc(v___y_1512_);
v___x_1522_ = lean_apply_9(v___f_1509_, v___x_1510_, v___x_1521_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v_a_1520_, lean_box(0));
return v___x_1522_;
}
else
{
lean_dec_ref(v___y_1511_);
lean_dec_ref(v___f_1509_);
lean_dec_ref(v_job_1508_);
return v___x_1518_;
}
}
else
{
lean_object* v___x_1523_; 
lean_dec_ref(v_self_1507_);
lean_inc_ref(v___y_1515_);
lean_inc(v___y_1514_);
lean_inc(v___y_1513_);
lean_inc(v___y_1512_);
v___x_1523_ = lean_apply_9(v___f_1509_, v___x_1510_, v_job_1508_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, lean_box(0));
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* v___x_1524_, lean_object* v_self_1525_, lean_object* v_job_1526_, lean_object* v___f_1527_, lean_object* v___x_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
uint8_t v___x_4126__boxed_1536_; lean_object* v_res_1537_; 
v___x_4126__boxed_1536_ = lean_unbox(v___x_1524_);
v_res_1537_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(v___x_4126__boxed_1536_, v_self_1525_, v_job_1526_, v___f_1527_, v___x_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec(v___y_1530_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object* v_self_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_wsIdx_1548_; lean_object* v_baseName_1549_; lean_object* v_config_1550_; lean_object* v___f_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v_job_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; lean_object* v___y_1574_; lean_object* v___x_1575_; 
v_wsIdx_1548_ = lean_ctor_get(v_self_1540_, 0);
v_baseName_1549_ = lean_ctor_get(v_self_1540_, 1);
v_config_1550_ = lean_ctor_get(v_self_1540_, 6);
lean_inc_ref(v_self_1540_);
lean_inc_ref(v_config_1550_);
v___f_1551_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1551_, 0, v_config_1550_);
lean_closure_set(v___f_1551_, 1, v_self_1540_);
v___x_1552_ = l_Lake_instDataKindUnit;
v___x_1553_ = 1;
lean_inc(v_baseName_1549_);
v___x_1554_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1549_, v___x_1553_);
v___x_1555_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0));
lean_inc_ref(v___x_1554_);
v___x_1556_ = lean_string_append(v___x_1554_, v___x_1555_);
v___x_1557_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1));
v___x_1558_ = lean_string_append(v___x_1557_, v___x_1554_);
lean_dec_ref(v___x_1554_);
v___x_1559_ = lean_string_append(v___x_1558_, v___x_1555_);
v___x_1560_ = lean_box(0);
v___x_1561_ = lean_box(0);
v___x_1562_ = lean_unsigned_to_nat(0u);
v___x_1563_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1564_ = 0;
v___x_1565_ = 0;
v___x_1566_ = l_Lake_BuildTrace_nil(v___x_1559_);
v___x_1567_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1567_, 0, v___x_1563_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
lean_ctor_set(v___x_1567_, 2, v___x_1562_);
lean_ctor_set_uint8(v___x_1567_, sizeof(void*)*3, v___x_1564_);
lean_ctor_set_uint8(v___x_1567_, sizeof(void*)*3 + 1, v___x_1565_);
v___x_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1560_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = lean_task_pure(v___x_1568_);
v___x_1570_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_job_1571_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_1571_, 0, v___x_1569_);
lean_ctor_set(v_job_1571_, 1, v___x_1561_);
lean_ctor_set(v_job_1571_, 2, v___x_1570_);
lean_ctor_set_uint8(v_job_1571_, sizeof(void*)*3, v___x_1565_);
v___x_1572_ = lean_nat_dec_eq(v_wsIdx_1548_, v___x_1562_);
v___x_1573_ = lean_box(v___x_1572_);
v___y_1574_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 12, 5);
lean_closure_set(v___y_1574_, 0, v___x_1573_);
lean_closure_set(v___y_1574_, 1, v_self_1540_);
lean_closure_set(v___y_1574_, 2, v_job_1571_);
lean_closure_set(v___y_1574_, 3, v___f_1551_);
lean_closure_set(v___y_1574_, 4, v___x_1560_);
v___x_1575_ = l_Lake_ensureJob___redArg(v___x_1552_, v___y_1574_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1600_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
v_a_1577_ = lean_ctor_get(v___x_1575_, 1);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1579_ = v___x_1575_;
v_isShared_1580_ = v_isSharedCheck_1600_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_inc(v_a_1576_);
lean_dec(v___x_1575_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1600_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_task_1581_; lean_object* v_kind_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1598_; 
v_task_1581_ = lean_ctor_get(v_a_1576_, 0);
v_kind_1582_ = lean_ctor_get(v_a_1576_, 1);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_a_1576_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; 
v_unused_1599_ = lean_ctor_get(v_a_1576_, 2);
lean_dec(v_unused_1599_);
v___x_1584_ = v_a_1576_;
v_isShared_1585_ = v_isSharedCheck_1598_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_kind_1582_);
lean_inc(v_task_1581_);
lean_dec(v_a_1576_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1598_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v_registeredJobs_1586_; lean_object* v_job_1588_; 
v_registeredJobs_1586_ = lean_ctor_get(v_a_1545_, 4);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 2, v___x_1556_);
v_job_1588_ = v___x_1584_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_task_1581_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_kind_1582_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v___x_1556_);
v_job_1588_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
lean_ctor_set_uint8(v_job_1588_, sizeof(void*)*3, v___x_1565_);
v___x_1589_ = lean_st_ref_take(v_registeredJobs_1586_);
lean_inc_ref(v_job_1588_);
v___x_1590_ = l_Lake_Job_toOpaque___redArg(v_job_1588_);
v___x_1591_ = lean_array_push(v___x_1589_, v___x_1590_);
v___x_1592_ = lean_st_ref_put(v_registeredJobs_1586_, v___x_1591_);
v___x_1593_ = l_Lake_Job_renew___redArg(v_job_1588_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v___x_1593_);
v___x_1595_ = v___x_1579_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_a_1577_);
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
else
{
lean_dec_ref(v___x_1556_);
return v___x_1575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(lean_object* v_self_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(v_self_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec(v_a_1603_);
return v_res_1609_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_box(0);
v___x_1611_ = l_Lean_Json_compress(v___x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t v_fmt_1612_){
_start:
{
if (v_fmt_1612_ == 0)
{
lean_object* v___x_1613_; 
v___x_1613_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
return v___x_1613_;
}
else
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
return v___x_1614_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_1615_){
_start:
{
uint8_t v_fmt_boxed_1616_; lean_object* v_res_1617_; 
v_fmt_boxed_1616_ = lean_unbox(v_fmt_1615_);
v_res_1617_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_boxed_1616_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(uint8_t v_fmt_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_1618_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object* v_fmt_1621_, lean_object* v_a_1622_){
_start:
{
uint8_t v_fmt_boxed_1623_; lean_object* v_res_1624_; 
v_fmt_boxed_1623_ = lean_unbox(v_fmt_1621_);
v_res_1624_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(v_fmt_boxed_1623_, v_a_1622_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v___y_1625_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
uint8_t v___y_67__boxed_1630_; lean_object* v_res_1631_; 
v___y_67__boxed_1630_ = lean_unbox(v___y_1628_);
v_res_1631_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_67__boxed_1630_, v___y_1629_);
return v_res_1631_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1634_; uint8_t v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___f_1634_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_1635_ = 1;
v___x_1636_ = l_Lake_instDataKindUnit;
v___x_1637_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__1));
v___x_1638_ = l_Lake_Package_keyword;
v___x_1639_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v___x_1637_);
lean_ctor_set(v___x_1639_, 2, v___x_1636_);
lean_ctor_set(v___x_1639_, 3, v___f_1634_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*4, v___x_1635_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*4 + 1, v___x_1635_);
return v___x_1639_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_obj_once(&l_Lake_Package_extraDepFacetConfig___closed__2, &l_Lake_Package_extraDepFacetConfig___closed__2_once, _init_l_Lake_Package_extraDepFacetConfig___closed__2);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object* v_self_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_origName_1660_; lean_object* v_dir_1661_; lean_object* v_scope_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v_origName_1660_ = lean_ctor_get(v_self_1656_, 3);
lean_inc(v_origName_1660_);
v_dir_1661_ = lean_ctor_get(v_self_1656_, 4);
lean_inc_ref(v_dir_1661_);
v_scope_1662_ = lean_ctor_get(v_self_1656_, 10);
lean_inc_ref(v_scope_1662_);
lean_dec_ref(v_self_1656_);
v___x_1663_ = lean_string_utf8_byte_size(v_scope_1662_);
v___x_1664_ = lean_unsigned_to_nat(0u);
v___x_1665_ = lean_nat_dec_eq(v___x_1663_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v_log_1666_; uint8_t v_action_1667_; uint8_t v_wantsRebuild_1668_; lean_object* v_trace_1669_; lean_object* v_buildTime_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_log_1666_ = lean_ctor_get(v_a_1658_, 0);
v_action_1667_ = lean_ctor_get_uint8(v_a_1658_, sizeof(void*)*3);
v_wantsRebuild_1668_ = lean_ctor_get_uint8(v_a_1658_, sizeof(void*)*3 + 1);
v_trace_1669_ = lean_ctor_get(v_a_1658_, 1);
v_buildTime_1670_ = lean_ctor_get(v_a_1658_, 2);
v___x_1671_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
v___x_1672_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1671_, v_dir_1661_);
if (lean_obj_tag(v___x_1672_) == 1)
{
lean_object* v_toContext_1673_; lean_object* v_lakeEnv_1674_; lean_object* v_val_1675_; lean_object* v_toolchain_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v_toContext_1673_ = lean_ctor_get(v_a_1657_, 1);
v_lakeEnv_1674_ = lean_ctor_get(v_toContext_1673_, 0);
v_val_1675_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_val_1675_);
lean_dec_ref_known(v___x_1672_, 1);
v_toolchain_1676_ = lean_ctor_get(v_lakeEnv_1674_, 19);
v___x_1677_ = lean_string_utf8_byte_size(v_toolchain_1676_);
v___x_1678_ = lean_nat_dec_eq(v___x_1677_, v___x_1664_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1679_ = l_Lean_Name_toString(v_origName_1660_, v___x_1665_);
lean_inc_ref(v_lakeEnv_1674_);
v___x_1680_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_1674_, v_scope_1662_, v___x_1679_);
lean_dec_ref(v___x_1679_);
lean_dec_ref(v_scope_1662_);
v___x_1681_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1));
v___x_1682_ = lean_string_append(v___x_1680_, v___x_1681_);
v___x_1683_ = lean_string_append(v___x_1682_, v_val_1675_);
lean_dec(v_val_1675_);
v___x_1684_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2));
v___x_1685_ = lean_string_append(v___x_1683_, v___x_1684_);
v___x_1686_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1687_ = l_Lake_uriEncode(v_toolchain_1676_, v___x_1686_);
v___x_1688_ = lean_string_append(v___x_1685_, v___x_1687_);
lean_dec_ref(v___x_1687_);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
lean_ctor_set(v___x_1689_, 1, v_a_1658_);
return v___x_1689_;
}
else
{
lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1700_; 
lean_inc(v_buildTime_1670_);
lean_inc_ref(v_trace_1669_);
lean_inc_ref(v_log_1666_);
lean_dec(v_val_1675_);
lean_dec_ref(v_scope_1662_);
lean_dec(v_origName_1660_);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_a_1658_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; lean_object* v_unused_1702_; lean_object* v_unused_1703_; 
v_unused_1701_ = lean_ctor_get(v_a_1658_, 2);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_a_1658_, 1);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_a_1658_, 0);
lean_dec(v_unused_1703_);
v___x_1691_ = v_a_1658_;
v_isShared_1692_ = v_isSharedCheck_1700_;
goto v_resetjp_1690_;
}
else
{
lean_dec(v_a_1658_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1700_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1693_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4));
v___x_1694_ = lean_array_get_size(v_log_1666_);
v___x_1695_ = lean_array_push(v_log_1666_, v___x_1693_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1695_);
v___x_1697_ = v___x_1691_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_trace_1669_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_buildTime_1670_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*3, v_action_1667_);
lean_ctor_set_uint8(v_reuseFailAlloc_1699_, sizeof(void*)*3 + 1, v_wantsRebuild_1668_);
v___x_1697_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1694_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
return v___x_1698_;
}
}
}
}
else
{
lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1714_; 
lean_inc(v_buildTime_1670_);
lean_inc_ref(v_trace_1669_);
lean_inc_ref(v_log_1666_);
lean_dec(v___x_1672_);
lean_dec_ref(v_scope_1662_);
lean_dec(v_origName_1660_);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_a_1658_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; lean_object* v_unused_1716_; lean_object* v_unused_1717_; 
v_unused_1715_ = lean_ctor_get(v_a_1658_, 2);
lean_dec(v_unused_1715_);
v_unused_1716_ = lean_ctor_get(v_a_1658_, 1);
lean_dec(v_unused_1716_);
v_unused_1717_ = lean_ctor_get(v_a_1658_, 0);
lean_dec(v_unused_1717_);
v___x_1705_ = v_a_1658_;
v_isShared_1706_ = v_isSharedCheck_1714_;
goto v_resetjp_1704_;
}
else
{
lean_dec(v_a_1658_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1714_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1707_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6));
v___x_1708_ = lean_array_get_size(v_log_1666_);
v___x_1709_ = lean_array_push(v_log_1666_, v___x_1707_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1709_);
v___x_1711_ = v___x_1705_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_trace_1669_);
lean_ctor_set(v_reuseFailAlloc_1713_, 2, v_buildTime_1670_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, sizeof(void*)*3, v_action_1667_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, sizeof(void*)*3 + 1, v_wantsRebuild_1668_);
v___x_1711_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1712_, 0, v___x_1708_);
lean_ctor_set(v___x_1712_, 1, v___x_1711_);
return v___x_1712_;
}
}
}
}
else
{
lean_object* v_log_1718_; uint8_t v_action_1719_; uint8_t v_wantsRebuild_1720_; lean_object* v_trace_1721_; lean_object* v_buildTime_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1733_; 
lean_dec_ref(v_scope_1662_);
lean_dec_ref(v_dir_1661_);
lean_dec(v_origName_1660_);
v_log_1718_ = lean_ctor_get(v_a_1658_, 0);
v_action_1719_ = lean_ctor_get_uint8(v_a_1658_, sizeof(void*)*3);
v_wantsRebuild_1720_ = lean_ctor_get_uint8(v_a_1658_, sizeof(void*)*3 + 1);
v_trace_1721_ = lean_ctor_get(v_a_1658_, 1);
v_buildTime_1722_ = lean_ctor_get(v_a_1658_, 2);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_a_1658_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1724_ = v_a_1658_;
v_isShared_1725_ = v_isSharedCheck_1733_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_buildTime_1722_);
lean_inc(v_trace_1721_);
lean_inc(v_log_1718_);
lean_dec(v_a_1658_);
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
lean_object* v_rev_1770_; lean_object* v_log_1771_; uint8_t v_action_1772_; uint8_t v_wantsRebuild_1773_; lean_object* v_trace_1774_; lean_object* v_buildTime_1775_; lean_object* v_dir_1784_; lean_object* v_config_1785_; lean_object* v_remoteUrl_1786_; lean_object* v_buildArchive_1787_; lean_object* v___y_1789_; lean_object* v___y_1790_; uint8_t v___y_1791_; uint8_t v___y_1792_; lean_object* v___y_1793_; lean_object* v_val_1794_; lean_object* v___y_1814_; lean_object* v_releaseRepo_1835_; 
v_dir_1784_ = lean_ctor_get(v_self_1766_, 4);
lean_inc_ref(v_dir_1784_);
v_config_1785_ = lean_ctor_get(v_self_1766_, 6);
lean_inc_ref(v_config_1785_);
v_remoteUrl_1786_ = lean_ctor_get(v_self_1766_, 11);
lean_inc_ref(v_remoteUrl_1786_);
v_buildArchive_1787_ = lean_ctor_get(v_self_1766_, 21);
lean_inc_ref(v_buildArchive_1787_);
lean_dec_ref(v_self_1766_);
v_releaseRepo_1835_ = lean_ctor_get(v_config_1785_, 10);
lean_inc(v_releaseRepo_1835_);
lean_dec_ref(v_config_1785_);
if (lean_obj_tag(v_releaseRepo_1835_) == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1836_ = lean_string_utf8_byte_size(v_remoteUrl_1786_);
v___x_1837_ = lean_unsigned_to_nat(0u);
v___x_1838_ = lean_nat_dec_eq(v___x_1836_, v___x_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1839_, 0, v_remoteUrl_1786_);
v___y_1814_ = v___x_1839_;
goto v___jp_1813_;
}
else
{
lean_dec_ref(v_remoteUrl_1786_);
v___y_1814_ = v_releaseRepo_1835_;
goto v___jp_1813_;
}
}
else
{
lean_dec_ref(v_remoteUrl_1786_);
v___y_1814_ = v_releaseRepo_1835_;
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
lean_object* v_log_1815_; uint8_t v_action_1816_; uint8_t v_wantsRebuild_1817_; lean_object* v_trace_1818_; lean_object* v_buildTime_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1834_; 
v_log_1815_ = lean_ctor_get(v_a_1767_, 0);
v_action_1816_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*3);
v_wantsRebuild_1817_ = lean_ctor_get_uint8(v_a_1767_, sizeof(void*)*3 + 1);
v_trace_1818_ = lean_ctor_get(v_a_1767_, 1);
v_buildTime_1819_ = lean_ctor_get(v_a_1767_, 2);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_a_1767_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1821_ = v_a_1767_;
v_isShared_1822_ = v_isSharedCheck_1834_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_buildTime_1819_);
lean_inc(v_trace_1818_);
lean_inc(v_log_1815_);
lean_dec(v_a_1767_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1834_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_dir_1784_);
v___x_1824_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v___x_1823_, v_dir_1784_);
if (lean_obj_tag(v___y_1814_) == 0)
{
if (lean_obj_tag(v___x_1824_) == 1)
{
lean_object* v_val_1825_; 
lean_del_object(v___x_1821_);
v_val_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_val_1825_);
lean_dec_ref_known(v___x_1824_, 1);
v___y_1789_ = v_buildTime_1819_;
v___y_1790_ = v_trace_1818_;
v___y_1791_ = v_wantsRebuild_1817_;
v___y_1792_ = v_action_1816_;
v___y_1793_ = v_log_1815_;
v_val_1794_ = v_val_1825_;
goto v___jp_1788_;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
lean_dec(v___x_1824_);
lean_dec_ref(v_buildArchive_1787_);
lean_dec_ref(v_dir_1784_);
v___x_1826_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6));
v___x_1827_ = lean_array_get_size(v_log_1815_);
v___x_1828_ = lean_array_push(v_log_1815_, v___x_1826_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1828_);
v___x_1830_ = v___x_1821_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_trace_1818_);
lean_ctor_set(v_reuseFailAlloc_1832_, 2, v_buildTime_1819_);
lean_ctor_set_uint8(v_reuseFailAlloc_1832_, sizeof(void*)*3, v_action_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1832_, sizeof(void*)*3 + 1, v_wantsRebuild_1817_);
v___x_1830_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1827_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
return v___x_1831_;
}
}
}
else
{
lean_object* v_val_1833_; 
lean_dec(v___x_1824_);
lean_del_object(v___x_1821_);
v_val_1833_ = lean_ctor_get(v___y_1814_, 0);
lean_inc(v_val_1833_);
lean_dec_ref_known(v___y_1814_, 1);
v___y_1789_ = v_buildTime_1819_;
v___y_1790_ = v_trace_1818_;
v___y_1791_ = v_wantsRebuild_1817_;
v___y_1792_ = v_action_1816_;
v___y_1793_ = v_log_1815_;
v_val_1794_ = v_val_1833_;
goto v___jp_1788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(lean_object* v_self_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1840_, v_a_1841_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object* v_self_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1844_, v_a_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object* v_self_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(v_self_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(lean_object* v_val_1862_, lean_object* v_a_x3f_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_log_1866_; uint8_t v_action_1867_; uint8_t v_wantsRebuild_1868_; lean_object* v_trace_1869_; lean_object* v_buildTime_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1882_; 
v_log_1866_ = lean_ctor_get(v___y_1864_, 0);
v_action_1867_ = lean_ctor_get_uint8(v___y_1864_, sizeof(void*)*3);
v_wantsRebuild_1868_ = lean_ctor_get_uint8(v___y_1864_, sizeof(void*)*3 + 1);
v_trace_1869_ = lean_ctor_get(v___y_1864_, 1);
v_buildTime_1870_ = lean_ctor_get(v___y_1864_, 2);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___y_1864_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1872_ = v___y_1864_;
v_isShared_1873_ = v_isSharedCheck_1882_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_buildTime_1870_);
lean_inc(v_trace_1869_);
lean_inc(v_log_1866_);
lean_dec(v___y_1864_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1882_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1874_ = lean_io_mono_ms_now();
v___x_1875_ = lean_nat_sub(v___x_1874_, v_val_1862_);
lean_dec(v___x_1874_);
v___x_1876_ = lean_box(0);
v___x_1877_ = lean_nat_add(v_buildTime_1870_, v___x_1875_);
lean_dec(v___x_1875_);
lean_dec(v_buildTime_1870_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 2, v___x_1877_);
v___x_1879_ = v___x_1872_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_log_1866_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_trace_1869_);
lean_ctor_set(v_reuseFailAlloc_1881_, 2, v___x_1877_);
lean_ctor_set_uint8(v_reuseFailAlloc_1881_, sizeof(void*)*3, v_action_1867_);
lean_ctor_set_uint8(v_reuseFailAlloc_1881_, sizeof(void*)*3 + 1, v_wantsRebuild_1868_);
v___x_1879_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1876_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
return v___x_1880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0___boxed(lean_object* v_val_1883_, lean_object* v_a_x3f_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v_val_1883_, v_a_x3f_1884_, v___y_1885_);
lean_dec(v_a_x3f_1884_);
lean_dec(v_val_1883_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(lean_object* v_url_1893_, lean_object* v_archiveFile_1894_, lean_object* v_headers_1895_, lean_object* v_depTrace_1896_, lean_object* v_traceFile_1897_, uint8_t v_action_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_a_1903_; lean_object* v_a_1904_; lean_object* v_log_1907_; uint8_t v_action_1908_; uint8_t v_wantsRebuild_1909_; lean_object* v_trace_1910_; lean_object* v_buildTime_1911_; lean_object* v_toBuildConfig_1917_; lean_object* v_log_1918_; uint8_t v_action_1919_; uint8_t v_wantsRebuild_1920_; lean_object* v_trace_1921_; lean_object* v_buildTime_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_2012_; 
v_toBuildConfig_1917_ = lean_ctor_get(v_a_1899_, 0);
v_log_1918_ = lean_ctor_get(v_a_1900_, 0);
v_action_1919_ = lean_ctor_get_uint8(v_a_1900_, sizeof(void*)*3);
v_wantsRebuild_1920_ = lean_ctor_get_uint8(v_a_1900_, sizeof(void*)*3 + 1);
v_trace_1921_ = lean_ctor_get(v_a_1900_, 1);
v_buildTime_1922_ = lean_ctor_get(v_a_1900_, 2);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_a_1900_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1924_ = v_a_1900_;
v_isShared_1925_ = v_isSharedCheck_2012_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_buildTime_1922_);
lean_inc(v_trace_1921_);
lean_inc(v_log_1918_);
lean_dec(v_a_1900_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_2012_;
goto v_resetjp_1923_;
}
v___jp_1902_:
{
lean_object* v___x_1905_; 
v___x_1905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1905_, 0, v_a_1903_);
lean_ctor_set(v___x_1905_, 1, v_a_1904_);
return v___x_1905_;
}
v___jp_1906_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1912_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1));
v___x_1913_ = lean_array_get_size(v_log_1907_);
v___x_1914_ = lean_array_push(v_log_1907_, v___x_1912_);
v___x_1915_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
lean_ctor_set(v___x_1915_, 1, v_trace_1910_);
lean_ctor_set(v___x_1915_, 2, v_buildTime_1911_);
lean_ctor_set_uint8(v___x_1915_, sizeof(void*)*3, v_action_1908_);
lean_ctor_set_uint8(v___x_1915_, sizeof(void*)*3 + 1, v_wantsRebuild_1909_);
v___x_1916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1913_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
return v___x_1916_;
}
v_resetjp_1923_:
{
uint8_t v_noBuild_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v_noBuild_1926_ = lean_ctor_get_uint8(v_toBuildConfig_1917_, sizeof(void*)*4 + 2);
v___x_1927_ = l_Lake_JobAction_merge(v_action_1919_, v_action_1898_);
v___x_1928_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2));
lean_inc_ref(v_traceFile_1897_);
v___x_1929_ = l_System_FilePath_addExtension(v_traceFile_1897_, v___x_1928_);
if (v_noBuild_1926_ == 0)
{
lean_object* v___x_1930_; lean_object* v_a_1932_; lean_object* v_a_1933_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1930_ = lean_io_mono_ms_now();
v___x_1937_ = lean_array_get_size(v_log_1918_);
v___x_1938_ = l_Lake_download(v_url_1893_, v_archiveFile_1894_, v_headers_1895_, v_log_1918_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v_a_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
v_a_1940_ = lean_ctor_get(v___x_1938_, 1);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1938_, 2);
v___x_1941_ = lean_array_get_size(v_a_1940_);
v___x_1942_ = l_Array_extract___redArg(v_a_1940_, v___x_1937_, v___x_1941_);
v___x_1943_ = lean_box(0);
v___x_1944_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1896_, v___x_1943_, v___x_1942_);
v___x_1945_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1897_, v___x_1944_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1982_; 
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v___x_1945_, 0);
lean_dec(v_unused_1983_);
v___x_1947_ = v___x_1945_;
v_isShared_1948_ = v_isSharedCheck_1982_;
goto v_resetjp_1946_;
}
else
{
lean_dec(v___x_1945_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1982_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lake_removeFileIfExists(v___x_1929_);
lean_dec_ref(v___x_1929_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1972_; 
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v___x_1949_, 0);
lean_dec(v_unused_1973_);
v___x_1951_ = v___x_1949_;
v_isShared_1952_ = v_isSharedCheck_1972_;
goto v_resetjp_1950_;
}
else
{
lean_dec(v___x_1949_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1972_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v_a_1940_);
v___x_1954_ = v___x_1924_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1940_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_trace_1921_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_buildTime_1922_);
lean_ctor_set_uint8(v_reuseFailAlloc_1971_, sizeof(void*)*3 + 1, v_wantsRebuild_1920_);
v___x_1954_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1956_; 
lean_ctor_set_uint8(v___x_1954_, sizeof(void*)*3, v___x_1927_);
lean_inc(v_a_1939_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v_a_1939_);
v___x_1956_ = v___x_1951_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1939_);
v___x_1956_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1958_; 
if (v_isShared_1948_ == 0)
{
lean_ctor_set_tag(v___x_1947_, 1);
lean_ctor_set(v___x_1947_, 0, v___x_1956_);
v___x_1958_ = v___x_1947_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1959_; lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
v___x_1959_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1930_, v___x_1958_, v___x_1954_);
lean_dec_ref(v___x_1958_);
lean_dec(v___x_1930_);
v_a_1960_ = lean_ctor_get(v___x_1959_, 1);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v___x_1959_, 0);
lean_dec(v_unused_1968_);
v___x_1962_ = v___x_1959_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1959_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v_a_1939_);
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1939_);
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
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
lean_del_object(v___x_1947_);
lean_dec(v_a_1939_);
v_a_1974_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1949_, 1);
v___x_1975_ = lean_io_error_to_string(v_a_1974_);
v___x_1976_ = 3;
v___x_1977_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1977_, 0, v___x_1975_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*1, v___x_1976_);
v___x_1978_ = lean_array_push(v_a_1940_, v___x_1977_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_1978_);
v___x_1980_ = v___x_1924_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_trace_1921_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_buildTime_1922_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*3 + 1, v_wantsRebuild_1920_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*3, v___x_1927_);
v_a_1932_ = v___x_1941_;
v_a_1933_ = v___x_1980_;
goto v___jp_1931_;
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1990_; 
lean_dec(v_a_1939_);
lean_dec_ref(v___x_1929_);
v_a_1984_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___x_1945_, 1);
v___x_1985_ = lean_io_error_to_string(v_a_1984_);
v___x_1986_ = 3;
v___x_1987_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1987_, 0, v___x_1985_);
lean_ctor_set_uint8(v___x_1987_, sizeof(void*)*1, v___x_1986_);
v___x_1988_ = lean_array_push(v_a_1940_, v___x_1987_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_1988_);
v___x_1990_ = v___x_1924_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_trace_1921_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_buildTime_1922_);
lean_ctor_set_uint8(v_reuseFailAlloc_1991_, sizeof(void*)*3 + 1, v_wantsRebuild_1920_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_ctor_set_uint8(v___x_1990_, sizeof(void*)*3, v___x_1927_);
v_a_1932_ = v___x_1941_;
v_a_1933_ = v___x_1990_;
goto v___jp_1931_;
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v_a_1993_; lean_object* v___x_1995_; 
lean_dec_ref(v___x_1929_);
lean_dec_ref(v_traceFile_1897_);
v_a_1992_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1992_);
v_a_1993_ = lean_ctor_get(v___x_1938_, 1);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1938_, 2);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v_a_1993_);
v___x_1995_ = v___x_1924_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1993_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v_trace_1921_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_buildTime_1922_);
lean_ctor_set_uint8(v_reuseFailAlloc_1996_, sizeof(void*)*3 + 1, v_wantsRebuild_1920_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*3, v___x_1927_);
v_a_1932_ = v_a_1992_;
v_a_1933_ = v___x_1995_;
goto v___jp_1931_;
}
}
v___jp_1931_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v_a_1936_; 
v___x_1934_ = lean_box(0);
v___x_1935_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1930_, v___x_1934_, v_a_1933_);
lean_dec(v___x_1930_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 1);
lean_inc(v_a_1936_);
lean_dec_ref(v___x_1935_);
v_a_1903_ = v_a_1932_;
v_a_1904_ = v_a_1936_;
goto v___jp_1902_;
}
}
else
{
uint8_t v___x_1997_; 
lean_dec_ref(v_archiveFile_1894_);
lean_dec_ref(v_url_1893_);
v___x_1997_ = l_System_FilePath_pathExists(v_traceFile_1897_);
lean_dec_ref(v_traceFile_1897_);
if (v___x_1997_ == 0)
{
lean_dec_ref(v___x_1929_);
lean_del_object(v___x_1924_);
v_log_1907_ = v_log_1918_;
v_action_1908_ = v___x_1927_;
v_wantsRebuild_1909_ = v_noBuild_1926_;
v_trace_1910_ = v_trace_1921_;
v_buildTime_1911_ = v_buildTime_1922_;
goto v___jp_1906_;
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1998_ = lean_box(0);
v___x_1999_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_2000_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1896_, v___x_1998_, v___x_1999_);
v___x_2001_ = l_Lake_BuildMetadata_writeFile(v___x_1929_, v___x_2000_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_dec_ref_known(v___x_2001_, 1);
lean_del_object(v___x_1924_);
v_log_1907_ = v_log_1918_;
v_action_1908_ = v___x_1927_;
v_wantsRebuild_1909_ = v_noBuild_1926_;
v_trace_1910_ = v_trace_1921_;
v_buildTime_1911_ = v_buildTime_1922_;
goto v___jp_1906_;
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2009_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
v___x_2003_ = lean_io_error_to_string(v_a_2002_);
v___x_2004_ = 3;
v___x_2005_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*1, v___x_2004_);
v___x_2006_ = lean_array_get_size(v_log_1918_);
v___x_2007_ = lean_array_push(v_log_1918_, v___x_2005_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_2007_);
v___x_2009_ = v___x_1924_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_trace_1921_);
lean_ctor_set(v_reuseFailAlloc_2011_, 2, v_buildTime_1922_);
v___x_2009_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2010_; 
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*3, v___x_1927_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*3 + 1, v_noBuild_1926_);
v___x_2010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2006_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
return v___x_2010_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___boxed(lean_object* v_url_2013_, lean_object* v_archiveFile_2014_, lean_object* v_headers_2015_, lean_object* v_depTrace_2016_, lean_object* v_traceFile_2017_, lean_object* v_action_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_){
_start:
{
uint8_t v_action_boxed_2022_; lean_object* v_res_2023_; 
v_action_boxed_2022_ = lean_unbox(v_action_2018_);
v_res_2023_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2013_, v_archiveFile_2014_, v_headers_2015_, v_depTrace_2016_, v_traceFile_2017_, v_action_boxed_2022_, v_a_2019_, v_a_2020_);
lean_dec_ref(v_a_2019_);
lean_dec_ref(v_depTrace_2016_);
lean_dec_ref(v_headers_2015_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(lean_object* v_url_2024_, lean_object* v_archiveFile_2025_, lean_object* v_headers_2026_, lean_object* v_a_2027_, lean_object* v_depTrace_2028_, lean_object* v_traceFile_2029_, uint8_t v_action_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2024_, v_archiveFile_2025_, v_headers_2026_, v_depTrace_2028_, v_traceFile_2029_, v_action_2030_, v_a_2034_, v_a_2035_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___boxed(lean_object* v_url_2038_, lean_object* v_archiveFile_2039_, lean_object* v_headers_2040_, lean_object* v_a_2041_, lean_object* v_depTrace_2042_, lean_object* v_traceFile_2043_, lean_object* v_action_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
uint8_t v_action_boxed_2051_; lean_object* v_res_2052_; 
v_action_boxed_2051_ = lean_unbox(v_action_2044_);
v_res_2052_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(v_url_2038_, v_archiveFile_2039_, v_headers_2040_, v_a_2041_, v_depTrace_2042_, v_traceFile_2043_, v_action_boxed_2051_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec_ref(v_depTrace_2042_);
lean_dec_ref(v_a_2041_);
lean_dec_ref(v_headers_2040_);
return v_res_2052_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(lean_object* v_x_2053_, lean_object* v_x_2054_){
_start:
{
if (lean_obj_tag(v_x_2053_) == 0)
{
if (lean_obj_tag(v_x_2054_) == 0)
{
uint8_t v___x_2055_; 
v___x_2055_ = 1;
return v___x_2055_;
}
else
{
uint8_t v___x_2056_; 
v___x_2056_ = 0;
return v___x_2056_;
}
}
else
{
if (lean_obj_tag(v_x_2054_) == 0)
{
uint8_t v___x_2057_; 
v___x_2057_ = 0;
return v___x_2057_;
}
else
{
lean_object* v_val_2058_; lean_object* v_val_2059_; uint64_t v___x_2060_; uint64_t v___x_2061_; uint8_t v___x_2062_; 
v_val_2058_ = lean_ctor_get(v_x_2053_, 0);
v_val_2059_ = lean_ctor_get(v_x_2054_, 0);
v___x_2060_ = lean_unbox_uint64(v_val_2058_);
v___x_2061_ = lean_unbox_uint64(v_val_2059_);
v___x_2062_ = lean_uint64_dec_eq(v___x_2060_, v___x_2061_);
return v___x_2062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2063_, lean_object* v_x_2064_){
_start:
{
uint8_t v_res_2065_; lean_object* v_r_2066_; 
v_res_2065_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v_x_2063_, v_x_2064_);
lean_dec(v_x_2064_);
lean_dec(v_x_2063_);
v_r_2066_ = lean_box(v_res_2065_);
return v_r_2066_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object* v_info_2067_, lean_object* v_self_2068_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_io_metadata(v_info_2067_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v_modified_2072_; uint8_t v___x_2073_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v_modified_2072_ = lean_ctor_get(v_a_2071_, 1);
lean_inc_ref(v_modified_2072_);
lean_dec(v_a_2071_);
v___x_2073_ = l_IO_FS_instOrdSystemTime_ord(v_self_2068_, v_modified_2072_);
lean_dec_ref(v_modified_2072_);
if (v___x_2073_ == 0)
{
uint8_t v___x_2074_; 
v___x_2074_ = 1;
return v___x_2074_;
}
else
{
uint8_t v___x_2075_; 
v___x_2075_ = 0;
return v___x_2075_;
}
}
else
{
uint8_t v___x_2076_; 
lean_dec_ref_known(v___x_2070_, 1);
v___x_2076_ = 0;
return v___x_2076_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object* v_info_2077_, lean_object* v_self_2078_, lean_object* v_a_2079_){
_start:
{
uint8_t v_res_2080_; lean_object* v_r_2081_; 
v_res_2080_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2077_, v_self_2078_);
lean_dec_ref(v_self_2078_);
lean_dec_ref(v_info_2077_);
v_r_2081_ = lean_box(v_res_2080_);
return v_r_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(lean_object* v_info_2082_, lean_object* v_depTrace_2083_, lean_object* v_depHash_2084_, lean_object* v_oldTrace_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
uint64_t v_hash_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v_hash_2089_ = lean_ctor_get_uint64(v_depTrace_2083_, sizeof(void*)*3);
v___x_2090_ = lean_box_uint64(v_hash_2089_);
v___x_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
v___x_2092_ = l_Option_instBEq_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v___x_2091_, v_depHash_2084_);
lean_dec_ref_known(v___x_2091_, 1);
if (v___x_2092_ == 0)
{
lean_object* v_toBuildConfig_2093_; uint8_t v_oldMode_2094_; 
v_toBuildConfig_2093_ = lean_ctor_get(v_a_2086_, 0);
v_oldMode_2094_ = lean_ctor_get_uint8(v_toBuildConfig_2093_, sizeof(void*)*4);
if (v_oldMode_2094_ == 0)
{
uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = 0;
v___x_2096_ = lean_box(v___x_2095_);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v_a_2087_);
return v___x_2097_;
}
else
{
uint8_t v___x_2098_; 
v___x_2098_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2082_, v_oldTrace_2085_);
if (v___x_2098_ == 0)
{
uint8_t v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2099_ = 0;
v___x_2100_ = lean_box(v___x_2099_);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v_a_2087_);
return v___x_2101_;
}
else
{
uint8_t v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2102_ = 1;
v___x_2103_ = lean_box(v___x_2102_);
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
lean_ctor_set(v___x_2104_, 1, v_a_2087_);
return v___x_2104_;
}
}
}
else
{
uint8_t v___x_2105_; 
v___x_2105_ = l_System_FilePath_pathExists(v_info_2082_);
if (v___x_2105_ == 0)
{
uint8_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = 0;
v___x_2107_ = lean_box(v___x_2106_);
v___x_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
lean_ctor_set(v___x_2108_, 1, v_a_2087_);
return v___x_2108_;
}
else
{
uint8_t v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = 2;
v___x_2110_ = lean_box(v___x_2109_);
v___x_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
lean_ctor_set(v___x_2111_, 1, v_a_2087_);
return v___x_2111_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(lean_object* v_info_2112_, lean_object* v_depTrace_2113_, lean_object* v_depHash_2114_, lean_object* v_oldTrace_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2112_, v_depTrace_2113_, v_depHash_2114_, v_oldTrace_2115_, v_a_2116_, v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec_ref(v_oldTrace_2115_);
lean_dec(v_depHash_2114_);
lean_dec_ref(v_depTrace_2113_);
lean_dec_ref(v_info_2112_);
return v_res_2119_;
}
}
static lean_object* _init_l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0(void){
_start:
{
uint8_t v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = 0;
v___x_2121_ = l_Lake_OutputStatus_ctorIdx(v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(lean_object* v_a_2122_, lean_object* v_info_2123_, lean_object* v_depTrace_2124_, lean_object* v_savedTrace_2125_, lean_object* v_oldTrace_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
if (lean_obj_tag(v_savedTrace_2125_) == 2)
{
lean_object* v_data_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2184_; 
v_data_2133_ = lean_ctor_get(v_savedTrace_2125_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_savedTrace_2125_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2135_ = v_savedTrace_2125_;
v_isShared_2136_ = v_isSharedCheck_2184_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_data_2133_);
lean_dec(v_savedTrace_2125_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2184_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
uint64_t v_depHash_2137_; lean_object* v_log_2138_; lean_object* v___x_2139_; lean_object* v___x_2141_; 
v_depHash_2137_ = lean_ctor_get_uint64(v_data_2133_, sizeof(void*)*3);
v_log_2138_ = lean_ctor_get(v_data_2133_, 2);
lean_inc_ref(v_log_2138_);
lean_dec_ref(v_data_2133_);
v___x_2139_ = lean_box_uint64(v_depHash_2137_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set_tag(v___x_2135_, 1);
lean_ctor_set(v___x_2135_, 0, v___x_2139_);
v___x_2141_ = v___x_2135_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2142_; lean_object* v_a_2143_; lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2182_; 
v___x_2142_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2123_, v_depTrace_2124_, v___x_2141_, v_oldTrace_2126_, v_a_2130_, v_a_2131_);
lean_dec_ref(v___x_2141_);
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
v_a_2144_ = lean_ctor_get(v___x_2142_, 1);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2146_ = v___x_2142_;
v_isShared_2147_ = v_isSharedCheck_2182_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_inc(v_a_2143_);
lean_dec(v___x_2142_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2182_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___y_2149_; uint8_t v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2153_ = lean_unbox(v_a_2143_);
v___x_2154_ = l_Lake_OutputStatus_ctorIdx(v___x_2153_);
v___x_2155_ = lean_obj_once(&l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0, &l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0_once, _init_l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0);
v___x_2156_ = lean_nat_dec_eq(v___x_2154_, v___x_2155_);
lean_dec(v___x_2154_);
if (v___x_2156_ == 0)
{
lean_object* v_log_2157_; uint8_t v_action_2158_; uint8_t v_wantsRebuild_2159_; lean_object* v_trace_2160_; lean_object* v_buildTime_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2181_; 
v_log_2157_ = lean_ctor_get(v_a_2144_, 0);
v_action_2158_ = lean_ctor_get_uint8(v_a_2144_, sizeof(void*)*3);
v_wantsRebuild_2159_ = lean_ctor_get_uint8(v_a_2144_, sizeof(void*)*3 + 1);
v_trace_2160_ = lean_ctor_get(v_a_2144_, 1);
v_buildTime_2161_ = lean_ctor_get(v_a_2144_, 2);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_a_2144_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2163_ = v_a_2144_;
v_isShared_2164_ = v_isSharedCheck_2181_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_buildTime_2161_);
lean_inc(v_trace_2160_);
lean_inc(v_log_2157_);
lean_dec(v_a_2144_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2181_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
uint8_t v___x_2165_; uint8_t v___x_2166_; lean_object* v___x_2168_; 
v___x_2165_ = 2;
v___x_2166_ = l_Lake_JobAction_merge(v_action_2158_, v___x_2165_);
if (v_isShared_2164_ == 0)
{
v___x_2168_ = v___x_2163_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_log_2157_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_trace_2160_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_buildTime_2161_);
lean_ctor_set_uint8(v_reuseFailAlloc_2180_, sizeof(void*)*3 + 1, v_wantsRebuild_2159_);
v___x_2168_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2169_; 
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*3, v___x_2166_);
v___x_2169_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_2138_, v_a_2122_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v___x_2168_);
lean_dec_ref(v_log_2138_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 1);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 2);
v___y_2149_ = v_a_2170_;
goto v___jp_2148_;
}
else
{
lean_object* v_a_2171_; lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_del_object(v___x_2146_);
lean_dec(v_a_2143_);
v_a_2171_ = lean_ctor_get(v___x_2169_, 0);
v_a_2172_ = lean_ctor_get(v___x_2169_, 1);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2169_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_inc(v_a_2171_);
lean_dec(v___x_2169_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2171_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_2138_);
v___y_2149_ = v_a_2144_;
goto v___jp_2148_;
}
v___jp_2148_:
{
lean_object* v___x_2151_; 
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 1, v___y_2149_);
v___x_2151_ = v___x_2146_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2143_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v___y_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
}
else
{
lean_object* v_toBuildConfig_2185_; uint8_t v_oldMode_2186_; 
lean_dec(v_savedTrace_2125_);
v_toBuildConfig_2185_ = lean_ctor_get(v_a_2130_, 0);
v_oldMode_2186_ = lean_ctor_get_uint8(v_toBuildConfig_2185_, sizeof(void*)*4);
if (v_oldMode_2186_ == 0)
{
uint8_t v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = 0;
v___x_2188_ = lean_box(v___x_2187_);
v___x_2189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v_a_2131_);
return v___x_2189_;
}
else
{
uint8_t v___x_2190_; 
v___x_2190_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2123_, v_oldTrace_2126_);
if (v___x_2190_ == 0)
{
uint8_t v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = 0;
v___x_2192_ = lean_box(v___x_2191_);
v___x_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
lean_ctor_set(v___x_2193_, 1, v_a_2131_);
return v___x_2193_;
}
else
{
uint8_t v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = 1;
v___x_2195_ = lean_box(v___x_2194_);
v___x_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v_a_2131_);
return v___x_2196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object* v_a_2197_, lean_object* v_info_2198_, lean_object* v_depTrace_2199_, lean_object* v_savedTrace_2200_, lean_object* v_oldTrace_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_2197_, v_info_2198_, v_depTrace_2199_, v_savedTrace_2200_, v_oldTrace_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec(v_a_2202_);
lean_dec_ref(v_oldTrace_2201_);
lean_dec_ref(v_depTrace_2199_);
lean_dec_ref(v_info_2198_);
lean_dec_ref(v_a_2197_);
return v_res_2208_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_unsigned_to_nat(0u);
v___x_2214_ = lean_nat_to_int(v___x_2213_);
return v___x_2214_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4(void){
_start:
{
uint32_t v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = 0;
v___x_2216_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3);
v___x_2217_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set_uint32(v___x_2217_, sizeof(void*)*1, v___x_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(lean_object* v_self_2218_, lean_object* v_url_2219_, lean_object* v_archiveFile_2220_, lean_object* v_headers_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v___y_2230_; uint8_t v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; uint8_t v___y_2234_; lean_object* v___y_2235_; uint8_t v_a_2261_; lean_object* v_a_2262_; lean_object* v_a_2277_; lean_object* v_a_2278_; lean_object* v_log_2280_; uint8_t v_action_2281_; uint8_t v_wantsRebuild_2282_; lean_object* v_trace_2283_; lean_object* v_buildTime_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2324_; 
v_log_2280_ = lean_ctor_get(v_a_2227_, 0);
v_action_2281_ = lean_ctor_get_uint8(v_a_2227_, sizeof(void*)*3);
v_wantsRebuild_2282_ = lean_ctor_get_uint8(v_a_2227_, sizeof(void*)*3 + 1);
v_trace_2283_ = lean_ctor_get(v_a_2227_, 1);
v_buildTime_2284_ = lean_ctor_get(v_a_2227_, 2);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_a_2227_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2286_ = v_a_2227_;
v_isShared_2287_ = v_isSharedCheck_2324_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_buildTime_2284_);
lean_inc(v_trace_2283_);
lean_inc(v_log_2280_);
lean_dec(v_a_2227_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2324_;
goto v_resetjp_2285_;
}
v___jp_2229_:
{
uint8_t v___x_2236_; uint8_t v___x_2237_; uint8_t v___x_2238_; lean_object* v___x_2239_; 
v___x_2236_ = 1;
v___x_2237_ = 3;
v___x_2238_ = l_Lake_JobAction_merge(v___y_2234_, v___x_2237_);
v___x_2239_ = l_Lake_untar(v_archiveFile_2220_, v___y_2235_, v___x_2236_, v___y_2232_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2249_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
v_a_2241_ = lean_ctor_get(v___x_2239_, 1);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2243_ = v___x_2239_;
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_inc(v_a_2240_);
lean_dec(v___x_2239_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2249_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2245_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2245_, 0, v_a_2241_);
lean_ctor_set(v___x_2245_, 1, v___y_2230_);
lean_ctor_set(v___x_2245_, 2, v___y_2233_);
lean_ctor_set_uint8(v___x_2245_, sizeof(void*)*3, v___x_2238_);
lean_ctor_set_uint8(v___x_2245_, sizeof(void*)*3 + 1, v___y_2231_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 1, v___x_2245_);
v___x_2247_ = v___x_2243_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2240_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2259_; 
v_a_2250_ = lean_ctor_get(v___x_2239_, 0);
v_a_2251_ = lean_ctor_get(v___x_2239_, 1);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2253_ = v___x_2239_;
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_inc(v_a_2250_);
lean_dec(v___x_2239_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2259_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
v___x_2255_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2255_, 0, v_a_2251_);
lean_ctor_set(v___x_2255_, 1, v___y_2230_);
lean_ctor_set(v___x_2255_, 2, v___y_2233_);
lean_ctor_set_uint8(v___x_2255_, sizeof(void*)*3, v___x_2238_);
lean_ctor_set_uint8(v___x_2255_, sizeof(void*)*3 + 1, v___y_2231_);
if (v_isShared_2254_ == 0)
{
lean_ctor_set(v___x_2253_, 1, v___x_2255_);
v___x_2257_ = v___x_2253_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2250_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
v___jp_2260_:
{
lean_object* v_config_2263_; lean_object* v_dir_2264_; lean_object* v_buildDir_2265_; lean_object* v_log_2266_; uint8_t v_action_2267_; uint8_t v_wantsRebuild_2268_; lean_object* v_trace_2269_; lean_object* v_buildTime_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; uint8_t v___x_2273_; 
v_config_2263_ = lean_ctor_get(v_self_2218_, 6);
lean_inc_ref(v_config_2263_);
v_dir_2264_ = lean_ctor_get(v_self_2218_, 4);
lean_inc_ref(v_dir_2264_);
lean_dec_ref(v_self_2218_);
v_buildDir_2265_ = lean_ctor_get(v_config_2263_, 5);
lean_inc_ref(v_buildDir_2265_);
lean_dec_ref(v_config_2263_);
v_log_2266_ = lean_ctor_get(v_a_2262_, 0);
v_action_2267_ = lean_ctor_get_uint8(v_a_2262_, sizeof(void*)*3);
v_wantsRebuild_2268_ = lean_ctor_get_uint8(v_a_2262_, sizeof(void*)*3 + 1);
v_trace_2269_ = lean_ctor_get(v_a_2262_, 1);
v_buildTime_2270_ = lean_ctor_get(v_a_2262_, 2);
v___x_2271_ = l_System_FilePath_normalize(v_buildDir_2265_);
v___x_2272_ = l_Lake_joinRelative(v_dir_2264_, v___x_2271_);
v___x_2273_ = l_System_FilePath_pathExists(v___x_2272_);
if (v_a_2261_ == 0)
{
lean_inc(v_buildTime_2270_);
lean_inc_ref(v_trace_2269_);
lean_inc_ref(v_log_2266_);
lean_dec_ref(v_a_2262_);
v___y_2230_ = v_trace_2269_;
v___y_2231_ = v_wantsRebuild_2268_;
v___y_2232_ = v_log_2266_;
v___y_2233_ = v_buildTime_2270_;
v___y_2234_ = v_action_2267_;
v___y_2235_ = v___x_2272_;
goto v___jp_2229_;
}
else
{
if (v___x_2273_ == 0)
{
lean_inc(v_buildTime_2270_);
lean_inc_ref(v_trace_2269_);
lean_inc_ref(v_log_2266_);
lean_dec_ref(v_a_2262_);
v___y_2230_ = v_trace_2269_;
v___y_2231_ = v_wantsRebuild_2268_;
v___y_2232_ = v_log_2266_;
v___y_2233_ = v_buildTime_2270_;
v___y_2234_ = v_action_2267_;
v___y_2235_ = v___x_2272_;
goto v___jp_2229_;
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
lean_dec_ref(v___x_2272_);
lean_dec_ref(v_archiveFile_2220_);
v___x_2274_ = lean_box(0);
v___x_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v_a_2262_);
return v___x_2275_;
}
}
}
v___jp_2276_:
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2279_, 0, v_a_2277_);
lean_ctor_set(v___x_2279_, 1, v_a_2278_);
return v___x_2279_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; uint64_t v___x_2289_; uint64_t v___x_2290_; uint64_t v_depTrace_2291_; lean_object* v___x_2292_; lean_object* v_traceFile_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; lean_object* v___x_2298_; 
v___x_2288_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0));
v___x_2289_ = l_Lake_Hash_nil;
v___x_2290_ = lean_string_hash(v_url_2219_);
v_depTrace_2291_ = lean_uint64_mix_hash(v___x_2289_, v___x_2290_);
v___x_2292_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1));
lean_inc_ref(v_archiveFile_2220_);
v_traceFile_2293_ = l_System_FilePath_addExtension(v_archiveFile_2220_, v___x_2292_);
v___x_2294_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2));
v___x_2295_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
v___x_2296_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2296_, 0, v___x_2294_);
lean_ctor_set(v___x_2296_, 1, v___x_2288_);
lean_ctor_set(v___x_2296_, 2, v___x_2295_);
lean_ctor_set_uint64(v___x_2296_, sizeof(void*)*3, v_depTrace_2291_);
v___x_2297_ = 4;
lean_inc_ref(v_traceFile_2293_);
v___x_2298_ = l_Lake_readTraceFile(v_traceFile_2293_, v_log_2280_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v_a_2300_; lean_object* v___x_2302_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
v_a_2300_ = lean_ctor_get(v___x_2298_, 1);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2298_, 2);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v_a_2300_);
v___x_2302_ = v___x_2286_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2300_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_trace_2283_);
lean_ctor_set(v_reuseFailAlloc_2318_, 2, v_buildTime_2284_);
lean_ctor_set_uint8(v_reuseFailAlloc_2318_, sizeof(void*)*3, v_action_2281_);
lean_ctor_set_uint8(v_reuseFailAlloc_2318_, sizeof(void*)*3 + 1, v_wantsRebuild_2282_);
v___x_2302_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_2222_, v_archiveFile_2220_, v___x_2296_, v_a_2299_, v___x_2295_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v___x_2302_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v_a_2305_; uint8_t v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
v_a_2305_ = lean_ctor_get(v___x_2303_, 1);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2303_, 2);
v___x_2306_ = lean_unbox(v_a_2304_);
lean_dec(v_a_2304_);
v___x_2307_ = l_Lake_OutputStatus_ctorIdx(v___x_2306_);
v___x_2308_ = lean_obj_once(&l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0, &l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0_once, _init_l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___closed__0);
v___x_2309_ = lean_nat_dec_eq(v___x_2307_, v___x_2308_);
lean_dec(v___x_2307_);
if (v___x_2309_ == 0)
{
uint8_t v___x_2310_; 
lean_dec_ref_known(v___x_2296_, 3);
lean_dec_ref(v_traceFile_2293_);
lean_dec_ref(v_url_2219_);
v___x_2310_ = 1;
v_a_2261_ = v___x_2310_;
v_a_2262_ = v_a_2305_;
goto v___jp_2260_;
}
else
{
uint8_t v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = 0;
lean_inc_ref(v_archiveFile_2220_);
v___x_2312_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2219_, v_archiveFile_2220_, v_headers_2221_, v___x_2296_, v_traceFile_2293_, v___x_2297_, v_a_2226_, v_a_2305_);
lean_dec_ref_known(v___x_2296_, 3);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 1);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2312_, 2);
v_a_2261_ = v___x_2311_;
v_a_2262_ = v_a_2313_;
goto v___jp_2260_;
}
else
{
lean_object* v_a_2314_; lean_object* v_a_2315_; 
lean_dec_ref(v_archiveFile_2220_);
lean_dec_ref(v_self_2218_);
v_a_2314_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2314_);
v_a_2315_ = lean_ctor_get(v___x_2312_, 1);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2312_, 2);
v_a_2277_ = v_a_2314_;
v_a_2278_ = v_a_2315_;
goto v___jp_2276_;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v_a_2317_; 
lean_dec_ref_known(v___x_2296_, 3);
lean_dec_ref(v_traceFile_2293_);
lean_dec_ref(v_archiveFile_2220_);
lean_dec_ref(v_url_2219_);
lean_dec_ref(v_self_2218_);
v_a_2316_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2316_);
v_a_2317_ = lean_ctor_get(v___x_2303_, 1);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2303_, 2);
v_a_2277_ = v_a_2316_;
v_a_2278_ = v_a_2317_;
goto v___jp_2276_;
}
}
}
else
{
lean_object* v_a_2319_; lean_object* v_a_2320_; lean_object* v___x_2322_; 
lean_dec_ref_known(v___x_2296_, 3);
lean_dec_ref(v_traceFile_2293_);
lean_dec_ref(v_archiveFile_2220_);
lean_dec_ref(v_url_2219_);
lean_dec_ref(v_self_2218_);
v_a_2319_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2319_);
v_a_2320_ = lean_ctor_get(v___x_2298_, 1);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2298_, 2);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v_a_2320_);
v___x_2322_ = v___x_2286_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2320_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_trace_2283_);
lean_ctor_set(v_reuseFailAlloc_2323_, 2, v_buildTime_2284_);
lean_ctor_set_uint8(v_reuseFailAlloc_2323_, sizeof(void*)*3, v_action_2281_);
lean_ctor_set_uint8(v_reuseFailAlloc_2323_, sizeof(void*)*3 + 1, v_wantsRebuild_2282_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
v_a_2277_ = v_a_2319_;
v_a_2278_ = v___x_2322_;
goto v___jp_2276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object* v_self_2325_, lean_object* v_url_2326_, lean_object* v_archiveFile_2327_, lean_object* v_headers_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_self_2325_, v_url_2326_, v_archiveFile_2327_, v_headers_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec_ref(v_headers_2328_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object* v_a_2337_, lean_object* v_info_2338_, lean_object* v_depTrace_2339_, lean_object* v_depHash_2340_, lean_object* v_oldTrace_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2338_, v_depTrace_2339_, v_depHash_2340_, v_oldTrace_2341_, v_a_2345_, v_a_2346_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object* v_a_2349_, lean_object* v_info_2350_, lean_object* v_depTrace_2351_, lean_object* v_depHash_2352_, lean_object* v_oldTrace_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_2349_, v_info_2350_, v_depTrace_2351_, v_depHash_2352_, v_oldTrace_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec_ref(v_oldTrace_2353_);
lean_dec(v_depHash_2352_);
lean_dec_ref(v_depTrace_2351_);
lean_dec_ref(v_info_2350_);
lean_dec_ref(v_a_2349_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_getUrl_2361_, lean_object* v_pkg_2362_, lean_object* v_archiveFile_2363_, lean_object* v_headers_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
uint8_t v_r_2373_; lean_object* v___y_2374_; lean_object* v_a_2378_; lean_object* v___x_2394_; 
lean_inc_ref(v___y_2369_);
lean_inc(v___y_2368_);
lean_inc(v___y_2367_);
lean_inc(v___y_2366_);
lean_inc_ref(v___y_2365_);
lean_inc_ref(v_pkg_2362_);
v___x_2394_ = lean_apply_8(v_getUrl_2361_, v_pkg_2362_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, lean_box(0));
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v_a_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
v_a_2396_ = lean_ctor_get(v___x_2394_, 1);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2394_, 2);
lean_inc_ref(v_pkg_2362_);
v___x_2397_ = lean_apply_1(v_archiveFile_2363_, v_pkg_2362_);
v___x_2398_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2362_, v_a_2395_, v___x_2397_, v_headers_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v_a_2396_);
lean_dec_ref(v___y_2365_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; uint8_t v___x_2400_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 1);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 2);
v___x_2400_ = 1;
v_r_2373_ = v___x_2400_;
v___y_2374_ = v_a_2399_;
goto v___jp_2372_;
}
else
{
lean_object* v_a_2401_; 
v_a_2401_ = lean_ctor_get(v___x_2398_, 1);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2398_, 2);
v_a_2378_ = v_a_2401_;
goto v___jp_2377_;
}
}
else
{
lean_object* v_a_2402_; 
lean_dec_ref(v___y_2365_);
lean_dec_ref(v_archiveFile_2363_);
lean_dec_ref(v_pkg_2362_);
v_a_2402_ = lean_ctor_get(v___x_2394_, 1);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___x_2394_, 2);
v_a_2378_ = v_a_2402_;
goto v___jp_2377_;
}
v___jp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = lean_box(v_r_2373_);
v___x_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
lean_ctor_set(v___x_2376_, 1, v___y_2374_);
return v___x_2376_;
}
v___jp_2377_:
{
lean_object* v_log_2379_; uint8_t v_action_2380_; uint8_t v_wantsRebuild_2381_; lean_object* v_trace_2382_; lean_object* v_buildTime_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2393_; 
v_log_2379_ = lean_ctor_get(v_a_2378_, 0);
v_action_2380_ = lean_ctor_get_uint8(v_a_2378_, sizeof(void*)*3);
v_wantsRebuild_2381_ = lean_ctor_get_uint8(v_a_2378_, sizeof(void*)*3 + 1);
v_trace_2382_ = lean_ctor_get(v_a_2378_, 1);
v_buildTime_2383_ = lean_ctor_get(v_a_2378_, 2);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_a_2378_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2385_ = v_a_2378_;
v_isShared_2386_ = v_isSharedCheck_2393_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_buildTime_2383_);
lean_inc(v_trace_2382_);
lean_inc(v_log_2379_);
lean_dec(v_a_2378_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2393_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
uint8_t v___x_2387_; uint8_t v___x_2388_; lean_object* v___x_2390_; 
v___x_2387_ = 4;
v___x_2388_ = l_Lake_JobAction_merge(v_action_2380_, v___x_2387_);
if (v_isShared_2386_ == 0)
{
v___x_2390_ = v___x_2385_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_log_2379_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_trace_2382_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v_buildTime_2383_);
lean_ctor_set_uint8(v_reuseFailAlloc_2392_, sizeof(void*)*3 + 1, v_wantsRebuild_2381_);
v___x_2390_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
uint8_t v___x_2391_; 
lean_ctor_set_uint8(v___x_2390_, sizeof(void*)*3, v___x_2388_);
v___x_2391_ = 0;
v_r_2373_ = v___x_2391_;
v___y_2374_ = v___x_2390_;
goto v___jp_2372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_getUrl_2403_, lean_object* v_pkg_2404_, lean_object* v_archiveFile_2405_, lean_object* v_headers_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(v_getUrl_2403_, v_pkg_2404_, v_archiveFile_2405_, v_headers_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v_headers_2406_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* v_getUrl_2415_, lean_object* v_archiveFile_2416_, lean_object* v_headers_2417_, lean_object* v_facet_2418_, lean_object* v___x_2419_, lean_object* v_pkg_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_baseName_2428_; lean_object* v___f_2429_; uint8_t v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_baseName_2428_ = lean_ctor_get(v_pkg_2420_, 1);
lean_inc(v_baseName_2428_);
v___f_2429_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2429_, 0, v_getUrl_2415_);
lean_closure_set(v___f_2429_, 1, v_pkg_2420_);
lean_closure_set(v___f_2429_, 2, v_archiveFile_2416_);
lean_closure_set(v___f_2429_, 3, v_headers_2417_);
v___x_2430_ = 1;
v___x_2431_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2428_, v___x_2430_);
v___x_2432_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2433_ = lean_string_append(v___x_2431_, v___x_2432_);
v___x_2434_ = l_Lake_Name_eraseHead(v_facet_2418_);
v___x_2435_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2434_, v___x_2430_);
v___x_2436_ = lean_string_append(v___x_2433_, v___x_2435_);
lean_dec_ref(v___x_2435_);
v___x_2437_ = lean_unsigned_to_nat(0u);
v___x_2438_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2419_);
v___x_2439_ = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(v___x_2439_, 0, lean_box(0));
lean_closure_set(v___x_2439_, 1, v___x_2419_);
lean_closure_set(v___x_2439_, 2, v___f_2429_);
lean_closure_set(v___x_2439_, 3, v___x_2437_);
lean_closure_set(v___x_2439_, 4, v___x_2438_);
v___x_2440_ = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM___boxed), 9, 2);
lean_closure_set(v___x_2440_, 0, lean_box(0));
lean_closure_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM___boxed), 9, 2);
lean_closure_set(v___x_2441_, 0, lean_box(0));
lean_closure_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = l_Lake_ensureJob___redArg(v___x_2419_, v___x_2441_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2467_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_a_2444_ = lean_ctor_get(v___x_2442_, 1);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2446_ = v___x_2442_;
v_isShared_2447_ = v_isSharedCheck_2467_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2467_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v_task_2448_; lean_object* v_kind_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2465_; 
v_task_2448_ = lean_ctor_get(v_a_2443_, 0);
v_kind_2449_ = lean_ctor_get(v_a_2443_, 1);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_a_2443_);
if (v_isSharedCheck_2465_ == 0)
{
lean_object* v_unused_2466_; 
v_unused_2466_ = lean_ctor_get(v_a_2443_, 2);
lean_dec(v_unused_2466_);
v___x_2451_ = v_a_2443_;
v_isShared_2452_ = v_isSharedCheck_2465_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_kind_2449_);
lean_inc(v_task_2448_);
lean_dec(v_a_2443_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2465_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v_registeredJobs_2453_; lean_object* v_job_2455_; 
v_registeredJobs_2453_ = lean_ctor_get(v___y_2425_, 4);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 2, v___x_2436_);
v_job_2455_ = v___x_2451_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_task_2448_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_kind_2449_);
lean_ctor_set(v_reuseFailAlloc_2464_, 2, v___x_2436_);
v_job_2455_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
lean_ctor_set_uint8(v_job_2455_, sizeof(void*)*3, v___x_2430_);
v___x_2456_ = lean_st_ref_take(v_registeredJobs_2453_);
lean_inc_ref(v_job_2455_);
v___x_2457_ = l_Lake_Job_toOpaque___redArg(v_job_2455_);
v___x_2458_ = lean_array_push(v___x_2456_, v___x_2457_);
v___x_2459_ = lean_st_ref_put(v_registeredJobs_2453_, v___x_2458_);
v___x_2460_ = l_Lake_Job_renew___redArg(v_job_2455_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2460_);
v___x_2462_ = v___x_2446_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2460_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_a_2444_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2436_);
return v___x_2442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v_getUrl_2468_, lean_object* v_archiveFile_2469_, lean_object* v_headers_2470_, lean_object* v_facet_2471_, lean_object* v___x_2472_, lean_object* v_pkg_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_2468_, v_archiveFile_2469_, v_headers_2470_, v_facet_2471_, v___x_2472_, v_pkg_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec(v___y_2475_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object* v_facet_2489_, lean_object* v_archiveFile_2490_, lean_object* v_getUrl_2491_, lean_object* v_headers_2492_){
_start:
{
lean_object* v___x_2493_; lean_object* v___f_2494_; lean_object* v___x_2495_; uint8_t v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2493_ = l_Lake_instDataKindBool;
v___f_2494_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2494_, 0, v_getUrl_2491_);
lean_closure_set(v___f_2494_, 1, v_archiveFile_2490_);
lean_closure_set(v___f_2494_, 2, v_headers_2492_);
lean_closure_set(v___f_2494_, 3, v_facet_2489_);
lean_closure_set(v___f_2494_, 4, v___x_2493_);
v___x_2495_ = l_Lake_Package_keyword;
v___x_2496_ = 1;
v___x_2497_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_2498_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2498_, 0, v___x_2495_);
lean_ctor_set(v___x_2498_, 1, v___f_2494_);
lean_ctor_set(v___x_2498_, 2, v___x_2493_);
lean_ctor_set(v___x_2498_, 3, v___x_2497_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*4, v___x_2496_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*4 + 1, v___x_2496_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* v_facet_2499_, lean_object* v_archiveFile_2500_, lean_object* v_getUrl_2501_, lean_object* v_headers_2502_, lean_object* v_inst_2503_){
_start:
{
lean_object* v___x_2504_; lean_object* v___f_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2504_ = l_Lake_instDataKindBool;
v___f_2505_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2505_, 0, v_getUrl_2501_);
lean_closure_set(v___f_2505_, 1, v_archiveFile_2500_);
lean_closure_set(v___f_2505_, 2, v_headers_2502_);
lean_closure_set(v___f_2505_, 3, v_facet_2499_);
lean_closure_set(v___f_2505_, 4, v___x_2504_);
v___x_2506_ = l_Lake_Package_keyword;
v___x_2507_ = 1;
v___x_2508_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_2509_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2509_, 0, v___x_2506_);
lean_ctor_set(v___x_2509_, 1, v___f_2505_);
lean_ctor_set(v___x_2509_, 2, v___x_2504_);
lean_ctor_set(v___x_2509_, 3, v___x_2508_);
lean_ctor_set_uint8(v___x_2509_, sizeof(void*)*4, v___x_2507_);
lean_ctor_set_uint8(v___x_2509_, sizeof(void*)*4 + 1, v___x_2507_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_what_2511_, lean_object* v_baseName_2512_, lean_object* v_optFacet_2513_, uint8_t v_success_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_a_2523_; lean_object* v_a_2524_; 
if (v_success_2514_ == 0)
{
lean_object* v_toBuildConfig_2545_; uint8_t v_verbosity_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v_toBuildConfig_2545_ = lean_ctor_get(v___y_2519_, 0);
v_verbosity_2546_ = lean_ctor_get_uint8(v_toBuildConfig_2545_, sizeof(void*)*4 + 4);
v___x_2547_ = l_Lake_Verbosity_ctorIdx(v_verbosity_2546_);
v___x_2548_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_2549_ = lean_nat_dec_eq(v___x_2547_, v___x_2548_);
lean_dec(v___x_2547_);
if (v___x_2549_ == 0)
{
lean_object* v___x_2550_; 
lean_dec(v_optFacet_2513_);
lean_dec(v_baseName_2512_);
v___x_2550_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_2523_ = v___x_2550_;
v_a_2524_ = v___y_2520_;
goto v___jp_2522_;
}
else
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2551_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2552_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2512_, v___x_2549_);
v___x_2553_ = lean_string_append(v___x_2551_, v___x_2552_);
lean_dec_ref(v___x_2552_);
v___x_2554_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2555_ = lean_string_append(v___x_2553_, v___x_2554_);
v___x_2556_ = l_Lake_Name_eraseHead(v_optFacet_2513_);
v___x_2557_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2556_, v___x_2549_);
v___x_2558_ = lean_string_append(v___x_2555_, v___x_2557_);
lean_dec_ref(v___x_2557_);
v___x_2559_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_2560_ = lean_string_append(v___x_2558_, v___x_2559_);
v_a_2523_ = v___x_2560_;
v_a_2524_ = v___y_2520_;
goto v___jp_2522_;
}
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
lean_dec(v_optFacet_2513_);
lean_dec(v_baseName_2512_);
v___x_2561_ = lean_box(0);
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
lean_ctor_set(v___x_2562_, 1, v___y_2520_);
return v___x_2562_;
}
v___jp_2522_:
{
lean_object* v_log_2525_; uint8_t v_action_2526_; uint8_t v_wantsRebuild_2527_; lean_object* v_trace_2528_; lean_object* v_buildTime_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2544_; 
v_log_2525_ = lean_ctor_get(v_a_2524_, 0);
v_action_2526_ = lean_ctor_get_uint8(v_a_2524_, sizeof(void*)*3);
v_wantsRebuild_2527_ = lean_ctor_get_uint8(v_a_2524_, sizeof(void*)*3 + 1);
v_trace_2528_ = lean_ctor_get(v_a_2524_, 1);
v_buildTime_2529_ = lean_ctor_get(v_a_2524_, 2);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_a_2524_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2531_ = v_a_2524_;
v_isShared_2532_ = v_isSharedCheck_2544_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_buildTime_2529_);
lean_inc(v_trace_2528_);
lean_inc(v_log_2525_);
lean_dec(v_a_2524_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2544_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2541_; 
v___x_2533_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0));
v___x_2534_ = lean_string_append(v___x_2533_, v_what_2511_);
v___x_2535_ = lean_string_append(v___x_2534_, v_a_2523_);
lean_dec_ref(v_a_2523_);
v___x_2536_ = 3;
v___x_2537_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set_uint8(v___x_2537_, sizeof(void*)*1, v___x_2536_);
v___x_2538_ = lean_array_get_size(v_log_2525_);
v___x_2539_ = lean_array_push(v_log_2525_, v___x_2537_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 0, v___x_2539_);
v___x_2541_ = v___x_2531_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_trace_2528_);
lean_ctor_set(v_reuseFailAlloc_2543_, 2, v_buildTime_2529_);
lean_ctor_set_uint8(v_reuseFailAlloc_2543_, sizeof(void*)*3, v_action_2526_);
lean_ctor_set_uint8(v_reuseFailAlloc_2543_, sizeof(void*)*3 + 1, v_wantsRebuild_2527_);
v___x_2541_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2538_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
return v___x_2542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_what_2563_, lean_object* v_baseName_2564_, lean_object* v_optFacet_2565_, lean_object* v_success_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
uint8_t v_success_boxed_2574_; lean_object* v_res_2575_; 
v_success_boxed_2574_ = lean_unbox(v_success_2566_);
v_res_2575_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(v_what_2563_, v_baseName_2564_, v_optFacet_2565_, v_success_boxed_2574_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec_ref(v_what_2563_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object* v___x_2576_, lean_object* v___x_2577_, lean_object* v___f_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v___x_2586_; 
lean_inc_ref(v___y_2579_);
lean_inc_ref(v___y_2583_);
lean_inc(v___y_2582_);
lean_inc(v___y_2581_);
lean_inc(v___y_2580_);
v___x_2586_ = lean_apply_7(v___y_2579_, v___x_2576_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, lean_box(0));
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2599_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_a_2588_ = lean_ctor_get(v___x_2586_, 1);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2590_ = v___x_2586_;
v_isShared_2591_ = v_isSharedCheck_2599_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2599_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2592_ = lean_unsigned_to_nat(0u);
v___x_2593_ = 0;
v___x_2594_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2595_ = l_Lake_Job_mapM___redArg(v___x_2577_, v_a_2587_, v___f_2578_, v___x_2592_, v___x_2593_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___x_2594_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 0, v___x_2595_);
v___x_2597_ = v___x_2590_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_a_2588_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
else
{
lean_object* v_a_2600_; lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec_ref(v___y_2579_);
lean_dec_ref(v___f_2578_);
lean_dec(v___x_2577_);
v_a_2600_ = lean_ctor_get(v___x_2586_, 0);
v_a_2601_ = lean_ctor_get(v___x_2586_, 1);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2586_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_inc(v_a_2600_);
lean_dec(v___x_2586_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2600_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v___x_2609_, lean_object* v___x_2610_, lean_object* v___f_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(v___x_2609_, v___x_2610_, v___f_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec(v___y_2613_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object* v_what_2620_, lean_object* v_optFacet_2621_, lean_object* v_facet_2622_, lean_object* v___x_2623_, lean_object* v_pkg_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v_baseName_2632_; lean_object* v_keyName_2633_; lean_object* v___f_2634_; uint8_t v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___f_2645_; uint8_t v___x_2646_; lean_object* v___x_2647_; 
v_baseName_2632_ = lean_ctor_get(v_pkg_2624_, 1);
v_keyName_2633_ = lean_ctor_get(v_pkg_2624_, 2);
lean_inc(v_optFacet_2621_);
lean_inc_n(v_baseName_2632_, 2);
v___f_2634_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2634_, 0, v_what_2620_);
lean_closure_set(v___f_2634_, 1, v_baseName_2632_);
lean_closure_set(v___f_2634_, 2, v_optFacet_2621_);
v___x_2635_ = 1;
v___x_2636_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2632_, v___x_2635_);
v___x_2637_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2638_ = lean_string_append(v___x_2636_, v___x_2637_);
v___x_2639_ = l_Lake_Name_eraseHead(v_facet_2622_);
v___x_2640_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2639_, v___x_2635_);
v___x_2641_ = lean_string_append(v___x_2638_, v___x_2640_);
lean_dec_ref(v___x_2640_);
lean_inc(v_keyName_2633_);
v___x_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2642_, 0, v_keyName_2633_);
v___x_2643_ = l_Lake_Package_keyword;
v___x_2644_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2642_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
lean_ctor_set(v___x_2644_, 2, v_pkg_2624_);
lean_ctor_set(v___x_2644_, 3, v_optFacet_2621_);
lean_inc(v___x_2623_);
v___f_2645_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2645_, 0, v___x_2644_);
lean_closure_set(v___f_2645_, 1, v___x_2623_);
lean_closure_set(v___f_2645_, 2, v___f_2634_);
v___x_2646_ = 0;
v___x_2647_ = l_Lake_ensureJob___redArg(v___x_2623_, v___f_2645_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2672_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
v_a_2649_ = lean_ctor_get(v___x_2647_, 1);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2651_ = v___x_2647_;
v_isShared_2652_ = v_isSharedCheck_2672_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_inc(v_a_2648_);
lean_dec(v___x_2647_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2672_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v_task_2653_; lean_object* v_kind_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2670_; 
v_task_2653_ = lean_ctor_get(v_a_2648_, 0);
v_kind_2654_ = lean_ctor_get(v_a_2648_, 1);
v_isSharedCheck_2670_ = !lean_is_exclusive(v_a_2648_);
if (v_isSharedCheck_2670_ == 0)
{
lean_object* v_unused_2671_; 
v_unused_2671_ = lean_ctor_get(v_a_2648_, 2);
lean_dec(v_unused_2671_);
v___x_2656_ = v_a_2648_;
v_isShared_2657_ = v_isSharedCheck_2670_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_kind_2654_);
lean_inc(v_task_2653_);
lean_dec(v_a_2648_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2670_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v_registeredJobs_2658_; lean_object* v_job_2660_; 
v_registeredJobs_2658_ = lean_ctor_get(v___y_2629_, 4);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 2, v___x_2641_);
v_job_2660_ = v___x_2656_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_task_2653_);
lean_ctor_set(v_reuseFailAlloc_2669_, 1, v_kind_2654_);
lean_ctor_set(v_reuseFailAlloc_2669_, 2, v___x_2641_);
v_job_2660_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
lean_ctor_set_uint8(v_job_2660_, sizeof(void*)*3, v___x_2646_);
v___x_2661_ = lean_st_ref_take(v_registeredJobs_2658_);
lean_inc_ref(v_job_2660_);
v___x_2662_ = l_Lake_Job_toOpaque___redArg(v_job_2660_);
v___x_2663_ = lean_array_push(v___x_2661_, v___x_2662_);
v___x_2664_ = lean_st_ref_put(v_registeredJobs_2658_, v___x_2663_);
v___x_2665_ = l_Lake_Job_renew___redArg(v_job_2660_);
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2665_);
v___x_2667_ = v___x_2651_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_a_2649_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2641_);
return v___x_2647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object* v_what_2673_, lean_object* v_optFacet_2674_, lean_object* v_facet_2675_, lean_object* v___x_2676_, lean_object* v_pkg_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(v_what_2673_, v_optFacet_2674_, v_facet_2675_, v___x_2676_, v_pkg_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec(v___y_2679_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object* v_facet_2693_, lean_object* v_optFacet_2694_, lean_object* v_what_2695_){
_start:
{
lean_object* v___x_2696_; lean_object* v___f_2697_; lean_object* v___x_2698_; uint8_t v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2696_ = l_Lake_instDataKindUnit;
v___f_2697_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2697_, 0, v_what_2695_);
lean_closure_set(v___f_2697_, 1, v_optFacet_2694_);
lean_closure_set(v___f_2697_, 2, v_facet_2693_);
lean_closure_set(v___f_2697_, 3, v___x_2696_);
v___x_2698_ = l_Lake_Package_keyword;
v___x_2699_ = 1;
v___x_2700_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2701_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2701_, 0, v___x_2698_);
lean_ctor_set(v___x_2701_, 1, v___f_2697_);
lean_ctor_set(v___x_2701_, 2, v___x_2696_);
lean_ctor_set(v___x_2701_, 3, v___x_2700_);
lean_ctor_set_uint8(v___x_2701_, sizeof(void*)*4, v___x_2699_);
lean_ctor_set_uint8(v___x_2701_, sizeof(void*)*4 + 1, v___x_2699_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* v_facet_2702_, lean_object* v_optFacet_2703_, lean_object* v_what_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_){
_start:
{
lean_object* v___x_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2707_ = l_Lake_instDataKindUnit;
v___f_2708_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2708_, 0, v_what_2704_);
lean_closure_set(v___f_2708_, 1, v_optFacet_2703_);
lean_closure_set(v___f_2708_, 2, v_facet_2702_);
lean_closure_set(v___f_2708_, 3, v___x_2707_);
v___x_2709_ = l_Lake_Package_keyword;
v___x_2710_ = 1;
v___x_2711_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2712_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2712_, 0, v___x_2709_);
lean_ctor_set(v___x_2712_, 1, v___f_2708_);
lean_ctor_set(v___x_2712_, 2, v___x_2707_);
lean_ctor_set(v___x_2712_, 3, v___x_2711_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*4, v___x_2710_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*4 + 1, v___x_2710_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* v_baseName_2714_, lean_object* v___x_2715_, uint8_t v_success_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_a_2725_; lean_object* v_a_2726_; 
if (v_success_2716_ == 0)
{
lean_object* v_toBuildConfig_2746_; uint8_t v_verbosity_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v_toBuildConfig_2746_ = lean_ctor_get(v___y_2721_, 0);
v_verbosity_2747_ = lean_ctor_get_uint8(v_toBuildConfig_2746_, sizeof(void*)*4 + 4);
v___x_2748_ = l_Lake_Verbosity_ctorIdx(v_verbosity_2747_);
v___x_2749_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_2750_ = lean_nat_dec_eq(v___x_2748_, v___x_2749_);
lean_dec(v___x_2748_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; 
lean_dec(v___x_2715_);
lean_dec(v_baseName_2714_);
v___x_2751_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_2725_ = v___x_2751_;
v_a_2726_ = v___y_2722_;
goto v___jp_2724_;
}
else
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2752_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2753_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2714_, v___x_2750_);
v___x_2754_ = lean_string_append(v___x_2752_, v___x_2753_);
lean_dec_ref(v___x_2753_);
v___x_2755_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2756_ = lean_string_append(v___x_2754_, v___x_2755_);
v___x_2757_ = l_Lake_Name_eraseHead(v___x_2715_);
v___x_2758_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2757_, v___x_2750_);
v___x_2759_ = lean_string_append(v___x_2756_, v___x_2758_);
lean_dec_ref(v___x_2758_);
v___x_2760_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_2761_ = lean_string_append(v___x_2759_, v___x_2760_);
v_a_2725_ = v___x_2761_;
v_a_2726_ = v___y_2722_;
goto v___jp_2724_;
}
}
else
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_dec(v___x_2715_);
lean_dec(v_baseName_2714_);
v___x_2762_ = lean_box(0);
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
lean_ctor_set(v___x_2763_, 1, v___y_2722_);
return v___x_2763_;
}
v___jp_2724_:
{
lean_object* v_log_2727_; uint8_t v_action_2728_; uint8_t v_wantsRebuild_2729_; lean_object* v_trace_2730_; lean_object* v_buildTime_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2745_; 
v_log_2727_ = lean_ctor_get(v_a_2726_, 0);
v_action_2728_ = lean_ctor_get_uint8(v_a_2726_, sizeof(void*)*3);
v_wantsRebuild_2729_ = lean_ctor_get_uint8(v_a_2726_, sizeof(void*)*3 + 1);
v_trace_2730_ = lean_ctor_get(v_a_2726_, 1);
v_buildTime_2731_ = lean_ctor_get(v_a_2726_, 2);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_a_2726_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2733_ = v_a_2726_;
v_isShared_2734_ = v_isSharedCheck_2745_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_buildTime_2731_);
lean_inc(v_trace_2730_);
lean_inc(v_log_2727_);
lean_dec(v_a_2726_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2745_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2735_ = ((lean_object*)(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0));
v___x_2736_ = lean_string_append(v___x_2735_, v_a_2725_);
lean_dec_ref(v_a_2725_);
v___x_2737_ = 3;
v___x_2738_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*1, v___x_2737_);
v___x_2739_ = lean_array_get_size(v_log_2727_);
v___x_2740_ = lean_array_push(v_log_2727_, v___x_2738_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v___x_2740_);
v___x_2742_ = v___x_2733_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_trace_2730_);
lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_buildTime_2731_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*3, v_action_2728_);
lean_ctor_set_uint8(v_reuseFailAlloc_2744_, sizeof(void*)*3 + 1, v_wantsRebuild_2729_);
v___x_2742_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2743_; 
v___x_2743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2739_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
return v___x_2743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object* v_baseName_2764_, lean_object* v___x_2765_, lean_object* v_success_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
uint8_t v_success_boxed_2774_; lean_object* v_res_2775_; 
v_success_boxed_2774_ = lean_unbox(v_success_2766_);
v_res_2775_ = l_Lake_Package_buildCacheFacetConfig___lam__1(v_baseName_2764_, v___x_2765_, v_success_boxed_2774_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* v___x_2776_, lean_object* v___x_2777_, lean_object* v___x_2778_, lean_object* v_pkg_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_baseName_2787_; lean_object* v_keyName_2788_; lean_object* v___f_2789_; uint8_t v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___f_2800_; uint8_t v___x_2801_; lean_object* v___x_2802_; 
v_baseName_2787_ = lean_ctor_get(v_pkg_2779_, 1);
v_keyName_2788_ = lean_ctor_get(v_pkg_2779_, 2);
lean_inc(v___x_2776_);
lean_inc_n(v_baseName_2787_, 2);
v___f_2789_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2789_, 0, v_baseName_2787_);
lean_closure_set(v___f_2789_, 1, v___x_2776_);
v___x_2790_ = 1;
v___x_2791_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2787_, v___x_2790_);
v___x_2792_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2793_ = lean_string_append(v___x_2791_, v___x_2792_);
v___x_2794_ = l_Lake_Name_eraseHead(v___x_2777_);
v___x_2795_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2794_, v___x_2790_);
v___x_2796_ = lean_string_append(v___x_2793_, v___x_2795_);
lean_dec_ref(v___x_2795_);
lean_inc(v_keyName_2788_);
v___x_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2797_, 0, v_keyName_2788_);
v___x_2798_ = l_Lake_Package_keyword;
v___x_2799_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
lean_ctor_set(v___x_2799_, 2, v_pkg_2779_);
lean_ctor_set(v___x_2799_, 3, v___x_2776_);
lean_inc(v___x_2778_);
v___f_2800_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2800_, 0, v___x_2799_);
lean_closure_set(v___f_2800_, 1, v___x_2778_);
lean_closure_set(v___f_2800_, 2, v___f_2789_);
v___x_2801_ = 0;
v___x_2802_ = l_Lake_ensureJob___redArg(v___x_2778_, v___f_2800_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2827_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_a_2804_ = lean_ctor_get(v___x_2802_, 1);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2806_ = v___x_2802_;
v_isShared_2807_ = v_isSharedCheck_2827_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2827_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v_task_2808_; lean_object* v_kind_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2825_; 
v_task_2808_ = lean_ctor_get(v_a_2803_, 0);
v_kind_2809_ = lean_ctor_get(v_a_2803_, 1);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_a_2803_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v_a_2803_, 2);
lean_dec(v_unused_2826_);
v___x_2811_ = v_a_2803_;
v_isShared_2812_ = v_isSharedCheck_2825_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_kind_2809_);
lean_inc(v_task_2808_);
lean_dec(v_a_2803_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2825_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v_registeredJobs_2813_; lean_object* v_job_2815_; 
v_registeredJobs_2813_ = lean_ctor_get(v___y_2784_, 4);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 2, v___x_2796_);
v_job_2815_ = v___x_2811_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_task_2808_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v_kind_2809_);
lean_ctor_set(v_reuseFailAlloc_2824_, 2, v___x_2796_);
v_job_2815_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2822_; 
lean_ctor_set_uint8(v_job_2815_, sizeof(void*)*3, v___x_2801_);
v___x_2816_ = lean_st_ref_take(v_registeredJobs_2813_);
lean_inc_ref(v_job_2815_);
v___x_2817_ = l_Lake_Job_toOpaque___redArg(v_job_2815_);
v___x_2818_ = lean_array_push(v___x_2816_, v___x_2817_);
v___x_2819_ = lean_st_ref_put(v_registeredJobs_2813_, v___x_2818_);
v___x_2820_ = l_Lake_Job_renew___redArg(v_job_2815_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2820_);
v___x_2822_ = v___x_2806_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v_a_2804_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2796_);
return v___x_2802_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object* v___x_2828_, lean_object* v___x_2829_, lean_object* v___x_2830_, lean_object* v_pkg_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Lake_Package_buildCacheFacetConfig___lam__2(v___x_2828_, v___x_2829_, v___x_2830_, v_pkg_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec(v___y_2833_);
return v_res_2839_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___f_2843_; 
v___x_2840_ = l_Lake_instDataKindUnit;
v___x_2841_ = l_Lake_Package_buildCacheFacet;
v___x_2842_ = l_Lake_Package_optBuildCacheFacet;
v___f_2843_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2843_, 0, v___x_2842_);
lean_closure_set(v___f_2843_, 1, v___x_2841_);
lean_closure_set(v___f_2843_, 2, v___x_2840_);
return v___f_2843_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; lean_object* v___f_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___f_2844_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2845_ = 1;
v___x_2846_ = l_Lake_instDataKindUnit;
v___f_2847_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__0, &l_Lake_Package_buildCacheFacetConfig___closed__0_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__0);
v___x_2848_ = l_Lake_Package_keyword;
v___x_2849_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
lean_ctor_set(v___x_2849_, 1, v___f_2847_);
lean_ctor_set(v___x_2849_, 2, v___x_2846_);
lean_ctor_set(v___x_2849_, 3, v___f_2844_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*4, v___x_2845_);
lean_ctor_set_uint8(v___x_2849_, sizeof(void*)*4 + 1, v___x_2845_);
return v___x_2849_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig(void){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__1, &l_Lake_Package_buildCacheFacetConfig___closed__1_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__1);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* v_pkg_2852_, lean_object* v_dir_2853_, lean_object* v___x_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
uint8_t v_r_2863_; lean_object* v___y_2864_; lean_object* v_a_2868_; lean_object* v___x_2884_; 
lean_inc_ref(v_pkg_2852_);
v___x_2884_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_pkg_2852_, v___y_2859_, v___y_2860_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v_a_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
v_a_2886_ = lean_ctor_get(v___x_2884_, 1);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2884_, 2);
v___x_2887_ = l_Lake_defaultLakeDir;
v___x_2888_ = l_Lake_joinRelative(v_dir_2853_, v___x_2887_);
v___x_2889_ = ((lean_object*)(l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0));
v___x_2890_ = l_Lake_joinRelative(v___x_2888_, v___x_2889_);
v___x_2891_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2852_, v_a_2885_, v___x_2890_, v___x_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v_a_2886_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; uint8_t v___x_2893_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 1);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___x_2891_, 2);
v___x_2893_ = 1;
v_r_2863_ = v___x_2893_;
v___y_2864_ = v_a_2892_;
goto v___jp_2862_;
}
else
{
lean_object* v_a_2894_; 
v_a_2894_ = lean_ctor_get(v___x_2891_, 1);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2891_, 2);
v_a_2868_ = v_a_2894_;
goto v___jp_2867_;
}
}
else
{
lean_object* v_a_2895_; 
lean_dec_ref(v_dir_2853_);
lean_dec_ref(v_pkg_2852_);
v_a_2895_ = lean_ctor_get(v___x_2884_, 1);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2884_, 2);
v_a_2868_ = v_a_2895_;
goto v___jp_2867_;
}
v___jp_2862_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = lean_box(v_r_2863_);
v___x_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set(v___x_2866_, 1, v___y_2864_);
return v___x_2866_;
}
v___jp_2867_:
{
lean_object* v_log_2869_; uint8_t v_action_2870_; uint8_t v_wantsRebuild_2871_; lean_object* v_trace_2872_; lean_object* v_buildTime_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2883_; 
v_log_2869_ = lean_ctor_get(v_a_2868_, 0);
v_action_2870_ = lean_ctor_get_uint8(v_a_2868_, sizeof(void*)*3);
v_wantsRebuild_2871_ = lean_ctor_get_uint8(v_a_2868_, sizeof(void*)*3 + 1);
v_trace_2872_ = lean_ctor_get(v_a_2868_, 1);
v_buildTime_2873_ = lean_ctor_get(v_a_2868_, 2);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_a_2868_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2875_ = v_a_2868_;
v_isShared_2876_ = v_isSharedCheck_2883_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_buildTime_2873_);
lean_inc(v_trace_2872_);
lean_inc(v_log_2869_);
lean_dec(v_a_2868_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2883_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
uint8_t v___x_2877_; uint8_t v___x_2878_; lean_object* v___x_2880_; 
v___x_2877_ = 4;
v___x_2878_ = l_Lake_JobAction_merge(v_action_2870_, v___x_2877_);
if (v_isShared_2876_ == 0)
{
v___x_2880_ = v___x_2875_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_log_2869_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_trace_2872_);
lean_ctor_set(v_reuseFailAlloc_2882_, 2, v_buildTime_2873_);
lean_ctor_set_uint8(v_reuseFailAlloc_2882_, sizeof(void*)*3 + 1, v_wantsRebuild_2871_);
v___x_2880_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
uint8_t v___x_2881_; 
lean_ctor_set_uint8(v___x_2880_, sizeof(void*)*3, v___x_2878_);
v___x_2881_ = 0;
v_r_2863_ = v___x_2881_;
v___y_2864_ = v___x_2880_;
goto v___jp_2862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* v_pkg_2896_, lean_object* v_dir_2897_, lean_object* v___x_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Lake_Package_optBarrelFacetConfig___lam__0(v_pkg_2896_, v_dir_2897_, v___x_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec_ref(v___x_2898_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* v___x_2907_, lean_object* v___f_2908_, lean_object* v___x_2909_, lean_object* v___x_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = l_Lake_Job_async___redArg(v___x_2907_, v___f_2908_, v___x_2909_, v___x_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
v___x_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
lean_ctor_set(v___x_2919_, 1, v___y_2916_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object* v___x_2920_, lean_object* v___f_2921_, lean_object* v___x_2922_, lean_object* v___x_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lake_Package_optBarrelFacetConfig___lam__1(v___x_2920_, v___f_2921_, v___x_2922_, v___x_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec(v___y_2925_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* v___x_2932_, lean_object* v___x_2933_, lean_object* v___x_2934_, lean_object* v_pkg_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_baseName_2943_; lean_object* v_dir_2944_; lean_object* v___f_2945_; uint8_t v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___f_2955_; lean_object* v___x_2956_; 
v_baseName_2943_ = lean_ctor_get(v_pkg_2935_, 1);
lean_inc(v_baseName_2943_);
v_dir_2944_ = lean_ctor_get(v_pkg_2935_, 4);
lean_inc_ref(v_dir_2944_);
v___f_2945_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2945_, 0, v_pkg_2935_);
lean_closure_set(v___f_2945_, 1, v_dir_2944_);
lean_closure_set(v___f_2945_, 2, v___x_2932_);
v___x_2946_ = 1;
v___x_2947_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2943_, v___x_2946_);
v___x_2948_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2949_ = lean_string_append(v___x_2947_, v___x_2948_);
v___x_2950_ = l_Lake_Name_eraseHead(v___x_2933_);
v___x_2951_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2950_, v___x_2946_);
v___x_2952_ = lean_string_append(v___x_2949_, v___x_2951_);
lean_dec_ref(v___x_2951_);
v___x_2953_ = lean_unsigned_to_nat(0u);
v___x_2954_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2934_);
v___f_2955_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2955_, 0, v___x_2934_);
lean_closure_set(v___f_2955_, 1, v___f_2945_);
lean_closure_set(v___f_2955_, 2, v___x_2953_);
lean_closure_set(v___f_2955_, 3, v___x_2954_);
v___x_2956_ = l_Lake_ensureJob___redArg(v___x_2934_, v___f_2955_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2981_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
v_a_2958_ = lean_ctor_get(v___x_2956_, 1);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2960_ = v___x_2956_;
v_isShared_2961_ = v_isSharedCheck_2981_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_inc(v_a_2957_);
lean_dec(v___x_2956_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2981_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v_task_2962_; lean_object* v_kind_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2979_; 
v_task_2962_ = lean_ctor_get(v_a_2957_, 0);
v_kind_2963_ = lean_ctor_get(v_a_2957_, 1);
v_isSharedCheck_2979_ = !lean_is_exclusive(v_a_2957_);
if (v_isSharedCheck_2979_ == 0)
{
lean_object* v_unused_2980_; 
v_unused_2980_ = lean_ctor_get(v_a_2957_, 2);
lean_dec(v_unused_2980_);
v___x_2965_ = v_a_2957_;
v_isShared_2966_ = v_isSharedCheck_2979_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_kind_2963_);
lean_inc(v_task_2962_);
lean_dec(v_a_2957_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2979_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v_registeredJobs_2967_; lean_object* v_job_2969_; 
v_registeredJobs_2967_ = lean_ctor_get(v___y_2940_, 4);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 2, v___x_2952_);
v_job_2969_ = v___x_2965_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_task_2962_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v_kind_2963_);
lean_ctor_set(v_reuseFailAlloc_2978_, 2, v___x_2952_);
v_job_2969_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2976_; 
lean_ctor_set_uint8(v_job_2969_, sizeof(void*)*3, v___x_2946_);
v___x_2970_ = lean_st_ref_take(v_registeredJobs_2967_);
lean_inc_ref(v_job_2969_);
v___x_2971_ = l_Lake_Job_toOpaque___redArg(v_job_2969_);
v___x_2972_ = lean_array_push(v___x_2970_, v___x_2971_);
v___x_2973_ = lean_st_ref_put(v_registeredJobs_2967_, v___x_2972_);
v___x_2974_ = l_Lake_Job_renew___redArg(v_job_2969_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 0, v___x_2974_);
v___x_2976_ = v___x_2960_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2974_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_a_2958_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2952_);
return v___x_2956_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object* v___x_2982_, lean_object* v___x_2983_, lean_object* v___x_2984_, lean_object* v_pkg_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lake_Package_optBarrelFacetConfig___lam__2(v___x_2982_, v___x_2983_, v___x_2984_, v_pkg_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec(v___y_2987_);
return v_res_2993_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___f_2997_; 
v___x_2994_ = l_Lake_instDataKindBool;
v___x_2995_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_2996_ = l_Lake_Reservoir_lakeHeaders;
v___f_2997_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2997_, 0, v___x_2996_);
lean_closure_set(v___f_2997_, 1, v___x_2995_);
lean_closure_set(v___f_2997_, 2, v___x_2994_);
return v___f_2997_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2998_; uint8_t v___x_2999_; lean_object* v___x_3000_; lean_object* v___f_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___f_2998_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_2999_ = 1;
v___x_3000_ = l_Lake_instDataKindBool;
v___f_3001_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__0, &l_Lake_Package_optBarrelFacetConfig___closed__0_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__0);
v___x_3002_ = l_Lake_Package_keyword;
v___x_3003_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
lean_ctor_set(v___x_3003_, 1, v___f_3001_);
lean_ctor_set(v___x_3003_, 2, v___x_3000_);
lean_ctor_set(v___x_3003_, 3, v___f_2998_);
lean_ctor_set_uint8(v___x_3003_, sizeof(void*)*4, v___x_2999_);
lean_ctor_set_uint8(v___x_3003_, sizeof(void*)*4 + 1, v___x_2999_);
return v___x_3003_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig(void){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__1, &l_Lake_Package_optBarrelFacetConfig___closed__1_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__1);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* v_baseName_3006_, lean_object* v___x_3007_, uint8_t v_success_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v_a_3017_; lean_object* v_a_3018_; 
if (v_success_3008_ == 0)
{
lean_object* v_toBuildConfig_3038_; uint8_t v_verbosity_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v_toBuildConfig_3038_ = lean_ctor_get(v___y_3013_, 0);
v_verbosity_3039_ = lean_ctor_get_uint8(v_toBuildConfig_3038_, sizeof(void*)*4 + 4);
v___x_3040_ = l_Lake_Verbosity_ctorIdx(v_verbosity_3039_);
v___x_3041_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_3042_ = lean_nat_dec_eq(v___x_3040_, v___x_3041_);
lean_dec(v___x_3040_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; 
lean_dec(v___x_3007_);
lean_dec(v_baseName_3006_);
v___x_3043_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_3017_ = v___x_3043_;
v_a_3018_ = v___y_3014_;
goto v___jp_3016_;
}
else
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3044_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3045_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3006_, v___x_3042_);
v___x_3046_ = lean_string_append(v___x_3044_, v___x_3045_);
lean_dec_ref(v___x_3045_);
v___x_3047_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3048_ = lean_string_append(v___x_3046_, v___x_3047_);
v___x_3049_ = l_Lake_Name_eraseHead(v___x_3007_);
v___x_3050_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3049_, v___x_3042_);
v___x_3051_ = lean_string_append(v___x_3048_, v___x_3050_);
lean_dec_ref(v___x_3050_);
v___x_3052_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_3053_ = lean_string_append(v___x_3051_, v___x_3052_);
v_a_3017_ = v___x_3053_;
v_a_3018_ = v___y_3014_;
goto v___jp_3016_;
}
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
lean_dec(v___x_3007_);
lean_dec(v_baseName_3006_);
v___x_3054_ = lean_box(0);
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v___y_3014_);
return v___x_3055_;
}
v___jp_3016_:
{
lean_object* v_log_3019_; uint8_t v_action_3020_; uint8_t v_wantsRebuild_3021_; lean_object* v_trace_3022_; lean_object* v_buildTime_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3037_; 
v_log_3019_ = lean_ctor_get(v_a_3018_, 0);
v_action_3020_ = lean_ctor_get_uint8(v_a_3018_, sizeof(void*)*3);
v_wantsRebuild_3021_ = lean_ctor_get_uint8(v_a_3018_, sizeof(void*)*3 + 1);
v_trace_3022_ = lean_ctor_get(v_a_3018_, 1);
v_buildTime_3023_ = lean_ctor_get(v_a_3018_, 2);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_a_3018_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3025_ = v_a_3018_;
v_isShared_3026_ = v_isSharedCheck_3037_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_buildTime_3023_);
lean_inc(v_trace_3022_);
lean_inc(v_log_3019_);
lean_dec(v_a_3018_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3037_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; uint8_t v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3027_ = ((lean_object*)(l_Lake_Package_barrelFacetConfig___lam__1___closed__0));
v___x_3028_ = lean_string_append(v___x_3027_, v_a_3017_);
lean_dec_ref(v_a_3017_);
v___x_3029_ = 3;
v___x_3030_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3030_, 0, v___x_3028_);
lean_ctor_set_uint8(v___x_3030_, sizeof(void*)*1, v___x_3029_);
v___x_3031_ = lean_array_get_size(v_log_3019_);
v___x_3032_ = lean_array_push(v_log_3019_, v___x_3030_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v___x_3032_);
v___x_3034_ = v___x_3025_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_trace_3022_);
lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_buildTime_3023_);
lean_ctor_set_uint8(v_reuseFailAlloc_3036_, sizeof(void*)*3, v_action_3020_);
lean_ctor_set_uint8(v_reuseFailAlloc_3036_, sizeof(void*)*3 + 1, v_wantsRebuild_3021_);
v___x_3034_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3035_; 
v___x_3035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3031_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
return v___x_3035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object* v_baseName_3056_, lean_object* v___x_3057_, lean_object* v_success_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
uint8_t v_success_boxed_3066_; lean_object* v_res_3067_; 
v_success_boxed_3066_ = lean_unbox(v_success_3058_);
v_res_3067_ = l_Lake_Package_barrelFacetConfig___lam__1(v_baseName_3056_, v___x_3057_, v_success_boxed_3066_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* v___x_3068_, lean_object* v___x_3069_, lean_object* v___x_3070_, lean_object* v_pkg_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_baseName_3079_; lean_object* v_keyName_3080_; lean_object* v___f_3081_; uint8_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___f_3092_; uint8_t v___x_3093_; lean_object* v___x_3094_; 
v_baseName_3079_ = lean_ctor_get(v_pkg_3071_, 1);
v_keyName_3080_ = lean_ctor_get(v_pkg_3071_, 2);
lean_inc(v___x_3068_);
lean_inc_n(v_baseName_3079_, 2);
v___f_3081_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3081_, 0, v_baseName_3079_);
lean_closure_set(v___f_3081_, 1, v___x_3068_);
v___x_3082_ = 1;
v___x_3083_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3079_, v___x_3082_);
v___x_3084_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3085_ = lean_string_append(v___x_3083_, v___x_3084_);
v___x_3086_ = l_Lake_Name_eraseHead(v___x_3069_);
v___x_3087_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3086_, v___x_3082_);
v___x_3088_ = lean_string_append(v___x_3085_, v___x_3087_);
lean_dec_ref(v___x_3087_);
lean_inc(v_keyName_3080_);
v___x_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3089_, 0, v_keyName_3080_);
v___x_3090_ = l_Lake_Package_keyword;
v___x_3091_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3089_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
lean_ctor_set(v___x_3091_, 2, v_pkg_3071_);
lean_ctor_set(v___x_3091_, 3, v___x_3068_);
lean_inc(v___x_3070_);
v___f_3092_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3092_, 0, v___x_3091_);
lean_closure_set(v___f_3092_, 1, v___x_3070_);
lean_closure_set(v___f_3092_, 2, v___f_3081_);
v___x_3093_ = 0;
v___x_3094_ = l_Lake_ensureJob___redArg(v___x_3070_, v___f_3092_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3119_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_a_3096_ = lean_ctor_get(v___x_3094_, 1);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3098_ = v___x_3094_;
v_isShared_3099_ = v_isSharedCheck_3119_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3119_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v_task_3100_; lean_object* v_kind_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3117_; 
v_task_3100_ = lean_ctor_get(v_a_3095_, 0);
v_kind_3101_ = lean_ctor_get(v_a_3095_, 1);
v_isSharedCheck_3117_ = !lean_is_exclusive(v_a_3095_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v_a_3095_, 2);
lean_dec(v_unused_3118_);
v___x_3103_ = v_a_3095_;
v_isShared_3104_ = v_isSharedCheck_3117_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_kind_3101_);
lean_inc(v_task_3100_);
lean_dec(v_a_3095_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3117_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v_registeredJobs_3105_; lean_object* v_job_3107_; 
v_registeredJobs_3105_ = lean_ctor_get(v___y_3076_, 4);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 2, v___x_3088_);
v_job_3107_ = v___x_3103_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_task_3100_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_kind_3101_);
lean_ctor_set(v_reuseFailAlloc_3116_, 2, v___x_3088_);
v_job_3107_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3114_; 
lean_ctor_set_uint8(v_job_3107_, sizeof(void*)*3, v___x_3093_);
v___x_3108_ = lean_st_ref_take(v_registeredJobs_3105_);
lean_inc_ref(v_job_3107_);
v___x_3109_ = l_Lake_Job_toOpaque___redArg(v_job_3107_);
v___x_3110_ = lean_array_push(v___x_3108_, v___x_3109_);
v___x_3111_ = lean_st_ref_put(v_registeredJobs_3105_, v___x_3110_);
v___x_3112_ = l_Lake_Job_renew___redArg(v_job_3107_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 0, v___x_3112_);
v___x_3114_ = v___x_3098_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_a_3096_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3088_);
return v___x_3094_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object* v___x_3120_, lean_object* v___x_3121_, lean_object* v___x_3122_, lean_object* v_pkg_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Lake_Package_barrelFacetConfig___lam__2(v___x_3120_, v___x_3121_, v___x_3122_, v_pkg_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec(v___y_3125_);
return v_res_3131_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___f_3135_; 
v___x_3132_ = l_Lake_instDataKindUnit;
v___x_3133_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3134_ = l_Lake_Package_optReservoirBarrelFacet;
v___f_3135_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3135_, 0, v___x_3134_);
lean_closure_set(v___f_3135_, 1, v___x_3133_);
lean_closure_set(v___f_3135_, 2, v___x_3132_);
return v___f_3135_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3136_; uint8_t v___x_3137_; lean_object* v___x_3138_; lean_object* v___f_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___f_3136_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3137_ = 1;
v___x_3138_ = l_Lake_instDataKindUnit;
v___f_3139_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__0, &l_Lake_Package_barrelFacetConfig___closed__0_once, _init_l_Lake_Package_barrelFacetConfig___closed__0);
v___x_3140_ = l_Lake_Package_keyword;
v___x_3141_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
lean_ctor_set(v___x_3141_, 1, v___f_3139_);
lean_ctor_set(v___x_3141_, 2, v___x_3138_);
lean_ctor_set(v___x_3141_, 3, v___f_3136_);
lean_ctor_set_uint8(v___x_3141_, sizeof(void*)*4, v___x_3137_);
lean_ctor_set_uint8(v___x_3141_, sizeof(void*)*4 + 1, v___x_3137_);
return v___x_3141_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig(void){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__1, &l_Lake_Package_barrelFacetConfig___closed__1_once, _init_l_Lake_Package_barrelFacetConfig___closed__1);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object* v_pkg_3143_, lean_object* v_dir_3144_, lean_object* v_buildArchive_3145_, lean_object* v___x_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
uint8_t v_r_3155_; lean_object* v___y_3156_; lean_object* v_a_3160_; lean_object* v___x_3176_; 
lean_inc_ref(v_pkg_3143_);
v___x_3176_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_pkg_3143_, v___y_3152_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v_a_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
v_a_3178_ = lean_ctor_get(v___x_3176_, 1);
lean_inc(v_a_3178_);
lean_dec_ref_known(v___x_3176_, 2);
v___x_3179_ = l_Lake_defaultLakeDir;
v___x_3180_ = l_Lake_joinRelative(v_dir_3144_, v___x_3179_);
v___x_3181_ = l_Lake_joinRelative(v___x_3180_, v_buildArchive_3145_);
v___x_3182_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_3143_, v_a_3177_, v___x_3181_, v___x_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v_a_3178_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; uint8_t v___x_3184_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 1);
lean_inc(v_a_3183_);
lean_dec_ref_known(v___x_3182_, 2);
v___x_3184_ = 1;
v_r_3155_ = v___x_3184_;
v___y_3156_ = v_a_3183_;
goto v___jp_3154_;
}
else
{
lean_object* v_a_3185_; 
v_a_3185_ = lean_ctor_get(v___x_3182_, 1);
lean_inc(v_a_3185_);
lean_dec_ref_known(v___x_3182_, 2);
v_a_3160_ = v_a_3185_;
goto v___jp_3159_;
}
}
else
{
lean_object* v_a_3186_; 
lean_dec_ref(v_buildArchive_3145_);
lean_dec_ref(v_dir_3144_);
lean_dec_ref(v_pkg_3143_);
v_a_3186_ = lean_ctor_get(v___x_3176_, 1);
lean_inc(v_a_3186_);
lean_dec_ref_known(v___x_3176_, 2);
v_a_3160_ = v_a_3186_;
goto v___jp_3159_;
}
v___jp_3154_:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_box(v_r_3155_);
v___x_3158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
lean_ctor_set(v___x_3158_, 1, v___y_3156_);
return v___x_3158_;
}
v___jp_3159_:
{
lean_object* v_log_3161_; uint8_t v_action_3162_; uint8_t v_wantsRebuild_3163_; lean_object* v_trace_3164_; lean_object* v_buildTime_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3175_; 
v_log_3161_ = lean_ctor_get(v_a_3160_, 0);
v_action_3162_ = lean_ctor_get_uint8(v_a_3160_, sizeof(void*)*3);
v_wantsRebuild_3163_ = lean_ctor_get_uint8(v_a_3160_, sizeof(void*)*3 + 1);
v_trace_3164_ = lean_ctor_get(v_a_3160_, 1);
v_buildTime_3165_ = lean_ctor_get(v_a_3160_, 2);
v_isSharedCheck_3175_ = !lean_is_exclusive(v_a_3160_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3167_ = v_a_3160_;
v_isShared_3168_ = v_isSharedCheck_3175_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_buildTime_3165_);
lean_inc(v_trace_3164_);
lean_inc(v_log_3161_);
lean_dec(v_a_3160_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3175_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
uint8_t v___x_3169_; uint8_t v___x_3170_; lean_object* v___x_3172_; 
v___x_3169_ = 4;
v___x_3170_ = l_Lake_JobAction_merge(v_action_3162_, v___x_3169_);
if (v_isShared_3168_ == 0)
{
v___x_3172_ = v___x_3167_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_log_3161_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v_trace_3164_);
lean_ctor_set(v_reuseFailAlloc_3174_, 2, v_buildTime_3165_);
lean_ctor_set_uint8(v_reuseFailAlloc_3174_, sizeof(void*)*3 + 1, v_wantsRebuild_3163_);
v___x_3172_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
uint8_t v___x_3173_; 
lean_ctor_set_uint8(v___x_3172_, sizeof(void*)*3, v___x_3170_);
v___x_3173_ = 0;
v_r_3155_ = v___x_3173_;
v___y_3156_ = v___x_3172_;
goto v___jp_3154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object* v_pkg_3187_, lean_object* v_dir_3188_, lean_object* v_buildArchive_3189_, lean_object* v___x_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_res_3198_; 
v_res_3198_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(v_pkg_3187_, v_dir_3188_, v_buildArchive_3189_, v___x_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec_ref(v___x_3190_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object* v___x_3199_, lean_object* v___x_3200_, lean_object* v___x_3201_, lean_object* v___x_3202_, lean_object* v_pkg_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v_baseName_3211_; lean_object* v_dir_3212_; lean_object* v_buildArchive_3213_; lean_object* v___f_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___f_3223_; lean_object* v___x_3224_; 
v_baseName_3211_ = lean_ctor_get(v_pkg_3203_, 1);
lean_inc(v_baseName_3211_);
v_dir_3212_ = lean_ctor_get(v_pkg_3203_, 4);
lean_inc_ref(v_dir_3212_);
v_buildArchive_3213_ = lean_ctor_get(v_pkg_3203_, 21);
lean_inc_ref(v_buildArchive_3213_);
v___f_3214_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3214_, 0, v_pkg_3203_);
lean_closure_set(v___f_3214_, 1, v_dir_3212_);
lean_closure_set(v___f_3214_, 2, v_buildArchive_3213_);
lean_closure_set(v___f_3214_, 3, v___x_3199_);
v___x_3215_ = 1;
v___x_3216_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3211_, v___x_3215_);
v___x_3217_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3218_ = lean_string_append(v___x_3216_, v___x_3217_);
v___x_3219_ = l_Lake_Name_eraseHead(v___x_3200_);
v___x_3220_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3219_, v___x_3215_);
v___x_3221_ = lean_string_append(v___x_3218_, v___x_3220_);
lean_dec_ref(v___x_3220_);
v___x_3222_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_3201_);
v___f_3223_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_3223_, 0, v___x_3201_);
lean_closure_set(v___f_3223_, 1, v___f_3214_);
lean_closure_set(v___f_3223_, 2, v___x_3202_);
lean_closure_set(v___f_3223_, 3, v___x_3222_);
v___x_3224_ = l_Lake_ensureJob___redArg(v___x_3201_, v___f_3223_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3249_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
v_a_3226_ = lean_ctor_get(v___x_3224_, 1);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3228_ = v___x_3224_;
v_isShared_3229_ = v_isSharedCheck_3249_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_inc(v_a_3225_);
lean_dec(v___x_3224_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3249_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_task_3230_; lean_object* v_kind_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3247_; 
v_task_3230_ = lean_ctor_get(v_a_3225_, 0);
v_kind_3231_ = lean_ctor_get(v_a_3225_, 1);
v_isSharedCheck_3247_ = !lean_is_exclusive(v_a_3225_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; 
v_unused_3248_ = lean_ctor_get(v_a_3225_, 2);
lean_dec(v_unused_3248_);
v___x_3233_ = v_a_3225_;
v_isShared_3234_ = v_isSharedCheck_3247_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_kind_3231_);
lean_inc(v_task_3230_);
lean_dec(v_a_3225_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3247_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v_registeredJobs_3235_; lean_object* v_job_3237_; 
v_registeredJobs_3235_ = lean_ctor_get(v___y_3208_, 4);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 2, v___x_3221_);
v_job_3237_ = v___x_3233_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_task_3230_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_kind_3231_);
lean_ctor_set(v_reuseFailAlloc_3246_, 2, v___x_3221_);
v_job_3237_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
lean_ctor_set_uint8(v_job_3237_, sizeof(void*)*3, v___x_3215_);
v___x_3238_ = lean_st_ref_take(v_registeredJobs_3235_);
lean_inc_ref(v_job_3237_);
v___x_3239_ = l_Lake_Job_toOpaque___redArg(v_job_3237_);
v___x_3240_ = lean_array_push(v___x_3238_, v___x_3239_);
v___x_3241_ = lean_st_ref_put(v_registeredJobs_3235_, v___x_3240_);
v___x_3242_ = l_Lake_Job_renew___redArg(v_job_3237_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3242_);
v___x_3244_ = v___x_3228_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v_a_3226_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3221_);
return v___x_3224_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_3250_, lean_object* v___x_3251_, lean_object* v___x_3252_, lean_object* v___x_3253_, lean_object* v_pkg_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(v___x_3250_, v___x_3251_, v___x_3252_, v___x_3253_, v_pkg_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec(v___y_3256_);
return v_res_3262_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___f_3269_; 
v___x_3265_ = lean_unsigned_to_nat(0u);
v___x_3266_ = l_Lake_instDataKindBool;
v___x_3267_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3268_ = ((lean_object*)(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0));
v___f_3269_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed), 12, 4);
lean_closure_set(v___f_3269_, 0, v___x_3268_);
lean_closure_set(v___f_3269_, 1, v___x_3267_);
lean_closure_set(v___f_3269_, 2, v___x_3266_);
lean_closure_set(v___f_3269_, 3, v___x_3265_);
return v___f_3269_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3270_; uint8_t v___x_3271_; lean_object* v___x_3272_; lean_object* v___f_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___f_3270_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_3271_ = 1;
v___x_3272_ = l_Lake_instDataKindBool;
v___f_3273_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__1, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1);
v___x_3274_ = l_Lake_Package_keyword;
v___x_3275_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
lean_ctor_set(v___x_3275_, 1, v___f_3273_);
lean_ctor_set(v___x_3275_, 2, v___x_3272_);
lean_ctor_set(v___x_3275_, 3, v___f_3270_);
lean_ctor_set_uint8(v___x_3275_, sizeof(void*)*4, v___x_3271_);
lean_ctor_set_uint8(v___x_3275_, sizeof(void*)*4 + 1, v___x_3271_);
return v___x_3275_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__2, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* v_baseName_3278_, lean_object* v___x_3279_, uint8_t v_success_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v_a_3289_; lean_object* v_a_3290_; 
if (v_success_3280_ == 0)
{
lean_object* v_toBuildConfig_3310_; uint8_t v_verbosity_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v_toBuildConfig_3310_ = lean_ctor_get(v___y_3285_, 0);
v_verbosity_3311_ = lean_ctor_get_uint8(v_toBuildConfig_3310_, sizeof(void*)*4 + 4);
v___x_3312_ = l_Lake_Verbosity_ctorIdx(v_verbosity_3311_);
v___x_3313_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0);
v___x_3314_ = lean_nat_dec_eq(v___x_3312_, v___x_3313_);
lean_dec(v___x_3312_);
if (v___x_3314_ == 0)
{
lean_object* v___x_3315_; 
lean_dec(v___x_3279_);
lean_dec(v_baseName_3278_);
v___x_3315_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v_a_3289_ = v___x_3315_;
v_a_3290_ = v___y_3286_;
goto v___jp_3288_;
}
else
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3316_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3317_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3278_, v___x_3314_);
v___x_3318_ = lean_string_append(v___x_3316_, v___x_3317_);
lean_dec_ref(v___x_3317_);
v___x_3319_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3320_ = lean_string_append(v___x_3318_, v___x_3319_);
v___x_3321_ = l_Lake_Name_eraseHead(v___x_3279_);
v___x_3322_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3321_, v___x_3314_);
v___x_3323_ = lean_string_append(v___x_3320_, v___x_3322_);
lean_dec_ref(v___x_3322_);
v___x_3324_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__4));
v___x_3325_ = lean_string_append(v___x_3323_, v___x_3324_);
v_a_3289_ = v___x_3325_;
v_a_3290_ = v___y_3286_;
goto v___jp_3288_;
}
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
lean_dec(v___x_3279_);
lean_dec(v_baseName_3278_);
v___x_3326_ = lean_box(0);
v___x_3327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
lean_ctor_set(v___x_3327_, 1, v___y_3286_);
return v___x_3327_;
}
v___jp_3288_:
{
lean_object* v_log_3291_; uint8_t v_action_3292_; uint8_t v_wantsRebuild_3293_; lean_object* v_trace_3294_; lean_object* v_buildTime_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3309_; 
v_log_3291_ = lean_ctor_get(v_a_3290_, 0);
v_action_3292_ = lean_ctor_get_uint8(v_a_3290_, sizeof(void*)*3);
v_wantsRebuild_3293_ = lean_ctor_get_uint8(v_a_3290_, sizeof(void*)*3 + 1);
v_trace_3294_ = lean_ctor_get(v_a_3290_, 1);
v_buildTime_3295_ = lean_ctor_get(v_a_3290_, 2);
v_isSharedCheck_3309_ = !lean_is_exclusive(v_a_3290_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3297_ = v_a_3290_;
v_isShared_3298_ = v_isSharedCheck_3309_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_buildTime_3295_);
lean_inc(v_trace_3294_);
lean_inc(v_log_3291_);
lean_dec(v_a_3290_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3309_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; uint8_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3306_; 
v___x_3299_ = ((lean_object*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0));
v___x_3300_ = lean_string_append(v___x_3299_, v_a_3289_);
lean_dec_ref(v_a_3289_);
v___x_3301_ = 3;
v___x_3302_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3302_, 0, v___x_3300_);
lean_ctor_set_uint8(v___x_3302_, sizeof(void*)*1, v___x_3301_);
v___x_3303_ = lean_array_get_size(v_log_3291_);
v___x_3304_ = lean_array_push(v_log_3291_, v___x_3302_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3304_);
v___x_3306_ = v___x_3297_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v___x_3304_);
lean_ctor_set(v_reuseFailAlloc_3308_, 1, v_trace_3294_);
lean_ctor_set(v_reuseFailAlloc_3308_, 2, v_buildTime_3295_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, sizeof(void*)*3, v_action_3292_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, sizeof(void*)*3 + 1, v_wantsRebuild_3293_);
v___x_3306_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
lean_object* v___x_3307_; 
v___x_3307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3303_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
return v___x_3307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object* v_baseName_3328_, lean_object* v___x_3329_, lean_object* v_success_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
uint8_t v_success_boxed_3338_; lean_object* v_res_3339_; 
v_success_boxed_3338_ = lean_unbox(v_success_3330_);
v_res_3339_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(v_baseName_3328_, v___x_3329_, v_success_boxed_3338_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* v___x_3340_, lean_object* v___x_3341_, lean_object* v___x_3342_, lean_object* v_pkg_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_baseName_3351_; lean_object* v_keyName_3352_; lean_object* v___f_3353_; uint8_t v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___f_3364_; uint8_t v___x_3365_; lean_object* v___x_3366_; 
v_baseName_3351_ = lean_ctor_get(v_pkg_3343_, 1);
v_keyName_3352_ = lean_ctor_get(v_pkg_3343_, 2);
lean_inc(v___x_3340_);
lean_inc_n(v_baseName_3351_, 2);
v___f_3353_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3353_, 0, v_baseName_3351_);
lean_closure_set(v___f_3353_, 1, v___x_3340_);
v___x_3354_ = 1;
v___x_3355_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3351_, v___x_3354_);
v___x_3356_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3357_ = lean_string_append(v___x_3355_, v___x_3356_);
v___x_3358_ = l_Lake_Name_eraseHead(v___x_3341_);
v___x_3359_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3358_, v___x_3354_);
v___x_3360_ = lean_string_append(v___x_3357_, v___x_3359_);
lean_dec_ref(v___x_3359_);
lean_inc(v_keyName_3352_);
v___x_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3361_, 0, v_keyName_3352_);
v___x_3362_ = l_Lake_Package_keyword;
v___x_3363_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3361_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
lean_ctor_set(v___x_3363_, 2, v_pkg_3343_);
lean_ctor_set(v___x_3363_, 3, v___x_3340_);
lean_inc(v___x_3342_);
v___f_3364_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3364_, 0, v___x_3363_);
lean_closure_set(v___f_3364_, 1, v___x_3342_);
lean_closure_set(v___f_3364_, 2, v___f_3353_);
v___x_3365_ = 0;
v___x_3366_ = l_Lake_ensureJob___redArg(v___x_3342_, v___f_3364_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3391_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
v_a_3368_ = lean_ctor_get(v___x_3366_, 1);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3370_ = v___x_3366_;
v_isShared_3371_ = v_isSharedCheck_3391_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_inc(v_a_3367_);
lean_dec(v___x_3366_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3391_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v_task_3372_; lean_object* v_kind_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3389_; 
v_task_3372_ = lean_ctor_get(v_a_3367_, 0);
v_kind_3373_ = lean_ctor_get(v_a_3367_, 1);
v_isSharedCheck_3389_ = !lean_is_exclusive(v_a_3367_);
if (v_isSharedCheck_3389_ == 0)
{
lean_object* v_unused_3390_; 
v_unused_3390_ = lean_ctor_get(v_a_3367_, 2);
lean_dec(v_unused_3390_);
v___x_3375_ = v_a_3367_;
v_isShared_3376_ = v_isSharedCheck_3389_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_kind_3373_);
lean_inc(v_task_3372_);
lean_dec(v_a_3367_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3389_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v_registeredJobs_3377_; lean_object* v_job_3379_; 
v_registeredJobs_3377_ = lean_ctor_get(v___y_3348_, 4);
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 2, v___x_3360_);
v_job_3379_ = v___x_3375_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_task_3372_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_kind_3373_);
lean_ctor_set(v_reuseFailAlloc_3388_, 2, v___x_3360_);
v_job_3379_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3386_; 
lean_ctor_set_uint8(v_job_3379_, sizeof(void*)*3, v___x_3365_);
v___x_3380_ = lean_st_ref_take(v_registeredJobs_3377_);
lean_inc_ref(v_job_3379_);
v___x_3381_ = l_Lake_Job_toOpaque___redArg(v_job_3379_);
v___x_3382_ = lean_array_push(v___x_3380_, v___x_3381_);
v___x_3383_ = lean_st_ref_put(v_registeredJobs_3377_, v___x_3382_);
v___x_3384_ = l_Lake_Job_renew___redArg(v_job_3379_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3384_);
v___x_3386_ = v___x_3370_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v_a_3368_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3360_);
return v___x_3366_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_3392_, lean_object* v___x_3393_, lean_object* v___x_3394_, lean_object* v_pkg_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(v___x_3392_, v___x_3393_, v___x_3394_, v_pkg_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec(v___y_3397_);
return v_res_3403_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___f_3407_; 
v___x_3404_ = l_Lake_instDataKindUnit;
v___x_3405_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3406_ = l_Lake_Package_optGitHubReleaseFacet;
v___f_3407_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3407_, 0, v___x_3406_);
lean_closure_set(v___f_3407_, 1, v___x_3405_);
lean_closure_set(v___f_3407_, 2, v___x_3404_);
return v___f_3407_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3408_; uint8_t v___x_3409_; lean_object* v___x_3410_; lean_object* v___f_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___f_3408_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3409_ = 1;
v___x_3410_ = l_Lake_instDataKindUnit;
v___f_3411_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__0, &l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0);
v___x_3412_ = l_Lake_Package_keyword;
v___x_3413_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v___f_3411_);
lean_ctor_set(v___x_3413_, 2, v___x_3410_);
lean_ctor_set(v___x_3413_, 3, v___f_3408_);
lean_ctor_set_uint8(v___x_3413_, sizeof(void*)*4, v___x_3409_);
lean_ctor_set_uint8(v___x_3413_, sizeof(void*)*4 + 1, v___x_3409_);
return v___x_3413_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_3414_; 
v___x_3414_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__1, &l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* v_build_3415_, uint8_t v_x_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_log_3424_; uint8_t v_action_3425_; uint8_t v_wantsRebuild_3426_; lean_object* v_buildTime_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3436_; 
v_log_3424_ = lean_ctor_get(v___y_3422_, 0);
v_action_3425_ = lean_ctor_get_uint8(v___y_3422_, sizeof(void*)*3);
v_wantsRebuild_3426_ = lean_ctor_get_uint8(v___y_3422_, sizeof(void*)*3 + 1);
v_buildTime_3427_ = lean_ctor_get(v___y_3422_, 2);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___y_3422_);
if (v_isSharedCheck_3436_ == 0)
{
lean_object* v_unused_3437_; 
v_unused_3437_ = lean_ctor_get(v___y_3422_, 1);
lean_dec(v_unused_3437_);
v___x_3429_ = v___y_3422_;
v_isShared_3430_ = v_isSharedCheck_3436_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_buildTime_3427_);
lean_inc(v_log_3424_);
lean_dec(v___y_3422_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3436_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; lean_object* v___x_3433_; 
v___x_3431_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 1, v___x_3431_);
v___x_3433_ = v___x_3429_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_log_3424_);
lean_ctor_set(v_reuseFailAlloc_3435_, 1, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3435_, 2, v_buildTime_3427_);
lean_ctor_set_uint8(v_reuseFailAlloc_3435_, sizeof(void*)*3, v_action_3425_);
lean_ctor_set_uint8(v_reuseFailAlloc_3435_, sizeof(void*)*3 + 1, v_wantsRebuild_3426_);
v___x_3433_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
lean_object* v___x_3434_; 
lean_inc_ref(v___y_3421_);
lean_inc(v___y_3420_);
lean_inc(v___y_3419_);
lean_inc(v___y_3418_);
v___x_3434_ = lean_apply_7(v_build_3415_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___x_3433_, lean_box(0));
return v___x_3434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* v_build_3438_, lean_object* v_x_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
uint8_t v_x_1603__boxed_3447_; lean_object* v_res_3448_; 
v_x_1603__boxed_3447_ = lean_unbox(v_x_3439_);
v_res_3448_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(v_build_3438_, v_x_1603__boxed_3447_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec(v___y_3441_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* v_self_3449_, lean_object* v_build_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_){
_start:
{
lean_object* v_wsIdx_3458_; lean_object* v___x_3459_; uint8_t v___x_3460_; 
v_wsIdx_3458_ = lean_ctor_get(v_self_3449_, 0);
v___x_3459_ = lean_unsigned_to_nat(0u);
v___x_3460_ = lean_nat_dec_eq(v_wsIdx_3458_, v___x_3459_);
if (v___x_3460_ == 0)
{
lean_object* v___f_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___f_3461_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3461_, 0, v_build_3450_);
v___x_3462_ = lean_box(0);
lean_inc_ref(v_a_3451_);
v___x_3463_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3449_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3474_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
v_a_3465_ = lean_ctor_get(v___x_3463_, 1);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3467_ = v___x_3463_;
v_isShared_3468_ = v_isSharedCheck_3474_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_inc(v_a_3464_);
lean_dec(v___x_3463_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3474_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3472_; 
v___x_3469_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3470_ = l_Lake_Job_bindM___redArg(v___x_3462_, v_a_3464_, v___f_3461_, v___x_3459_, v___x_3460_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v___x_3469_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3470_);
v___x_3472_ = v___x_3467_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v_a_3465_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec_ref(v___f_3461_);
lean_dec_ref(v_a_3451_);
v_a_3475_ = lean_ctor_get(v___x_3463_, 0);
v_a_3476_ = lean_ctor_get(v___x_3463_, 1);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3463_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_inc(v_a_3475_);
lean_dec(v___x_3463_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3475_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
else
{
uint8_t v___x_3484_; uint8_t v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec_ref(v_self_3449_);
v___x_3484_ = 0;
v___x_3485_ = 0;
v___x_3486_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3487_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3487_, 0, v_a_3456_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
lean_ctor_set(v___x_3487_, 2, v___x_3459_);
lean_ctor_set_uint8(v___x_3487_, sizeof(void*)*3, v___x_3484_);
lean_ctor_set_uint8(v___x_3487_, sizeof(void*)*3 + 1, v___x_3485_);
lean_inc_ref(v_a_3455_);
lean_inc(v_a_3454_);
lean_inc(v_a_3453_);
lean_inc(v_a_3452_);
v___x_3488_ = lean_apply_7(v_build_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v___x_3487_, lean_box(0));
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3498_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 1);
v_a_3490_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3492_ = v___x_3488_;
v_isShared_3493_ = v_isSharedCheck_3498_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3489_);
lean_inc(v_a_3490_);
lean_dec(v___x_3488_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3498_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v_log_3494_; lean_object* v___x_3496_; 
v_log_3494_ = lean_ctor_get(v_a_3489_, 0);
lean_inc_ref(v_log_3494_);
lean_dec(v_a_3489_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 1, v_log_3494_);
v___x_3496_ = v___x_3492_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3490_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_log_3494_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
else
{
lean_object* v_a_3499_; lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3508_; 
v_a_3499_ = lean_ctor_get(v___x_3488_, 1);
v_a_3500_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3502_ = v___x_3488_;
v_isShared_3503_ = v_isSharedCheck_3508_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3499_);
lean_inc(v_a_3500_);
lean_dec(v___x_3488_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3508_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v_log_3504_; lean_object* v___x_3506_; 
v_log_3504_ = lean_ctor_get(v_a_3499_, 0);
lean_inc_ref(v_log_3504_);
lean_dec(v_a_3499_);
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 1, v_log_3504_);
v___x_3506_ = v___x_3502_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3500_);
lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_log_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___boxed(lean_object* v_self_3509_, lean_object* v_build_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3509_, v_build_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
lean_dec_ref(v_a_3515_);
lean_dec(v_a_3514_);
lean_dec(v_a_3513_);
lean_dec(v_a_3512_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* v_00_u03b1_3519_, lean_object* v_self_3520_, lean_object* v_build_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3520_, v_build_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___boxed(lean_object* v_00_u03b1_3530_, lean_object* v_self_3531_, lean_object* v_build_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lake_Package_afterBuildCacheAsync(v_00_u03b1_3530_, v_self_3531_, v_build_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_);
lean_dec_ref(v_a_3537_);
lean_dec(v_a_3536_);
lean_dec(v_a_3535_);
lean_dec(v_a_3534_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* v_build_3541_, uint8_t v_x_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v_log_3550_; uint8_t v_action_3551_; uint8_t v_wantsRebuild_3552_; lean_object* v_buildTime_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3562_; 
v_log_3550_ = lean_ctor_get(v___y_3548_, 0);
v_action_3551_ = lean_ctor_get_uint8(v___y_3548_, sizeof(void*)*3);
v_wantsRebuild_3552_ = lean_ctor_get_uint8(v___y_3548_, sizeof(void*)*3 + 1);
v_buildTime_3553_ = lean_ctor_get(v___y_3548_, 2);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___y_3548_);
if (v_isSharedCheck_3562_ == 0)
{
lean_object* v_unused_3563_; 
v_unused_3563_ = lean_ctor_get(v___y_3548_, 1);
lean_dec(v_unused_3563_);
v___x_3555_ = v___y_3548_;
v_isShared_3556_ = v_isSharedCheck_3562_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_buildTime_3553_);
lean_inc(v_log_3550_);
lean_dec(v___y_3548_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3562_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3557_; lean_object* v___x_3559_; 
v___x_3557_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 1, v___x_3557_);
v___x_3559_ = v___x_3555_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_log_3550_);
lean_ctor_set(v_reuseFailAlloc_3561_, 1, v___x_3557_);
lean_ctor_set(v_reuseFailAlloc_3561_, 2, v_buildTime_3553_);
lean_ctor_set_uint8(v_reuseFailAlloc_3561_, sizeof(void*)*3, v_action_3551_);
lean_ctor_set_uint8(v_reuseFailAlloc_3561_, sizeof(void*)*3 + 1, v_wantsRebuild_3552_);
v___x_3559_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
lean_object* v___x_3560_; 
lean_inc_ref(v___y_3547_);
lean_inc(v___y_3546_);
lean_inc(v___y_3545_);
lean_inc(v___y_3544_);
v___x_3560_ = lean_apply_7(v_build_3541_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___x_3559_, lean_box(0));
return v___x_3560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* v_build_3564_, lean_object* v_x_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
uint8_t v_x_1633__boxed_3573_; lean_object* v_res_3574_; 
v_x_1633__boxed_3573_ = lean_unbox(v_x_3565_);
v_res_3574_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(v_build_3564_, v_x_1633__boxed_3573_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec(v___y_3567_);
return v_res_3574_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* v_self_3575_, lean_object* v_build_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v_wsIdx_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; lean_object* v___x_3587_; 
v_wsIdx_3584_ = lean_ctor_get(v_self_3575_, 0);
v___x_3585_ = lean_unsigned_to_nat(0u);
v___x_3586_ = lean_nat_dec_eq(v_wsIdx_3584_, v___x_3585_);
v___x_3587_ = lean_box(0);
if (v___x_3586_ == 0)
{
lean_object* v___f_3588_; lean_object* v___x_3589_; 
v___f_3588_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3588_, 0, v_build_3576_);
lean_inc_ref(v_a_3577_);
v___x_3589_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3575_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3600_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
v_a_3591_ = lean_ctor_get(v___x_3589_, 1);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3593_ = v___x_3589_;
v_isShared_3594_ = v_isSharedCheck_3600_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_inc(v_a_3590_);
lean_dec(v___x_3589_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3600_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3598_; 
v___x_3595_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3596_ = l_Lake_Job_mapM___redArg(v___x_3587_, v_a_3590_, v___f_3588_, v___x_3585_, v___x_3586_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v___x_3595_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v___x_3596_);
v___x_3598_ = v___x_3593_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3596_);
lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_a_3591_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
else
{
lean_object* v_a_3601_; lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_dec_ref(v___f_3588_);
lean_dec_ref(v_a_3577_);
v_a_3601_ = lean_ctor_get(v___x_3589_, 0);
v_a_3602_ = lean_ctor_get(v___x_3589_, 1);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3589_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_inc(v_a_3601_);
lean_dec(v___x_3589_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3601_);
lean_ctor_set(v_reuseFailAlloc_3608_, 1, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
else
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
lean_dec_ref(v_self_3575_);
v___x_3610_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_3611_ = l_Lake_Job_async___redArg(v___x_3587_, v_build_3576_, v___x_3585_, v___x_3610_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
v___x_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
lean_ctor_set(v___x_3612_, 1, v_a_3582_);
return v___x_3612_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___boxed(lean_object* v_self_3613_, lean_object* v_build_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3613_, v_build_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_);
lean_dec_ref(v_a_3619_);
lean_dec(v_a_3618_);
lean_dec(v_a_3617_);
lean_dec(v_a_3616_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* v_00_u03b1_3623_, lean_object* v_self_3624_, lean_object* v_build_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3624_, v_build_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___boxed(lean_object* v_00_u03b1_3634_, lean_object* v_self_3635_, lean_object* v_build_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_Lake_Package_afterBuildCacheSync(v_00_u03b1_3634_, v_self_3635_, v_build_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_);
lean_dec_ref(v_a_3641_);
lean_dec(v_a_3640_);
lean_dec(v_a_3639_);
lean_dec(v_a_3638_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(lean_object* v_k_3645_, lean_object* v_v_3646_, lean_object* v_t_3647_){
_start:
{
if (lean_obj_tag(v_t_3647_) == 0)
{
lean_object* v_size_3648_; lean_object* v_k_3649_; lean_object* v_v_3650_; lean_object* v_l_3651_; lean_object* v_r_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3932_; 
v_size_3648_ = lean_ctor_get(v_t_3647_, 0);
v_k_3649_ = lean_ctor_get(v_t_3647_, 1);
v_v_3650_ = lean_ctor_get(v_t_3647_, 2);
v_l_3651_ = lean_ctor_get(v_t_3647_, 3);
v_r_3652_ = lean_ctor_get(v_t_3647_, 4);
v_isSharedCheck_3932_ = !lean_is_exclusive(v_t_3647_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3654_ = v_t_3647_;
v_isShared_3655_ = v_isSharedCheck_3932_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_r_3652_);
lean_inc(v_l_3651_);
lean_inc(v_v_3650_);
lean_inc(v_k_3649_);
lean_inc(v_size_3648_);
lean_dec(v_t_3647_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3932_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
uint8_t v___x_3656_; 
v___x_3656_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3645_, v_k_3649_);
switch(v___x_3656_)
{
case 0:
{
lean_object* v_impl_3657_; lean_object* v___x_3658_; 
lean_dec(v_size_3648_);
v_impl_3657_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3645_, v_v_3646_, v_l_3651_);
v___x_3658_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3652_) == 0)
{
lean_object* v_size_3659_; lean_object* v_size_3660_; lean_object* v_k_3661_; lean_object* v_v_3662_; lean_object* v_l_3663_; lean_object* v_r_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; 
v_size_3659_ = lean_ctor_get(v_r_3652_, 0);
v_size_3660_ = lean_ctor_get(v_impl_3657_, 0);
lean_inc(v_size_3660_);
v_k_3661_ = lean_ctor_get(v_impl_3657_, 1);
lean_inc(v_k_3661_);
v_v_3662_ = lean_ctor_get(v_impl_3657_, 2);
lean_inc(v_v_3662_);
v_l_3663_ = lean_ctor_get(v_impl_3657_, 3);
lean_inc(v_l_3663_);
v_r_3664_ = lean_ctor_get(v_impl_3657_, 4);
lean_inc(v_r_3664_);
v___x_3665_ = lean_unsigned_to_nat(3u);
v___x_3666_ = lean_nat_mul(v___x_3665_, v_size_3659_);
v___x_3667_ = lean_nat_dec_lt(v___x_3666_, v_size_3660_);
lean_dec(v___x_3666_);
if (v___x_3667_ == 0)
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3671_; 
lean_dec(v_r_3664_);
lean_dec(v_l_3663_);
lean_dec(v_v_3662_);
lean_dec(v_k_3661_);
v___x_3668_ = lean_nat_add(v___x_3658_, v_size_3660_);
lean_dec(v_size_3660_);
v___x_3669_ = lean_nat_add(v___x_3668_, v_size_3659_);
lean_dec(v___x_3668_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 3, v_impl_3657_);
lean_ctor_set(v___x_3654_, 0, v___x_3669_);
v___x_3671_ = v___x_3654_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3672_, 1, v_k_3649_);
lean_ctor_set(v_reuseFailAlloc_3672_, 2, v_v_3650_);
lean_ctor_set(v_reuseFailAlloc_3672_, 3, v_impl_3657_);
lean_ctor_set(v_reuseFailAlloc_3672_, 4, v_r_3652_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
else
{
lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3738_; 
v_isSharedCheck_3738_ = !lean_is_exclusive(v_impl_3657_);
if (v_isSharedCheck_3738_ == 0)
{
lean_object* v_unused_3739_; lean_object* v_unused_3740_; lean_object* v_unused_3741_; lean_object* v_unused_3742_; lean_object* v_unused_3743_; 
v_unused_3739_ = lean_ctor_get(v_impl_3657_, 4);
lean_dec(v_unused_3739_);
v_unused_3740_ = lean_ctor_get(v_impl_3657_, 3);
lean_dec(v_unused_3740_);
v_unused_3741_ = lean_ctor_get(v_impl_3657_, 2);
lean_dec(v_unused_3741_);
v_unused_3742_ = lean_ctor_get(v_impl_3657_, 1);
lean_dec(v_unused_3742_);
v_unused_3743_ = lean_ctor_get(v_impl_3657_, 0);
lean_dec(v_unused_3743_);
v___x_3674_ = v_impl_3657_;
v_isShared_3675_ = v_isSharedCheck_3738_;
goto v_resetjp_3673_;
}
else
{
lean_dec(v_impl_3657_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3738_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v_size_3676_; lean_object* v_size_3677_; lean_object* v_k_3678_; lean_object* v_v_3679_; lean_object* v_l_3680_; lean_object* v_r_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v_size_3676_ = lean_ctor_get(v_l_3663_, 0);
v_size_3677_ = lean_ctor_get(v_r_3664_, 0);
v_k_3678_ = lean_ctor_get(v_r_3664_, 1);
v_v_3679_ = lean_ctor_get(v_r_3664_, 2);
v_l_3680_ = lean_ctor_get(v_r_3664_, 3);
v_r_3681_ = lean_ctor_get(v_r_3664_, 4);
v___x_3682_ = lean_unsigned_to_nat(2u);
v___x_3683_ = lean_nat_mul(v___x_3682_, v_size_3676_);
v___x_3684_ = lean_nat_dec_lt(v_size_3677_, v___x_3683_);
lean_dec(v___x_3683_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3713_; 
lean_inc(v_r_3681_);
lean_inc(v_l_3680_);
lean_inc(v_v_3679_);
lean_inc(v_k_3678_);
v_isSharedCheck_3713_ = !lean_is_exclusive(v_r_3664_);
if (v_isSharedCheck_3713_ == 0)
{
lean_object* v_unused_3714_; lean_object* v_unused_3715_; lean_object* v_unused_3716_; lean_object* v_unused_3717_; lean_object* v_unused_3718_; 
v_unused_3714_ = lean_ctor_get(v_r_3664_, 4);
lean_dec(v_unused_3714_);
v_unused_3715_ = lean_ctor_get(v_r_3664_, 3);
lean_dec(v_unused_3715_);
v_unused_3716_ = lean_ctor_get(v_r_3664_, 2);
lean_dec(v_unused_3716_);
v_unused_3717_ = lean_ctor_get(v_r_3664_, 1);
lean_dec(v_unused_3717_);
v_unused_3718_ = lean_ctor_get(v_r_3664_, 0);
lean_dec(v_unused_3718_);
v___x_3686_ = v_r_3664_;
v_isShared_3687_ = v_isSharedCheck_3713_;
goto v_resetjp_3685_;
}
else
{
lean_dec(v_r_3664_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3713_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___x_3701_; lean_object* v___y_3703_; 
v___x_3688_ = lean_nat_add(v___x_3658_, v_size_3660_);
lean_dec(v_size_3660_);
v___x_3689_ = lean_nat_add(v___x_3688_, v_size_3659_);
lean_dec(v___x_3688_);
v___x_3701_ = lean_nat_add(v___x_3658_, v_size_3676_);
if (lean_obj_tag(v_l_3680_) == 0)
{
lean_object* v_size_3711_; 
v_size_3711_ = lean_ctor_get(v_l_3680_, 0);
lean_inc(v_size_3711_);
v___y_3703_ = v_size_3711_;
goto v___jp_3702_;
}
else
{
lean_object* v___x_3712_; 
v___x_3712_ = lean_unsigned_to_nat(0u);
v___y_3703_ = v___x_3712_;
goto v___jp_3702_;
}
v___jp_3690_:
{
lean_object* v___x_3694_; lean_object* v___x_3696_; 
v___x_3694_ = lean_nat_add(v___y_3692_, v___y_3693_);
lean_dec(v___y_3693_);
lean_dec(v___y_3692_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 4, v_r_3652_);
lean_ctor_set(v___x_3686_, 3, v_r_3681_);
lean_ctor_set(v___x_3686_, 2, v_v_3650_);
lean_ctor_set(v___x_3686_, 1, v_k_3649_);
lean_ctor_set(v___x_3686_, 0, v___x_3694_);
v___x_3696_ = v___x_3686_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3694_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v_k_3649_);
lean_ctor_set(v_reuseFailAlloc_3700_, 2, v_v_3650_);
lean_ctor_set(v_reuseFailAlloc_3700_, 3, v_r_3681_);
lean_ctor_set(v_reuseFailAlloc_3700_, 4, v_r_3652_);
v___x_3696_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
lean_object* v___x_3698_; 
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 4, v___x_3696_);
lean_ctor_set(v___x_3674_, 3, v___y_3691_);
lean_ctor_set(v___x_3674_, 2, v_v_3679_);
lean_ctor_set(v___x_3674_, 1, v_k_3678_);
lean_ctor_set(v___x_3674_, 0, v___x_3689_);
v___x_3698_ = v___x_3674_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v_k_3678_);
lean_ctor_set(v_reuseFailAlloc_3699_, 2, v_v_3679_);
lean_ctor_set(v_reuseFailAlloc_3699_, 3, v___y_3691_);
lean_ctor_set(v_reuseFailAlloc_3699_, 4, v___x_3696_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
v___jp_3702_:
{
lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3704_ = lean_nat_add(v___x_3701_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec(v___x_3701_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 4, v_l_3680_);
lean_ctor_set(v___x_3654_, 3, v_l_3663_);
lean_ctor_set(v___x_3654_, 2, v_v_3662_);
lean_ctor_set(v___x_3654_, 1, v_k_3661_);
lean_ctor_set(v___x_3654_, 0, v___x_3704_);
v___x_3706_ = v___x_3654_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v_k_3661_);
lean_ctor_set(v_reuseFailAlloc_3710_, 2, v_v_3662_);
lean_ctor_set(v_reuseFailAlloc_3710_, 3, v_l_3663_);
lean_ctor_set(v_reuseFailAlloc_3710_, 4, v_l_3680_);
v___x_3706_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3707_; 
v___x_3707_ = lean_nat_add(v___x_3658_, v_size_3659_);
if (lean_obj_tag(v_r_3681_) == 0)
{
lean_object* v_size_3708_; 
v_size_3708_ = lean_ctor_get(v_r_3681_, 0);
lean_inc(v_size_3708_);
v___y_3691_ = v___x_3706_;
v___y_3692_ = v___x_3707_;
v___y_3693_ = v_size_3708_;
goto v___jp_3690_;
}
else
{
lean_object* v___x_3709_; 
v___x_3709_ = lean_unsigned_to_nat(0u);
v___y_3691_ = v___x_3706_;
v___y_3692_ = v___x_3707_;
v___y_3693_ = v___x_3709_;
goto v___jp_3690_;
}
}
}
}
}
else
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3724_; 
lean_del_object(v___x_3654_);
v___x_3719_ = lean_nat_add(v___x_3658_, v_size_3660_);
lean_dec(v_size_3660_);
v___x_3720_ = lean_nat_add(v___x_3719_, v_size_3659_);
lean_dec(v___x_3719_);
v___x_3721_ = lean_nat_add(v___x_3658_, v_size_3659_);
v___x_3722_ = lean_nat_add(v___x_3721_, v_size_3677_);
lean_dec(v___x_3721_);
lean_inc_ref(v_r_3652_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 4, v_r_3652_);
lean_ctor_set(v___x_3674_, 3, v_r_3664_);
lean_ctor_set(v___x_3674_, 2, v_v_3650_);
lean_ctor_set(v___x_3674_, 1, v_k_3649_);
lean_ctor_set(v___x_3674_, 0, v___x_3722_);
v___x_3724_ = v___x_3674_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v_k_3649_);
lean_ctor_set(v_reuseFailAlloc_3737_, 2, v_v_3650_);
lean_ctor_set(v_reuseFailAlloc_3737_, 3, v_r_3664_);
lean_ctor_set(v_reuseFailAlloc_3737_, 4, v_r_3652_);
v___x_3724_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
v_isSharedCheck_3731_ = !lean_is_exclusive(v_r_3652_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; lean_object* v_unused_3733_; lean_object* v_unused_3734_; lean_object* v_unused_3735_; lean_object* v_unused_3736_; 
v_unused_3732_ = lean_ctor_get(v_r_3652_, 4);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_r_3652_, 3);
lean_dec(v_unused_3733_);
v_unused_3734_ = lean_ctor_get(v_r_3652_, 2);
lean_dec(v_unused_3734_);
v_unused_3735_ = lean_ctor_get(v_r_3652_, 1);
lean_dec(v_unused_3735_);
v_unused_3736_ = lean_ctor_get(v_r_3652_, 0);
lean_dec(v_unused_3736_);
v___x_3726_ = v_r_3652_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_dec(v_r_3652_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 4, v___x_3724_);
lean_ctor_set(v___x_3726_, 3, v_l_3663_);
lean_ctor_set(v___x_3726_, 2, v_v_3662_);
lean_ctor_set(v___x_3726_, 1, v_k_3661_);
lean_ctor_set(v___x_3726_, 0, v___x_3720_);
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_k_3661_);
lean_ctor_set(v_reuseFailAlloc_3730_, 2, v_v_3662_);
lean_ctor_set(v_reuseFailAlloc_3730_, 3, v_l_3663_);
lean_ctor_set(v_reuseFailAlloc_3730_, 4, v___x_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3744_; 
v_l_3744_ = lean_ctor_get(v_impl_3657_, 3);
lean_inc(v_l_3744_);
if (lean_obj_tag(v_l_3744_) == 0)
{
lean_object* v_r_3745_; lean_object* v_k_3746_; lean_object* v_v_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3758_; 
v_r_3745_ = lean_ctor_get(v_impl_3657_, 4);
v_k_3746_ = lean_ctor_get(v_impl_3657_, 1);
v_v_3747_ = lean_ctor_get(v_impl_3657_, 2);
v_isSharedCheck_3758_ = !lean_is_exclusive(v_impl_3657_);
if (v_isSharedCheck_3758_ == 0)
{
lean_object* v_unused_3759_; lean_object* v_unused_3760_; 
v_unused_3759_ = lean_ctor_get(v_impl_3657_, 3);
lean_dec(v_unused_3759_);
v_unused_3760_ = lean_ctor_get(v_impl_3657_, 0);
lean_dec(v_unused_3760_);
v___x_3749_ = v_impl_3657_;
v_isShared_3750_ = v_isSharedCheck_3758_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_r_3745_);
lean_inc(v_v_3747_);
lean_inc(v_k_3746_);
lean_dec(v_impl_3657_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3758_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3751_; lean_object* v___x_3753_; 
v___x_3751_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3745_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 3, v_r_3745_);
lean_ctor_set(v___x_3749_, 2, v_v_3650_);
lean_ctor_set(v___x_3749_, 1, v_k_3649_);
lean_ctor_set(v___x_3749_, 0, v___x_3658_);
v___x_3753_ = v___x_3749_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3658_);
lean_ctor_set(v_reuseFailAlloc_3757_, 1, v_k_3649_);
lean_ctor_set(v_reuseFailAlloc_3757_, 2, v_v_3650_);
lean_ctor_set(v_reuseFailAlloc_3757_, 3, v_r_3745_);
lean_ctor_set(v_reuseFailAlloc_3757_, 4, v_r_3745_);
v___x_3753_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
lean_object* v___x_3755_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 4, v___x_3753_);
lean_ctor_set(v___x_3654_, 3, v_l_3744_);
lean_ctor_set(v___x_3654_, 2, v_v_3747_);
lean_ctor_set(v___x_3654_, 1, v_k_3746_);
lean_ctor_set(v___x_3654_, 0, v___x_3751_);
v___x_3755_ = v___x_3654_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3751_);
lean_ctor_set(v_reuseFailAlloc_3756_, 1, v_k_3746_);
lean_ctor_set(v_reuseFailAlloc_3756_, 2, v_v_3747_);
lean_ctor_set(v_reuseFailAlloc_3756_, 3, v_l_3744_);
lean_ctor_set(v_reuseFailAlloc_3756_, 4, v___x_3753_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
else
{
lean_object* v_r_3761_; 
v_r_3761_ = lean_ctor_get(v_impl_3657_, 4);
lean_inc(v_r_3761_);
if (lean_obj_tag(v_r_3761_) == 0)
{
lean_object* v_k_3762_; lean_object* v_v_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3786_; 
v_k_3762_ = lean_ctor_get(v_impl_3657_, 1);
v_v_3763_ = lean_ctor_get(v_impl_3657_, 2);
v_isSharedCheck_3786_ = !lean_is_exclusive(v_impl_3657_);
if (v_isSharedCheck_3786_ == 0)
{
lean_object* v_unused_3787_; lean_object* v_unused_3788_; lean_object* v_unused_3789_; 
v_unused_3787_ = lean_ctor_get(v_impl_3657_, 4);
lean_dec(v_unused_3787_);
v_unused_3788_ = lean_ctor_get(v_impl_3657_, 3);
lean_dec(v_unused_3788_);
v_unused_3789_ = lean_ctor_get(v_impl_3657_, 0);
lean_dec(v_unused_3789_);
v___x_3765_ = v_impl_3657_;
v_isShared_3766_ = v_isSharedCheck_3786_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_v_3763_);
lean_inc(v_k_3762_);
lean_dec(v_impl_3657_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3786_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v_k_3767_; lean_object* v_v_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3782_; 
v_k_3767_ = lean_ctor_get(v_r_3761_, 1);
v_v_3768_ = lean_ctor_get(v_r_3761_, 2);
v_isSharedCheck_3782_ = !lean_is_exclusive(v_r_3761_);
if (v_isSharedCheck_3782_ == 0)
{
lean_object* v_unused_3783_; lean_object* v_unused_3784_; lean_object* v_unused_3785_; 
v_unused_3783_ = lean_ctor_get(v_r_3761_, 4);
lean_dec(v_unused_3783_);
v_unused_3784_ = lean_ctor_get(v_r_3761_, 3);
lean_dec(v_unused_3784_);
v_unused_3785_ = lean_ctor_get(v_r_3761_, 0);
lean_dec(v_unused_3785_);
v___x_3770_ = v_r_3761_;
v_isShared_3771_ = v_isSharedCheck_3782_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_v_3768_);
lean_inc(v_k_3767_);
lean_dec(v_r_3761_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3782_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3772_; lean_object* v___x_3774_; 
v___x_3772_ = lean_unsigned_to_nat(3u);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 4, v_l_3744_);
lean_ctor_set(v___x_3770_, 3, v_l_3744_);
lean_ctor_set(v___x_3770_, 2, v_v_3763_);
lean_ctor_set(v___x_3770_, 1, v_k_3762_);
lean_ctor_set(v___x_3770_, 0, v___x_3658_);
v___x_3774_ = v___x_3770_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3658_);
lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_k_3762_);
lean_ctor_set(v_reuseFailAlloc_3781_, 2, v_v_3763_);
lean_ctor_set(v_reuseFailAlloc_3781_, 3, v_l_3744_);
lean_ctor_set(v_reuseFailAlloc_3781_, 4, v_l_3744_);
v___x_3774_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
lean_object* v___x_3776_; 
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 4, v_l_3744_);
lean_ctor_set(v___x_3765_, 2, v_v_3650_);
lean_ctor_set(v___x_3765_, 1, v_k_3649_);
lean_ctor_set(v___x_3765_, 0, v___x_3658_);
v___x_3776_ = v___x_3765_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3658_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_k_3649_);
lean_ctor_set(v_reuseFailAlloc_3780_, 2, v_v_3650_);
lean_ctor_set(v_reuseFailAlloc_3780_, 3, v_l_3744_);
lean_ctor_set(v_reuseFailAlloc_3780_, 4, v_l_3744_);
v___x_3776_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
lean_object* v___x_3778_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 4, v___x_3776_);
lean_ctor_set(v___x_3654_, 3, v___x_3774_);
lean_ctor_set(v___x_3654_, 2, v_v_3768_);
lean_ctor_set(v___x_3654_, 1, v_k_3767_);
lean_ctor_set(v___x_3654_, 0, v___x_3772_);
v___x_3778_ = v___x_3654_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3772_);
lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_k_3767_);
lean_ctor_set(v_reuseFailAlloc_3779_, 2, v_v_3768_);
lean_ctor_set(v_reuseFailAlloc_3779_, 3, v___x_3774_);
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
}
}
else
{
lean_object* v___x_3790_; lean_object* v___x_3792_; 
v___x_3790_ = lean_unsigned_to_nat(2u);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 4, v_r_3761_);
lean_ctor_set(v___x_3654_, 3, v_impl_3657_);
lean_ctor_set(v___x_3654_, 0, v___x_3790_);
v___x_3792_ = v___x_3654_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v___x_3790_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_k_3649_);
lean_ctor_set(v_reuseFailAlloc_3793_, 2, v_v_3650_);
lean_ctor_set(v_reuseFailAlloc_3793_, 3, v_impl_3657_);
lean_ctor_set(v_reuseFailAlloc_3793_, 4, v_r_3761_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3795_; 
lean_dec(v_v_3650_);
lean_dec(v_k_3649_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 2, v_v_3646_);
lean_ctor_set(v___x_3654_, 1, v_k_3645_);
v___x_3795_ = v___x_3654_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_size_3648_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_k_3645_);
lean_ctor_set(v_reuseFailAlloc_3796_, 2, v_v_3646_);
lean_ctor_set(v_reuseFailAlloc_3796_, 3, v_l_3651_);
lean_ctor_set(v_reuseFailAlloc_3796_, 4, v_r_3652_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
default: 
{
lean_object* v_impl_3797_; lean_object* v___x_3798_; 
lean_dec(v_size_3648_);
v_impl_3797_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3645_, v_v_3646_, v_r_3652_);
v___x_3798_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3651_) == 0)
{
lean_object* v_size_3799_; lean_object* v_size_3800_; lean_object* v_k_3801_; lean_object* v_v_3802_; lean_object* v_l_3803_; lean_object* v_r_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
v_size_3799_ = lean_ctor_get(v_l_3651_, 0);
v_size_3800_ = lean_ctor_get(v_impl_3797_, 0);
lean_inc(v_size_3800_);
v_k_3801_ = lean_ctor_get(v_impl_3797_, 1);
lean_inc(v_k_3801_);
v_v_3802_ = lean_ctor_get(v_impl_3797_, 2);
lean_inc(v_v_3802_);
v_l_3803_ = lean_ctor_get(v_impl_3797_, 3);
lean_inc(v_l_3803_);
v_r_3804_ = lean_ctor_get(v_impl_3797_, 4);
lean_inc(v_r_3804_);
v___x_3805_ = lean_unsigned_to_nat(3u);
v___x_3806_ = lean_nat_mul(v___x_3805_, v_size_3799_);
v___x_3807_ = lean_nat_dec_lt(v___x_3806_, v_size_3800_);
lean_dec(v___x_3806_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
lean_dec(v_r_3804_);
lean_dec(v_l_3803_);
lean_dec(v_v_3802_);
lean_dec(v_k_3801_);
v___x_3808_ = lean_nat_add(v___x_3798_, v_size_3799_);
v___x_3809_ = lean_nat_add(v___x_3808_, v_size_3800_);
lean_dec(v_size_3800_);
lean_dec(v___x_3808_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 4, v_impl_3797_);
lean_ctor_set(v___x_3654_, 0, v___x_3809_);
v___x_3811_ = v___x_3654_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_k_3649_);
lean_ctor_set(v_reuseFailAlloc_3812_, 2, v_v_3650_);
lean_ctor_set(v_reuseFailAlloc_3812_, 3, v_l_3651_);
lean_ctor_set(v_reuseFailAlloc_3812_, 4, v_impl_3797_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
else
{
lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3876_; 
v_isSharedCheck_3876_ = !lean_is_exclusive(v_impl_3797_);
if (v_isSharedCheck_3876_ == 0)
{
lean_object* v_unused_3877_; lean_object* v_unused_3878_; lean_object* v_unused_3879_; lean_object* v_unused_3880_; lean_object* v_unused_3881_; 
v_unused_3877_ = lean_ctor_get(v_impl_3797_, 4);
lean_dec(v_unused_3877_);
v_unused_3878_ = lean_ctor_get(v_impl_3797_, 3);
lean_dec(v_unused_3878_);
v_unused_3879_ = lean_ctor_get(v_impl_3797_, 2);
lean_dec(v_unused_3879_);
v_unused_3880_ = lean_ctor_get(v_impl_3797_, 1);
lean_dec(v_unused_3880_);
v_unused_3881_ = lean_ctor_get(v_impl_3797_, 0);
lean_dec(v_unused_3881_);
v___x_3814_ = v_impl_3797_;
v_isShared_3815_ = v_isSharedCheck_3876_;
goto v_resetjp_3813_;
}
else
{
lean_dec(v_impl_3797_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3876_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v_size_3816_; lean_object* v_k_3817_; lean_object* v_v_3818_; lean_object* v_l_3819_; lean_object* v_r_3820_; lean_object* v_size_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; uint8_t v___x_3824_; 
v_size_3816_ = lean_ctor_get(v_l_3803_, 0);
v_k_3817_ = lean_ctor_get(v_l_3803_, 1);
v_v_3818_ = lean_ctor_get(v_l_3803_, 2);
v_l_3819_ = lean_ctor_get(v_l_3803_, 3);
v_r_3820_ = lean_ctor_get(v_l_3803_, 4);
v_size_3821_ = lean_ctor_get(v_r_3804_, 0);
v___x_3822_ = lean_unsigned_to_nat(2u);
v___x_3823_ = lean_nat_mul(v___x_3822_, v_size_3821_);
v___x_3824_ = lean_nat_dec_lt(v_size_3816_, v___x_3823_);
lean_dec(v___x_3823_);
if (v___x_3824_ == 0)
{
lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3852_; 
lean_inc(v_r_3820_);
lean_inc(v_l_3819_);
lean_inc(v_v_3818_);
lean_inc(v_k_3817_);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_l_3803_);
if (v_isSharedCheck_3852_ == 0)
{
lean_object* v_unused_3853_; lean_object* v_unused_3854_; lean_object* v_unused_3855_; lean_object* v_unused_3856_; lean_object* v_unused_3857_; 
v_unused_3853_ = lean_ctor_get(v_l_3803_, 4);
lean_dec(v_unused_3853_);
v_unused_3854_ = lean_ctor_get(v_l_3803_, 3);
lean_dec(v_unused_3854_);
v_unused_3855_ = lean_ctor_get(v_l_3803_, 2);
lean_dec(v_unused_3855_);
v_unused_3856_ = lean_ctor_get(v_l_3803_, 1);
lean_dec(v_unused_3856_);
v_unused_3857_ = lean_ctor_get(v_l_3803_, 0);
lean_dec(v_unused_3857_);
v___x_3826_ = v_l_3803_;
v_isShared_3827_ = v_isSharedCheck_3852_;
goto v_resetjp_3825_;
}
else
{
lean_dec(v_l_3803_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3852_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3842_; 
v___x_3828_ = lean_nat_add(v___x_3798_, v_size_3799_);
v___x_3829_ = lean_nat_add(v___x_3828_, v_size_3800_);
lean_dec(v_size_3800_);
if (lean_obj_tag(v_l_3819_) == 0)
{
lean_object* v_size_3850_; 
v_size_3850_ = lean_ctor_get(v_l_3819_, 0);
lean_inc(v_size_3850_);
v___y_3842_ = v_size_3850_;
goto v___jp_3841_;
}
else
{
lean_object* v___x_3851_; 
v___x_3851_ = lean_unsigned_to_nat(0u);
v___y_3842_ = v___x_3851_;
goto v___jp_3841_;
}
v___jp_3830_:
{
lean_object* v___x_3834_; lean_object* v___x_3836_; 
v___x_3834_ = lean_nat_add(v___y_3832_, v___y_3833_);
lean_dec(v___y_3833_);
lean_dec(v___y_3832_);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 4, v_r_3804_);
lean_ctor_set(v___x_3826_, 3, v_r_3820_);
lean_ctor_set(v___x_3826_, 2, v_v_3802_);
lean_ctor_set(v___x_3826_, 1, v_k_3801_);
lean_ctor_set(v___x_3826_, 0, v___x_3834_);
v___x_3836_ = v___x_3826_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3834_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v_k_3801_);
lean_ctor_set(v_reuseFailAlloc_3840_, 2, v_v_3802_);
lean_ctor_set(v_reuseFailAlloc_3840_, 3, v_r_3820_);
lean_ctor_set(v_reuseFailAlloc_3840_, 4, v_r_3804_);
v___x_3836_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v___x_3838_; 
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 4, v___x_3836_);
lean_ctor_set(v___x_3814_, 3, v___y_3831_);
lean_ctor_set(v___x_3814_, 2, v_v_3818_);
lean_ctor_set(v___x_3814_, 1, v_k_3817_);
lean_ctor_set(v___x_3814_, 0, v___x_3829_);
v___x_3838_ = v___x_3814_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3829_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v_k_3817_);
lean_ctor_set(v_reuseFailAlloc_3839_, 2, v_v_3818_);
lean_ctor_set(v_reuseFailAlloc_3839_, 3, v___y_3831_);
lean_ctor_set(v_reuseFailAlloc_3839_, 4, v___x_3836_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
v___jp_3841_:
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3843_ = lean_nat_add(v___x_3828_, v___y_3842_);
lean_dec(v___y_3842_);
lean_dec(v___x_3828_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 4, v_l_3819_);
lean_ctor_set(v___x_3654_, 0, v___x_3843_);
v___x_3845_ = v___x_3654_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3849_, 1, v_k_3649_);
lean_ctor_set(v_reuseFailAlloc_3849_, 2, v_v_3650_);
lean_ctor_set(v_reuseFailAlloc_3849_, 3, v_l_3651_);
lean_ctor_set(v_reuseFailAlloc_3849_, 4, v_l_3819_);
v___x_3845_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3846_; 
v___x_3846_ = lean_nat_add(v___x_3798_, v_size_3821_);
if (lean_obj_tag(v_r_3820_) == 0)
{
lean_object* v_size_3847_; 
v_size_3847_ = lean_ctor_get(v_r_3820_, 0);
lean_inc(v_size_3847_);
v___y_3831_ = v___x_3845_;
v___y_3832_ = v___x_3846_;
v___y_3833_ = v_size_3847_;
goto v___jp_3830_;
}
else
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_unsigned_to_nat(0u);
v___y_3831_ = v___x_3845_;
v___y_3832_ = v___x_3846_;
v___y_3833_ = v___x_3848_;
goto v___jp_3830_;
}
}
}
}
}
else
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3862_; 
lean_del_object(v___x_3654_);
v___x_3858_ = lean_nat_add(v___x_3798_, v_size_3799_);
v___x_3859_ = lean_nat_add(v___x_3858_, v_size_3800_);
lean_dec(v_size_3800_);
v___x_3860_ = lean_nat_add(v___x_3858_, v_size_3816_);
lean_dec(v___x_3858_);
lean_inc_ref(v_l_3651_);
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 4, v_l_3803_);
lean_ctor_set(v___x_3814_, 3, v_l_3651_);
lean_ctor_set(v___x_3814_, 2, v_v_3650_);
lean_ctor_set(v___x_3814_, 1, v_k_3649_);
lean_ctor_set(v___x_3814_, 0, v___x_3860_);
v___x_3862_ = v___x_3814_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3860_);
lean_ctor_set(v_reuseFailAlloc_3875_, 1, v_k_3649_);
lean_ctor_set(v_reuseFailAlloc_3875_, 2, v_v_3650_);
lean_ctor_set(v_reuseFailAlloc_3875_, 3, v_l_3651_);
lean_ctor_set(v_reuseFailAlloc_3875_, 4, v_l_3803_);
v___x_3862_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
v_isSharedCheck_3869_ = !lean_is_exclusive(v_l_3651_);
if (v_isSharedCheck_3869_ == 0)
{
lean_object* v_unused_3870_; lean_object* v_unused_3871_; lean_object* v_unused_3872_; lean_object* v_unused_3873_; lean_object* v_unused_3874_; 
v_unused_3870_ = lean_ctor_get(v_l_3651_, 4);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v_l_3651_, 3);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_l_3651_, 2);
lean_dec(v_unused_3872_);
v_unused_3873_ = lean_ctor_get(v_l_3651_, 1);
lean_dec(v_unused_3873_);
v_unused_3874_ = lean_ctor_get(v_l_3651_, 0);
lean_dec(v_unused_3874_);
v___x_3864_ = v_l_3651_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_dec(v_l_3651_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 4, v_r_3804_);
lean_ctor_set(v___x_3864_, 3, v___x_3862_);
lean_ctor_set(v___x_3864_, 2, v_v_3802_);
lean_ctor_set(v___x_3864_, 1, v_k_3801_);
lean_ctor_set(v___x_3864_, 0, v___x_3859_);
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3868_, 1, v_k_3801_);
lean_ctor_set(v_reuseFailAlloc_3868_, 2, v_v_3802_);
lean_ctor_set(v_reuseFailAlloc_3868_, 3, v___x_3862_);
lean_ctor_set(v_reuseFailAlloc_3868_, 4, v_r_3804_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3882_; 
v_l_3882_ = lean_ctor_get(v_impl_3797_, 3);
lean_inc(v_l_3882_);
if (lean_obj_tag(v_l_3882_) == 0)
{
lean_object* v_r_3883_; lean_object* v_k_3884_; lean_object* v_v_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3908_; 
v_r_3883_ = lean_ctor_get(v_impl_3797_, 4);
v_k_3884_ = lean_ctor_get(v_impl_3797_, 1);
v_v_3885_ = lean_ctor_get(v_impl_3797_, 2);
v_isSharedCheck_3908_ = !lean_is_exclusive(v_impl_3797_);
if (v_isSharedCheck_3908_ == 0)
{
lean_object* v_unused_3909_; lean_object* v_unused_3910_; 
v_unused_3909_ = lean_ctor_get(v_impl_3797_, 3);
lean_dec(v_unused_3909_);
v_unused_3910_ = lean_ctor_get(v_impl_3797_, 0);
lean_dec(v_unused_3910_);
v___x_3887_ = v_impl_3797_;
v_isShared_3888_ = v_isSharedCheck_3908_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_r_3883_);
lean_inc(v_v_3885_);
lean_inc(v_k_3884_);
lean_dec(v_impl_3797_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3908_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v_k_3889_; lean_object* v_v_3890_; lean_object* v___x_3892_; uint8_t v_isShared_3893_; uint8_t v_isSharedCheck_3904_; 
v_k_3889_ = lean_ctor_get(v_l_3882_, 1);
v_v_3890_ = lean_ctor_get(v_l_3882_, 2);
v_isSharedCheck_3904_ = !lean_is_exclusive(v_l_3882_);
if (v_isSharedCheck_3904_ == 0)
{
lean_object* v_unused_3905_; lean_object* v_unused_3906_; lean_object* v_unused_3907_; 
v_unused_3905_ = lean_ctor_get(v_l_3882_, 4);
lean_dec(v_unused_3905_);
v_unused_3906_ = lean_ctor_get(v_l_3882_, 3);
lean_dec(v_unused_3906_);
v_unused_3907_ = lean_ctor_get(v_l_3882_, 0);
lean_dec(v_unused_3907_);
v___x_3892_ = v_l_3882_;
v_isShared_3893_ = v_isSharedCheck_3904_;
goto v_resetjp_3891_;
}
else
{
lean_inc(v_v_3890_);
lean_inc(v_k_3889_);
lean_dec(v_l_3882_);
v___x_3892_ = lean_box(0);
v_isShared_3893_ = v_isSharedCheck_3904_;
goto v_resetjp_3891_;
}
v_resetjp_3891_:
{
lean_object* v___x_3894_; lean_object* v___x_3896_; 
v___x_3894_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3883_, 2);
if (v_isShared_3893_ == 0)
{
lean_ctor_set(v___x_3892_, 4, v_r_3883_);
lean_ctor_set(v___x_3892_, 3, v_r_3883_);
lean_ctor_set(v___x_3892_, 2, v_v_3650_);
lean_ctor_set(v___x_3892_, 1, v_k_3649_);
lean_ctor_set(v___x_3892_, 0, v___x_3798_);
v___x_3896_ = v___x_3892_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3798_);
lean_ctor_set(v_reuseFailAlloc_3903_, 1, v_k_3649_);
lean_ctor_set(v_reuseFailAlloc_3903_, 2, v_v_3650_);
lean_ctor_set(v_reuseFailAlloc_3903_, 3, v_r_3883_);
lean_ctor_set(v_reuseFailAlloc_3903_, 4, v_r_3883_);
v___x_3896_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
lean_object* v___x_3898_; 
lean_inc(v_r_3883_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 3, v_r_3883_);
lean_ctor_set(v___x_3887_, 0, v___x_3798_);
v___x_3898_ = v___x_3887_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3798_);
lean_ctor_set(v_reuseFailAlloc_3902_, 1, v_k_3884_);
lean_ctor_set(v_reuseFailAlloc_3902_, 2, v_v_3885_);
lean_ctor_set(v_reuseFailAlloc_3902_, 3, v_r_3883_);
lean_ctor_set(v_reuseFailAlloc_3902_, 4, v_r_3883_);
v___x_3898_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
lean_object* v___x_3900_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 4, v___x_3898_);
lean_ctor_set(v___x_3654_, 3, v___x_3896_);
lean_ctor_set(v___x_3654_, 2, v_v_3890_);
lean_ctor_set(v___x_3654_, 1, v_k_3889_);
lean_ctor_set(v___x_3654_, 0, v___x_3894_);
v___x_3900_ = v___x_3654_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3894_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v_k_3889_);
lean_ctor_set(v_reuseFailAlloc_3901_, 2, v_v_3890_);
lean_ctor_set(v_reuseFailAlloc_3901_, 3, v___x_3896_);
lean_ctor_set(v_reuseFailAlloc_3901_, 4, v___x_3898_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
}
}
}
else
{
lean_object* v_r_3911_; 
v_r_3911_ = lean_ctor_get(v_impl_3797_, 4);
lean_inc(v_r_3911_);
if (lean_obj_tag(v_r_3911_) == 0)
{
lean_object* v_k_3912_; lean_object* v_v_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3924_; 
v_k_3912_ = lean_ctor_get(v_impl_3797_, 1);
v_v_3913_ = lean_ctor_get(v_impl_3797_, 2);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_impl_3797_);
if (v_isSharedCheck_3924_ == 0)
{
lean_object* v_unused_3925_; lean_object* v_unused_3926_; lean_object* v_unused_3927_; 
v_unused_3925_ = lean_ctor_get(v_impl_3797_, 4);
lean_dec(v_unused_3925_);
v_unused_3926_ = lean_ctor_get(v_impl_3797_, 3);
lean_dec(v_unused_3926_);
v_unused_3927_ = lean_ctor_get(v_impl_3797_, 0);
lean_dec(v_unused_3927_);
v___x_3915_ = v_impl_3797_;
v_isShared_3916_ = v_isSharedCheck_3924_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_v_3913_);
lean_inc(v_k_3912_);
lean_dec(v_impl_3797_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3924_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3917_; lean_object* v___x_3919_; 
v___x_3917_ = lean_unsigned_to_nat(3u);
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 4, v_l_3882_);
lean_ctor_set(v___x_3915_, 2, v_v_3650_);
lean_ctor_set(v___x_3915_, 1, v_k_3649_);
lean_ctor_set(v___x_3915_, 0, v___x_3798_);
v___x_3919_ = v___x_3915_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3798_);
lean_ctor_set(v_reuseFailAlloc_3923_, 1, v_k_3649_);
lean_ctor_set(v_reuseFailAlloc_3923_, 2, v_v_3650_);
lean_ctor_set(v_reuseFailAlloc_3923_, 3, v_l_3882_);
lean_ctor_set(v_reuseFailAlloc_3923_, 4, v_l_3882_);
v___x_3919_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3921_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 4, v_r_3911_);
lean_ctor_set(v___x_3654_, 3, v___x_3919_);
lean_ctor_set(v___x_3654_, 2, v_v_3913_);
lean_ctor_set(v___x_3654_, 1, v_k_3912_);
lean_ctor_set(v___x_3654_, 0, v___x_3917_);
v___x_3921_ = v___x_3654_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3917_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v_k_3912_);
lean_ctor_set(v_reuseFailAlloc_3922_, 2, v_v_3913_);
lean_ctor_set(v_reuseFailAlloc_3922_, 3, v___x_3919_);
lean_ctor_set(v_reuseFailAlloc_3922_, 4, v_r_3911_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
else
{
lean_object* v___x_3928_; lean_object* v___x_3930_; 
v___x_3928_ = lean_unsigned_to_nat(2u);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 4, v_impl_3797_);
lean_ctor_set(v___x_3654_, 3, v_r_3911_);
lean_ctor_set(v___x_3654_, 0, v___x_3928_);
v___x_3930_ = v___x_3654_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3928_);
lean_ctor_set(v_reuseFailAlloc_3931_, 1, v_k_3649_);
lean_ctor_set(v_reuseFailAlloc_3931_, 2, v_v_3650_);
lean_ctor_set(v_reuseFailAlloc_3931_, 3, v_r_3911_);
lean_ctor_set(v_reuseFailAlloc_3931_, 4, v_impl_3797_);
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
}
}
}
}
else
{
lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3933_ = lean_unsigned_to_nat(1u);
v___x_3934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
lean_ctor_set(v___x_3934_, 1, v_k_3645_);
lean_ctor_set(v___x_3934_, 2, v_v_3646_);
lean_ctor_set(v___x_3934_, 3, v_t_3647_);
lean_ctor_set(v___x_3934_, 4, v_t_3647_);
return v___x_3934_;
}
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3935_ = lean_box(1);
v___x_3936_ = l_Lake_Package_depsFacetConfig;
v___x_3937_ = l_Lake_Package_depsFacet;
v___x_3938_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3937_, v___x_3936_, v___x_3935_);
return v___x_3938_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3939_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__0, &l_Lake_Package_initFacetConfigs___closed__0_once, _init_l_Lake_Package_initFacetConfigs___closed__0);
v___x_3940_ = l_Lake_Package_transDepsFacetConfig;
v___x_3941_ = l_Lake_Package_transDepsFacet;
v___x_3942_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3941_, v___x_3940_, v___x_3939_);
return v___x_3942_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3943_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__1, &l_Lake_Package_initFacetConfigs___closed__1_once, _init_l_Lake_Package_initFacetConfigs___closed__1);
v___x_3944_ = l_Lake_Package_defaultModulesFacetConfig;
v___x_3945_ = l_Lake_Package_defaultModulesFacet;
v___x_3946_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3945_, v___x_3944_, v___x_3943_);
return v___x_3946_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3947_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__2, &l_Lake_Package_initFacetConfigs___closed__2_once, _init_l_Lake_Package_initFacetConfigs___closed__2);
v___x_3948_ = l_Lake_Package_extraDepFacetConfig;
v___x_3949_ = l_Lake_Package_extraDepFacet;
v___x_3950_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3949_, v___x_3948_, v___x_3947_);
return v___x_3950_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3951_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__3, &l_Lake_Package_initFacetConfigs___closed__3_once, _init_l_Lake_Package_initFacetConfigs___closed__3);
v___x_3952_ = l_Lake_Package_optBuildCacheFacetConfig;
v___x_3953_ = l_Lake_Package_optBuildCacheFacet;
v___x_3954_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3953_, v___x_3952_, v___x_3951_);
return v___x_3954_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3955_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__4, &l_Lake_Package_initFacetConfigs___closed__4_once, _init_l_Lake_Package_initFacetConfigs___closed__4);
v___x_3956_ = l_Lake_Package_buildCacheFacetConfig;
v___x_3957_ = l_Lake_Package_buildCacheFacet;
v___x_3958_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3957_, v___x_3956_, v___x_3955_);
return v___x_3958_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3959_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__5, &l_Lake_Package_initFacetConfigs___closed__5_once, _init_l_Lake_Package_initFacetConfigs___closed__5);
v___x_3960_ = l_Lake_Package_optBarrelFacetConfig;
v___x_3961_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3962_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3961_, v___x_3960_, v___x_3959_);
return v___x_3962_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3963_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__6, &l_Lake_Package_initFacetConfigs___closed__6_once, _init_l_Lake_Package_initFacetConfigs___closed__6);
v___x_3964_ = l_Lake_Package_barrelFacetConfig;
v___x_3965_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3966_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3965_, v___x_3964_, v___x_3963_);
return v___x_3966_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3967_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__7, &l_Lake_Package_initFacetConfigs___closed__7_once, _init_l_Lake_Package_initFacetConfigs___closed__7);
v___x_3968_ = l_Lake_Package_optGitHubReleaseFacetConfig;
v___x_3969_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3970_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3969_, v___x_3968_, v___x_3967_);
return v___x_3970_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__9(void){
_start:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3971_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__8, &l_Lake_Package_initFacetConfigs___closed__8_once, _init_l_Lake_Package_initFacetConfigs___closed__8);
v___x_3972_ = l_Lake_Package_gitHubReleaseFacetConfig;
v___x_3973_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3974_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3973_, v___x_3972_, v___x_3971_);
return v___x_3974_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs(void){
_start:
{
lean_object* v___x_3975_; 
v___x_3975_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__9, &l_Lake_Package_initFacetConfigs___closed__9_once, _init_l_Lake_Package_initFacetConfigs___closed__9);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3976_, lean_object* v_k_3977_, lean_object* v_v_3978_, lean_object* v_t_3979_, lean_object* v_hl_3980_){
_start:
{
lean_object* v___x_3981_; 
v___x_3981_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3977_, v_v_3978_, v_t_3979_);
return v___x_3981_;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs(void){
_start:
{
lean_object* v___x_3982_; 
v___x_3982_ = l_Lake_Package_initFacetConfigs;
return v___x_3982_;
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
