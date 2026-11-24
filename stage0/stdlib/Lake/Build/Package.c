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
lean_object* l_Lean_instToJsonBool___lam__0___boxed(lean_object*);
lean_object* l_instToStringBool___lam__0___boxed(lean_object*);
lean_object* l_Lake_formatQuery___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lake_Package_optReservoirBarrelFacet;
lean_object* l_Lake_Name_eraseHead(lean_object*);
extern lean_object* l_Lake_Package_optArtifactCacheFacet;
extern lean_object* l_Lake_Package_optGitHubReleaseFacet;
extern lean_object* l_Lake_instDataKindUnit;
extern lean_object* l_Lake_Package_optBuildCacheFacet;
extern lean_object* l_Lake_Package_keyword;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildMetadata_writeFile(lean_object*, lean_object*);
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
lean_object* l_Lake_Package_cacheScope(lean_object*);
lean_object* l_Lake_Cache_writeMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lake_Internal_packageHasChanges(lean_object*);
lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lake_Internal_noOutputs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_CacheService_downloadRevisionOutputs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
lean_object* l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(lean_object*);
lean_object* l_Lake_Internal_packageNotReservoir(lean_object*);
extern lean_object* l_Lake_CacheToolchain_none;
extern lean_object* l_Lake_CachePlatform_system;
extern lean_object* l_Lake_CachePlatform_none;
lean_object* l_Lake_Internal_packageServiceRequiresScope(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lake_Package_artifactCacheFacet;
extern lean_object* l_Lake_Reservoir_lakeHeaders;
lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Job_async___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobM_runSpawnM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_FetchM_runJobM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_instQueryJsonUnit___lam__0(lean_object*);
lean_object* l_Lake_instQueryTextUnit___lam__0(lean_object*);
lean_object* l_Lake_GitRepo_findTag_x3f(lean_object*, lean_object*);
extern lean_object* l_Lake_Git_defaultRemote;
lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*);
extern lean_object* l_Lake_Package_reservoirBarrelFacet;
extern lean_object* l_Lake_Package_gitHubReleaseFacet;
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
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "building from source; failed to fetch artifact cache"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "building from source; failed to fetch GitHub release"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3;
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__4;
static lean_once_cell_t l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__5;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__0_value;
static const lean_closure_object l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToJsonBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__1_value;
static const lean_ctor_object l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__0_value),((lean_object*)&l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__1_value)}};
static const lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__2_value;
static const lean_closure_object l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__2_value)} };
static const lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__3 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = "package has no associated cache service; if you are the maintainer, set `downloadCacheService` on the package"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__0_value;
static const lean_ctor_object l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__1_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "package's cache service not found `"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__2 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__2_value;
static const lean_string_object l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "`; check with the maintainer about how to configure the service"};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__3 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__3_value;
static const lean_ctor_object l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__4 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCacheFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCacheFacetConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCacheFacetConfig___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCacheFacetConfig___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCacheFacetConfig___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCacheFacetConfig___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Package_optArtifactCacheFacetConfig___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_optArtifactCacheFacetConfig___closed__0;
static lean_once_cell_t l_Lake_Package_optArtifactCacheFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_optArtifactCacheFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCacheFacetConfig;
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
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "failed to fetch "};
static const lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instQueryTextUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__0_value;
static const lean_closure_object l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instQueryJsonUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__1_value;
static const lean_ctor_object l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__0_value),((lean_object*)&l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__1_value)}};
static const lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__2 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__2_value;
static const lean_closure_object l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_formatQuery___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__2_value)} };
static const lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__3 = (const lean_object*)&l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lake_Package_artifactCacheFacetConfig___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "failed to fetch artifact cache"};
static const lean_object* l_Lake_Package_artifactCacheFacetConfig___lam__1___closed__0 = (const lean_object*)&l_Lake_Package_artifactCacheFacetConfig___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_artifactCacheFacetConfig___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_artifactCacheFacetConfig___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_artifactCacheFacetConfig___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_artifactCacheFacetConfig___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Package_artifactCacheFacetConfig___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_artifactCacheFacetConfig___closed__0;
static lean_once_cell_t l_Lake_Package_artifactCacheFacetConfig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_artifactCacheFacetConfig___closed__1;
LEAN_EXPORT lean_object* l_Lake_Package_artifactCacheFacetConfig;
static const lean_string_object l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "build.barrel"};
static const lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0 = (const lean_object*)&l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lake_Package_initFacetConfigs___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_initFacetConfigs___closed__10;
static lean_once_cell_t l_Lake_Package_initFacetConfigs___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Package_initFacetConfigs___closed__11;
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
lean_dec_ref(v_a_42_);
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
lean_inc_ref(v___y_317_);
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
size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v___x_343_ = ((size_t)0ULL);
v___x_344_ = lean_usize_of_nat(v___x_341_);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__1(v_a_332_, v___x_343_, v___x_344_, v_b_313_);
lean_dec(v_a_332_);
v___y_335_ = v___x_345_;
goto v___jp_334_;
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
lean_object* v_a_346_; lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref(v___y_314_);
lean_dec_ref(v_b_313_);
v_a_346_ = lean_ctor_get(v___x_331_, 0);
v_a_347_ = lean_ctor_get(v___x_331_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_331_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_inc(v_a_346_);
lean_dec(v___x_331_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_346_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_object* v_a_355_; lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec_ref(v___y_314_);
lean_dec_ref(v_b_313_);
v_a_355_ = lean_ctor_get(v___x_328_, 0);
v_a_356_ = lean_ctor_get(v___x_328_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_328_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_inc(v_a_355_);
lean_dec(v___x_328_);
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
lean_object* v___x_364_; 
lean_dec_ref(v___y_314_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v_b_313_);
lean_ctor_set(v___x_364_, 1, v___y_319_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3___boxed(lean_object* v_as_365_, lean_object* v_i_366_, lean_object* v_stop_367_, lean_object* v_b_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
size_t v_i_boxed_376_; size_t v_stop_boxed_377_; lean_object* v_res_378_; 
v_i_boxed_376_ = lean_unbox_usize(v_i_366_);
lean_dec(v_i_366_);
v_stop_boxed_377_ = lean_unbox_usize(v_stop_367_);
lean_dec(v_stop_367_);
v_res_378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_as_365_, v_i_boxed_376_, v_stop_boxed_377_, v_b_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v_as_365_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(lean_object* v___x_379_, lean_object* v___x_380_, lean_object* v___x_381_, lean_object* v___x_382_, lean_object* v_depPkgs_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_a_392_; lean_object* v_a_393_; uint8_t v___x_412_; 
v___x_412_ = lean_nat_dec_lt(v___x_379_, v___x_381_);
if (v___x_412_ == 0)
{
lean_dec_ref(v___y_384_);
v_a_392_ = v___x_382_;
v_a_393_ = v___y_389_;
goto v___jp_391_;
}
else
{
size_t v___x_413_; size_t v___x_414_; lean_object* v___x_415_; 
v___x_413_ = ((size_t)0ULL);
v___x_414_ = lean_usize_of_nat(v___x_381_);
v___x_415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__3(v_depPkgs_383_, v___x_413_, v___x_414_, v___x_382_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v_a_417_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
v_a_417_ = lean_ctor_get(v___x_415_, 1);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_415_, 2);
v_a_392_ = v_a_416_;
v_a_393_ = v_a_417_;
goto v___jp_391_;
}
else
{
lean_object* v_a_418_; lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec(v___x_380_);
lean_dec(v___x_379_);
v_a_418_ = lean_ctor_get(v___x_415_, 0);
v_a_419_ = lean_ctor_get(v___x_415_, 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_415_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_inc(v_a_418_);
lean_dec(v___x_415_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_418_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
v___jp_391_:
{
lean_object* v_toArray_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_410_; 
v_toArray_394_ = lean_ctor_get(v_a_392_, 1);
v_isSharedCheck_410_ = !lean_is_exclusive(v_a_392_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v_a_392_, 0);
lean_dec(v_unused_411_);
v___x_396_ = v_a_392_;
v_isShared_397_ = v_isSharedCheck_410_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_toArray_394_);
lean_dec(v_a_392_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_410_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_398_ = lean_mk_empty_array_with_capacity(v___x_379_);
v___x_399_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_400_ = 0;
v___x_401_ = 0;
v___x_402_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_403_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_403_, 0, v___x_398_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
lean_ctor_set(v___x_403_, 2, v___x_379_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*3, v___x_400_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*3 + 1, v___x_401_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*3 + 2, v___x_401_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_403_);
lean_ctor_set(v___x_396_, 0, v_toArray_394_);
v___x_405_ = v___x_396_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_toArray_394_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v___x_403_);
v___x_405_ = v_reuseFailAlloc_409_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_task_pure(v___x_405_);
v___x_407_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_380_);
lean_ctor_set(v___x_407_, 2, v___x_399_);
lean_ctor_set_uint8(v___x_407_, sizeof(void*)*3, v___x_401_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v_a_393_);
return v___x_408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed(lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v___x_429_, lean_object* v___x_430_, lean_object* v_depPkgs_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0(v___x_427_, v___x_428_, v___x_429_, v___x_430_, v_depPkgs_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v_depPkgs_431_);
lean_dec(v___x_429_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(lean_object* v_self_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_depPkgs_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___f_453_; lean_object* v___x_454_; 
v_depPkgs_448_ = lean_ctor_get(v_self_440_, 14);
lean_inc_ref(v_depPkgs_448_);
lean_dec_ref(v_self_440_);
v___x_449_ = lean_box(0);
v___x_450_ = l_Lake_OrdHashSet_empty___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__2;
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_array_get_size(v_depPkgs_448_);
v___f_453_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___lam__0___boxed), 12, 5);
lean_closure_set(v___f_453_, 0, v___x_451_);
lean_closure_set(v___f_453_, 1, v___x_449_);
lean_closure_set(v___f_453_, 2, v___x_452_);
lean_closure_set(v___f_453_, 3, v___x_450_);
lean_closure_set(v___f_453_, 4, v_depPkgs_448_);
v___x_454_ = l_Lake_ensureJob___redArg(v___x_449_, v___f_453_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps___boxed(lean_object* v_self_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps(v_self_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec(v_a_457_);
return v_res_463_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(lean_object* v_00_u03b2_464_, lean_object* v_m_465_, lean_object* v_a_466_){
_start:
{
uint8_t v___x_467_; 
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___redArg(v_m_465_, v_a_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0___boxed(lean_object* v_00_u03b2_468_, lean_object* v_m_469_, lean_object* v_a_470_){
_start:
{
uint8_t v_res_471_; lean_object* v_r_472_; 
v_res_471_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0(v_00_u03b2_468_, v_m_469_, v_a_470_);
lean_dec_ref(v_a_470_);
lean_dec_ref(v_m_469_);
v_r_472_ = lean_box(v_res_471_);
return v_r_472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1(lean_object* v_00_u03b2_473_, lean_object* v_m_474_, lean_object* v_a_475_, lean_object* v_b_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1___redArg(v_m_474_, v_a_475_, v_b_476_);
return v___x_477_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_478_, lean_object* v_a_479_, lean_object* v_x_480_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___redArg(v_a_479_, v_x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_482_, lean_object* v_a_483_, lean_object* v_x_484_){
_start:
{
uint8_t v_res_485_; lean_object* v_r_486_; 
v_res_485_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__0_spec__2(v_00_u03b2_482_, v_a_483_, v_x_484_);
lean_dec(v_x_484_);
lean_dec_ref(v_a_483_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_487_, lean_object* v_data_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4___redArg(v_data_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_490_, lean_object* v_i_491_, lean_object* v_source_492_, lean_object* v_target_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7___redArg(v_i_491_, v_source_492_, v_target_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8(lean_object* v_00_u03b2_495_, lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lake_OrdHashSet_insert___at___00__private_Lake_Build_Package_0__Lake_Package_recComputeTransDeps_spec__0_spec__1_spec__4_spec__7_spec__8___redArg(v_x_496_, v_x_497_);
return v___x_498_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(lean_object* v_a_499_, lean_object* v_x_500_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
uint8_t v___x_501_; 
v___x_501_ = 0;
return v___x_501_;
}
else
{
lean_object* v_key_502_; lean_object* v_tail_503_; lean_object* v_name_504_; lean_object* v_name_505_; uint8_t v___x_506_; 
v_key_502_ = lean_ctor_get(v_x_500_, 0);
v_tail_503_ = lean_ctor_get(v_x_500_, 2);
v_name_504_ = lean_ctor_get(v_key_502_, 1);
v_name_505_ = lean_ctor_get(v_a_499_, 1);
v___x_506_ = lean_name_eq(v_name_504_, v_name_505_);
if (v___x_506_ == 0)
{
v_x_500_ = v_tail_503_;
goto _start;
}
else
{
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg___boxed(lean_object* v_a_508_, lean_object* v_x_509_){
_start:
{
uint8_t v_res_510_; lean_object* v_r_511_; 
v_res_510_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_508_, v_x_509_);
lean_dec(v_x_509_);
lean_dec_ref(v_a_508_);
v_r_511_ = lean_box(v_res_510_);
return v_r_511_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(lean_object* v_m_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_buckets_514_; lean_object* v_name_515_; lean_object* v___x_516_; uint64_t v___y_518_; 
v_buckets_514_ = lean_ctor_get(v_m_512_, 1);
v_name_515_ = lean_ctor_get(v_a_513_, 1);
v___x_516_ = lean_array_get_size(v_buckets_514_);
if (lean_obj_tag(v_name_515_) == 0)
{
uint64_t v___x_532_; 
v___x_532_ = 1723ULL;
v___y_518_ = v___x_532_;
goto v___jp_517_;
}
else
{
uint64_t v_hash_533_; 
v_hash_533_ = lean_ctor_get_uint64(v_name_515_, sizeof(void*)*2);
v___y_518_ = v_hash_533_;
goto v___jp_517_;
}
v___jp_517_:
{
uint64_t v___x_519_; uint64_t v___x_520_; uint64_t v_fold_521_; uint64_t v___x_522_; uint64_t v___x_523_; uint64_t v___x_524_; size_t v___x_525_; size_t v___x_526_; size_t v___x_527_; size_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_519_ = 32ULL;
v___x_520_ = lean_uint64_shift_right(v___y_518_, v___x_519_);
v_fold_521_ = lean_uint64_xor(v___y_518_, v___x_520_);
v___x_522_ = 16ULL;
v___x_523_ = lean_uint64_shift_right(v_fold_521_, v___x_522_);
v___x_524_ = lean_uint64_xor(v_fold_521_, v___x_523_);
v___x_525_ = lean_uint64_to_usize(v___x_524_);
v___x_526_ = lean_usize_of_nat(v___x_516_);
v___x_527_ = ((size_t)1ULL);
v___x_528_ = lean_usize_sub(v___x_526_, v___x_527_);
v___x_529_ = lean_usize_land(v___x_525_, v___x_528_);
v___x_530_ = lean_array_uget_borrowed(v_buckets_514_, v___x_529_);
v___x_531_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_513_, v___x_530_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg___boxed(lean_object* v_m_534_, lean_object* v_a_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(v_m_534_, v_a_535_);
lean_dec_ref(v_a_535_);
lean_dec_ref(v_m_534_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
return v_x_538_;
}
else
{
lean_object* v_key_540_; lean_object* v_value_541_; lean_object* v_tail_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_569_; 
v_key_540_ = lean_ctor_get(v_x_539_, 0);
v_value_541_ = lean_ctor_get(v_x_539_, 1);
v_tail_542_ = lean_ctor_get(v_x_539_, 2);
v_isSharedCheck_569_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_569_ == 0)
{
v___x_544_ = v_x_539_;
v_isShared_545_ = v_isSharedCheck_569_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_tail_542_);
lean_inc(v_value_541_);
lean_inc(v_key_540_);
lean_dec(v_x_539_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_569_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v_name_546_; lean_object* v___x_547_; uint64_t v___y_549_; 
v_name_546_ = lean_ctor_get(v_key_540_, 1);
v___x_547_ = lean_array_get_size(v_x_538_);
if (lean_obj_tag(v_name_546_) == 0)
{
uint64_t v___x_567_; 
v___x_567_ = 1723ULL;
v___y_549_ = v___x_567_;
goto v___jp_548_;
}
else
{
uint64_t v_hash_568_; 
v_hash_568_ = lean_ctor_get_uint64(v_name_546_, sizeof(void*)*2);
v___y_549_ = v_hash_568_;
goto v___jp_548_;
}
v___jp_548_:
{
uint64_t v___x_550_; uint64_t v___x_551_; uint64_t v_fold_552_; uint64_t v___x_553_; uint64_t v___x_554_; uint64_t v___x_555_; size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; size_t v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_550_ = 32ULL;
v___x_551_ = lean_uint64_shift_right(v___y_549_, v___x_550_);
v_fold_552_ = lean_uint64_xor(v___y_549_, v___x_551_);
v___x_553_ = 16ULL;
v___x_554_ = lean_uint64_shift_right(v_fold_552_, v___x_553_);
v___x_555_ = lean_uint64_xor(v_fold_552_, v___x_554_);
v___x_556_ = lean_uint64_to_usize(v___x_555_);
v___x_557_ = lean_usize_of_nat(v___x_547_);
v___x_558_ = ((size_t)1ULL);
v___x_559_ = lean_usize_sub(v___x_557_, v___x_558_);
v___x_560_ = lean_usize_land(v___x_556_, v___x_559_);
v___x_561_ = lean_array_uget_borrowed(v_x_538_, v___x_560_);
lean_inc(v___x_561_);
if (v_isShared_545_ == 0)
{
lean_ctor_set(v___x_544_, 2, v___x_561_);
v___x_563_ = v___x_544_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_key_540_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_value_541_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v___x_561_);
v___x_563_ = v_reuseFailAlloc_566_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; 
v___x_564_ = lean_array_uset(v_x_538_, v___x_560_, v___x_563_);
v_x_538_ = v___x_564_;
v_x_539_ = v_tail_542_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3___redArg(lean_object* v_i_570_, lean_object* v_source_571_, lean_object* v_target_572_){
_start:
{
lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_573_ = lean_array_get_size(v_source_571_);
v___x_574_ = lean_nat_dec_lt(v_i_570_, v___x_573_);
if (v___x_574_ == 0)
{
lean_dec_ref(v_source_571_);
lean_dec(v_i_570_);
return v_target_572_;
}
else
{
lean_object* v_es_575_; lean_object* v___x_576_; lean_object* v_source_577_; lean_object* v_target_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_es_575_ = lean_array_fget(v_source_571_, v_i_570_);
v___x_576_ = lean_box(0);
v_source_577_ = lean_array_fset(v_source_571_, v_i_570_, v___x_576_);
v_target_578_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6___redArg(v_target_572_, v_es_575_);
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_add(v_i_570_, v___x_579_);
lean_dec(v_i_570_);
v_i_570_ = v___x_580_;
v_source_571_ = v_source_577_;
v_target_572_ = v_target_578_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2___redArg(lean_object* v_data_582_){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_nbuckets_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_583_ = lean_array_get_size(v_data_582_);
v___x_584_ = lean_unsigned_to_nat(2u);
v_nbuckets_585_ = lean_nat_mul(v___x_583_, v___x_584_);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_box(0);
v___x_588_ = lean_mk_array(v_nbuckets_585_, v___x_587_);
v___x_589_ = lean_array_propagate_mark(v_data_582_, v___x_588_);
v___x_590_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3___redArg(v___x_586_, v_data_582_, v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1___redArg(lean_object* v_m_591_, lean_object* v_a_592_, lean_object* v_b_593_){
_start:
{
lean_object* v_size_594_; lean_object* v_buckets_595_; lean_object* v_name_596_; lean_object* v___x_597_; uint64_t v___y_599_; 
v_size_594_ = lean_ctor_get(v_m_591_, 0);
v_buckets_595_ = lean_ctor_get(v_m_591_, 1);
v_name_596_ = lean_ctor_get(v_a_592_, 1);
v___x_597_ = lean_array_get_size(v_buckets_595_);
if (lean_obj_tag(v_name_596_) == 0)
{
uint64_t v___x_636_; 
v___x_636_ = 1723ULL;
v___y_599_ = v___x_636_;
goto v___jp_598_;
}
else
{
uint64_t v_hash_637_; 
v_hash_637_ = lean_ctor_get_uint64(v_name_596_, sizeof(void*)*2);
v___y_599_ = v_hash_637_;
goto v___jp_598_;
}
v___jp_598_:
{
uint64_t v___x_600_; uint64_t v___x_601_; uint64_t v_fold_602_; uint64_t v___x_603_; uint64_t v___x_604_; uint64_t v___x_605_; size_t v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v___x_609_; size_t v___x_610_; lean_object* v_bkt_611_; uint8_t v___x_612_; 
v___x_600_ = 32ULL;
v___x_601_ = lean_uint64_shift_right(v___y_599_, v___x_600_);
v_fold_602_ = lean_uint64_xor(v___y_599_, v___x_601_);
v___x_603_ = 16ULL;
v___x_604_ = lean_uint64_shift_right(v_fold_602_, v___x_603_);
v___x_605_ = lean_uint64_xor(v_fold_602_, v___x_604_);
v___x_606_ = lean_uint64_to_usize(v___x_605_);
v___x_607_ = lean_usize_of_nat(v___x_597_);
v___x_608_ = ((size_t)1ULL);
v___x_609_ = lean_usize_sub(v___x_607_, v___x_608_);
v___x_610_ = lean_usize_land(v___x_606_, v___x_609_);
v_bkt_611_ = lean_array_uget_borrowed(v_buckets_595_, v___x_610_);
v___x_612_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_592_, v_bkt_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_633_; 
lean_inc_ref(v_buckets_595_);
lean_inc(v_size_594_);
v_isSharedCheck_633_ = !lean_is_exclusive(v_m_591_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; lean_object* v_unused_635_; 
v_unused_634_ = lean_ctor_get(v_m_591_, 1);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_m_591_, 0);
lean_dec(v_unused_635_);
v___x_614_ = v_m_591_;
v_isShared_615_ = v_isSharedCheck_633_;
goto v_resetjp_613_;
}
else
{
lean_dec(v_m_591_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_633_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v_size_x27_617_; lean_object* v___x_618_; lean_object* v_buckets_x27_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_616_ = lean_unsigned_to_nat(1u);
v_size_x27_617_ = lean_nat_add(v_size_594_, v___x_616_);
lean_dec(v_size_594_);
lean_inc(v_bkt_611_);
v___x_618_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_618_, 0, v_a_592_);
lean_ctor_set(v___x_618_, 1, v_b_593_);
lean_ctor_set(v___x_618_, 2, v_bkt_611_);
v_buckets_x27_619_ = lean_array_uset(v_buckets_595_, v___x_610_, v___x_618_);
v___x_620_ = lean_unsigned_to_nat(4u);
v___x_621_ = lean_nat_mul(v_size_x27_617_, v___x_620_);
v___x_622_ = lean_unsigned_to_nat(3u);
v___x_623_ = lean_nat_div(v___x_621_, v___x_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_array_get_size(v_buckets_x27_619_);
v___x_625_ = lean_nat_dec_le(v___x_623_, v___x_624_);
lean_dec(v___x_623_);
if (v___x_625_ == 0)
{
lean_object* v_val_626_; lean_object* v___x_628_; 
v_val_626_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2___redArg(v_buckets_x27_619_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v_val_626_);
lean_ctor_set(v___x_614_, 0, v_size_x27_617_);
v___x_628_ = v___x_614_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_size_x27_617_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_val_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
else
{
lean_object* v___x_631_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v_buckets_x27_619_);
lean_ctor_set(v___x_614_, 0, v_size_x27_617_);
v___x_631_ = v___x_614_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_size_x27_617_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_buckets_x27_619_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_dec(v_b_593_);
lean_dec_ref(v_a_592_);
return v_m_591_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(lean_object* v_as_638_, size_t v_sz_639_, size_t v_i_640_, lean_object* v_b_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_a_645_; lean_object* v_a_646_; uint8_t v___x_650_; 
v___x_650_ = lean_usize_dec_lt(v_i_640_, v_sz_639_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v_b_641_);
lean_ctor_set(v___x_651_, 1, v___y_642_);
return v___x_651_;
}
else
{
lean_object* v_fst_652_; lean_object* v_snd_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_668_; 
v_fst_652_ = lean_ctor_get(v_b_641_, 0);
v_snd_653_ = lean_ctor_get(v_b_641_, 1);
v_isSharedCheck_668_ = !lean_is_exclusive(v_b_641_);
if (v_isSharedCheck_668_ == 0)
{
v___x_655_ = v_b_641_;
v_isShared_656_ = v_isSharedCheck_668_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_snd_653_);
lean_inc(v_fst_652_);
lean_dec(v_b_641_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_668_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_a_657_; uint8_t v___x_658_; 
v_a_657_ = lean_array_uget_borrowed(v_as_638_, v_i_640_);
v___x_658_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(v_snd_653_, v_a_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_659_ = lean_box(0);
lean_inc_n(v_a_657_, 2);
v___x_660_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1___redArg(v_snd_653_, v_a_657_, v___x_659_);
v___x_661_ = lean_array_push(v_fst_652_, v_a_657_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v___x_660_);
lean_ctor_set(v___x_655_, 0, v___x_661_);
v___x_663_ = v___x_655_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_660_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
v_a_645_ = v___x_663_;
v_a_646_ = v___y_642_;
goto v___jp_644_;
}
}
else
{
lean_object* v___x_666_; 
if (v_isShared_656_ == 0)
{
v___x_666_ = v___x_655_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_fst_652_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_snd_653_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
v_a_645_ = v___x_666_;
v_a_646_ = v___y_642_;
goto v___jp_644_;
}
}
}
}
v___jp_644_:
{
size_t v___x_647_; size_t v___x_648_; 
v___x_647_ = ((size_t)1ULL);
v___x_648_ = lean_usize_add(v_i_640_, v___x_647_);
v_i_640_ = v___x_648_;
v_b_641_ = v_a_645_;
v___y_642_ = v_a_646_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg___boxed(lean_object* v_as_669_, lean_object* v_sz_670_, lean_object* v_i_671_, lean_object* v_b_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
size_t v_sz_boxed_675_; size_t v_i_boxed_676_; lean_object* v_res_677_; 
v_sz_boxed_675_ = lean_unbox_usize(v_sz_670_);
lean_dec(v_sz_670_);
v_i_boxed_676_ = lean_unbox_usize(v_i_671_);
lean_dec(v_i_671_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(v_as_669_, v_sz_boxed_675_, v_i_boxed_676_, v_b_672_, v___y_673_);
lean_dec_ref(v_as_669_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3(lean_object* v_self_683_, lean_object* v_as_684_, size_t v_sz_685_, size_t v_i_686_, lean_object* v_b_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_a_696_; lean_object* v_a_697_; uint8_t v___x_699_; 
v___x_699_ = lean_usize_dec_lt(v_i_686_, v_sz_685_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
lean_dec_ref(v___y_688_);
lean_dec_ref(v_self_683_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v_b_687_);
lean_ctor_set(v___x_700_, 1, v___y_693_);
return v___x_700_;
}
else
{
lean_object* v_fst_701_; lean_object* v_snd_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_802_; 
v_fst_701_ = lean_ctor_get(v_b_687_, 0);
v_snd_702_ = lean_ctor_get(v_b_687_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v_b_687_);
if (v_isSharedCheck_802_ == 0)
{
v___x_704_ = v_b_687_;
v_isShared_705_ = v_isSharedCheck_802_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_snd_702_);
lean_inc(v_fst_701_);
lean_dec(v_b_687_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_802_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_targetMods_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v_mods_736_; lean_object* v_a_737_; lean_object* v___x_773_; 
v_mods_736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__0));
v_a_737_ = lean_array_uget_borrowed(v_as_684_, v_i_686_);
v___x_773_ = l_Lake_Package_findTargetDecl_x3f(v_a_737_, v_self_683_);
if (lean_obj_tag(v___x_773_) == 0)
{
goto v___jp_738_;
}
else
{
lean_object* v_val_774_; lean_object* v_name_775_; lean_object* v_kind_776_; lean_object* v_config_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_800_; 
v_val_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_val_774_);
lean_dec_ref_known(v___x_773_, 1);
v_name_775_ = lean_ctor_get(v_val_774_, 1);
v_kind_776_ = lean_ctor_get(v_val_774_, 2);
v_config_777_ = lean_ctor_get(v_val_774_, 3);
v_isSharedCheck_800_ = !lean_is_exclusive(v_val_774_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v_val_774_, 0);
lean_dec(v_unused_801_);
v___x_779_ = v_val_774_;
v_isShared_780_ = v_isSharedCheck_800_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_config_777_);
lean_inc(v_kind_776_);
lean_inc(v_name_775_);
lean_dec(v_val_774_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_800_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__2));
v___x_782_ = lean_name_eq(v_kind_776_, v___x_781_);
lean_dec(v_kind_776_);
if (v___x_782_ == 0)
{
lean_del_object(v___x_779_);
lean_dec(v_config_777_);
lean_dec(v_name_775_);
goto v___jp_738_;
}
else
{
lean_object* v_keyName_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_788_; 
v_keyName_783_ = lean_ctor_get(v_self_683_, 2);
lean_inc(v_name_775_);
lean_inc_ref(v_self_683_);
v___x_784_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_784_, 0, v_self_683_);
lean_ctor_set(v___x_784_, 1, v_name_775_);
lean_ctor_set(v___x_784_, 2, v_config_777_);
v___x_785_ = l_Lake_LeanLib_modulesFacet;
lean_inc(v_keyName_783_);
v___x_786_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_786_, 0, v_keyName_783_);
lean_ctor_set(v___x_786_, 1, v_name_775_);
if (v_isShared_780_ == 0)
{
lean_ctor_set_tag(v___x_779_, 1);
lean_ctor_set(v___x_779_, 3, v___x_785_);
lean_ctor_set(v___x_779_, 2, v___x_784_);
lean_ctor_set(v___x_779_, 1, v___x_781_);
lean_ctor_set(v___x_779_, 0, v___x_786_);
v___x_788_ = v___x_779_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v___x_785_);
v___x_788_ = v_reuseFailAlloc_799_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; 
lean_inc_ref(v___y_688_);
lean_inc_ref(v___y_692_);
lean_inc_ref(v___y_691_);
lean_inc(v___y_690_);
lean_inc(v___y_689_);
v___x_789_ = lean_apply_7(v___y_688_, v___x_788_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, lean_box(0));
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v_a_791_; lean_object* v___x_792_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
v_a_791_ = lean_ctor_get(v___x_789_, 1);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_789_, 2);
v___x_792_ = l_Lake_Job_await___redArg(v_a_790_, v_a_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v_a_794_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
v_a_794_ = lean_ctor_get(v___x_792_, 1);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_792_, 2);
lean_inc_ref(v___y_688_);
v_targetMods_707_ = v_a_793_;
v___y_708_ = v___y_688_;
v___y_709_ = v___y_689_;
v___y_710_ = v___y_690_;
v___y_711_ = v___y_691_;
v___y_712_ = v___y_692_;
v___y_713_ = v_a_794_;
goto v___jp_706_;
}
else
{
lean_object* v_a_795_; lean_object* v_a_796_; 
lean_del_object(v___x_704_);
lean_dec(v_snd_702_);
lean_dec(v_fst_701_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v_self_683_);
v_a_795_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_795_);
v_a_796_ = lean_ctor_get(v___x_792_, 1);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_792_, 2);
v_a_696_ = v_a_795_;
v_a_697_ = v_a_796_;
goto v___jp_695_;
}
}
else
{
lean_object* v_a_797_; lean_object* v_a_798_; 
lean_del_object(v___x_704_);
lean_dec(v_snd_702_);
lean_dec(v_fst_701_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v_self_683_);
v_a_797_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_797_);
v_a_798_ = lean_ctor_get(v___x_789_, 1);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_789_, 2);
v_a_696_ = v_a_797_;
v_a_697_ = v_a_798_;
goto v___jp_695_;
}
}
}
}
}
v___jp_706_:
{
lean_object* v___x_715_; 
lean_dec_ref(v___y_708_);
if (v_isShared_705_ == 0)
{
v___x_715_ = v___x_704_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_fst_701_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_snd_702_);
v___x_715_ = v_reuseFailAlloc_735_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
size_t v_sz_716_; size_t v___x_717_; lean_object* v___x_718_; 
v_sz_716_ = lean_array_size(v_targetMods_707_);
v___x_717_ = ((size_t)0ULL);
v___x_718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(v_targetMods_707_, v_sz_716_, v___x_717_, v___x_715_, v___y_713_);
lean_dec_ref(v_targetMods_707_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v_a_720_; lean_object* v_fst_721_; lean_object* v_snd_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_732_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
v_a_720_ = lean_ctor_get(v___x_718_, 1);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_718_, 2);
v_fst_721_ = lean_ctor_get(v_a_719_, 0);
v_snd_722_ = lean_ctor_get(v_a_719_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_a_719_);
if (v_isSharedCheck_732_ == 0)
{
v___x_724_ = v_a_719_;
v_isShared_725_ = v_isSharedCheck_732_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_snd_722_);
lean_inc(v_fst_721_);
lean_dec(v_a_719_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_732_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_fst_721_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_snd_722_);
v___x_727_ = v_reuseFailAlloc_731_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
size_t v___x_728_; size_t v___x_729_; 
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_add(v_i_686_, v___x_728_);
v_i_686_ = v___x_729_;
v_b_687_ = v___x_727_;
v___y_693_ = v_a_720_;
goto _start;
}
}
}
else
{
lean_object* v_a_733_; lean_object* v_a_734_; 
lean_dec_ref(v___y_688_);
lean_dec_ref(v_self_683_);
v_a_733_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_733_);
v_a_734_ = lean_ctor_get(v___x_718_, 1);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_718_, 2);
v_a_696_ = v_a_733_;
v_a_697_ = v_a_734_;
goto v___jp_695_;
}
}
}
v___jp_738_:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lake_Package_findTargetDecl_x3f(v_a_737_, v_self_683_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_inc_ref(v___y_688_);
v_targetMods_707_ = v_mods_736_;
v___y_708_ = v___y_688_;
v___y_709_ = v___y_689_;
v___y_710_ = v___y_690_;
v___y_711_ = v___y_691_;
v___y_712_ = v___y_692_;
v___y_713_ = v___y_693_;
goto v___jp_706_;
}
else
{
lean_object* v_val_740_; lean_object* v_name_741_; lean_object* v_kind_742_; lean_object* v_config_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_771_; 
v_val_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v___x_739_, 1);
v_name_741_ = lean_ctor_get(v_val_740_, 1);
v_kind_742_ = lean_ctor_get(v_val_740_, 2);
v_config_743_ = lean_ctor_get(v_val_740_, 3);
v_isSharedCheck_771_ = !lean_is_exclusive(v_val_740_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v_val_740_, 0);
lean_dec(v_unused_772_);
v___x_745_ = v_val_740_;
v_isShared_746_ = v_isSharedCheck_771_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_config_743_);
lean_inc(v_kind_742_);
lean_inc(v_name_741_);
lean_dec(v_val_740_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_771_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_747_ = l_Lake_LeanExe_keyword;
v___x_748_ = lean_name_eq(v_kind_742_, v___x_747_);
lean_dec(v_kind_742_);
if (v___x_748_ == 0)
{
lean_del_object(v___x_745_);
lean_dec(v_config_743_);
lean_dec(v_name_741_);
lean_inc_ref(v___y_688_);
v_targetMods_707_ = v_mods_736_;
v___y_708_ = v___y_688_;
v___y_709_ = v___y_689_;
v___y_710_ = v___y_690_;
v___y_711_ = v___y_691_;
v___y_712_ = v___y_692_;
v___y_713_ = v___y_693_;
goto v___jp_706_;
}
else
{
lean_object* v_root_749_; lean_object* v_keyName_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v_root_749_ = lean_ctor_get(v_config_743_, 2);
lean_inc_n(v_root_749_, 2);
v_keyName_750_ = lean_ctor_get(v_self_683_, 2);
v___x_751_ = l_Lake_LeanExeConfig_toLeanLibConfig___redArg(v_config_743_);
lean_dec(v_config_743_);
lean_inc_ref(v_self_683_);
v___x_752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_752_, 0, v_self_683_);
lean_ctor_set(v___x_752_, 1, v_name_741_);
lean_ctor_set(v___x_752_, 2, v___x_751_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v_root_749_);
v___x_754_ = l_Lake_Module_transImportsFacet;
lean_inc(v_keyName_750_);
v___x_755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_755_, 0, v_keyName_750_);
lean_ctor_set(v___x_755_, 1, v_root_749_);
v___x_756_ = l_Lake_Module_keyword;
lean_inc_ref(v___x_753_);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 1);
lean_ctor_set(v___x_745_, 3, v___x_754_);
lean_ctor_set(v___x_745_, 2, v___x_753_);
lean_ctor_set(v___x_745_, 1, v___x_756_);
lean_ctor_set(v___x_745_, 0, v___x_755_);
v___x_758_ = v___x_745_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v___x_754_);
v___x_758_ = v_reuseFailAlloc_770_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; 
lean_inc_ref(v___y_688_);
lean_inc_ref(v___y_692_);
lean_inc_ref(v___y_691_);
lean_inc(v___y_690_);
lean_inc(v___y_689_);
v___x_759_ = lean_apply_7(v___y_688_, v___x_758_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, lean_box(0));
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v_a_761_; lean_object* v___x_762_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
v_a_761_ = lean_ctor_get(v___x_759_, 1);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_759_, 2);
v___x_762_ = l_Lake_Job_await___redArg(v_a_760_, v_a_761_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
v_a_764_ = lean_ctor_get(v___x_762_, 1);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_762_, 2);
v___x_765_ = lean_array_push(v_a_763_, v___x_753_);
lean_inc_ref(v___y_688_);
v_targetMods_707_ = v___x_765_;
v___y_708_ = v___y_688_;
v___y_709_ = v___y_689_;
v___y_710_ = v___y_690_;
v___y_711_ = v___y_691_;
v___y_712_ = v___y_692_;
v___y_713_ = v_a_764_;
goto v___jp_706_;
}
else
{
lean_object* v_a_766_; lean_object* v_a_767_; 
lean_dec_ref_known(v___x_753_, 2);
lean_del_object(v___x_704_);
lean_dec(v_snd_702_);
lean_dec(v_fst_701_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v_self_683_);
v_a_766_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_766_);
v_a_767_ = lean_ctor_get(v___x_762_, 1);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_762_, 2);
v_a_696_ = v_a_766_;
v_a_697_ = v_a_767_;
goto v___jp_695_;
}
}
else
{
lean_object* v_a_768_; lean_object* v_a_769_; 
lean_dec_ref_known(v___x_753_, 2);
lean_del_object(v___x_704_);
lean_dec(v_snd_702_);
lean_dec(v_fst_701_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v_self_683_);
v_a_768_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_768_);
v_a_769_ = lean_ctor_get(v___x_759_, 1);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_759_, 2);
v_a_696_ = v_a_768_;
v_a_697_ = v_a_769_;
goto v___jp_695_;
}
}
}
}
}
}
}
}
v___jp_695_:
{
lean_object* v___x_698_; 
v___x_698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_698_, 0, v_a_696_);
lean_ctor_set(v___x_698_, 1, v_a_697_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___boxed(lean_object* v_self_803_, lean_object* v_as_804_, lean_object* v_sz_805_, lean_object* v_i_806_, lean_object* v_b_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
size_t v_sz_boxed_815_; size_t v_i_boxed_816_; lean_object* v_res_817_; 
v_sz_boxed_815_ = lean_unbox_usize(v_sz_805_);
lean_dec(v_sz_805_);
v_i_boxed_816_ = lean_unbox_usize(v_i_806_);
lean_dec(v_i_806_);
v_res_817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3(v_self_803_, v_as_804_, v_sz_boxed_815_, v_i_boxed_816_, v_b_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v_as_804_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0(lean_object* v_self_818_, lean_object* v_defaultTargets_819_, size_t v_sz_820_, size_t v___x_821_, lean_object* v___x_822_, lean_object* v___x_823_, lean_object* v___x_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3(v_self_818_, v_defaultTargets_819_, v_sz_820_, v___x_821_, v___x_822_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_858_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_a_834_ = lean_ctor_get(v___x_832_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_858_ == 0)
{
v___x_836_ = v___x_832_;
v_isShared_837_ = v_isSharedCheck_858_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_858_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v_fst_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_856_; 
v_fst_838_ = lean_ctor_get(v_a_833_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_a_833_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v_a_833_, 1);
lean_dec(v_unused_857_);
v___x_840_ = v_a_833_;
v_isShared_841_ = v_isSharedCheck_856_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_fst_838_);
lean_dec(v_a_833_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_856_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_842_ = lean_mk_empty_array_with_capacity(v___x_823_);
v___x_843_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_844_ = 0;
v___x_845_ = 0;
v___x_846_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_847_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_847_, 0, v___x_842_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
lean_ctor_set(v___x_847_, 2, v___x_823_);
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*3, v___x_844_);
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*3 + 1, v___x_845_);
lean_ctor_set_uint8(v___x_847_, sizeof(void*)*3 + 2, v___x_845_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v___x_847_);
lean_ctor_set(v___x_836_, 0, v_fst_838_);
v___x_849_ = v___x_836_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_fst_838_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_847_);
v___x_849_ = v_reuseFailAlloc_855_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_850_ = lean_task_pure(v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v___x_824_);
lean_ctor_set(v___x_851_, 2, v___x_843_);
lean_ctor_set_uint8(v___x_851_, sizeof(void*)*3, v___x_845_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v_a_834_);
lean_ctor_set(v___x_840_, 0, v___x_851_);
v___x_853_ = v___x_840_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_a_834_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
else
{
lean_object* v_a_859_; lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v___x_824_);
lean_dec(v___x_823_);
v_a_859_ = lean_ctor_get(v___x_832_, 0);
v_a_860_ = lean_ctor_get(v___x_832_, 1);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_832_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_inc(v_a_859_);
lean_dec(v___x_832_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_859_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0___boxed(lean_object* v_self_868_, lean_object* v_defaultTargets_869_, lean_object* v_sz_870_, lean_object* v___x_871_, lean_object* v___x_872_, lean_object* v___x_873_, lean_object* v___x_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
size_t v_sz_boxed_882_; size_t v___x_15567__boxed_883_; lean_object* v_res_884_; 
v_sz_boxed_882_ = lean_unbox_usize(v_sz_870_);
lean_dec(v_sz_870_);
v___x_15567__boxed_883_ = lean_unbox_usize(v___x_871_);
lean_dec(v___x_871_);
v_res_884_ = l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0(v_self_868_, v_defaultTargets_869_, v_sz_boxed_882_, v___x_15567__boxed_883_, v___x_872_, v___x_873_, v___x_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v_defaultTargets_869_);
return v_res_884_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_box(0);
v___x_886_ = lean_unsigned_to_nat(16u);
v___x_887_ = lean_mk_array(v___x_886_, v___x_885_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_seen_890_; 
v___x_888_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0, &l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__0);
v___x_889_ = lean_unsigned_to_nat(0u);
v_seen_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_seen_890_, 0, v___x_889_);
lean_ctor_set(v_seen_890_, 1, v___x_888_);
return v_seen_890_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2(void){
_start:
{
lean_object* v_seen_891_; lean_object* v_mods_892_; lean_object* v___x_893_; 
v_seen_891_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1, &l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__1);
v_mods_892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__3___closed__0));
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v_mods_892_);
lean_ctor_set(v___x_893_, 1, v_seen_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules(lean_object* v_self_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_defaultTargets_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; size_t v_sz_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___f_911_; lean_object* v___x_912_; 
v_defaultTargets_904_ = lean_ctor_get(v_self_896_, 17);
lean_inc_ref(v_defaultTargets_904_);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_box(0);
v___x_907_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___closed__2);
v_sz_908_ = lean_array_size(v_defaultTargets_904_);
v___x_909_ = lean_box_usize(v_sz_908_);
v___x_910_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___boxed__const__1));
v___f_911_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0___boxed), 14, 7);
lean_closure_set(v___f_911_, 0, v_self_896_);
lean_closure_set(v___f_911_, 1, v_defaultTargets_904_);
lean_closure_set(v___f_911_, 2, v___x_909_);
lean_closure_set(v___f_911_, 3, v___x_910_);
lean_closure_set(v___f_911_, 4, v___x_907_);
lean_closure_set(v___f_911_, 5, v___x_905_);
lean_closure_set(v___f_911_, 6, v___x_906_);
v___x_912_ = l_Lake_ensureJob___redArg(v___x_906_, v___f_911_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___boxed(lean_object* v_self_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules(v_self_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec(v_a_915_);
return v_res_921_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0(lean_object* v_00_u03b2_922_, lean_object* v_m_923_, lean_object* v_a_924_){
_start:
{
uint8_t v___x_925_; 
v___x_925_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___redArg(v_m_923_, v_a_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0___boxed(lean_object* v_00_u03b2_926_, lean_object* v_m_927_, lean_object* v_a_928_){
_start:
{
uint8_t v_res_929_; lean_object* v_r_930_; 
v_res_929_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0(v_00_u03b2_926_, v_m_927_, v_a_928_);
lean_dec_ref(v_a_928_);
lean_dec_ref(v_m_927_);
v_r_930_ = lean_box(v_res_929_);
return v_r_930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1(lean_object* v_00_u03b2_931_, lean_object* v_m_932_, lean_object* v_a_933_, lean_object* v_b_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1___redArg(v_m_932_, v_a_933_, v_b_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2(lean_object* v_as_936_, size_t v_sz_937_, size_t v_i_938_, lean_object* v_b_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___redArg(v_as_936_, v_sz_937_, v_i_938_, v_b_939_, v___y_945_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2___boxed(lean_object* v_as_948_, lean_object* v_sz_949_, lean_object* v_i_950_, lean_object* v_b_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
size_t v_sz_boxed_959_; size_t v_i_boxed_960_; lean_object* v_res_961_; 
v_sz_boxed_959_ = lean_unbox_usize(v_sz_949_);
lean_dec(v_sz_949_);
v_i_boxed_960_ = lean_unbox_usize(v_i_950_);
lean_dec(v_i_950_);
v_res_961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__2(v_as_948_, v_sz_boxed_959_, v_i_boxed_960_, v_b_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec_ref(v_as_948_);
return v_res_961_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0(lean_object* v_00_u03b2_962_, lean_object* v_a_963_, lean_object* v_x_964_){
_start:
{
uint8_t v___x_965_; 
v___x_965_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___redArg(v_a_963_, v_x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0___boxed(lean_object* v_00_u03b2_966_, lean_object* v_a_967_, lean_object* v_x_968_){
_start:
{
uint8_t v_res_969_; lean_object* v_r_970_; 
v_res_969_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__0_spec__0(v_00_u03b2_966_, v_a_967_, v_x_968_);
lean_dec(v_x_968_);
lean_dec_ref(v_a_967_);
v_r_970_ = lean_box(v_res_969_);
return v_r_970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2(lean_object* v_00_u03b2_971_, lean_object* v_data_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2___redArg(v_data_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_974_, lean_object* v_i_975_, lean_object* v_source_976_, lean_object* v_target_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3___redArg(v_i_975_, v_source_976_, v_target_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_979_, lean_object* v_x_980_, lean_object* v_x_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules_spec__1_spec__2_spec__3_spec__6___redArg(v_x_980_, v_x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0(lean_object* v_as_983_, size_t v_i_984_, size_t v_stop_985_, lean_object* v_b_986_){
_start:
{
uint8_t v___x_987_; 
v___x_987_ = lean_usize_dec_eq(v_i_984_, v_stop_985_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v_name_989_; uint8_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; size_t v___x_995_; size_t v___x_996_; 
v___x_988_ = lean_array_uget_borrowed(v_as_983_, v_i_984_);
v_name_989_ = lean_ctor_get(v___x_988_, 1);
v___x_990_ = 1;
lean_inc(v_name_989_);
v___x_991_ = l_Lean_Name_toString(v_name_989_, v___x_990_);
v___x_992_ = lean_string_append(v_b_986_, v___x_991_);
lean_dec_ref(v___x_991_);
v___x_993_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_depsFacetConfig_spec__0_spec__0___closed__0));
v___x_994_ = lean_string_append(v___x_992_, v___x_993_);
v___x_995_ = ((size_t)1ULL);
v___x_996_ = lean_usize_add(v_i_984_, v___x_995_);
v_i_984_ = v___x_996_;
v_b_986_ = v___x_994_;
goto _start;
}
else
{
return v_b_986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0___boxed(lean_object* v_as_998_, lean_object* v_i_999_, lean_object* v_stop_1000_, lean_object* v_b_1001_){
_start:
{
size_t v_i_boxed_1002_; size_t v_stop_boxed_1003_; lean_object* v_res_1004_; 
v_i_boxed_1002_ = lean_unbox_usize(v_i_999_);
lean_dec(v_i_999_);
v_stop_boxed_1003_ = lean_unbox_usize(v_stop_1000_);
lean_dec(v_stop_1000_);
v_res_1004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0(v_as_998_, v_i_boxed_1002_, v_stop_boxed_1003_, v_b_1001_);
lean_dec_ref(v_as_998_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2(size_t v_sz_1005_, size_t v_i_1006_, lean_object* v_bs_1007_){
_start:
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_usize_dec_lt(v_i_1006_, v_sz_1005_);
if (v___x_1008_ == 0)
{
return v_bs_1007_;
}
else
{
lean_object* v_v_1009_; lean_object* v_name_1010_; lean_object* v___x_1011_; lean_object* v_bs_x27_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; size_t v___x_1015_; size_t v___x_1016_; lean_object* v___x_1017_; 
v_v_1009_ = lean_array_uget_borrowed(v_bs_1007_, v_i_1006_);
v_name_1010_ = lean_ctor_get(v_v_1009_, 1);
lean_inc(v_name_1010_);
v___x_1011_ = lean_unsigned_to_nat(0u);
v_bs_x27_1012_ = lean_array_uset(v_bs_1007_, v_i_1006_, v___x_1011_);
v___x_1013_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1010_, v___x_1008_);
v___x_1014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
v___x_1015_ = ((size_t)1ULL);
v___x_1016_ = lean_usize_add(v_i_1006_, v___x_1015_);
v___x_1017_ = lean_array_uset(v_bs_x27_1012_, v_i_1006_, v___x_1014_);
v_i_1006_ = v___x_1016_;
v_bs_1007_ = v___x_1017_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2___boxed(lean_object* v_sz_1019_, lean_object* v_i_1020_, lean_object* v_bs_1021_){
_start:
{
size_t v_sz_boxed_1022_; size_t v_i_boxed_1023_; lean_object* v_res_1024_; 
v_sz_boxed_1022_ = lean_unbox_usize(v_sz_1019_);
lean_dec(v_sz_1019_);
v_i_boxed_1023_ = lean_unbox_usize(v_i_1020_);
lean_dec(v_i_1020_);
v_res_1024_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2(v_sz_boxed_1022_, v_i_boxed_1023_, v_bs_1021_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1(lean_object* v_a_1025_){
_start:
{
size_t v_sz_1026_; size_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_sz_1026_ = lean_array_size(v_a_1025_);
v___x_1027_ = ((size_t)0ULL);
v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1_spec__2(v_sz_1026_, v___x_1027_, v_a_1025_);
v___x_1029_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0(uint8_t v_fmt_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v___y_1033_; 
if (v_fmt_1030_ == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1040_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = lean_array_get_size(v_a_1031_);
v___x_1043_ = lean_nat_dec_lt(v___x_1041_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_dec_ref(v_a_1031_);
v___y_1033_ = v___x_1040_;
goto v___jp_1032_;
}
else
{
size_t v___x_1044_; size_t v___x_1045_; lean_object* v___x_1046_; 
v___x_1044_ = ((size_t)0ULL);
v___x_1045_ = lean_usize_of_nat(v___x_1042_);
v___x_1046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__0(v_a_1031_, v___x_1044_, v___x_1045_, v___x_1040_);
lean_dec_ref(v_a_1031_);
v___y_1033_ = v___x_1046_;
goto v___jp_1032_;
}
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = l_Lean_Array_toJson___at___00Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0_spec__1(v_a_1031_);
v___x_1048_ = l_Lean_Json_compress(v___x_1047_);
return v___x_1048_;
}
v___jp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1034_ = lean_unsigned_to_nat(1u);
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = lean_string_utf8_byte_size(v___y_1033_);
lean_inc_ref(v___y_1033_);
v___x_1037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1037_, 0, v___y_1033_);
lean_ctor_set(v___x_1037_, 1, v___x_1035_);
lean_ctor_set(v___x_1037_, 2, v___x_1036_);
v___x_1038_ = l_String_Slice_Pos_prevn(v___x_1037_, v___x_1036_, v___x_1034_);
lean_dec_ref_known(v___x_1037_, 3);
v___x_1039_ = lean_string_utf8_extract_fast(v___y_1033_, v___x_1035_, v___x_1038_);
lean_dec(v___x_1038_);
lean_dec_ref(v___y_1033_);
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0___boxed(lean_object* v_fmt_1049_, lean_object* v_a_1050_){
_start:
{
uint8_t v_fmt_boxed_1051_; lean_object* v_res_1052_; 
v_fmt_boxed_1051_ = lean_unbox(v_fmt_1049_);
v_res_1052_ = l_Lake_formatQuery___at___00Lake_Package_defaultModulesFacetConfig_spec__0(v_fmt_boxed_1051_, v_a_1050_);
return v_res_1052_;
}
}
static lean_object* _init_l_Lake_Package_defaultModulesFacetConfig___closed__2(void){
_start:
{
uint8_t v___x_1055_; lean_object* v___f_1056_; uint8_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1055_ = 1;
v___f_1056_ = ((lean_object*)(l_Lake_Package_defaultModulesFacetConfig___closed__0));
v___x_1057_ = 0;
v___x_1058_ = lean_box(0);
v___x_1059_ = ((lean_object*)(l_Lake_Package_defaultModulesFacetConfig___closed__1));
v___x_1060_ = l_Lake_Package_keyword;
v___x_1061_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v___x_1059_);
lean_ctor_set(v___x_1061_, 2, v___x_1058_);
lean_ctor_set(v___x_1061_, 3, v___f_1056_);
lean_ctor_set_uint8(v___x_1061_, sizeof(void*)*4, v___x_1057_);
lean_ctor_set_uint8(v___x_1061_, sizeof(void*)*4 + 1, v___x_1055_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lake_Package_defaultModulesFacetConfig(void){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_obj_once(&l_Lake_Package_defaultModulesFacetConfig___closed__2, &l_Lake_Package_defaultModulesFacetConfig___closed__2_once, _init_l_Lake_Package_defaultModulesFacetConfig___closed__2);
return v___x_1062_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig___closed__1(void){
_start:
{
uint8_t v___x_1064_; lean_object* v___f_1065_; uint8_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1064_ = 1;
v___f_1065_ = ((lean_object*)(l_Lake_Package_depsFacetConfig___closed__0));
v___x_1066_ = 0;
v___x_1067_ = lean_box(0);
v___x_1068_ = ((lean_object*)(l_Lake_Package_transDepsFacetConfig___closed__0));
v___x_1069_ = l_Lake_Package_keyword;
v___x_1070_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1068_);
lean_ctor_set(v___x_1070_, 2, v___x_1067_);
lean_ctor_set(v___x_1070_, 3, v___f_1065_);
lean_ctor_set_uint8(v___x_1070_, sizeof(void*)*4, v___x_1066_);
lean_ctor_set_uint8(v___x_1070_, sizeof(void*)*4 + 1, v___x_1064_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lake_Package_transDepsFacetConfig(void){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_obj_once(&l_Lake_Package_transDepsFacetConfig___closed__1, &l_Lake_Package_transDepsFacetConfig___closed__1_once, _init_l_Lake_Package_transDepsFacetConfig___closed__1);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(lean_object* v_self_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_config_1080_; uint8_t v_preferReleaseBuild_1081_; 
v_config_1080_ = lean_ctor_get(v_self_1072_, 6);
v_preferReleaseBuild_1081_ = lean_ctor_get_uint8(v_config_1080_, sizeof(void*)*29 + 2);
if (v_preferReleaseBuild_1081_ == 0)
{
lean_object* v_downloadCacheService_x3f_1082_; 
v_downloadCacheService_x3f_1082_ = lean_ctor_get(v_config_1080_, 12);
lean_inc(v_downloadCacheService_x3f_1082_);
if (lean_obj_tag(v_downloadCacheService_x3f_1082_) == 0)
{
lean_object* v_keyName_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v_keyName_1083_ = lean_ctor_get(v_self_1072_, 2);
v___x_1084_ = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(v_keyName_1083_);
v___x_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1085_, 0, v_keyName_1083_);
v___x_1086_ = l_Lake_Package_keyword;
v___x_1087_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
lean_ctor_set(v___x_1087_, 2, v_self_1072_);
lean_ctor_set(v___x_1087_, 3, v___x_1084_);
lean_inc_ref(v_a_1077_);
lean_inc_ref(v_a_1076_);
lean_inc(v_a_1075_);
lean_inc(v_a_1074_);
v___x_1088_ = lean_apply_7(v_a_1073_, v___x_1087_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, lean_box(0));
return v___x_1088_;
}
else
{
lean_object* v_keyName_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1100_; 
v_keyName_1089_ = lean_ctor_get(v_self_1072_, 2);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_downloadCacheService_x3f_1082_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v_downloadCacheService_x3f_1082_, 0);
lean_dec(v_unused_1101_);
v___x_1091_ = v_downloadCacheService_x3f_1082_;
v_isShared_1092_ = v_isSharedCheck_1100_;
goto v_resetjp_1090_;
}
else
{
lean_dec(v_downloadCacheService_x3f_1082_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1100_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1093_ = l_Lake_Package_optArtifactCacheFacet;
lean_inc(v_keyName_1089_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v_keyName_1089_);
v___x_1095_ = v___x_1091_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_keyName_1089_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = l_Lake_Package_keyword;
v___x_1097_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
lean_ctor_set(v___x_1097_, 2, v_self_1072_);
lean_ctor_set(v___x_1097_, 3, v___x_1093_);
lean_inc_ref(v_a_1077_);
lean_inc_ref(v_a_1076_);
lean_inc(v_a_1075_);
lean_inc(v_a_1074_);
v___x_1098_ = lean_apply_7(v_a_1073_, v___x_1097_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, lean_box(0));
return v___x_1098_;
}
}
}
}
else
{
lean_object* v_keyName_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_keyName_1102_ = lean_ctor_get(v_self_1072_, 2);
v___x_1103_ = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(v_keyName_1102_);
v___x_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_keyName_1102_);
v___x_1105_ = l_Lake_Package_keyword;
v___x_1106_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1104_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
lean_ctor_set(v___x_1106_, 2, v_self_1072_);
lean_ctor_set(v___x_1106_, 3, v___x_1103_);
lean_inc_ref(v_a_1077_);
lean_inc_ref(v_a_1076_);
lean_inc(v_a_1075_);
lean_inc(v_a_1074_);
v___x_1107_ = lean_apply_7(v_a_1073_, v___x_1106_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, lean_box(0));
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___boxed(lean_object* v_self_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(v_self_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec(v_a_1110_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t v_fmt_1119_, uint8_t v_a_1120_){
_start:
{
if (v_fmt_1119_ == 0)
{
if (v_a_1120_ == 0)
{
lean_object* v___x_1121_; 
v___x_1121_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0));
return v___x_1121_;
}
else
{
lean_object* v___x_1122_; 
v___x_1122_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1));
return v___x_1122_;
}
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1123_, 0, v_a_1120_);
v___x_1124_ = l_Lean_Json_compress(v___x_1123_);
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object* v_fmt_1125_, lean_object* v_a_1126_){
_start:
{
uint8_t v_fmt_boxed_1127_; uint8_t v_a_boxed_1128_; lean_object* v_res_1129_; 
v_fmt_boxed_1127_ = lean_unbox(v_fmt_1125_);
v_a_boxed_1128_ = lean_unbox(v_a_1126_);
v_res_1129_ = l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(v_fmt_boxed_1127_, v_a_boxed_1128_);
return v_res_1129_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1132_; uint8_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___f_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___f_1132_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_1133_ = 1;
v___x_1134_ = l_Lake_instDataKindBool;
v___f_1135_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__0));
v___x_1136_ = l_Lake_Package_keyword;
v___x_1137_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v___f_1135_);
lean_ctor_set(v___x_1137_, 2, v___x_1134_);
lean_ctor_set(v___x_1137_, 3, v___f_1132_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*4, v___x_1133_);
lean_ctor_set_uint8(v___x_1137_, sizeof(void*)*4 + 1, v___x_1133_);
return v___x_1137_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig(void){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_obj_once(&l_Lake_Package_optBuildCacheFacetConfig___closed__2, &l_Lake_Package_optBuildCacheFacetConfig___closed__2_once, _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(lean_object* v_self_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1158_; uint8_t v___y_1159_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; uint8_t v___y_1177_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; uint8_t v___y_1186_; lean_object* v_toContext_1191_; lean_object* v_lakeEnv_1192_; lean_object* v_packages_1193_; uint8_t v_noCache_1194_; lean_object* v_enableArtifactCache_x3f_1195_; lean_object* v_toolchain_1196_; uint8_t v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; uint8_t v___y_1202_; uint8_t v___y_1203_; uint8_t v_a_1204_; lean_object* v_a_1205_; uint8_t v_a_1208_; lean_object* v_a_1209_; 
v_toContext_1191_ = lean_ctor_get(v_a_1146_, 1);
v_lakeEnv_1192_ = lean_ctor_get(v_toContext_1191_, 0);
v_packages_1193_ = lean_ctor_get(v_toContext_1191_, 4);
v_noCache_1194_ = lean_ctor_get_uint8(v_lakeEnv_1192_, sizeof(void*)*20);
v_enableArtifactCache_x3f_1195_ = lean_ctor_get(v_lakeEnv_1192_, 6);
v_toolchain_1196_ = lean_ctor_get(v_lakeEnv_1192_, 19);
if (v_noCache_1194_ == 0)
{
uint8_t v___x_1232_; 
v___x_1232_ = 1;
v_a_1208_ = v___x_1232_;
v_a_1209_ = v_a_1147_;
goto v___jp_1207_;
}
else
{
uint8_t v___x_1233_; 
v___x_1233_ = 0;
v_a_1208_ = v___x_1233_;
v_a_1209_ = v_a_1147_;
goto v___jp_1207_;
}
v___jp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1152_ = l_Lake_Package_optBuildCacheFacet;
v___x_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___y_1151_);
v___x_1154_ = l_Lake_Package_keyword;
v___x_1155_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
lean_ctor_set(v___x_1155_, 2, v_self_1141_);
lean_ctor_set(v___x_1155_, 3, v___x_1152_);
lean_inc_ref(v_a_1146_);
lean_inc_ref(v_a_1145_);
lean_inc(v_a_1144_);
lean_inc(v_a_1143_);
v___x_1156_ = lean_apply_7(v_a_1142_, v___x_1155_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v___y_1150_, lean_box(0));
return v___x_1156_;
}
v___jp_1157_:
{
uint8_t v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1160_ = 1;
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1164_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1165_ = 0;
v___x_1166_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_1167_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1167_, 0, v___x_1163_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
lean_ctor_set(v___x_1167_, 2, v___x_1162_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*3, v___x_1165_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*3 + 1, v___y_1159_);
lean_ctor_set_uint8(v___x_1167_, sizeof(void*)*3 + 2, v___y_1159_);
v___x_1168_ = lean_box(v___x_1160_);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
lean_ctor_set(v___x_1169_, 1, v___x_1167_);
v___x_1170_ = lean_task_pure(v___x_1169_);
v___x_1171_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
lean_ctor_set(v___x_1171_, 1, v___x_1161_);
lean_ctor_set(v___x_1171_, 2, v___x_1164_);
lean_ctor_set_uint8(v___x_1171_, sizeof(void*)*3, v___y_1159_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v___y_1158_);
return v___x_1172_;
}
v___jp_1173_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1178_ = lean_string_utf8_byte_size(v___y_1174_);
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = lean_nat_dec_eq(v___x_1178_, v___x_1179_);
if (v___x_1180_ == 0)
{
v___y_1150_ = v___y_1176_;
v___y_1151_ = v___y_1175_;
goto v___jp_1149_;
}
else
{
lean_dec(v___y_1175_);
lean_dec_ref(v_a_1142_);
lean_dec_ref(v_self_1141_);
v___y_1158_ = v___y_1176_;
v___y_1159_ = v___y_1177_;
goto v___jp_1157_;
}
}
v___jp_1181_:
{
if (v___y_1186_ == 0)
{
lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0));
v___x_1188_ = lean_string_dec_eq(v___y_1183_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; uint8_t v___x_1190_; 
v___x_1189_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1));
v___x_1190_ = lean_string_dec_eq(v___y_1183_, v___x_1189_);
lean_dec_ref(v___y_1183_);
if (v___x_1190_ == 0)
{
lean_dec(v___y_1185_);
lean_dec_ref(v_a_1142_);
lean_dec_ref(v_self_1141_);
v___y_1158_ = v___y_1184_;
v___y_1159_ = v___x_1190_;
goto v___jp_1157_;
}
else
{
v___y_1174_ = v___y_1182_;
v___y_1175_ = v___y_1185_;
v___y_1176_ = v___y_1184_;
v___y_1177_ = v___y_1186_;
goto v___jp_1173_;
}
}
else
{
lean_dec_ref(v___y_1183_);
v___y_1174_ = v___y_1182_;
v___y_1175_ = v___y_1185_;
v___y_1176_ = v___y_1184_;
v___y_1177_ = v___y_1186_;
goto v___jp_1173_;
}
}
else
{
lean_dec_ref(v___y_1183_);
v___y_1150_ = v___y_1184_;
v___y_1151_ = v___y_1185_;
goto v___jp_1149_;
}
}
v___jp_1197_:
{
if (v___y_1202_ == 0)
{
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v_a_1142_);
lean_dec_ref(v_self_1141_);
v___y_1158_ = v_a_1205_;
v___y_1159_ = v___y_1202_;
goto v___jp_1157_;
}
else
{
if (v___y_1198_ == 0)
{
if (lean_obj_tag(v___y_1199_) == 0)
{
v___y_1182_ = v_toolchain_1196_;
v___y_1183_ = v___y_1200_;
v___y_1184_ = v_a_1205_;
v___y_1185_ = v___y_1201_;
v___y_1186_ = v___y_1203_;
goto v___jp_1181_;
}
else
{
lean_dec_ref_known(v___y_1199_, 1);
if (v_a_1204_ == 0)
{
v___y_1182_ = v_toolchain_1196_;
v___y_1183_ = v___y_1200_;
v___y_1184_ = v_a_1205_;
v___y_1185_ = v___y_1201_;
v___y_1186_ = v___y_1203_;
goto v___jp_1181_;
}
else
{
lean_dec_ref(v___y_1200_);
v___y_1150_ = v_a_1205_;
v___y_1151_ = v___y_1201_;
goto v___jp_1149_;
}
}
}
else
{
uint8_t v___x_1206_; 
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v_a_1142_);
lean_dec_ref(v_self_1141_);
v___x_1206_ = 0;
v___y_1158_ = v_a_1205_;
v___y_1159_ = v___x_1206_;
goto v___jp_1157_;
}
}
}
v___jp_1207_:
{
lean_object* v_config_1210_; lean_object* v_keyName_1211_; lean_object* v_dir_1212_; lean_object* v_scope_1213_; lean_object* v_buildDir_1214_; uint8_t v_preferReleaseBuild_1215_; lean_object* v_downloadCacheService_x3f_1216_; lean_object* v_enableArtifactCache_x3f_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v_config_1210_ = lean_ctor_get(v_self_1141_, 6);
v_keyName_1211_ = lean_ctor_get(v_self_1141_, 2);
v_dir_1212_ = lean_ctor_get(v_self_1141_, 4);
v_scope_1213_ = lean_ctor_get(v_self_1141_, 10);
v_buildDir_1214_ = lean_ctor_get(v_config_1210_, 5);
v_preferReleaseBuild_1215_ = lean_ctor_get_uint8(v_config_1210_, sizeof(void*)*29 + 2);
v_downloadCacheService_x3f_1216_ = lean_ctor_get(v_config_1210_, 12);
v_enableArtifactCache_x3f_1217_ = lean_ctor_get(v_config_1210_, 25);
lean_inc_ref(v_buildDir_1214_);
v___x_1218_ = l_System_FilePath_normalize(v_buildDir_1214_);
lean_inc_ref(v_dir_1212_);
v___x_1219_ = l_Lake_joinRelative(v_dir_1212_, v___x_1218_);
v___x_1220_ = l_System_FilePath_pathExists(v___x_1219_);
lean_dec_ref(v___x_1219_);
if (lean_obj_tag(v_enableArtifactCache_x3f_1217_) == 0)
{
if (lean_obj_tag(v_enableArtifactCache_x3f_1195_) == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_config_1223_; lean_object* v_enableArtifactCache_x3f_1224_; 
v___x_1221_ = lean_unsigned_to_nat(0u);
v___x_1222_ = lean_array_fget_borrowed(v_packages_1193_, v___x_1221_);
v_config_1223_ = lean_ctor_get(v___x_1222_, 6);
v_enableArtifactCache_x3f_1224_ = lean_ctor_get(v_config_1223_, 25);
if (lean_obj_tag(v_enableArtifactCache_x3f_1224_) == 0)
{
uint8_t v___x_1225_; 
v___x_1225_ = 0;
lean_inc(v_keyName_1211_);
lean_inc_ref(v_scope_1213_);
lean_inc(v_downloadCacheService_x3f_1216_);
v___y_1198_ = v___x_1220_;
v___y_1199_ = v_downloadCacheService_x3f_1216_;
v___y_1200_ = v_scope_1213_;
v___y_1201_ = v_keyName_1211_;
v___y_1202_ = v_a_1208_;
v___y_1203_ = v_preferReleaseBuild_1215_;
v_a_1204_ = v___x_1225_;
v_a_1205_ = v_a_1209_;
goto v___jp_1197_;
}
else
{
lean_object* v_val_1226_; uint8_t v___x_1227_; 
v_val_1226_ = lean_ctor_get(v_enableArtifactCache_x3f_1224_, 0);
v___x_1227_ = lean_unbox(v_val_1226_);
lean_inc(v_keyName_1211_);
lean_inc_ref(v_scope_1213_);
lean_inc(v_downloadCacheService_x3f_1216_);
v___y_1198_ = v___x_1220_;
v___y_1199_ = v_downloadCacheService_x3f_1216_;
v___y_1200_ = v_scope_1213_;
v___y_1201_ = v_keyName_1211_;
v___y_1202_ = v_a_1208_;
v___y_1203_ = v_preferReleaseBuild_1215_;
v_a_1204_ = v___x_1227_;
v_a_1205_ = v_a_1209_;
goto v___jp_1197_;
}
}
else
{
lean_object* v_val_1228_; uint8_t v___x_1229_; 
v_val_1228_ = lean_ctor_get(v_enableArtifactCache_x3f_1195_, 0);
v___x_1229_ = lean_unbox(v_val_1228_);
lean_inc(v_keyName_1211_);
lean_inc_ref(v_scope_1213_);
lean_inc(v_downloadCacheService_x3f_1216_);
v___y_1198_ = v___x_1220_;
v___y_1199_ = v_downloadCacheService_x3f_1216_;
v___y_1200_ = v_scope_1213_;
v___y_1201_ = v_keyName_1211_;
v___y_1202_ = v_a_1208_;
v___y_1203_ = v_preferReleaseBuild_1215_;
v_a_1204_ = v___x_1229_;
v_a_1205_ = v_a_1209_;
goto v___jp_1197_;
}
}
else
{
lean_object* v_val_1230_; uint8_t v___x_1231_; 
v_val_1230_ = lean_ctor_get(v_enableArtifactCache_x3f_1217_, 0);
v___x_1231_ = lean_unbox(v_val_1230_);
lean_inc(v_keyName_1211_);
lean_inc_ref(v_scope_1213_);
lean_inc(v_downloadCacheService_x3f_1216_);
v___y_1198_ = v___x_1220_;
v___y_1199_ = v_downloadCacheService_x3f_1216_;
v___y_1200_ = v_scope_1213_;
v___y_1201_ = v_keyName_1211_;
v___y_1202_ = v_a_1208_;
v___y_1203_ = v_preferReleaseBuild_1215_;
v_a_1204_ = v___x_1231_;
v_a_1205_ = v_a_1209_;
goto v___jp_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___boxed(lean_object* v_self_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec(v_a_1236_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object* v_self_1247_, lean_object* v_facet_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_toBuildConfig_1252_; uint8_t v_verbosity_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v_toBuildConfig_1252_ = lean_ctor_get(v_a_1249_, 0);
v_verbosity_1253_ = lean_ctor_get_uint8(v_toBuildConfig_1252_, sizeof(void*)*6 + 4);
v___x_1254_ = lean_box(v_verbosity_1253_);
v___x_1255_ = lean_obj_tag_nat(v___x_1254_);
lean_dec(v___x_1254_);
v___x_1256_ = lean_unsigned_to_nat(2u);
v___x_1257_ = lean_nat_dec_eq(v___x_1255_, v___x_1256_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec(v_facet_1248_);
lean_dec_ref(v_self_1247_);
v___x_1258_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v_a_1250_);
return v___x_1259_;
}
else
{
lean_object* v_baseName_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_baseName_1260_ = lean_ctor_get(v_self_1247_, 1);
lean_inc(v_baseName_1260_);
lean_dec_ref(v_self_1247_);
v___x_1261_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1262_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1260_, v___x_1257_);
v___x_1263_ = lean_string_append(v___x_1261_, v___x_1262_);
lean_dec_ref(v___x_1262_);
v___x_1264_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1265_ = lean_string_append(v___x_1263_, v___x_1264_);
v___x_1266_ = l_Lake_Name_eraseHead(v_facet_1248_);
v___x_1267_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1266_, v___x_1257_);
v___x_1268_ = lean_string_append(v___x_1265_, v___x_1267_);
lean_dec_ref(v___x_1267_);
v___x_1269_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1270_ = lean_string_append(v___x_1268_, v___x_1269_);
v___x_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v_a_1250_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* v_self_1272_, lean_object* v_facet_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(v_self_1272_, v_facet_1273_, v_a_1274_, v_a_1275_);
lean_dec_ref(v_a_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* v_self_1278_, lean_object* v_facet_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_toBuildConfig_1287_; uint8_t v_verbosity_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v_toBuildConfig_1287_ = lean_ctor_get(v_a_1284_, 0);
v_verbosity_1288_ = lean_ctor_get_uint8(v_toBuildConfig_1287_, sizeof(void*)*6 + 4);
v___x_1289_ = lean_box(v_verbosity_1288_);
v___x_1290_ = lean_obj_tag_nat(v___x_1289_);
lean_dec(v___x_1289_);
v___x_1291_ = lean_unsigned_to_nat(2u);
v___x_1292_ = lean_nat_dec_eq(v___x_1290_, v___x_1291_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec(v_facet_1279_);
lean_dec_ref(v_self_1278_);
v___x_1293_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v_a_1285_);
return v___x_1294_;
}
else
{
lean_object* v_baseName_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_baseName_1295_ = lean_ctor_get(v_self_1278_, 1);
lean_inc(v_baseName_1295_);
lean_dec_ref(v_self_1278_);
v___x_1296_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1297_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1295_, v___x_1292_);
v___x_1298_ = lean_string_append(v___x_1296_, v___x_1297_);
lean_dec_ref(v___x_1297_);
v___x_1299_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1300_ = lean_string_append(v___x_1298_, v___x_1299_);
v___x_1301_ = l_Lake_Name_eraseHead(v_facet_1279_);
v___x_1302_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1301_, v___x_1292_);
v___x_1303_ = lean_string_append(v___x_1300_, v___x_1302_);
lean_dec_ref(v___x_1302_);
v___x_1304_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1305_ = lean_string_append(v___x_1303_, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v_a_1285_);
return v___x_1306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* v_self_1307_, lean_object* v_facet_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(v_self_1307_, v_facet_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
return v_res_1316_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_1321_ = l_Lake_Name_eraseHead(v___x_1320_);
return v___x_1321_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = l_Lake_Package_optArtifactCacheFacet;
v___x_1323_ = l_Lake_Name_eraseHead(v___x_1322_);
return v___x_1323_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__5(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_1325_ = l_Lake_Name_eraseHead(v___x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(lean_object* v_self_1326_, uint8_t v_success_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v_a_1336_; lean_object* v_a_1337_; lean_object* v_a_1359_; lean_object* v_a_1360_; lean_object* v_a_1382_; lean_object* v_a_1383_; 
if (v_success_1327_ == 0)
{
lean_object* v_config_1404_; uint8_t v_preferReleaseBuild_1405_; 
v_config_1404_ = lean_ctor_get(v_self_1326_, 6);
v_preferReleaseBuild_1405_ = lean_ctor_get_uint8(v_config_1404_, sizeof(void*)*29 + 2);
if (v_preferReleaseBuild_1405_ == 0)
{
lean_object* v_downloadCacheService_x3f_1406_; 
v_downloadCacheService_x3f_1406_ = lean_ctor_get(v_config_1404_, 12);
if (lean_obj_tag(v_downloadCacheService_x3f_1406_) == 0)
{
lean_object* v_toBuildConfig_1407_; lean_object* v_baseName_1408_; uint8_t v_verbosity_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v_toBuildConfig_1407_ = lean_ctor_get(v___y_1332_, 0);
v_baseName_1408_ = lean_ctor_get(v_self_1326_, 1);
lean_inc(v_baseName_1408_);
lean_dec_ref(v_self_1326_);
v_verbosity_1409_ = lean_ctor_get_uint8(v_toBuildConfig_1407_, sizeof(void*)*6 + 4);
v___x_1410_ = lean_box(v_verbosity_1409_);
v___x_1411_ = lean_obj_tag_nat(v___x_1410_);
lean_dec(v___x_1410_);
v___x_1412_ = lean_unsigned_to_nat(2u);
v___x_1413_ = lean_nat_dec_eq(v___x_1411_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; 
lean_dec(v_baseName_1408_);
v___x_1414_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_1336_ = v___x_1414_;
v_a_1337_ = v___y_1333_;
goto v___jp_1335_;
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1415_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1416_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1408_, v___x_1413_);
v___x_1417_ = lean_string_append(v___x_1415_, v___x_1416_);
lean_dec_ref(v___x_1416_);
v___x_1418_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1419_ = lean_string_append(v___x_1417_, v___x_1418_);
v___x_1420_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
v___x_1421_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1420_, v___x_1413_);
v___x_1422_ = lean_string_append(v___x_1419_, v___x_1421_);
lean_dec_ref(v___x_1421_);
v___x_1423_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1424_ = lean_string_append(v___x_1422_, v___x_1423_);
v_a_1336_ = v___x_1424_;
v_a_1337_ = v___y_1333_;
goto v___jp_1335_;
}
}
else
{
lean_object* v_toBuildConfig_1425_; lean_object* v_baseName_1426_; uint8_t v_verbosity_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v_toBuildConfig_1425_ = lean_ctor_get(v___y_1332_, 0);
v_baseName_1426_ = lean_ctor_get(v_self_1326_, 1);
lean_inc(v_baseName_1426_);
lean_dec_ref(v_self_1326_);
v_verbosity_1427_ = lean_ctor_get_uint8(v_toBuildConfig_1425_, sizeof(void*)*6 + 4);
v___x_1428_ = lean_box(v_verbosity_1427_);
v___x_1429_ = lean_obj_tag_nat(v___x_1428_);
lean_dec(v___x_1428_);
v___x_1430_ = lean_unsigned_to_nat(2u);
v___x_1431_ = lean_nat_dec_eq(v___x_1429_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
lean_dec(v_baseName_1426_);
v___x_1432_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_1359_ = v___x_1432_;
v_a_1360_ = v___y_1333_;
goto v___jp_1358_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1433_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1434_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1426_, v___x_1431_);
v___x_1435_ = lean_string_append(v___x_1433_, v___x_1434_);
lean_dec_ref(v___x_1434_);
v___x_1436_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1437_ = lean_string_append(v___x_1435_, v___x_1436_);
v___x_1438_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__4);
v___x_1439_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1438_, v___x_1431_);
v___x_1440_ = lean_string_append(v___x_1437_, v___x_1439_);
lean_dec_ref(v___x_1439_);
v___x_1441_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1442_ = lean_string_append(v___x_1440_, v___x_1441_);
v_a_1359_ = v___x_1442_;
v_a_1360_ = v___y_1333_;
goto v___jp_1358_;
}
}
}
else
{
lean_object* v_toBuildConfig_1443_; lean_object* v_baseName_1444_; uint8_t v_verbosity_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v_toBuildConfig_1443_ = lean_ctor_get(v___y_1332_, 0);
v_baseName_1444_ = lean_ctor_get(v_self_1326_, 1);
lean_inc(v_baseName_1444_);
lean_dec_ref(v_self_1326_);
v_verbosity_1445_ = lean_ctor_get_uint8(v_toBuildConfig_1443_, sizeof(void*)*6 + 4);
v___x_1446_ = lean_box(v_verbosity_1445_);
v___x_1447_ = lean_obj_tag_nat(v___x_1446_);
lean_dec(v___x_1446_);
v___x_1448_ = lean_unsigned_to_nat(2u);
v___x_1449_ = lean_nat_dec_eq(v___x_1447_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
lean_dec(v_baseName_1444_);
v___x_1450_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_1382_ = v___x_1450_;
v_a_1383_ = v___y_1333_;
goto v___jp_1381_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1451_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1452_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1444_, v___x_1449_);
v___x_1453_ = lean_string_append(v___x_1451_, v___x_1452_);
lean_dec_ref(v___x_1452_);
v___x_1454_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1455_ = lean_string_append(v___x_1453_, v___x_1454_);
v___x_1456_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__5, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__5_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__5);
v___x_1457_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1456_, v___x_1449_);
v___x_1458_ = lean_string_append(v___x_1455_, v___x_1457_);
lean_dec_ref(v___x_1457_);
v___x_1459_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1460_ = lean_string_append(v___x_1458_, v___x_1459_);
v_a_1382_ = v___x_1460_;
v_a_1383_ = v___y_1333_;
goto v___jp_1381_;
}
}
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec_ref(v_self_1326_);
v___x_1461_ = lean_box(0);
v___x_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1462_, 0, v___x_1461_);
lean_ctor_set(v___x_1462_, 1, v___y_1333_);
return v___x_1462_;
}
v___jp_1335_:
{
lean_object* v_log_1338_; uint8_t v_action_1339_; uint8_t v_wantsRebuild_1340_; uint8_t v_canceled_1341_; lean_object* v_trace_1342_; lean_object* v_buildTime_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1357_; 
v_log_1338_ = lean_ctor_get(v_a_1337_, 0);
v_action_1339_ = lean_ctor_get_uint8(v_a_1337_, sizeof(void*)*3);
v_wantsRebuild_1340_ = lean_ctor_get_uint8(v_a_1337_, sizeof(void*)*3 + 1);
v_canceled_1341_ = lean_ctor_get_uint8(v_a_1337_, sizeof(void*)*3 + 2);
v_trace_1342_ = lean_ctor_get(v_a_1337_, 1);
v_buildTime_1343_ = lean_ctor_get(v_a_1337_, 2);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_a_1337_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1345_ = v_a_1337_;
v_isShared_1346_ = v_isSharedCheck_1357_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_buildTime_1343_);
lean_inc(v_trace_1342_);
lean_inc(v_log_1338_);
lean_dec(v_a_1337_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1357_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1347_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0));
v___x_1348_ = lean_string_append(v___x_1347_, v_a_1336_);
lean_dec_ref(v_a_1336_);
v___x_1349_ = 0;
v___x_1350_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*1, v___x_1349_);
v___x_1351_ = lean_box(0);
v___x_1352_ = lean_array_push(v_log_1338_, v___x_1350_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1352_);
v___x_1354_ = v___x_1345_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_trace_1342_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_buildTime_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1356_, sizeof(void*)*3, v_action_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1356_, sizeof(void*)*3 + 1, v_wantsRebuild_1340_);
lean_ctor_set_uint8(v_reuseFailAlloc_1356_, sizeof(void*)*3 + 2, v_canceled_1341_);
v___x_1354_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1351_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
return v___x_1355_;
}
}
}
v___jp_1358_:
{
lean_object* v_log_1361_; uint8_t v_action_1362_; uint8_t v_wantsRebuild_1363_; uint8_t v_canceled_1364_; lean_object* v_trace_1365_; lean_object* v_buildTime_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1380_; 
v_log_1361_ = lean_ctor_get(v_a_1360_, 0);
v_action_1362_ = lean_ctor_get_uint8(v_a_1360_, sizeof(void*)*3);
v_wantsRebuild_1363_ = lean_ctor_get_uint8(v_a_1360_, sizeof(void*)*3 + 1);
v_canceled_1364_ = lean_ctor_get_uint8(v_a_1360_, sizeof(void*)*3 + 2);
v_trace_1365_ = lean_ctor_get(v_a_1360_, 1);
v_buildTime_1366_ = lean_ctor_get(v_a_1360_, 2);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_a_1360_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1368_ = v_a_1360_;
v_isShared_1369_ = v_isSharedCheck_1380_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_buildTime_1366_);
lean_inc(v_trace_1365_);
lean_inc(v_log_1361_);
lean_dec(v_a_1360_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1380_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1370_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1));
v___x_1371_ = lean_string_append(v___x_1370_, v_a_1359_);
lean_dec_ref(v_a_1359_);
v___x_1372_ = 0;
v___x_1373_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*1, v___x_1372_);
v___x_1374_ = lean_box(0);
v___x_1375_ = lean_array_push(v_log_1361_, v___x_1373_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1375_);
v___x_1377_ = v___x_1368_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_trace_1365_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_buildTime_1366_);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, sizeof(void*)*3, v_action_1362_);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, sizeof(void*)*3 + 1, v_wantsRebuild_1363_);
lean_ctor_set_uint8(v_reuseFailAlloc_1379_, sizeof(void*)*3 + 2, v_canceled_1364_);
v___x_1377_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1374_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
return v___x_1378_;
}
}
}
v___jp_1381_:
{
lean_object* v_log_1384_; uint8_t v_action_1385_; uint8_t v_wantsRebuild_1386_; uint8_t v_canceled_1387_; lean_object* v_trace_1388_; lean_object* v_buildTime_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1403_; 
v_log_1384_ = lean_ctor_get(v_a_1383_, 0);
v_action_1385_ = lean_ctor_get_uint8(v_a_1383_, sizeof(void*)*3);
v_wantsRebuild_1386_ = lean_ctor_get_uint8(v_a_1383_, sizeof(void*)*3 + 1);
v_canceled_1387_ = lean_ctor_get_uint8(v_a_1383_, sizeof(void*)*3 + 2);
v_trace_1388_ = lean_ctor_get(v_a_1383_, 1);
v_buildTime_1389_ = lean_ctor_get(v_a_1383_, 2);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_a_1383_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1391_ = v_a_1383_;
v_isShared_1392_ = v_isSharedCheck_1403_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_buildTime_1389_);
lean_inc(v_trace_1388_);
lean_inc(v_log_1384_);
lean_dec(v_a_1383_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1403_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1393_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2));
v___x_1394_ = lean_string_append(v___x_1393_, v_a_1382_);
lean_dec_ref(v_a_1382_);
v___x_1395_ = 2;
v___x_1396_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1396_, 0, v___x_1394_);
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*1, v___x_1395_);
v___x_1397_ = lean_box(0);
v___x_1398_ = lean_array_push(v_log_1384_, v___x_1396_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1398_);
v___x_1400_ = v___x_1391_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_trace_1388_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_buildTime_1389_);
lean_ctor_set_uint8(v_reuseFailAlloc_1402_, sizeof(void*)*3, v_action_1385_);
lean_ctor_set_uint8(v_reuseFailAlloc_1402_, sizeof(void*)*3 + 1, v_wantsRebuild_1386_);
lean_ctor_set_uint8(v_reuseFailAlloc_1402_, sizeof(void*)*3 + 2, v_canceled_1387_);
v___x_1400_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1401_; 
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1397_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
return v___x_1401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* v_self_1463_, lean_object* v_success_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
uint8_t v_success_boxed_1472_; lean_object* v_res_1473_; 
v_success_boxed_1472_ = lean_unbox(v_success_1464_);
v_res_1473_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(v_self_1463_, v_success_boxed_1472_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* v_self_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
lean_object* v___f_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_inc_ref(v_self_1474_);
v___f_1482_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(v___f_1482_, 0, v_self_1474_);
v___x_1483_ = l_Lake_instDataKindUnit;
lean_inc_ref(v_a_1475_);
v___x_1484_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1497_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_a_1486_ = lean_ctor_get(v___x_1484_, 1);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1488_ = v___x_1484_;
v_isShared_1489_ = v_isSharedCheck_1497_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1497_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; uint8_t v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = 0;
v___x_1492_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_1493_ = l_Lake_Job_mapM___redArg(v___x_1483_, v_a_1485_, v___f_1482_, v___x_1490_, v___x_1491_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v___x_1492_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1493_);
v___x_1495_ = v___x_1488_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_a_1486_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_dec_ref(v___f_1482_);
lean_dec_ref(v_a_1475_);
v_a_1498_ = lean_ctor_get(v___x_1484_, 0);
v_a_1499_ = lean_ctor_get(v___x_1484_, 1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1484_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_inc(v_a_1498_);
lean_dec(v___x_1484_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1498_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(lean_object* v_self_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_a_1511_);
lean_dec(v_a_1510_);
lean_dec(v_a_1509_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* v_self_1516_, lean_object* v_as_1517_, size_t v_sz_1518_, size_t v_i_1519_, lean_object* v_b_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
uint8_t v___x_1528_; 
v___x_1528_ = lean_usize_dec_lt(v_i_1519_, v_sz_1518_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_dec_ref(v___y_1521_);
lean_dec_ref(v_self_1516_);
v___x_1529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1529_, 0, v_b_1520_);
lean_ctor_set(v___x_1529_, 1, v___y_1526_);
return v___x_1529_;
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1530_ = lean_array_uget_borrowed(v_as_1517_, v_i_1519_);
lean_inc_ref(v___y_1521_);
lean_inc(v_a_1530_);
lean_inc_ref(v_self_1516_);
v___x_1531_ = l_Lake_Package_fetchTargetJob(v_self_1516_, v_a_1530_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v_a_1533_; lean_object* v___x_1534_; size_t v___x_1535_; size_t v___x_1536_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
v_a_1533_ = lean_ctor_get(v___x_1531_, 1);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1531_, 2);
v___x_1534_ = l_Lake_Job_mix___redArg(v_b_1520_, v_a_1532_);
v___x_1535_ = ((size_t)1ULL);
v___x_1536_ = lean_usize_add(v_i_1519_, v___x_1535_);
v_i_1519_ = v___x_1536_;
v_b_1520_ = v___x_1534_;
v___y_1526_ = v_a_1533_;
goto _start;
}
else
{
lean_object* v_a_1538_; lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref(v___y_1521_);
lean_dec_ref(v_b_1520_);
lean_dec_ref(v_self_1516_);
v_a_1538_ = lean_ctor_get(v___x_1531_, 0);
v_a_1539_ = lean_ctor_get(v___x_1531_, 1);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1531_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_inc(v_a_1538_);
lean_dec(v___x_1531_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1538_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* v_self_1547_, lean_object* v_as_1548_, lean_object* v_sz_1549_, lean_object* v_i_1550_, lean_object* v_b_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
size_t v_sz_boxed_1559_; size_t v_i_boxed_1560_; lean_object* v_res_1561_; 
v_sz_boxed_1559_ = lean_unbox_usize(v_sz_1549_);
lean_dec(v_sz_1549_);
v_i_boxed_1560_ = lean_unbox_usize(v_i_1550_);
lean_dec(v_i_1550_);
v_res_1561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1547_, v_as_1548_, v_sz_boxed_1559_, v_i_boxed_1560_, v_b_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v_as_1548_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object* v_config_1562_, lean_object* v_self_1563_, lean_object* v_____r_1564_, lean_object* v_job_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v_extraDepTargets_1573_; size_t v_sz_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
v_extraDepTargets_1573_ = lean_ctor_get(v_config_1562_, 2);
v_sz_1574_ = lean_array_size(v_extraDepTargets_1573_);
v___x_1575_ = ((size_t)0ULL);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1563_, v_extraDepTargets_1573_, v_sz_1574_, v___x_1575_, v_job_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object* v_config_1577_, lean_object* v_self_1578_, lean_object* v_____r_1579_, lean_object* v_job_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(v_config_1577_, v_self_1578_, v_____r_1579_, v_job_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v_config_1577_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(uint8_t v___x_1589_, lean_object* v_self_1590_, lean_object* v_job_1591_, lean_object* v___f_1592_, lean_object* v___x_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
if (v___x_1589_ == 0)
{
lean_object* v___x_1601_; 
lean_inc_ref(v___y_1594_);
v___x_1601_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1590_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v_a_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
v_a_1603_ = lean_ctor_get(v___x_1601_, 1);
lean_inc(v_a_1603_);
lean_dec_ref_known(v___x_1601_, 2);
v___x_1604_ = l_Lake_Job_add___redArg(v_job_1591_, v_a_1602_);
lean_inc_ref(v___y_1598_);
lean_inc_ref(v___y_1597_);
lean_inc(v___y_1596_);
lean_inc(v___y_1595_);
v___x_1605_ = lean_apply_9(v___f_1592_, v___x_1593_, v___x_1604_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v_a_1603_, lean_box(0));
return v___x_1605_;
}
else
{
lean_dec_ref(v___y_1594_);
lean_dec_ref(v___f_1592_);
lean_dec_ref(v_job_1591_);
return v___x_1601_;
}
}
else
{
lean_object* v___x_1606_; 
lean_dec_ref(v_self_1590_);
lean_inc_ref(v___y_1598_);
lean_inc_ref(v___y_1597_);
lean_inc(v___y_1596_);
lean_inc(v___y_1595_);
v___x_1606_ = lean_apply_9(v___f_1592_, v___x_1593_, v_job_1591_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, lean_box(0));
return v___x_1606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* v___x_1607_, lean_object* v_self_1608_, lean_object* v_job_1609_, lean_object* v___f_1610_, lean_object* v___x_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
uint8_t v___x_4202__boxed_1619_; lean_object* v_res_1620_; 
v___x_4202__boxed_1619_ = lean_unbox(v___x_1607_);
v_res_1620_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(v___x_4202__boxed_1619_, v_self_1608_, v_job_1609_, v___f_1610_, v___x_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec(v___y_1613_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object* v_self_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_wsIdx_1631_; lean_object* v_baseName_1632_; lean_object* v_config_1633_; lean_object* v___f_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v_job_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; lean_object* v___y_1657_; lean_object* v___x_1658_; 
v_wsIdx_1631_ = lean_ctor_get(v_self_1623_, 0);
v_baseName_1632_ = lean_ctor_get(v_self_1623_, 1);
v_config_1633_ = lean_ctor_get(v_self_1623_, 6);
lean_inc_ref(v_self_1623_);
lean_inc_ref(v_config_1633_);
v___f_1634_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1634_, 0, v_config_1633_);
lean_closure_set(v___f_1634_, 1, v_self_1623_);
v___x_1635_ = l_Lake_instDataKindUnit;
v___x_1636_ = 1;
lean_inc(v_baseName_1632_);
v___x_1637_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1632_, v___x_1636_);
v___x_1638_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0));
lean_inc_ref(v___x_1637_);
v___x_1639_ = lean_string_append(v___x_1637_, v___x_1638_);
v___x_1640_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1));
v___x_1641_ = lean_string_append(v___x_1640_, v___x_1637_);
lean_dec_ref(v___x_1637_);
v___x_1642_ = lean_string_append(v___x_1641_, v___x_1638_);
v___x_1643_ = lean_box(0);
v___x_1644_ = lean_box(0);
v___x_1645_ = lean_unsigned_to_nat(0u);
v___x_1646_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1647_ = 0;
v___x_1648_ = 0;
v___x_1649_ = l_Lake_BuildTrace_nil(v___x_1642_);
v___x_1650_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1650_, 0, v___x_1646_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
lean_ctor_set(v___x_1650_, 2, v___x_1645_);
lean_ctor_set_uint8(v___x_1650_, sizeof(void*)*3, v___x_1647_);
lean_ctor_set_uint8(v___x_1650_, sizeof(void*)*3 + 1, v___x_1648_);
lean_ctor_set_uint8(v___x_1650_, sizeof(void*)*3 + 2, v___x_1648_);
v___x_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1643_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_task_pure(v___x_1651_);
v___x_1653_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_job_1654_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_1654_, 0, v___x_1652_);
lean_ctor_set(v_job_1654_, 1, v___x_1644_);
lean_ctor_set(v_job_1654_, 2, v___x_1653_);
lean_ctor_set_uint8(v_job_1654_, sizeof(void*)*3, v___x_1648_);
v___x_1655_ = lean_nat_dec_eq(v_wsIdx_1631_, v___x_1645_);
v___x_1656_ = lean_box(v___x_1655_);
v___y_1657_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 12, 5);
lean_closure_set(v___y_1657_, 0, v___x_1656_);
lean_closure_set(v___y_1657_, 1, v_self_1623_);
lean_closure_set(v___y_1657_, 2, v_job_1654_);
lean_closure_set(v___y_1657_, 3, v___f_1634_);
lean_closure_set(v___y_1657_, 4, v___x_1643_);
v___x_1658_ = l_Lake_ensureJob___redArg(v___x_1635_, v___y_1657_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1683_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_a_1660_ = lean_ctor_get(v___x_1658_, 1);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1662_ = v___x_1658_;
v_isShared_1663_ = v_isSharedCheck_1683_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1683_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v_task_1664_; lean_object* v_kind_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1681_; 
v_task_1664_ = lean_ctor_get(v_a_1659_, 0);
v_kind_1665_ = lean_ctor_get(v_a_1659_, 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_a_1659_);
if (v_isSharedCheck_1681_ == 0)
{
lean_object* v_unused_1682_; 
v_unused_1682_ = lean_ctor_get(v_a_1659_, 2);
lean_dec(v_unused_1682_);
v___x_1667_ = v_a_1659_;
v_isShared_1668_ = v_isSharedCheck_1681_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_kind_1665_);
lean_inc(v_task_1664_);
lean_dec(v_a_1659_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1681_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v_registeredJobs_1669_; lean_object* v_job_1671_; 
v_registeredJobs_1669_ = lean_ctor_get(v_a_1628_, 4);
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 2, v___x_1639_);
v_job_1671_ = v___x_1667_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_task_1664_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_kind_1665_);
lean_ctor_set(v_reuseFailAlloc_1680_, 2, v___x_1639_);
v_job_1671_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
lean_ctor_set_uint8(v_job_1671_, sizeof(void*)*3, v___x_1648_);
v___x_1672_ = lean_st_ref_take(v_registeredJobs_1669_);
lean_inc_ref(v_job_1671_);
v___x_1673_ = l_Lake_Job_toOpaque___redArg(v_job_1671_);
v___x_1674_ = lean_array_push(v___x_1672_, v___x_1673_);
v___x_1675_ = lean_st_ref_put(v_registeredJobs_1669_, v___x_1674_);
v___x_1676_ = l_Lake_Job_renew___redArg(v_job_1671_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1676_);
v___x_1678_ = v___x_1662_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_a_1660_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1639_);
return v___x_1658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(lean_object* v_self_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(v_self_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec(v_a_1686_);
return v_res_1692_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_box(0);
v___x_1694_ = l_Lean_Json_compress(v___x_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t v_fmt_1695_){
_start:
{
if (v_fmt_1695_ == 0)
{
lean_object* v___x_1696_; 
v___x_1696_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
return v___x_1696_;
}
else
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
return v___x_1697_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_1698_){
_start:
{
uint8_t v_fmt_boxed_1699_; lean_object* v_res_1700_; 
v_fmt_boxed_1699_ = lean_unbox(v_fmt_1698_);
v_res_1700_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_boxed_1699_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(uint8_t v_fmt_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_1701_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object* v_fmt_1704_, lean_object* v_a_1705_){
_start:
{
uint8_t v_fmt_boxed_1706_; lean_object* v_res_1707_; 
v_fmt_boxed_1706_ = lean_unbox(v_fmt_1704_);
v_res_1707_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(v_fmt_boxed_1706_, v_a_1705_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v___y_1708_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
uint8_t v___y_67__boxed_1713_; lean_object* v_res_1714_; 
v___y_67__boxed_1713_ = lean_unbox(v___y_1711_);
v_res_1714_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_67__boxed_1713_, v___y_1712_);
return v_res_1714_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1717_; uint8_t v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___f_1717_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_1718_ = 1;
v___x_1719_ = l_Lake_instDataKindUnit;
v___x_1720_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__1));
v___x_1721_ = l_Lake_Package_keyword;
v___x_1722_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v___x_1720_);
lean_ctor_set(v___x_1722_, 2, v___x_1719_);
lean_ctor_set(v___x_1722_, 3, v___f_1717_);
lean_ctor_set_uint8(v___x_1722_, sizeof(void*)*4, v___x_1718_);
lean_ctor_set_uint8(v___x_1722_, sizeof(void*)*4 + 1, v___x_1718_);
return v___x_1722_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_obj_once(&l_Lake_Package_extraDepFacetConfig___closed__2, &l_Lake_Package_extraDepFacetConfig___closed__2_once, _init_l_Lake_Package_extraDepFacetConfig___closed__2);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object* v_self_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_origName_1743_; lean_object* v_dir_1744_; lean_object* v_scope_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v_origName_1743_ = lean_ctor_get(v_self_1739_, 3);
lean_inc(v_origName_1743_);
v_dir_1744_ = lean_ctor_get(v_self_1739_, 4);
lean_inc_ref(v_dir_1744_);
v_scope_1745_ = lean_ctor_get(v_self_1739_, 10);
lean_inc_ref(v_scope_1745_);
lean_dec_ref(v_self_1739_);
v___x_1746_ = lean_string_utf8_byte_size(v_scope_1745_);
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = lean_nat_dec_eq(v___x_1746_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_object* v_log_1749_; uint8_t v_action_1750_; uint8_t v_wantsRebuild_1751_; uint8_t v_canceled_1752_; lean_object* v_trace_1753_; lean_object* v_buildTime_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v_log_1749_ = lean_ctor_get(v_a_1741_, 0);
v_action_1750_ = lean_ctor_get_uint8(v_a_1741_, sizeof(void*)*3);
v_wantsRebuild_1751_ = lean_ctor_get_uint8(v_a_1741_, sizeof(void*)*3 + 1);
v_canceled_1752_ = lean_ctor_get_uint8(v_a_1741_, sizeof(void*)*3 + 2);
v_trace_1753_ = lean_ctor_get(v_a_1741_, 1);
v_buildTime_1754_ = lean_ctor_get(v_a_1741_, 2);
v___x_1755_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
v___x_1756_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1755_, v_dir_1744_);
if (lean_obj_tag(v___x_1756_) == 1)
{
lean_object* v_toContext_1757_; lean_object* v_lakeEnv_1758_; lean_object* v_val_1759_; lean_object* v_toolchain_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v_toContext_1757_ = lean_ctor_get(v_a_1740_, 1);
v_lakeEnv_1758_ = lean_ctor_get(v_toContext_1757_, 0);
v_val_1759_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_val_1759_);
lean_dec_ref_known(v___x_1756_, 1);
v_toolchain_1760_ = lean_ctor_get(v_lakeEnv_1758_, 19);
v___x_1761_ = lean_string_utf8_byte_size(v_toolchain_1760_);
v___x_1762_ = lean_nat_dec_eq(v___x_1761_, v___x_1747_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1763_ = l_Lean_Name_toString(v_origName_1743_, v___x_1748_);
lean_inc_ref(v_lakeEnv_1758_);
v___x_1764_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_1758_, v_scope_1745_, v___x_1763_);
lean_dec_ref(v___x_1763_);
lean_dec_ref(v_scope_1745_);
v___x_1765_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1));
v___x_1766_ = lean_string_append(v___x_1764_, v___x_1765_);
v___x_1767_ = lean_string_append(v___x_1766_, v_val_1759_);
lean_dec(v_val_1759_);
v___x_1768_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2));
v___x_1769_ = lean_string_append(v___x_1767_, v___x_1768_);
v___x_1770_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1771_ = l_Lake_uriEncode(v_toolchain_1760_, v___x_1770_);
v___x_1772_ = lean_string_append(v___x_1769_, v___x_1771_);
lean_dec_ref(v___x_1771_);
v___x_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v_a_1741_);
return v___x_1773_;
}
else
{
lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1784_; 
lean_inc(v_buildTime_1754_);
lean_inc_ref(v_trace_1753_);
lean_inc_ref(v_log_1749_);
lean_dec(v_val_1759_);
lean_dec_ref(v_scope_1745_);
lean_dec(v_origName_1743_);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_a_1741_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; lean_object* v_unused_1786_; lean_object* v_unused_1787_; 
v_unused_1785_ = lean_ctor_get(v_a_1741_, 2);
lean_dec(v_unused_1785_);
v_unused_1786_ = lean_ctor_get(v_a_1741_, 1);
lean_dec(v_unused_1786_);
v_unused_1787_ = lean_ctor_get(v_a_1741_, 0);
lean_dec(v_unused_1787_);
v___x_1775_ = v_a_1741_;
v_isShared_1776_ = v_isSharedCheck_1784_;
goto v_resetjp_1774_;
}
else
{
lean_dec(v_a_1741_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1784_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1777_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4));
v___x_1778_ = lean_array_get_size(v_log_1749_);
v___x_1779_ = lean_array_push(v_log_1749_, v___x_1777_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1779_);
v___x_1781_ = v___x_1775_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_trace_1753_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_buildTime_1754_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*3, v_action_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*3 + 1, v_wantsRebuild_1751_);
lean_ctor_set_uint8(v_reuseFailAlloc_1783_, sizeof(void*)*3 + 2, v_canceled_1752_);
v___x_1781_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1778_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
return v___x_1782_;
}
}
}
}
else
{
lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1798_; 
lean_inc(v_buildTime_1754_);
lean_inc_ref(v_trace_1753_);
lean_inc_ref(v_log_1749_);
lean_dec(v___x_1756_);
lean_dec_ref(v_scope_1745_);
lean_dec(v_origName_1743_);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_a_1741_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; lean_object* v_unused_1800_; lean_object* v_unused_1801_; 
v_unused_1799_ = lean_ctor_get(v_a_1741_, 2);
lean_dec(v_unused_1799_);
v_unused_1800_ = lean_ctor_get(v_a_1741_, 1);
lean_dec(v_unused_1800_);
v_unused_1801_ = lean_ctor_get(v_a_1741_, 0);
lean_dec(v_unused_1801_);
v___x_1789_ = v_a_1741_;
v_isShared_1790_ = v_isSharedCheck_1798_;
goto v_resetjp_1788_;
}
else
{
lean_dec(v_a_1741_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1798_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1791_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6));
v___x_1792_ = lean_array_get_size(v_log_1749_);
v___x_1793_ = lean_array_push(v_log_1749_, v___x_1791_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1793_);
v___x_1795_ = v___x_1789_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_trace_1753_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_buildTime_1754_);
lean_ctor_set_uint8(v_reuseFailAlloc_1797_, sizeof(void*)*3, v_action_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1797_, sizeof(void*)*3 + 1, v_wantsRebuild_1751_);
lean_ctor_set_uint8(v_reuseFailAlloc_1797_, sizeof(void*)*3 + 2, v_canceled_1752_);
v___x_1795_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1796_; 
v___x_1796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1792_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
return v___x_1796_;
}
}
}
}
else
{
lean_object* v_log_1802_; uint8_t v_action_1803_; uint8_t v_wantsRebuild_1804_; uint8_t v_canceled_1805_; lean_object* v_trace_1806_; lean_object* v_buildTime_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v_scope_1745_);
lean_dec_ref(v_dir_1744_);
lean_dec(v_origName_1743_);
v_log_1802_ = lean_ctor_get(v_a_1741_, 0);
v_action_1803_ = lean_ctor_get_uint8(v_a_1741_, sizeof(void*)*3);
v_wantsRebuild_1804_ = lean_ctor_get_uint8(v_a_1741_, sizeof(void*)*3 + 1);
v_canceled_1805_ = lean_ctor_get_uint8(v_a_1741_, sizeof(void*)*3 + 2);
v_trace_1806_ = lean_ctor_get(v_a_1741_, 1);
v_buildTime_1807_ = lean_ctor_get(v_a_1741_, 2);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_a_1741_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1809_ = v_a_1741_;
v_isShared_1810_ = v_isSharedCheck_1818_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_buildTime_1807_);
lean_inc(v_trace_1806_);
lean_inc(v_log_1802_);
lean_dec(v_a_1741_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1818_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1811_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8));
v___x_1812_ = lean_array_get_size(v_log_1802_);
v___x_1813_ = lean_array_push(v_log_1802_, v___x_1811_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1813_);
v___x_1815_ = v___x_1809_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1813_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_trace_1806_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_buildTime_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1817_, sizeof(void*)*3, v_action_1803_);
lean_ctor_set_uint8(v_reuseFailAlloc_1817_, sizeof(void*)*3 + 1, v_wantsRebuild_1804_);
lean_ctor_set_uint8(v_reuseFailAlloc_1817_, sizeof(void*)*3 + 2, v_canceled_1805_);
v___x_1815_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1812_);
lean_ctor_set(v___x_1816_, 1, v___x_1815_);
return v___x_1816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___boxed(lean_object* v_self_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1819_, v_a_1820_, v_a_1821_);
lean_dec_ref(v_a_1820_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object* v_self_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1824_, v_a_1829_, v_a_1830_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object* v_self_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(v_self_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___lam__0(lean_object* v_fetch_1842_, lean_object* v_pkg_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
uint8_t v_r_1852_; lean_object* v___y_1853_; lean_object* v___x_1856_; 
lean_inc_ref(v___y_1848_);
lean_inc_ref(v___y_1847_);
lean_inc(v___y_1846_);
lean_inc(v___y_1845_);
v___x_1856_ = lean_apply_8(v_fetch_1842_, v_pkg_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, lean_box(0));
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; uint8_t v___x_1858_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 1);
lean_inc(v_a_1857_);
lean_dec_ref_known(v___x_1856_, 2);
v___x_1858_ = 1;
v_r_1852_ = v___x_1858_;
v___y_1853_ = v_a_1857_;
goto v___jp_1851_;
}
else
{
lean_object* v_a_1859_; lean_object* v_log_1860_; uint8_t v_action_1861_; uint8_t v_wantsRebuild_1862_; uint8_t v_canceled_1863_; lean_object* v_trace_1864_; lean_object* v_buildTime_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1875_; 
v_a_1859_ = lean_ctor_get(v___x_1856_, 1);
lean_inc(v_a_1859_);
lean_dec_ref_known(v___x_1856_, 2);
v_log_1860_ = lean_ctor_get(v_a_1859_, 0);
v_action_1861_ = lean_ctor_get_uint8(v_a_1859_, sizeof(void*)*3);
v_wantsRebuild_1862_ = lean_ctor_get_uint8(v_a_1859_, sizeof(void*)*3 + 1);
v_canceled_1863_ = lean_ctor_get_uint8(v_a_1859_, sizeof(void*)*3 + 2);
v_trace_1864_ = lean_ctor_get(v_a_1859_, 1);
v_buildTime_1865_ = lean_ctor_get(v_a_1859_, 2);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_a_1859_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1867_ = v_a_1859_;
v_isShared_1868_ = v_isSharedCheck_1875_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_buildTime_1865_);
lean_inc(v_trace_1864_);
lean_inc(v_log_1860_);
lean_dec(v_a_1859_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1875_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
uint8_t v___x_1869_; uint8_t v___x_1870_; lean_object* v___x_1872_; 
v___x_1869_ = 4;
v___x_1870_ = l_Lake_JobAction_merge(v_action_1861_, v___x_1869_);
if (v_isShared_1868_ == 0)
{
v___x_1872_ = v___x_1867_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_log_1860_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_trace_1864_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_buildTime_1865_);
lean_ctor_set_uint8(v_reuseFailAlloc_1874_, sizeof(void*)*3 + 1, v_wantsRebuild_1862_);
lean_ctor_set_uint8(v_reuseFailAlloc_1874_, sizeof(void*)*3 + 2, v_canceled_1863_);
v___x_1872_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
uint8_t v___x_1873_; 
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*3, v___x_1870_);
v___x_1873_ = 0;
v_r_1852_ = v___x_1873_;
v___y_1853_ = v___x_1872_;
goto v___jp_1851_;
}
}
}
v___jp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = lean_box(v_r_1852_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
lean_ctor_set(v___x_1855_, 1, v___y_1853_);
return v___x_1855_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___lam__0___boxed(lean_object* v_fetch_1876_, lean_object* v_pkg_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___lam__0(v_fetch_1876_, v_pkg_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec(v___y_1879_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___lam__1(lean_object* v_fetch_1886_, lean_object* v_facet_1887_, lean_object* v___x_1888_, lean_object* v_pkg_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_baseName_1897_; lean_object* v___f_1898_; uint8_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v_baseName_1897_ = lean_ctor_get(v_pkg_1889_, 1);
lean_inc(v_baseName_1897_);
v___f_1898_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1898_, 0, v_fetch_1886_);
lean_closure_set(v___f_1898_, 1, v_pkg_1889_);
v___x_1899_ = 1;
v___x_1900_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1897_, v___x_1899_);
v___x_1901_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1902_ = lean_string_append(v___x_1900_, v___x_1901_);
v___x_1903_ = l_Lake_Name_eraseHead(v_facet_1887_);
v___x_1904_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1903_, v___x_1899_);
v___x_1905_ = lean_string_append(v___x_1902_, v___x_1904_);
lean_dec_ref(v___x_1904_);
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_1888_);
v___x_1908_ = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(v___x_1908_, 0, lean_box(0));
lean_closure_set(v___x_1908_, 1, v___x_1888_);
lean_closure_set(v___x_1908_, 2, v___f_1898_);
lean_closure_set(v___x_1908_, 3, v___x_1906_);
lean_closure_set(v___x_1908_, 4, v___x_1907_);
v___x_1909_ = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM___boxed), 9, 2);
lean_closure_set(v___x_1909_, 0, lean_box(0));
lean_closure_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM___boxed), 9, 2);
lean_closure_set(v___x_1910_, 0, lean_box(0));
lean_closure_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = l_Lake_ensureJob___redArg(v___x_1888_, v___x_1910_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1936_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
v_a_1913_ = lean_ctor_get(v___x_1911_, 1);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1915_ = v___x_1911_;
v_isShared_1916_ = v_isSharedCheck_1936_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1936_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v_task_1917_; lean_object* v_kind_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1934_; 
v_task_1917_ = lean_ctor_get(v_a_1912_, 0);
v_kind_1918_ = lean_ctor_get(v_a_1912_, 1);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_a_1912_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v_a_1912_, 2);
lean_dec(v_unused_1935_);
v___x_1920_ = v_a_1912_;
v_isShared_1921_ = v_isSharedCheck_1934_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_kind_1918_);
lean_inc(v_task_1917_);
lean_dec(v_a_1912_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1934_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_registeredJobs_1922_; lean_object* v_job_1924_; 
v_registeredJobs_1922_ = lean_ctor_get(v___y_1894_, 4);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 2, v___x_1905_);
v_job_1924_ = v___x_1920_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_task_1917_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_kind_1918_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v___x_1905_);
v_job_1924_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
lean_ctor_set_uint8(v_job_1924_, sizeof(void*)*3, v___x_1899_);
v___x_1925_ = lean_st_ref_take(v_registeredJobs_1922_);
lean_inc_ref(v_job_1924_);
v___x_1926_ = l_Lake_Job_toOpaque___redArg(v_job_1924_);
v___x_1927_ = lean_array_push(v___x_1925_, v___x_1926_);
v___x_1928_ = lean_st_ref_put(v_registeredJobs_1922_, v___x_1927_);
v___x_1929_ = l_Lake_Job_renew___redArg(v_job_1924_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1929_);
v___x_1931_ = v___x_1915_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_a_1913_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1905_);
return v___x_1911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___lam__1___boxed(lean_object* v_fetch_1937_, lean_object* v_facet_1938_, lean_object* v___x_1939_, lean_object* v_pkg_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___lam__1(v_fetch_1937_, v_facet_1938_, v___x_1939_, v_pkg_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec(v___y_1942_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg(lean_object* v_facet_1956_, lean_object* v_fetch_1957_){
_start:
{
lean_object* v___x_1958_; lean_object* v___f_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1958_ = l_Lake_instDataKindBool;
v___f_1959_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___lam__1___boxed), 11, 3);
lean_closure_set(v___f_1959_, 0, v_fetch_1957_);
lean_closure_set(v___f_1959_, 1, v_facet_1956_);
lean_closure_set(v___f_1959_, 2, v___x_1958_);
v___x_1960_ = l_Lake_Package_keyword;
v___x_1961_ = 1;
v___x_1962_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__3));
v___x_1963_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1963_, 0, v___x_1960_);
lean_ctor_set(v___x_1963_, 1, v___f_1959_);
lean_ctor_set(v___x_1963_, 2, v___x_1958_);
lean_ctor_set(v___x_1963_, 3, v___x_1962_);
lean_ctor_set_uint8(v___x_1963_, sizeof(void*)*4, v___x_1961_);
lean_ctor_set_uint8(v___x_1963_, sizeof(void*)*4 + 1, v___x_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig(lean_object* v_facet_1964_, lean_object* v_fetch_1965_, lean_object* v_inst_1966_){
_start:
{
lean_object* v___x_1967_; lean_object* v___f_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1967_ = l_Lake_instDataKindBool;
v___f_1968_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___lam__1___boxed), 11, 3);
lean_closure_set(v___f_1968_, 0, v_fetch_1965_);
lean_closure_set(v___f_1968_, 1, v_facet_1964_);
lean_closure_set(v___f_1968_, 2, v___x_1967_);
v___x_1969_ = l_Lake_Package_keyword;
v___x_1970_ = 1;
v___x_1971_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__3));
v___x_1972_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1972_, 0, v___x_1969_);
lean_ctor_set(v___x_1972_, 1, v___f_1968_);
lean_ctor_set(v___x_1972_, 2, v___x_1967_);
lean_ctor_set(v___x_1972_, 3, v___x_1971_);
lean_ctor_set_uint8(v___x_1972_, sizeof(void*)*4, v___x_1970_);
lean_ctor_set_uint8(v___x_1972_, sizeof(void*)*4 + 1, v___x_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__1(lean_object* v_x_1973_, lean_object* v_x_1974_){
_start:
{
if (lean_obj_tag(v_x_1973_) == 0)
{
if (lean_obj_tag(v_x_1974_) == 0)
{
uint8_t v___x_1975_; 
v___x_1975_ = 1;
return v___x_1975_;
}
else
{
uint8_t v___x_1976_; 
v___x_1976_ = 0;
return v___x_1976_;
}
}
else
{
if (lean_obj_tag(v_x_1974_) == 0)
{
uint8_t v___x_1977_; 
v___x_1977_ = 0;
return v___x_1977_;
}
else
{
lean_object* v_val_1978_; uint8_t v___x_1979_; 
v_val_1978_ = lean_ctor_get(v_x_1974_, 0);
v___x_1979_ = lean_unbox(v_val_1978_);
if (v___x_1979_ == 0)
{
lean_object* v_val_1980_; uint8_t v___x_1981_; 
v_val_1980_ = lean_ctor_get(v_x_1973_, 0);
v___x_1981_ = lean_unbox(v_val_1980_);
if (v___x_1981_ == 0)
{
uint8_t v___x_1982_; 
v___x_1982_ = 1;
return v___x_1982_;
}
else
{
uint8_t v___x_1983_; 
v___x_1983_ = lean_unbox(v_val_1978_);
return v___x_1983_;
}
}
else
{
lean_object* v_val_1984_; uint8_t v___x_1985_; 
v_val_1984_ = lean_ctor_get(v_x_1973_, 0);
v___x_1985_ = lean_unbox(v_val_1984_);
return v___x_1985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__1___boxed(lean_object* v_x_1986_, lean_object* v_x_1987_){
_start:
{
uint8_t v_res_1988_; lean_object* v_r_1989_; 
v_res_1988_ = l_instBEqOption_beq___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__1(v_x_1986_, v_x_1987_);
lean_dec(v_x_1987_);
lean_dec(v_x_1986_);
v_r_1989_ = lean_box(v_res_1988_);
return v_r_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___lam__0(lean_object* v_val_1990_, lean_object* v_e_1991_){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = lean_st_ref_take(v_val_1990_);
v___x_1994_ = lean_array_push(v___x_1993_, v_e_1991_);
v___x_1995_ = lean_st_ref_put(v_val_1990_, v___x_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___lam__0___boxed(lean_object* v_val_1996_, lean_object* v_e_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___lam__0(v_val_1996_, v_e_1997_);
lean_dec(v_val_1996_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__0(lean_object* v_pkg_2003_, lean_object* v___x_2004_, lean_object* v_val_2005_, lean_object* v_a_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, uint8_t v___y_2009_, lean_object* v_as_2010_, size_t v_sz_2011_, size_t v_i_2012_, lean_object* v_b_2013_, lean_object* v___y_2014_){
_start:
{
uint8_t v___x_2016_; 
v___x_2016_ = lean_usize_dec_lt(v_i_2012_, v_sz_2011_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; 
lean_dec(v_a_2006_);
lean_dec_ref(v_val_2005_);
lean_dec_ref(v___x_2004_);
lean_dec_ref(v_pkg_2003_);
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v_b_2013_);
return v___x_2017_;
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v_a_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec_ref(v_b_2013_);
v___x_2018_ = lean_box(0);
v___x_2019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__0___closed__0));
v_a_2020_ = lean_array_uget_borrowed(v_as_2010_, v_i_2012_);
lean_inc_ref(v_pkg_2003_);
v___x_2021_ = l_Lake_Package_cacheScope(v_pkg_2003_);
lean_inc(v_a_2006_);
lean_inc_ref(v_val_2005_);
lean_inc_ref(v___x_2004_);
lean_inc(v_a_2020_);
v___x_2022_ = l_Lake_CacheService_downloadRevisionOutputs_x3f(v_a_2020_, v___x_2004_, v_val_2005_, v___x_2021_, v_a_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2014_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2035_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2035_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2035_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
if (lean_obj_tag(v_a_2023_) == 1)
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2030_; 
lean_dec(v_a_2006_);
lean_dec_ref(v_val_2005_);
lean_dec_ref(v___x_2004_);
lean_dec_ref(v_pkg_2003_);
v___x_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2027_, 0, v_a_2023_);
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
lean_ctor_set(v___x_2028_, 1, v___x_2018_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2028_);
v___x_2030_ = v___x_2025_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
else
{
size_t v___x_2032_; size_t v___x_2033_; 
lean_del_object(v___x_2025_);
lean_dec(v_a_2023_);
v___x_2032_ = ((size_t)1ULL);
v___x_2033_ = lean_usize_add(v_i_2012_, v___x_2032_);
v_i_2012_ = v___x_2033_;
v_b_2013_ = v___x_2019_;
goto _start;
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec(v_a_2006_);
lean_dec_ref(v_val_2005_);
lean_dec_ref(v___x_2004_);
lean_dec_ref(v_pkg_2003_);
v_a_2036_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2022_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2022_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__0___boxed(lean_object* v_pkg_2044_, lean_object* v___x_2045_, lean_object* v_val_2046_, lean_object* v_a_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v_as_2051_, lean_object* v_sz_2052_, lean_object* v_i_2053_, lean_object* v_b_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
uint8_t v___y_121453__boxed_2057_; size_t v_sz_boxed_2058_; size_t v_i_boxed_2059_; lean_object* v_res_2060_; 
v___y_121453__boxed_2057_ = lean_unbox(v___y_2050_);
v_sz_boxed_2058_ = lean_unbox_usize(v_sz_2052_);
lean_dec(v_sz_2052_);
v_i_boxed_2059_ = lean_unbox_usize(v_i_2053_);
lean_dec(v_i_2053_);
v_res_2060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__0(v_pkg_2044_, v___x_2045_, v_val_2046_, v_a_2047_, v___y_2048_, v___y_2049_, v___y_121453__boxed_2057_, v_as_2051_, v_sz_boxed_2058_, v_i_boxed_2059_, v_b_2054_, v___y_2055_);
lean_dec_ref(v___y_2055_);
lean_dec_ref(v_as_2051_);
lean_dec_ref(v___y_2049_);
lean_dec_ref(v___y_2048_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___lam__1(lean_object* v_dir_2061_, lean_object* v_val_2062_, lean_object* v_a_2063_, lean_object* v_pkg_2064_, lean_object* v_lakeCache_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, uint8_t v___y_2068_, lean_object* v_____r_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_toBuildConfig_2077_; lean_object* v_log_2078_; uint8_t v_action_2079_; uint8_t v_wantsRebuild_2080_; uint8_t v_canceled_2081_; lean_object* v_trace_2082_; lean_object* v_buildTime_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2157_; 
v_toBuildConfig_2077_ = lean_ctor_get(v___y_2074_, 0);
v_log_2078_ = lean_ctor_get(v___y_2075_, 0);
v_action_2079_ = lean_ctor_get_uint8(v___y_2075_, sizeof(void*)*3);
v_wantsRebuild_2080_ = lean_ctor_get_uint8(v___y_2075_, sizeof(void*)*3 + 1);
v_canceled_2081_ = lean_ctor_get_uint8(v___y_2075_, sizeof(void*)*3 + 2);
v_trace_2082_ = lean_ctor_get(v___y_2075_, 1);
v_buildTime_2083_ = lean_ctor_get(v___y_2075_, 2);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___y_2075_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2085_ = v___y_2075_;
v_isShared_2086_ = v_isSharedCheck_2157_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_buildTime_2083_);
lean_inc(v_trace_2082_);
lean_inc(v_log_2078_);
lean_dec(v___y_2075_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2157_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v_maxRevs_2087_; lean_object* v___x_2088_; 
v_maxRevs_2087_ = lean_ctor_get(v_toBuildConfig_2077_, 5);
lean_inc(v_maxRevs_2087_);
v___x_2088_ = l_Lake_GitRepo_getHeadRevisions(v_dir_2061_, v_maxRevs_2087_, v_log_2078_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2144_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_a_2090_ = lean_ctor_get(v___x_2088_, 1);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2092_ = v___x_2088_;
v_isShared_2093_ = v_isSharedCheck_2144_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2144_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; size_t v_sz_2096_; size_t v___x_2097_; lean_object* v_startPos_2098_; lean_object* v___x_2099_; lean_object* v_val_2101_; lean_object* v_a_2129_; lean_object* v___f_2131_; lean_object* v___x_2132_; 
v___x_2094_ = lean_box(0);
v___x_2095_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__0___closed__0));
v_sz_2096_ = lean_array_size(v_a_2089_);
v___x_2097_ = ((size_t)0ULL);
v_startPos_2098_ = lean_array_get_size(v_a_2090_);
v___x_2099_ = lean_st_mk_ref(v_a_2090_);
lean_inc(v___x_2099_);
v___f_2131_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2131_, 0, v___x_2099_);
lean_inc(v_a_2063_);
lean_inc_ref(v_val_2062_);
v___x_2132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__0(v_pkg_2064_, v_lakeCache_2065_, v_val_2062_, v_a_2063_, v___y_2066_, v___y_2067_, v___y_2068_, v_a_2089_, v_sz_2096_, v___x_2097_, v___x_2095_, v___f_2131_);
lean_dec_ref(v___f_2131_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v_fst_2134_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v_fst_2134_ = lean_ctor_get(v_a_2133_, 0);
lean_inc(v_fst_2134_);
lean_dec(v_a_2133_);
if (lean_obj_tag(v_fst_2134_) == 0)
{
v_a_2129_ = v___x_2094_;
goto v___jp_2128_;
}
else
{
lean_object* v_val_2135_; 
v_val_2135_ = lean_ctor_get(v_fst_2134_, 0);
lean_inc(v_val_2135_);
lean_dec_ref_known(v_fst_2134_, 1);
v_a_2129_ = v_val_2135_;
goto v___jp_2128_;
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
v_a_2136_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2132_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2132_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
lean_ctor_set_tag(v___x_2138_, 0);
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
v_val_2101_ = v___x_2141_;
goto v___jp_2100_;
}
}
}
v___jp_2100_:
{
lean_object* v___x_2102_; 
v___x_2102_ = lean_st_ref_get(v___x_2099_);
lean_dec(v___x_2099_);
if (lean_obj_tag(v_val_2101_) == 0)
{
lean_object* v___x_2104_; 
lean_dec_ref_known(v_val_2101_, 1);
lean_dec(v_a_2089_);
lean_dec(v_a_2063_);
lean_dec_ref(v_val_2062_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2102_);
v___x_2104_ = v___x_2085_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_trace_2082_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_buildTime_2083_);
lean_ctor_set_uint8(v_reuseFailAlloc_2108_, sizeof(void*)*3, v_action_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2108_, sizeof(void*)*3 + 1, v_wantsRebuild_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2108_, sizeof(void*)*3 + 2, v_canceled_2081_);
v___x_2104_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 1);
lean_ctor_set(v___x_2092_, 1, v___x_2104_);
lean_ctor_set(v___x_2092_, 0, v_startPos_2098_);
v___x_2106_ = v___x_2092_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_startPos_2098_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
else
{
lean_object* v_a_2109_; 
v_a_2109_ = lean_ctor_get(v_val_2101_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v_val_2101_, 1);
if (lean_obj_tag(v_a_2109_) == 1)
{
lean_object* v_val_2110_; lean_object* v___x_2112_; 
lean_dec(v_a_2089_);
lean_dec(v_a_2063_);
lean_dec_ref(v_val_2062_);
v_val_2110_ = lean_ctor_get(v_a_2109_, 0);
lean_inc(v_val_2110_);
lean_dec_ref_known(v_a_2109_, 1);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2102_);
v___x_2112_ = v___x_2085_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_trace_2082_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_buildTime_2083_);
lean_ctor_set_uint8(v_reuseFailAlloc_2116_, sizeof(void*)*3, v_action_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2116_, sizeof(void*)*3 + 1, v_wantsRebuild_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2116_, sizeof(void*)*3 + 2, v_canceled_2081_);
v___x_2112_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2114_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 1, v___x_2112_);
lean_ctor_set(v___x_2092_, 0, v_val_2110_);
v___x_2114_ = v___x_2092_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_val_2110_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
else
{
lean_object* v___x_2117_; uint8_t v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2123_; 
lean_dec(v_a_2109_);
lean_inc(v_maxRevs_2087_);
v___x_2117_ = l_Lake_Internal_noOutputs(v_val_2062_, v_a_2063_, v_maxRevs_2087_, v_a_2089_);
lean_dec(v_a_2089_);
lean_dec(v_a_2063_);
v___x_2118_ = 3;
v___x_2119_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set_uint8(v___x_2119_, sizeof(void*)*1, v___x_2118_);
v___x_2120_ = lean_array_get_size(v___x_2102_);
v___x_2121_ = lean_array_push(v___x_2102_, v___x_2119_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2121_);
v___x_2123_ = v___x_2085_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_trace_2082_);
lean_ctor_set(v_reuseFailAlloc_2127_, 2, v_buildTime_2083_);
lean_ctor_set_uint8(v_reuseFailAlloc_2127_, sizeof(void*)*3, v_action_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2127_, sizeof(void*)*3 + 1, v_wantsRebuild_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2127_, sizeof(void*)*3 + 2, v_canceled_2081_);
v___x_2123_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2125_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 1);
lean_ctor_set(v___x_2092_, 1, v___x_2123_);
lean_ctor_set(v___x_2092_, 0, v___x_2120_);
v___x_2125_ = v___x_2092_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2126_, 1, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
v___jp_2128_:
{
lean_object* v___x_2130_; 
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v_a_2129_);
v_val_2101_ = v___x_2130_;
goto v___jp_2100_;
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2156_; 
lean_dec_ref(v_lakeCache_2065_);
lean_dec_ref(v_pkg_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_val_2062_);
v_a_2145_ = lean_ctor_get(v___x_2088_, 0);
v_a_2146_ = lean_ctor_get(v___x_2088_, 1);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2148_ = v___x_2088_;
v_isShared_2149_ = v_isSharedCheck_2156_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_inc(v_a_2145_);
lean_dec(v___x_2088_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2156_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v_a_2146_);
v___x_2151_ = v___x_2085_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2146_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_trace_2082_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_buildTime_2083_);
lean_ctor_set_uint8(v_reuseFailAlloc_2155_, sizeof(void*)*3, v_action_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2155_, sizeof(void*)*3 + 1, v_wantsRebuild_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2155_, sizeof(void*)*3 + 2, v_canceled_2081_);
v___x_2151_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2153_; 
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 1, v___x_2151_);
v___x_2153_ = v___x_2148_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2145_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___lam__1___boxed(lean_object* v_dir_2158_, lean_object* v_val_2159_, lean_object* v_a_2160_, lean_object* v_pkg_2161_, lean_object* v_lakeCache_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v_____r_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
uint8_t v___y_121537__boxed_2174_; lean_object* v_res_2175_; 
v___y_121537__boxed_2174_ = lean_unbox(v___y_2165_);
v_res_2175_ = l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___lam__1(v_dir_2158_, v_val_2159_, v_a_2160_, v_pkg_2161_, v_lakeCache_2162_, v___y_2163_, v___y_2164_, v___y_121537__boxed_2174_, v_____r_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec_ref(v___y_2164_);
lean_dec_ref(v___y_2163_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__2(lean_object* v___x_2179_, lean_object* v_as_2180_, size_t v_sz_2181_, size_t v_i_2182_, lean_object* v_b_2183_){
_start:
{
uint8_t v___x_2184_; 
v___x_2184_ = lean_usize_dec_lt(v_i_2182_, v_sz_2181_);
if (v___x_2184_ == 0)
{
lean_inc_ref(v_b_2183_);
return v_b_2183_;
}
else
{
lean_object* v_a_2185_; lean_object* v_cacheServices_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v_a_2185_ = lean_array_uget_borrowed(v_as_2180_, v_i_2182_);
v_cacheServices_2186_ = lean_ctor_get(v_a_2185_, 18);
v___x_2187_ = lean_box(0);
v___x_2188_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_2186_, v___x_2179_);
if (lean_obj_tag(v___x_2188_) == 1)
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
v___x_2190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v___x_2187_);
return v___x_2190_;
}
else
{
lean_object* v___x_2191_; size_t v___x_2192_; size_t v___x_2193_; 
lean_dec(v___x_2188_);
v___x_2191_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__2___closed__0));
v___x_2192_ = ((size_t)1ULL);
v___x_2193_ = lean_usize_add(v_i_2182_, v___x_2192_);
v_i_2182_ = v___x_2193_;
v_b_2183_ = v___x_2191_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__2___boxed(lean_object* v___x_2195_, lean_object* v_as_2196_, lean_object* v_sz_2197_, lean_object* v_i_2198_, lean_object* v_b_2199_){
_start:
{
size_t v_sz_boxed_2200_; size_t v_i_boxed_2201_; lean_object* v_res_2202_; 
v_sz_boxed_2200_ = lean_unbox_usize(v_sz_2197_);
lean_dec(v_sz_2197_);
v_i_boxed_2201_ = lean_unbox_usize(v_i_2198_);
lean_dec(v_i_2198_);
v_res_2202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__2(v___x_2195_, v_as_2196_, v_sz_boxed_2200_, v_i_boxed_2201_, v_b_2199_);
lean_dec_ref(v_b_2199_);
lean_dec_ref(v_as_2196_);
lean_dec(v___x_2195_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache(lean_object* v_pkg_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v___y_2221_; uint8_t v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v_baseName_2274_; lean_object* v_dir_2275_; lean_object* v_config_2276_; lean_object* v_scope_2277_; lean_object* v___y_2279_; lean_object* v___y_2280_; uint8_t v___y_2281_; lean_object* v___y_2282_; uint8_t v___y_2283_; uint8_t v___y_2284_; lean_object* v___y_2285_; uint8_t v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v_downloadCacheService_x3f_2298_; 
v_baseName_2274_ = lean_ctor_get(v_pkg_2212_, 1);
v_dir_2275_ = lean_ctor_get(v_pkg_2212_, 4);
v_config_2276_ = lean_ctor_get(v_pkg_2212_, 6);
v_scope_2277_ = lean_ctor_get(v_pkg_2212_, 10);
v_downloadCacheService_x3f_2298_ = lean_ctor_get(v_config_2276_, 12);
if (lean_obj_tag(v_downloadCacheService_x3f_2298_) == 0)
{
lean_object* v_log_2299_; uint8_t v_action_2300_; uint8_t v_wantsRebuild_2301_; uint8_t v_canceled_2302_; lean_object* v_trace_2303_; lean_object* v_buildTime_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_a_2213_);
lean_dec_ref(v_pkg_2212_);
v_log_2299_ = lean_ctor_get(v_a_2218_, 0);
v_action_2300_ = lean_ctor_get_uint8(v_a_2218_, sizeof(void*)*3);
v_wantsRebuild_2301_ = lean_ctor_get_uint8(v_a_2218_, sizeof(void*)*3 + 1);
v_canceled_2302_ = lean_ctor_get_uint8(v_a_2218_, sizeof(void*)*3 + 2);
v_trace_2303_ = lean_ctor_get(v_a_2218_, 1);
v_buildTime_2304_ = lean_ctor_get(v_a_2218_, 2);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_a_2218_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2306_ = v_a_2218_;
v_isShared_2307_ = v_isSharedCheck_2315_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_buildTime_2304_);
lean_inc(v_trace_2303_);
lean_inc(v_log_2299_);
lean_dec(v_a_2218_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2315_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2308_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__1));
v___x_2309_ = lean_array_get_size(v_log_2299_);
v___x_2310_ = lean_array_push(v_log_2299_, v___x_2308_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v___x_2310_);
v___x_2312_ = v___x_2306_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_trace_2303_);
lean_ctor_set(v_reuseFailAlloc_2314_, 2, v_buildTime_2304_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*3, v_action_2300_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*3 + 1, v_wantsRebuild_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2314_, sizeof(void*)*3 + 2, v_canceled_2302_);
v___x_2312_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; 
v___x_2313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2309_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
return v___x_2313_;
}
}
}
else
{
lean_object* v_toLeanConfig_2316_; uint8_t v_bootstrap_2317_; uint8_t v_fixedToolchain_2318_; lean_object* v_val_2319_; lean_object* v_log_2320_; uint8_t v_action_2321_; uint8_t v_wantsRebuild_2322_; uint8_t v_canceled_2323_; lean_object* v_trace_2324_; lean_object* v_buildTime_2325_; lean_object* v_toContext_2337_; lean_object* v_lakeEnv_2338_; lean_object* v_lakeConfig_2339_; lean_object* v_lakeCache_2340_; lean_object* v_packages_2341_; uint8_t v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; uint8_t v___y_2348_; lean_object* v___y_2349_; lean_object* v_a_2350_; lean_object* v_a_2351_; uint8_t v___y_2364_; uint8_t v___y_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; uint8_t v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; uint8_t v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2398_; lean_object* v___y_2399_; uint8_t v___y_2400_; lean_object* v_val_2407_; lean_object* v_cacheServices_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v_toLeanConfig_2316_ = lean_ctor_get(v_config_2276_, 1);
v_bootstrap_2317_ = lean_ctor_get_uint8(v_config_2276_, sizeof(void*)*29);
v_fixedToolchain_2318_ = lean_ctor_get_uint8(v_config_2276_, sizeof(void*)*29 + 6);
v_val_2319_ = lean_ctor_get(v_downloadCacheService_x3f_2298_, 0);
v_log_2320_ = lean_ctor_get(v_a_2218_, 0);
lean_inc_ref(v_log_2320_);
v_action_2321_ = lean_ctor_get_uint8(v_a_2218_, sizeof(void*)*3);
v_wantsRebuild_2322_ = lean_ctor_get_uint8(v_a_2218_, sizeof(void*)*3 + 1);
v_canceled_2323_ = lean_ctor_get_uint8(v_a_2218_, sizeof(void*)*3 + 2);
v_trace_2324_ = lean_ctor_get(v_a_2218_, 1);
lean_inc_ref(v_trace_2324_);
v_buildTime_2325_ = lean_ctor_get(v_a_2218_, 2);
lean_inc(v_buildTime_2325_);
v_toContext_2337_ = lean_ctor_get(v_a_2217_, 1);
v_lakeEnv_2338_ = lean_ctor_get(v_toContext_2337_, 0);
v_lakeConfig_2339_ = lean_ctor_get(v_toContext_2337_, 1);
v_lakeCache_2340_ = lean_ctor_get(v_toContext_2337_, 2);
v_packages_2341_ = lean_ctor_get(v_toContext_2337_, 4);
v_cacheServices_2428_ = lean_ctor_get(v_lakeConfig_2339_, 3);
v___x_2429_ = lean_box(0);
lean_inc(v_val_2319_);
v___x_2430_ = l_Lean_Name_str___override(v___x_2429_, v_val_2319_);
v___x_2431_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_cacheServices_2428_, v___x_2430_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v___x_2432_; size_t v_sz_2433_; size_t v___x_2434_; lean_object* v___x_2435_; lean_object* v_fst_2436_; 
v___x_2432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__2___closed__0));
v_sz_2433_ = lean_array_size(v_packages_2341_);
v___x_2434_ = ((size_t)0ULL);
v___x_2435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__2(v___x_2430_, v_packages_2341_, v_sz_2433_, v___x_2434_, v___x_2432_);
lean_dec(v___x_2430_);
v_fst_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_fst_2436_);
lean_dec_ref(v___x_2435_);
if (lean_obj_tag(v_fst_2436_) == 0)
{
lean_inc(v_val_2319_);
lean_dec_ref(v_a_2218_);
lean_dec_ref(v_a_2213_);
lean_dec_ref(v_pkg_2212_);
goto v___jp_2326_;
}
else
{
lean_object* v_val_2437_; 
v_val_2437_ = lean_ctor_get(v_fst_2436_, 0);
lean_inc(v_val_2437_);
lean_dec_ref_known(v_fst_2436_, 1);
if (lean_obj_tag(v_val_2437_) == 1)
{
lean_object* v_val_2438_; 
v_val_2438_ = lean_ctor_get(v_val_2437_, 0);
lean_inc(v_val_2438_);
lean_dec_ref_known(v_val_2437_, 1);
v_val_2407_ = v_val_2438_;
goto v___jp_2406_;
}
else
{
lean_inc(v_val_2319_);
lean_dec(v_val_2437_);
lean_dec_ref(v_a_2218_);
lean_dec_ref(v_a_2213_);
lean_dec_ref(v_pkg_2212_);
goto v___jp_2326_;
}
}
}
else
{
lean_object* v_val_2439_; 
lean_dec(v___x_2430_);
v_val_2439_ = lean_ctor_get(v___x_2431_, 0);
lean_inc(v_val_2439_);
lean_dec_ref_known(v___x_2431_, 1);
v_val_2407_ = v_val_2439_;
goto v___jp_2406_;
}
v___jp_2326_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2327_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__2));
v___x_2328_ = lean_string_append(v___x_2327_, v_val_2319_);
lean_dec(v_val_2319_);
v___x_2329_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__3));
v___x_2330_ = lean_string_append(v___x_2328_, v___x_2329_);
v___x_2331_ = 3;
v___x_2332_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set_uint8(v___x_2332_, sizeof(void*)*1, v___x_2331_);
v___x_2333_ = lean_array_get_size(v_log_2320_);
v___x_2334_ = lean_array_push(v_log_2320_, v___x_2332_);
v___x_2335_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
lean_ctor_set(v___x_2335_, 1, v_trace_2324_);
lean_ctor_set(v___x_2335_, 2, v_buildTime_2325_);
lean_ctor_set_uint8(v___x_2335_, sizeof(void*)*3, v_action_2321_);
lean_ctor_set_uint8(v___x_2335_, sizeof(void*)*3 + 1, v_wantsRebuild_2322_);
lean_ctor_set_uint8(v___x_2335_, sizeof(void*)*3 + 2, v_canceled_2323_);
v___x_2336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2333_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
return v___x_2336_;
}
v___jp_2342_:
{
lean_object* v_log_2352_; uint8_t v_action_2353_; uint8_t v_wantsRebuild_2354_; uint8_t v_canceled_2355_; lean_object* v_trace_2356_; lean_object* v_buildTime_2357_; lean_object* v___x_2358_; lean_object* v___f_2359_; uint8_t v___x_2360_; 
v_log_2352_ = lean_ctor_get(v_a_2351_, 0);
v_action_2353_ = lean_ctor_get_uint8(v_a_2351_, sizeof(void*)*3);
v_wantsRebuild_2354_ = lean_ctor_get_uint8(v_a_2351_, sizeof(void*)*3 + 1);
v_canceled_2355_ = lean_ctor_get_uint8(v_a_2351_, sizeof(void*)*3 + 2);
v_trace_2356_ = lean_ctor_get(v_a_2351_, 1);
v_buildTime_2357_ = lean_ctor_get(v_a_2351_, 2);
v___x_2358_ = lean_box(v___y_2343_);
lean_inc_ref(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc_ref(v_lakeCache_2340_);
lean_inc_ref(v_pkg_2212_);
lean_inc(v_a_2350_);
lean_inc_ref(v___y_2346_);
lean_inc_ref_n(v_dir_2275_, 2);
v___f_2359_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___lam__1___boxed), 16, 8);
lean_closure_set(v___f_2359_, 0, v_dir_2275_);
lean_closure_set(v___f_2359_, 1, v___y_2346_);
lean_closure_set(v___f_2359_, 2, v_a_2350_);
lean_closure_set(v___f_2359_, 3, v_pkg_2212_);
lean_closure_set(v___f_2359_, 4, v_lakeCache_2340_);
lean_closure_set(v___f_2359_, 5, v___y_2344_);
lean_closure_set(v___f_2359_, 6, v___y_2345_);
lean_closure_set(v___f_2359_, 7, v___x_2358_);
v___x_2360_ = l_Lake_GitRepo_hasNoDiff(v_dir_2275_);
if (v___x_2360_ == 0)
{
lean_inc(v_buildTime_2357_);
lean_inc_ref(v_trace_2356_);
lean_inc_ref(v_log_2352_);
lean_dec_ref(v_a_2351_);
lean_dec_ref(v___y_2346_);
lean_dec_ref(v___y_2345_);
v___y_2279_ = v___y_2347_;
v___y_2280_ = v_trace_2356_;
v___y_2281_ = v_wantsRebuild_2354_;
v___y_2282_ = v_a_2350_;
v___y_2283_ = v___y_2348_;
v___y_2284_ = v_action_2353_;
v___y_2285_ = v_log_2352_;
v___y_2286_ = v_canceled_2355_;
v___y_2287_ = v___f_2359_;
v___y_2288_ = v_buildTime_2357_;
v___y_2289_ = v___y_2349_;
goto v___jp_2278_;
}
else
{
if (v___y_2348_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec_ref(v___f_2359_);
v___x_2361_ = lean_box(0);
lean_inc_ref(v_lakeCache_2340_);
lean_inc_ref(v_pkg_2212_);
lean_inc(v_a_2350_);
lean_inc_ref(v_dir_2275_);
v___x_2362_ = l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___lam__1(v_dir_2275_, v___y_2346_, v_a_2350_, v_pkg_2212_, v_lakeCache_2340_, v___y_2344_, v___y_2345_, v___y_2343_, v___x_2361_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2351_);
lean_dec_ref(v_a_2213_);
lean_dec_ref(v___y_2345_);
v___y_2221_ = v___y_2347_;
v___y_2222_ = v___y_2348_;
v___y_2223_ = v_a_2350_;
v___y_2224_ = v___y_2349_;
v___y_2225_ = v___x_2362_;
goto v___jp_2220_;
}
else
{
lean_inc(v_buildTime_2357_);
lean_inc_ref(v_trace_2356_);
lean_inc_ref(v_log_2352_);
lean_dec_ref(v_a_2351_);
lean_dec_ref(v___y_2346_);
lean_dec_ref(v___y_2345_);
v___y_2279_ = v___y_2347_;
v___y_2280_ = v_trace_2356_;
v___y_2281_ = v_wantsRebuild_2354_;
v___y_2282_ = v_a_2350_;
v___y_2283_ = v___y_2348_;
v___y_2284_ = v_action_2353_;
v___y_2285_ = v_log_2352_;
v___y_2286_ = v_canceled_2355_;
v___y_2287_ = v___f_2359_;
v___y_2288_ = v_buildTime_2357_;
v___y_2289_ = v___y_2349_;
goto v___jp_2278_;
}
}
}
v___jp_2363_:
{
uint8_t v_isReservoir_2372_; 
v_isReservoir_2372_ = lean_ctor_get_uint8(v___y_2367_, sizeof(void*)*5 + 1);
if (v_isReservoir_2372_ == 0)
{
lean_object* v___x_2373_; 
lean_dec(v_buildTime_2325_);
lean_dec_ref(v_trace_2324_);
lean_dec_ref(v_log_2320_);
v___x_2373_ = lean_box(0);
v___y_2343_ = v___y_2364_;
v___y_2344_ = v___y_2366_;
v___y_2345_ = v___y_2371_;
v___y_2346_ = v___y_2369_;
v___y_2347_ = v___y_2368_;
v___y_2348_ = v___y_2365_;
v___y_2349_ = v___y_2367_;
v_a_2350_ = v___x_2373_;
v_a_2351_ = v___y_2370_;
goto v___jp_2342_;
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; 
v___x_2374_ = lean_string_utf8_byte_size(v_scope_2277_);
v___x_2375_ = lean_unsigned_to_nat(0u);
v___x_2376_ = lean_nat_dec_eq(v___x_2374_, v___x_2375_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; 
lean_dec(v_buildTime_2325_);
lean_dec_ref(v_trace_2324_);
lean_dec_ref(v_log_2320_);
lean_inc_ref(v_pkg_2212_);
v___x_2377_ = l___private_Lake_Config_Package_0__Lake_Package_reservoirScope(v_pkg_2212_);
v___y_2343_ = v___y_2364_;
v___y_2344_ = v___y_2366_;
v___y_2345_ = v___y_2371_;
v___y_2346_ = v___y_2369_;
v___y_2347_ = v___y_2368_;
v___y_2348_ = v___y_2365_;
v___y_2349_ = v___y_2367_;
v_a_2350_ = v___x_2377_;
v_a_2351_ = v___y_2370_;
goto v___jp_2342_;
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
lean_inc(v_baseName_2274_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec_ref(v_a_2213_);
lean_dec_ref(v_pkg_2212_);
v___x_2378_ = l_Lean_Name_toString(v_baseName_2274_, v___y_2365_);
v___x_2379_ = l_Lake_Internal_packageNotReservoir(v___x_2378_);
v___x_2380_ = 3;
v___x_2381_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2381_, 0, v___x_2379_);
lean_ctor_set_uint8(v___x_2381_, sizeof(void*)*1, v___x_2380_);
v___x_2382_ = lean_array_get_size(v_log_2320_);
v___x_2383_ = lean_array_push(v_log_2320_, v___x_2381_);
v___x_2384_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
lean_ctor_set(v___x_2384_, 1, v_trace_2324_);
lean_ctor_set(v___x_2384_, 2, v_buildTime_2325_);
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*3, v_action_2321_);
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*3 + 1, v_wantsRebuild_2322_);
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*3 + 2, v_canceled_2323_);
v___x_2385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2382_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
return v___x_2385_;
}
}
}
v___jp_2386_:
{
if (v_fixedToolchain_2318_ == 0)
{
if (v_bootstrap_2317_ == 0)
{
lean_object* v_toolchain_2394_; 
v_toolchain_2394_ = lean_ctor_get(v___y_2391_, 19);
lean_inc_ref(v_toolchain_2394_);
lean_dec_ref(v___y_2391_);
v___y_2364_ = v___y_2387_;
v___y_2365_ = v___y_2390_;
v___y_2366_ = v___y_2393_;
v___y_2367_ = v___y_2392_;
v___y_2368_ = v___y_2389_;
v___y_2369_ = v___y_2388_;
v___y_2370_ = v_a_2218_;
v___y_2371_ = v_toolchain_2394_;
goto v___jp_2363_;
}
else
{
lean_object* v___x_2395_; 
lean_dec_ref(v___y_2391_);
v___x_2395_ = l_Lake_CacheToolchain_none;
v___y_2364_ = v___y_2387_;
v___y_2365_ = v___y_2390_;
v___y_2366_ = v___y_2393_;
v___y_2367_ = v___y_2392_;
v___y_2368_ = v___y_2389_;
v___y_2369_ = v___y_2388_;
v___y_2370_ = v_a_2218_;
v___y_2371_ = v___x_2395_;
goto v___jp_2363_;
}
}
else
{
lean_object* v___x_2396_; 
lean_dec_ref(v___y_2391_);
v___x_2396_ = l_Lake_CacheToolchain_none;
v___y_2364_ = v___y_2387_;
v___y_2365_ = v___y_2390_;
v___y_2366_ = v___y_2393_;
v___y_2367_ = v___y_2392_;
v___y_2368_ = v___y_2389_;
v___y_2369_ = v___y_2388_;
v___y_2370_ = v_a_2218_;
v___y_2371_ = v___x_2396_;
goto v___jp_2363_;
}
}
v___jp_2397_:
{
lean_object* v_platformIndependent_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; 
v_platformIndependent_2401_ = lean_ctor_get(v_toLeanConfig_2316_, 10);
v___x_2402_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___closed__4));
v___x_2403_ = l_instBEqOption_beq___at___00__private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache_spec__1(v_platformIndependent_2401_, v___x_2402_);
if (v___x_2403_ == 0)
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lake_CachePlatform_system;
lean_inc_ref(v_lakeEnv_2338_);
lean_inc_ref(v_lakeCache_2340_);
v___y_2387_ = v___y_2400_;
v___y_2388_ = v___y_2398_;
v___y_2389_ = v_lakeCache_2340_;
v___y_2390_ = v___y_2400_;
v___y_2391_ = v_lakeEnv_2338_;
v___y_2392_ = v___y_2399_;
v___y_2393_ = v___x_2404_;
goto v___jp_2386_;
}
else
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lake_CachePlatform_none;
lean_inc_ref(v_lakeEnv_2338_);
lean_inc_ref(v_lakeCache_2340_);
v___y_2387_ = v___y_2400_;
v___y_2388_ = v___y_2398_;
v___y_2389_ = v_lakeCache_2340_;
v___y_2390_ = v___y_2400_;
v___y_2391_ = v_lakeEnv_2338_;
v___y_2392_ = v___y_2399_;
v___y_2393_ = v___x_2405_;
goto v___jp_2386_;
}
}
v___jp_2406_:
{
uint8_t v_hasPackageScopes_2408_; 
v_hasPackageScopes_2408_ = lean_ctor_get_uint8(v_val_2407_, sizeof(void*)*5);
if (v_hasPackageScopes_2408_ == 0)
{
lean_inc_ref(v_val_2407_);
v___y_2398_ = v_val_2407_;
v___y_2399_ = v_val_2407_;
v___y_2400_ = v_hasPackageScopes_2408_;
goto v___jp_2397_;
}
else
{
uint8_t v_isReservoir_2409_; 
v_isReservoir_2409_ = lean_ctor_get_uint8(v_val_2407_, sizeof(void*)*5 + 1);
if (v_isReservoir_2409_ == 0)
{
lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2423_; 
lean_inc(v_val_2319_);
lean_inc(v_baseName_2274_);
lean_dec_ref(v_val_2407_);
lean_dec_ref(v_a_2213_);
lean_dec_ref(v_pkg_2212_);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_a_2218_);
if (v_isSharedCheck_2423_ == 0)
{
lean_object* v_unused_2424_; lean_object* v_unused_2425_; lean_object* v_unused_2426_; 
v_unused_2424_ = lean_ctor_get(v_a_2218_, 2);
lean_dec(v_unused_2424_);
v_unused_2425_ = lean_ctor_get(v_a_2218_, 1);
lean_dec(v_unused_2425_);
v_unused_2426_ = lean_ctor_get(v_a_2218_, 0);
lean_dec(v_unused_2426_);
v___x_2411_ = v_a_2218_;
v_isShared_2412_ = v_isSharedCheck_2423_;
goto v_resetjp_2410_;
}
else
{
lean_dec(v_a_2218_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2423_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2420_; 
v___x_2413_ = l_Lean_Name_toString(v_baseName_2274_, v_isReservoir_2409_);
v___x_2414_ = l_Lake_Internal_packageServiceRequiresScope(v___x_2413_, v_val_2319_);
lean_dec(v_val_2319_);
v___x_2415_ = 3;
v___x_2416_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set_uint8(v___x_2416_, sizeof(void*)*1, v___x_2415_);
v___x_2417_ = lean_array_get_size(v_log_2320_);
v___x_2418_ = lean_array_push(v_log_2320_, v___x_2416_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v___x_2418_);
v___x_2420_ = v___x_2411_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2418_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_trace_2324_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_buildTime_2325_);
lean_ctor_set_uint8(v_reuseFailAlloc_2422_, sizeof(void*)*3, v_action_2321_);
lean_ctor_set_uint8(v_reuseFailAlloc_2422_, sizeof(void*)*3 + 1, v_wantsRebuild_2322_);
lean_ctor_set_uint8(v_reuseFailAlloc_2422_, sizeof(void*)*3 + 2, v_canceled_2323_);
v___x_2420_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2417_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
return v___x_2421_;
}
}
}
else
{
uint8_t v___x_2427_; 
v___x_2427_ = 0;
lean_inc_ref(v_val_2407_);
v___y_2398_ = v_val_2407_;
v___y_2399_ = v_val_2407_;
v___y_2400_ = v___x_2427_;
goto v___jp_2397_;
}
}
}
}
v___jp_2220_:
{
if (lean_obj_tag(v___y_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2264_; 
v_a_2226_ = lean_ctor_get(v___y_2225_, 1);
v_a_2227_ = lean_ctor_get(v___y_2225_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___y_2225_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2229_ = v___y_2225_;
v_isShared_2230_ = v_isSharedCheck_2264_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2226_);
lean_inc(v_a_2227_);
lean_dec(v___y_2225_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2264_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v_name_x3f_2231_; lean_object* v_log_2232_; uint8_t v_action_2233_; uint8_t v_wantsRebuild_2234_; uint8_t v_canceled_2235_; lean_object* v_trace_2236_; lean_object* v_buildTime_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_name_x3f_2231_ = lean_ctor_get(v___y_2224_, 0);
lean_inc(v_name_x3f_2231_);
lean_dec_ref(v___y_2224_);
v_log_2232_ = lean_ctor_get(v_a_2226_, 0);
v_action_2233_ = lean_ctor_get_uint8(v_a_2226_, sizeof(void*)*3);
v_wantsRebuild_2234_ = lean_ctor_get_uint8(v_a_2226_, sizeof(void*)*3 + 1);
v_canceled_2235_ = lean_ctor_get_uint8(v_a_2226_, sizeof(void*)*3 + 2);
v_trace_2236_ = lean_ctor_get(v_a_2226_, 1);
v_buildTime_2237_ = lean_ctor_get(v_a_2226_, 2);
v___x_2238_ = l_Lake_Package_cacheScope(v_pkg_2212_);
v___x_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___y_2223_);
v___x_2240_ = l_Lake_Cache_writeMap(v___y_2221_, v___x_2238_, v_a_2227_, v_name_x3f_2231_, v___x_2239_, v___y_2222_);
lean_dec(v_a_2227_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v_a_2241_);
v___x_2243_ = v___x_2229_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2241_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v_a_2226_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
else
{
lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2260_; 
lean_inc(v_buildTime_2237_);
lean_inc_ref(v_trace_2236_);
lean_inc_ref(v_log_2232_);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_a_2226_);
if (v_isSharedCheck_2260_ == 0)
{
lean_object* v_unused_2261_; lean_object* v_unused_2262_; lean_object* v_unused_2263_; 
v_unused_2261_ = lean_ctor_get(v_a_2226_, 2);
lean_dec(v_unused_2261_);
v_unused_2262_ = lean_ctor_get(v_a_2226_, 1);
lean_dec(v_unused_2262_);
v_unused_2263_ = lean_ctor_get(v_a_2226_, 0);
lean_dec(v_unused_2263_);
v___x_2246_ = v_a_2226_;
v_isShared_2247_ = v_isSharedCheck_2260_;
goto v_resetjp_2245_;
}
else
{
lean_dec(v_a_2226_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2260_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v_a_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2255_; 
v_a_2248_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v___x_2240_, 1);
v___x_2249_ = lean_io_error_to_string(v_a_2248_);
v___x_2250_ = 3;
v___x_2251_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set_uint8(v___x_2251_, sizeof(void*)*1, v___x_2250_);
v___x_2252_ = lean_array_get_size(v_log_2232_);
v___x_2253_ = lean_array_push(v_log_2232_, v___x_2251_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v___x_2253_);
v___x_2255_ = v___x_2246_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_trace_2236_);
lean_ctor_set(v_reuseFailAlloc_2259_, 2, v_buildTime_2237_);
lean_ctor_set_uint8(v_reuseFailAlloc_2259_, sizeof(void*)*3, v_action_2233_);
lean_ctor_set_uint8(v_reuseFailAlloc_2259_, sizeof(void*)*3 + 1, v_wantsRebuild_2234_);
lean_ctor_set_uint8(v_reuseFailAlloc_2259_, sizeof(void*)*3 + 2, v_canceled_2235_);
v___x_2255_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2257_; 
if (v_isShared_2230_ == 0)
{
lean_ctor_set_tag(v___x_2229_, 1);
lean_ctor_set(v___x_2229_, 1, v___x_2255_);
lean_ctor_set(v___x_2229_, 0, v___x_2252_);
v___x_2257_ = v___x_2229_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2252_);
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
}
}
else
{
lean_object* v_a_2265_; lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2221_);
lean_dec_ref(v_pkg_2212_);
v_a_2265_ = lean_ctor_get(v___y_2225_, 0);
v_a_2266_ = lean_ctor_get(v___y_2225_, 1);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___y_2225_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___y_2225_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_inc(v_a_2265_);
lean_dec(v___y_2225_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2265_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v_a_2266_);
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
v___jp_2278_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; uint8_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_inc(v_baseName_2274_);
v___x_2290_ = l_Lean_Name_toString(v_baseName_2274_, v___y_2283_);
v___x_2291_ = l_Lake_Internal_packageHasChanges(v___x_2290_);
v___x_2292_ = 2;
v___x_2293_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set_uint8(v___x_2293_, sizeof(void*)*1, v___x_2292_);
v___x_2294_ = lean_box(0);
v___x_2295_ = lean_array_push(v___y_2285_, v___x_2293_);
v___x_2296_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_ctor_set(v___x_2296_, 1, v___y_2280_);
lean_ctor_set(v___x_2296_, 2, v___y_2288_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*3, v___y_2284_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*3 + 1, v___y_2281_);
lean_ctor_set_uint8(v___x_2296_, sizeof(void*)*3 + 2, v___y_2286_);
lean_inc_ref(v_a_2217_);
lean_inc_ref(v_a_2216_);
lean_inc(v_a_2215_);
lean_inc(v_a_2214_);
v___x_2297_ = lean_apply_8(v___y_2287_, v___x_2294_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v___x_2296_, lean_box(0));
v___y_2221_ = v___y_2279_;
v___y_2222_ = v___y_2283_;
v___y_2223_ = v___y_2282_;
v___y_2224_ = v___y_2289_;
v___y_2225_ = v___x_2297_;
goto v___jp_2220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache___boxed(lean_object* v_pkg_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache(v_pkg_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
lean_dec_ref(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec(v_a_2443_);
lean_dec(v_a_2442_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCacheFacetConfig___lam__0(lean_object* v_pkg_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
uint8_t v_r_2458_; lean_object* v___y_2459_; lean_object* v___x_2462_; 
v___x_2462_ = l___private_Lake_Build_Package_0__Lake_Package_fetchArtifactCache(v_pkg_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; uint8_t v___x_2464_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 1);
lean_inc(v_a_2463_);
lean_dec_ref_known(v___x_2462_, 2);
v___x_2464_ = 1;
v_r_2458_ = v___x_2464_;
v___y_2459_ = v_a_2463_;
goto v___jp_2457_;
}
else
{
lean_object* v_a_2465_; lean_object* v_log_2466_; uint8_t v_action_2467_; uint8_t v_wantsRebuild_2468_; uint8_t v_canceled_2469_; lean_object* v_trace_2470_; lean_object* v_buildTime_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2481_; 
v_a_2465_ = lean_ctor_get(v___x_2462_, 1);
lean_inc(v_a_2465_);
lean_dec_ref_known(v___x_2462_, 2);
v_log_2466_ = lean_ctor_get(v_a_2465_, 0);
v_action_2467_ = lean_ctor_get_uint8(v_a_2465_, sizeof(void*)*3);
v_wantsRebuild_2468_ = lean_ctor_get_uint8(v_a_2465_, sizeof(void*)*3 + 1);
v_canceled_2469_ = lean_ctor_get_uint8(v_a_2465_, sizeof(void*)*3 + 2);
v_trace_2470_ = lean_ctor_get(v_a_2465_, 1);
v_buildTime_2471_ = lean_ctor_get(v_a_2465_, 2);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_a_2465_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2473_ = v_a_2465_;
v_isShared_2474_ = v_isSharedCheck_2481_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_buildTime_2471_);
lean_inc(v_trace_2470_);
lean_inc(v_log_2466_);
lean_dec(v_a_2465_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2481_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
uint8_t v___x_2475_; uint8_t v___x_2476_; lean_object* v___x_2478_; 
v___x_2475_ = 4;
v___x_2476_ = l_Lake_JobAction_merge(v_action_2467_, v___x_2475_);
if (v_isShared_2474_ == 0)
{
v___x_2478_ = v___x_2473_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_log_2466_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_trace_2470_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v_buildTime_2471_);
lean_ctor_set_uint8(v_reuseFailAlloc_2480_, sizeof(void*)*3 + 1, v_wantsRebuild_2468_);
lean_ctor_set_uint8(v_reuseFailAlloc_2480_, sizeof(void*)*3 + 2, v_canceled_2469_);
v___x_2478_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
uint8_t v___x_2479_; 
lean_ctor_set_uint8(v___x_2478_, sizeof(void*)*3, v___x_2476_);
v___x_2479_ = 0;
v_r_2458_ = v___x_2479_;
v___y_2459_ = v___x_2478_;
goto v___jp_2457_;
}
}
}
v___jp_2457_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_box(v_r_2458_);
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
lean_ctor_set(v___x_2461_, 1, v___y_2459_);
return v___x_2461_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCacheFacetConfig___lam__0___boxed(lean_object* v_pkg_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lake_Package_optArtifactCacheFacetConfig___lam__0(v_pkg_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec(v___y_2484_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCacheFacetConfig___lam__1(lean_object* v___x_2491_, lean_object* v___f_2492_, lean_object* v___x_2493_, lean_object* v___x_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = l_Lake_Job_async___redArg(v___x_2491_, v___f_2492_, v___x_2493_, v___x_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
lean_ctor_set(v___x_2503_, 1, v___y_2500_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCacheFacetConfig___lam__1___boxed(lean_object* v___x_2504_, lean_object* v___f_2505_, lean_object* v___x_2506_, lean_object* v___x_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Lake_Package_optArtifactCacheFacetConfig___lam__1(v___x_2504_, v___f_2505_, v___x_2506_, v___x_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec(v___y_2509_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCacheFacetConfig___lam__2(lean_object* v___x_2516_, lean_object* v___x_2517_, lean_object* v_pkg_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_baseName_2526_; lean_object* v___f_2527_; uint8_t v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___f_2537_; lean_object* v___x_2538_; 
v_baseName_2526_ = lean_ctor_get(v_pkg_2518_, 1);
lean_inc(v_baseName_2526_);
v___f_2527_ = lean_alloc_closure((void*)(l_Lake_Package_optArtifactCacheFacetConfig___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2527_, 0, v_pkg_2518_);
v___x_2528_ = 1;
v___x_2529_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2526_, v___x_2528_);
v___x_2530_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2531_ = lean_string_append(v___x_2529_, v___x_2530_);
v___x_2532_ = l_Lake_Name_eraseHead(v___x_2516_);
v___x_2533_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2532_, v___x_2528_);
v___x_2534_ = lean_string_append(v___x_2531_, v___x_2533_);
lean_dec_ref(v___x_2533_);
v___x_2535_ = lean_unsigned_to_nat(0u);
v___x_2536_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2517_);
v___f_2537_ = lean_alloc_closure((void*)(l_Lake_Package_optArtifactCacheFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2537_, 0, v___x_2517_);
lean_closure_set(v___f_2537_, 1, v___f_2527_);
lean_closure_set(v___f_2537_, 2, v___x_2535_);
lean_closure_set(v___f_2537_, 3, v___x_2536_);
v___x_2538_ = l_Lake_ensureJob___redArg(v___x_2517_, v___f_2537_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2563_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
v_a_2540_ = lean_ctor_get(v___x_2538_, 1);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2542_ = v___x_2538_;
v_isShared_2543_ = v_isSharedCheck_2563_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_inc(v_a_2539_);
lean_dec(v___x_2538_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2563_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v_task_2544_; lean_object* v_kind_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2561_; 
v_task_2544_ = lean_ctor_get(v_a_2539_, 0);
v_kind_2545_ = lean_ctor_get(v_a_2539_, 1);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_a_2539_);
if (v_isSharedCheck_2561_ == 0)
{
lean_object* v_unused_2562_; 
v_unused_2562_ = lean_ctor_get(v_a_2539_, 2);
lean_dec(v_unused_2562_);
v___x_2547_ = v_a_2539_;
v_isShared_2548_ = v_isSharedCheck_2561_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_kind_2545_);
lean_inc(v_task_2544_);
lean_dec(v_a_2539_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2561_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_registeredJobs_2549_; lean_object* v_job_2551_; 
v_registeredJobs_2549_ = lean_ctor_get(v___y_2523_, 4);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 2, v___x_2534_);
v_job_2551_ = v___x_2547_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_task_2544_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_kind_2545_);
lean_ctor_set(v_reuseFailAlloc_2560_, 2, v___x_2534_);
v_job_2551_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
lean_ctor_set_uint8(v_job_2551_, sizeof(void*)*3, v___x_2528_);
v___x_2552_ = lean_st_ref_take(v_registeredJobs_2549_);
lean_inc_ref(v_job_2551_);
v___x_2553_ = l_Lake_Job_toOpaque___redArg(v_job_2551_);
v___x_2554_ = lean_array_push(v___x_2552_, v___x_2553_);
v___x_2555_ = lean_st_ref_put(v_registeredJobs_2549_, v___x_2554_);
v___x_2556_ = l_Lake_Job_renew___redArg(v_job_2551_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v___x_2556_);
v___x_2558_ = v___x_2542_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
lean_ctor_set(v_reuseFailAlloc_2559_, 1, v_a_2540_);
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
lean_dec_ref(v___x_2534_);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optArtifactCacheFacetConfig___lam__2___boxed(lean_object* v___x_2564_, lean_object* v___x_2565_, lean_object* v_pkg_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lake_Package_optArtifactCacheFacetConfig___lam__2(v___x_2564_, v___x_2565_, v_pkg_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec(v___y_2568_);
return v_res_2574_;
}
}
static lean_object* _init_l_Lake_Package_optArtifactCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___f_2577_; 
v___x_2575_ = l_Lake_instDataKindBool;
v___x_2576_ = l_Lake_Package_optArtifactCacheFacet;
v___f_2577_ = lean_alloc_closure((void*)(l_Lake_Package_optArtifactCacheFacetConfig___lam__2___boxed), 10, 2);
lean_closure_set(v___f_2577_, 0, v___x_2576_);
lean_closure_set(v___f_2577_, 1, v___x_2575_);
return v___f_2577_;
}
}
static lean_object* _init_l_Lake_Package_optArtifactCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2578_; uint8_t v___x_2579_; lean_object* v___x_2580_; lean_object* v___f_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___f_2578_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_2579_ = 1;
v___x_2580_ = l_Lake_instDataKindBool;
v___f_2581_ = lean_obj_once(&l_Lake_Package_optArtifactCacheFacetConfig___closed__0, &l_Lake_Package_optArtifactCacheFacetConfig___closed__0_once, _init_l_Lake_Package_optArtifactCacheFacetConfig___closed__0);
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
static lean_object* _init_l_Lake_Package_optArtifactCacheFacetConfig(void){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_obj_once(&l_Lake_Package_optArtifactCacheFacetConfig___closed__1, &l_Lake_Package_optArtifactCacheFacetConfig___closed__1_once, _init_l_Lake_Package_optArtifactCacheFacetConfig___closed__1);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object* v_self_2594_, lean_object* v_a_2595_){
_start:
{
lean_object* v_rev_2598_; lean_object* v_log_2599_; uint8_t v_action_2600_; uint8_t v_wantsRebuild_2601_; uint8_t v_canceled_2602_; lean_object* v_trace_2603_; lean_object* v_buildTime_2604_; lean_object* v_dir_2613_; lean_object* v_config_2614_; lean_object* v_remoteUrl_2615_; lean_object* v_buildArchive_2616_; lean_object* v___y_2618_; uint8_t v___y_2619_; lean_object* v___y_2620_; uint8_t v___y_2621_; uint8_t v___y_2622_; lean_object* v___y_2623_; lean_object* v_val_2624_; lean_object* v___y_2644_; lean_object* v_releaseRepo_2666_; 
v_dir_2613_ = lean_ctor_get(v_self_2594_, 4);
lean_inc_ref(v_dir_2613_);
v_config_2614_ = lean_ctor_get(v_self_2594_, 6);
lean_inc_ref(v_config_2614_);
v_remoteUrl_2615_ = lean_ctor_get(v_self_2594_, 11);
lean_inc_ref(v_remoteUrl_2615_);
v_buildArchive_2616_ = lean_ctor_get(v_self_2594_, 22);
lean_inc_ref(v_buildArchive_2616_);
lean_dec_ref(v_self_2594_);
v_releaseRepo_2666_ = lean_ctor_get(v_config_2614_, 10);
lean_inc(v_releaseRepo_2666_);
lean_dec_ref(v_config_2614_);
if (lean_obj_tag(v_releaseRepo_2666_) == 0)
{
lean_object* v___x_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v___x_2667_ = lean_string_utf8_byte_size(v_remoteUrl_2615_);
v___x_2668_ = lean_unsigned_to_nat(0u);
v___x_2669_ = lean_nat_dec_eq(v___x_2667_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2670_, 0, v_remoteUrl_2615_);
v___y_2644_ = v___x_2670_;
goto v___jp_2643_;
}
else
{
lean_dec_ref(v_remoteUrl_2615_);
v___y_2644_ = v_releaseRepo_2666_;
goto v___jp_2643_;
}
}
else
{
lean_dec_ref(v_remoteUrl_2615_);
v___y_2644_ = v_releaseRepo_2666_;
goto v___jp_2643_;
}
v___jp_2597_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2605_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0));
v___x_2606_ = lean_string_append(v___x_2605_, v_rev_2598_);
lean_dec_ref(v_rev_2598_);
v___x_2607_ = 3;
v___x_2608_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2608_, 0, v___x_2606_);
lean_ctor_set_uint8(v___x_2608_, sizeof(void*)*1, v___x_2607_);
v___x_2609_ = lean_array_get_size(v_log_2599_);
v___x_2610_ = lean_array_push(v_log_2599_, v___x_2608_);
v___x_2611_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
lean_ctor_set(v___x_2611_, 1, v_trace_2603_);
lean_ctor_set(v___x_2611_, 2, v_buildTime_2604_);
lean_ctor_set_uint8(v___x_2611_, sizeof(void*)*3, v_action_2600_);
lean_ctor_set_uint8(v___x_2611_, sizeof(void*)*3 + 1, v_wantsRebuild_2601_);
lean_ctor_set_uint8(v___x_2611_, sizeof(void*)*3 + 2, v_canceled_2602_);
v___x_2612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2609_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
return v___x_2612_;
}
v___jp_2617_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
lean_inc_ref(v_dir_2613_);
v___x_2626_ = l_Lake_GitRepo_findTag_x3f(v___x_2625_, v_dir_2613_);
if (lean_obj_tag(v___x_2626_) == 1)
{
lean_object* v_val_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec_ref(v_dir_2613_);
v_val_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_val_2627_);
lean_dec_ref_known(v___x_2626_, 1);
v___x_2628_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2628_, 0, v___y_2620_);
lean_ctor_set(v___x_2628_, 1, v___y_2618_);
lean_ctor_set(v___x_2628_, 2, v___y_2623_);
lean_ctor_set_uint8(v___x_2628_, sizeof(void*)*3, v___y_2619_);
lean_ctor_set_uint8(v___x_2628_, sizeof(void*)*3 + 1, v___y_2621_);
lean_ctor_set_uint8(v___x_2628_, sizeof(void*)*3 + 2, v___y_2622_);
v___x_2629_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1));
v___x_2630_ = lean_string_append(v_val_2624_, v___x_2629_);
v___x_2631_ = lean_string_append(v___x_2630_, v_val_2627_);
lean_dec(v_val_2627_);
v___x_2632_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2));
v___x_2633_ = lean_string_append(v___x_2631_, v___x_2632_);
v___x_2634_ = lean_string_append(v___x_2633_, v_buildArchive_2616_);
lean_dec_ref(v_buildArchive_2616_);
v___x_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
lean_ctor_set(v___x_2635_, 1, v___x_2628_);
return v___x_2635_;
}
else
{
lean_object* v___x_2636_; 
lean_dec(v___x_2626_);
lean_dec_ref(v_val_2624_);
lean_dec_ref(v_buildArchive_2616_);
v___x_2636_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_2625_, v_dir_2613_);
if (lean_obj_tag(v___x_2636_) == 1)
{
lean_object* v_val_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v_val_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_val_2637_);
lean_dec_ref_known(v___x_2636_, 1);
v___x_2638_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3));
v___x_2639_ = lean_string_append(v___x_2638_, v_val_2637_);
lean_dec(v_val_2637_);
v___x_2640_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4));
v___x_2641_ = lean_string_append(v___x_2639_, v___x_2640_);
v_rev_2598_ = v___x_2641_;
v_log_2599_ = v___y_2620_;
v_action_2600_ = v___y_2619_;
v_wantsRebuild_2601_ = v___y_2621_;
v_canceled_2602_ = v___y_2622_;
v_trace_2603_ = v___y_2618_;
v_buildTime_2604_ = v___y_2623_;
goto v___jp_2597_;
}
else
{
lean_object* v___x_2642_; 
lean_dec(v___x_2636_);
v___x_2642_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_rev_2598_ = v___x_2642_;
v_log_2599_ = v___y_2620_;
v_action_2600_ = v___y_2619_;
v_wantsRebuild_2601_ = v___y_2621_;
v_canceled_2602_ = v___y_2622_;
v_trace_2603_ = v___y_2618_;
v_buildTime_2604_ = v___y_2623_;
goto v___jp_2597_;
}
}
}
v___jp_2643_:
{
lean_object* v_log_2645_; uint8_t v_action_2646_; uint8_t v_wantsRebuild_2647_; uint8_t v_canceled_2648_; lean_object* v_trace_2649_; lean_object* v_buildTime_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2665_; 
v_log_2645_ = lean_ctor_get(v_a_2595_, 0);
v_action_2646_ = lean_ctor_get_uint8(v_a_2595_, sizeof(void*)*3);
v_wantsRebuild_2647_ = lean_ctor_get_uint8(v_a_2595_, sizeof(void*)*3 + 1);
v_canceled_2648_ = lean_ctor_get_uint8(v_a_2595_, sizeof(void*)*3 + 2);
v_trace_2649_ = lean_ctor_get(v_a_2595_, 1);
v_buildTime_2650_ = lean_ctor_get(v_a_2595_, 2);
v_isSharedCheck_2665_ = !lean_is_exclusive(v_a_2595_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2652_ = v_a_2595_;
v_isShared_2653_ = v_isSharedCheck_2665_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_buildTime_2650_);
lean_inc(v_trace_2649_);
lean_inc(v_log_2645_);
lean_dec(v_a_2595_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2665_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_dir_2613_);
v___x_2655_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v___x_2654_, v_dir_2613_);
if (lean_obj_tag(v___y_2644_) == 0)
{
if (lean_obj_tag(v___x_2655_) == 1)
{
lean_object* v_val_2656_; 
lean_del_object(v___x_2652_);
v_val_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_val_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v___y_2618_ = v_trace_2649_;
v___y_2619_ = v_action_2646_;
v___y_2620_ = v_log_2645_;
v___y_2621_ = v_wantsRebuild_2647_;
v___y_2622_ = v_canceled_2648_;
v___y_2623_ = v_buildTime_2650_;
v_val_2624_ = v_val_2656_;
goto v___jp_2617_;
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
lean_dec(v___x_2655_);
lean_dec_ref(v_buildArchive_2616_);
lean_dec_ref(v_dir_2613_);
v___x_2657_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6));
v___x_2658_ = lean_array_get_size(v_log_2645_);
v___x_2659_ = lean_array_push(v_log_2645_, v___x_2657_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2659_);
v___x_2661_ = v___x_2652_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2659_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_trace_2649_);
lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_buildTime_2650_);
lean_ctor_set_uint8(v_reuseFailAlloc_2663_, sizeof(void*)*3, v_action_2646_);
lean_ctor_set_uint8(v_reuseFailAlloc_2663_, sizeof(void*)*3 + 1, v_wantsRebuild_2647_);
lean_ctor_set_uint8(v_reuseFailAlloc_2663_, sizeof(void*)*3 + 2, v_canceled_2648_);
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
else
{
lean_object* v_val_2664_; 
lean_dec(v___x_2655_);
lean_del_object(v___x_2652_);
v_val_2664_ = lean_ctor_get(v___y_2644_, 0);
lean_inc(v_val_2664_);
lean_dec_ref_known(v___y_2644_, 1);
v___y_2618_ = v_trace_2649_;
v___y_2619_ = v_action_2646_;
v___y_2620_ = v_log_2645_;
v___y_2621_ = v_wantsRebuild_2647_;
v___y_2622_ = v_canceled_2648_;
v___y_2623_ = v_buildTime_2650_;
v_val_2624_ = v_val_2664_;
goto v___jp_2617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(lean_object* v_self_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_2671_, v_a_2672_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object* v_self_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_2675_, v_a_2681_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object* v_self_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(v_self_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_);
lean_dec_ref(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(lean_object* v_val_2693_, lean_object* v_a_x3f_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v_log_2697_; uint8_t v_action_2698_; uint8_t v_wantsRebuild_2699_; uint8_t v_canceled_2700_; lean_object* v_trace_2701_; lean_object* v_buildTime_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2714_; 
v_log_2697_ = lean_ctor_get(v___y_2695_, 0);
v_action_2698_ = lean_ctor_get_uint8(v___y_2695_, sizeof(void*)*3);
v_wantsRebuild_2699_ = lean_ctor_get_uint8(v___y_2695_, sizeof(void*)*3 + 1);
v_canceled_2700_ = lean_ctor_get_uint8(v___y_2695_, sizeof(void*)*3 + 2);
v_trace_2701_ = lean_ctor_get(v___y_2695_, 1);
v_buildTime_2702_ = lean_ctor_get(v___y_2695_, 2);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___y_2695_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2704_ = v___y_2695_;
v_isShared_2705_ = v_isSharedCheck_2714_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_buildTime_2702_);
lean_inc(v_trace_2701_);
lean_inc(v_log_2697_);
lean_dec(v___y_2695_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2714_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2711_; 
v___x_2706_ = lean_io_mono_ms_now();
v___x_2707_ = lean_nat_sub(v___x_2706_, v_val_2693_);
lean_dec(v___x_2706_);
v___x_2708_ = lean_box(0);
v___x_2709_ = lean_nat_add(v_buildTime_2702_, v___x_2707_);
lean_dec(v___x_2707_);
lean_dec(v_buildTime_2702_);
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 2, v___x_2709_);
v___x_2711_ = v___x_2704_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_log_2697_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_trace_2701_);
lean_ctor_set(v_reuseFailAlloc_2713_, 2, v___x_2709_);
lean_ctor_set_uint8(v_reuseFailAlloc_2713_, sizeof(void*)*3, v_action_2698_);
lean_ctor_set_uint8(v_reuseFailAlloc_2713_, sizeof(void*)*3 + 1, v_wantsRebuild_2699_);
lean_ctor_set_uint8(v_reuseFailAlloc_2713_, sizeof(void*)*3 + 2, v_canceled_2700_);
v___x_2711_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
lean_object* v___x_2712_; 
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2708_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
return v___x_2712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0___boxed(lean_object* v_val_2715_, lean_object* v_a_x3f_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v_val_2715_, v_a_x3f_2716_, v___y_2717_);
lean_dec(v_a_x3f_2716_);
lean_dec(v_val_2715_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(lean_object* v_url_2725_, lean_object* v_archiveFile_2726_, lean_object* v_headers_2727_, lean_object* v_depTrace_2728_, lean_object* v_traceFile_2729_, uint8_t v_action_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_){
_start:
{
lean_object* v_a_2735_; lean_object* v_a_2736_; lean_object* v_log_2739_; uint8_t v_action_2740_; uint8_t v_wantsRebuild_2741_; uint8_t v_canceled_2742_; lean_object* v_trace_2743_; lean_object* v_buildTime_2744_; lean_object* v_toBuildConfig_2750_; lean_object* v_log_2751_; uint8_t v_action_2752_; uint8_t v_wantsRebuild_2753_; uint8_t v_canceled_2754_; lean_object* v_trace_2755_; lean_object* v_buildTime_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2857_; 
v_toBuildConfig_2750_ = lean_ctor_get(v_a_2731_, 0);
v_log_2751_ = lean_ctor_get(v_a_2732_, 0);
v_action_2752_ = lean_ctor_get_uint8(v_a_2732_, sizeof(void*)*3);
v_wantsRebuild_2753_ = lean_ctor_get_uint8(v_a_2732_, sizeof(void*)*3 + 1);
v_canceled_2754_ = lean_ctor_get_uint8(v_a_2732_, sizeof(void*)*3 + 2);
v_trace_2755_ = lean_ctor_get(v_a_2732_, 1);
v_buildTime_2756_ = lean_ctor_get(v_a_2732_, 2);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_a_2732_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2758_ = v_a_2732_;
v_isShared_2759_ = v_isSharedCheck_2857_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_buildTime_2756_);
lean_inc(v_trace_2755_);
lean_inc(v_log_2751_);
lean_dec(v_a_2732_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2857_;
goto v_resetjp_2757_;
}
v___jp_2734_:
{
lean_object* v___x_2737_; 
v___x_2737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2737_, 0, v_a_2735_);
lean_ctor_set(v___x_2737_, 1, v_a_2736_);
return v___x_2737_;
}
v___jp_2738_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2745_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1));
v___x_2746_ = lean_array_get_size(v_log_2739_);
v___x_2747_ = lean_array_push(v_log_2739_, v___x_2745_);
v___x_2748_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2748_, 0, v___x_2747_);
lean_ctor_set(v___x_2748_, 1, v_trace_2743_);
lean_ctor_set(v___x_2748_, 2, v_buildTime_2744_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*3, v_action_2740_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*3 + 1, v_wantsRebuild_2741_);
lean_ctor_set_uint8(v___x_2748_, sizeof(void*)*3 + 2, v_canceled_2742_);
v___x_2749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2746_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
return v___x_2749_;
}
v_resetjp_2757_:
{
uint8_t v_noBuild_2760_; uint8_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v_noBuild_2760_ = lean_ctor_get_uint8(v_toBuildConfig_2750_, sizeof(void*)*6 + 2);
v___x_2761_ = l_Lake_JobAction_merge(v_action_2752_, v_action_2730_);
v___x_2762_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2));
lean_inc_ref(v_traceFile_2729_);
v___x_2763_ = l_System_FilePath_addExtension(v_traceFile_2729_, v___x_2762_);
if (v_noBuild_2760_ == 0)
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lake_removeFileIfExists(v_traceFile_2729_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v___x_2765_; lean_object* v_a_2767_; lean_object* v_a_2768_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_dec_ref_known(v___x_2764_, 1);
v___x_2765_ = lean_io_mono_ms_now();
v___x_2772_ = lean_array_get_size(v_log_2751_);
v___x_2773_ = l_Lake_download(v_url_2725_, v_archiveFile_2726_, v_headers_2727_, v_log_2751_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v_a_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
v_a_2775_ = lean_ctor_get(v___x_2773_, 1);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2773_, 2);
v___x_2776_ = lean_array_get_size(v_a_2775_);
v___x_2777_ = l_Array_extract___redArg(v_a_2775_, v___x_2772_, v___x_2776_);
v___x_2778_ = lean_box(0);
v___x_2779_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2728_, v___x_2778_, v___x_2777_);
v___x_2780_ = l_Lake_BuildMetadata_writeFile(v_traceFile_2729_, v___x_2779_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2817_; 
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; 
v_unused_2818_ = lean_ctor_get(v___x_2780_, 0);
lean_dec(v_unused_2818_);
v___x_2782_ = v___x_2780_;
v_isShared_2783_ = v_isSharedCheck_2817_;
goto v_resetjp_2781_;
}
else
{
lean_dec(v___x_2780_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2817_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Lake_removeFileIfExists(v___x_2763_);
lean_dec_ref(v___x_2763_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2807_; 
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; 
v_unused_2808_ = lean_ctor_get(v___x_2784_, 0);
lean_dec(v_unused_2808_);
v___x_2786_ = v___x_2784_;
v_isShared_2787_ = v_isSharedCheck_2807_;
goto v_resetjp_2785_;
}
else
{
lean_dec(v___x_2784_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2807_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v_a_2775_);
v___x_2789_ = v___x_2758_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2775_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_trace_2755_);
lean_ctor_set(v_reuseFailAlloc_2806_, 2, v_buildTime_2756_);
lean_ctor_set_uint8(v_reuseFailAlloc_2806_, sizeof(void*)*3 + 1, v_wantsRebuild_2753_);
lean_ctor_set_uint8(v_reuseFailAlloc_2806_, sizeof(void*)*3 + 2, v_canceled_2754_);
v___x_2789_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2791_; 
lean_ctor_set_uint8(v___x_2789_, sizeof(void*)*3, v___x_2761_);
lean_inc(v_a_2774_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 0, v_a_2774_);
v___x_2791_ = v___x_2786_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2774_);
v___x_2791_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2793_; 
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 1);
lean_ctor_set(v___x_2782_, 0, v___x_2791_);
v___x_2793_ = v___x_2782_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2791_);
v___x_2793_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
v___x_2794_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_2765_, v___x_2793_, v___x_2789_);
lean_dec_ref(v___x_2793_);
lean_dec(v___x_2765_);
v_a_2795_ = lean_ctor_get(v___x_2794_, 1);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; 
v_unused_2803_ = lean_ctor_get(v___x_2794_, 0);
lean_dec(v_unused_2803_);
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v_a_2774_);
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2774_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_a_2795_);
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
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2815_; 
lean_del_object(v___x_2782_);
lean_dec(v_a_2774_);
v_a_2809_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2784_, 1);
v___x_2810_ = lean_io_error_to_string(v_a_2809_);
v___x_2811_ = 3;
v___x_2812_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set_uint8(v___x_2812_, sizeof(void*)*1, v___x_2811_);
v___x_2813_ = lean_array_push(v_a_2775_, v___x_2812_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2813_);
v___x_2815_ = v___x_2758_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_trace_2755_);
lean_ctor_set(v_reuseFailAlloc_2816_, 2, v_buildTime_2756_);
lean_ctor_set_uint8(v_reuseFailAlloc_2816_, sizeof(void*)*3 + 1, v_wantsRebuild_2753_);
lean_ctor_set_uint8(v_reuseFailAlloc_2816_, sizeof(void*)*3 + 2, v_canceled_2754_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_ctor_set_uint8(v___x_2815_, sizeof(void*)*3, v___x_2761_);
v_a_2767_ = v___x_2776_;
v_a_2768_ = v___x_2815_;
goto v___jp_2766_;
}
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2825_; 
lean_dec(v_a_2774_);
lean_dec_ref(v___x_2763_);
v_a_2819_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2820_ = lean_io_error_to_string(v_a_2819_);
v___x_2821_ = 3;
v___x_2822_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2822_, 0, v___x_2820_);
lean_ctor_set_uint8(v___x_2822_, sizeof(void*)*1, v___x_2821_);
v___x_2823_ = lean_array_push(v_a_2775_, v___x_2822_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2823_);
v___x_2825_ = v___x_2758_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_trace_2755_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_buildTime_2756_);
lean_ctor_set_uint8(v_reuseFailAlloc_2826_, sizeof(void*)*3 + 1, v_wantsRebuild_2753_);
lean_ctor_set_uint8(v_reuseFailAlloc_2826_, sizeof(void*)*3 + 2, v_canceled_2754_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_ctor_set_uint8(v___x_2825_, sizeof(void*)*3, v___x_2761_);
v_a_2767_ = v___x_2776_;
v_a_2768_ = v___x_2825_;
goto v___jp_2766_;
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v_a_2828_; lean_object* v___x_2830_; 
lean_dec_ref(v___x_2763_);
lean_dec_ref(v_traceFile_2729_);
v_a_2827_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2827_);
v_a_2828_ = lean_ctor_get(v___x_2773_, 1);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2773_, 2);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v_a_2828_);
v___x_2830_ = v___x_2758_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2828_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_trace_2755_);
lean_ctor_set(v_reuseFailAlloc_2831_, 2, v_buildTime_2756_);
lean_ctor_set_uint8(v_reuseFailAlloc_2831_, sizeof(void*)*3 + 1, v_wantsRebuild_2753_);
lean_ctor_set_uint8(v_reuseFailAlloc_2831_, sizeof(void*)*3 + 2, v_canceled_2754_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_ctor_set_uint8(v___x_2830_, sizeof(void*)*3, v___x_2761_);
v_a_2767_ = v_a_2827_;
v_a_2768_ = v___x_2830_;
goto v___jp_2766_;
}
}
v___jp_2766_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v_a_2771_; 
v___x_2769_ = lean_box(0);
v___x_2770_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_2765_, v___x_2769_, v_a_2768_);
lean_dec(v___x_2765_);
v_a_2771_ = lean_ctor_get(v___x_2770_, 1);
lean_inc(v_a_2771_);
lean_dec_ref(v___x_2770_);
v_a_2735_ = v_a_2767_;
v_a_2736_ = v_a_2771_;
goto v___jp_2734_;
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2839_; 
lean_dec_ref(v___x_2763_);
lean_dec_ref(v_traceFile_2729_);
lean_dec_ref(v_archiveFile_2726_);
lean_dec_ref(v_url_2725_);
v_a_2832_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2764_, 1);
v___x_2833_ = lean_io_error_to_string(v_a_2832_);
v___x_2834_ = 3;
v___x_2835_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set_uint8(v___x_2835_, sizeof(void*)*1, v___x_2834_);
v___x_2836_ = lean_array_get_size(v_log_2751_);
v___x_2837_ = lean_array_push(v_log_2751_, v___x_2835_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2837_);
v___x_2839_ = v___x_2758_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v_trace_2755_);
lean_ctor_set(v_reuseFailAlloc_2841_, 2, v_buildTime_2756_);
lean_ctor_set_uint8(v_reuseFailAlloc_2841_, sizeof(void*)*3 + 1, v_wantsRebuild_2753_);
lean_ctor_set_uint8(v_reuseFailAlloc_2841_, sizeof(void*)*3 + 2, v_canceled_2754_);
v___x_2839_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2840_; 
lean_ctor_set_uint8(v___x_2839_, sizeof(void*)*3, v___x_2761_);
v___x_2840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2836_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
return v___x_2840_;
}
}
}
else
{
uint8_t v___x_2842_; 
lean_dec_ref(v_archiveFile_2726_);
lean_dec_ref(v_url_2725_);
v___x_2842_ = l_System_FilePath_pathExists(v_traceFile_2729_);
lean_dec_ref(v_traceFile_2729_);
if (v___x_2842_ == 0)
{
lean_dec_ref(v___x_2763_);
lean_del_object(v___x_2758_);
v_log_2739_ = v_log_2751_;
v_action_2740_ = v___x_2761_;
v_wantsRebuild_2741_ = v_noBuild_2760_;
v_canceled_2742_ = v_canceled_2754_;
v_trace_2743_ = v_trace_2755_;
v_buildTime_2744_ = v_buildTime_2756_;
goto v___jp_2738_;
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2843_ = lean_box(0);
v___x_2844_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_2845_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_2728_, v___x_2843_, v___x_2844_);
v___x_2846_ = l_Lake_BuildMetadata_writeFile(v___x_2763_, v___x_2845_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_dec_ref_known(v___x_2846_, 1);
lean_del_object(v___x_2758_);
v_log_2739_ = v_log_2751_;
v_action_2740_ = v___x_2761_;
v_wantsRebuild_2741_ = v_noBuild_2760_;
v_canceled_2742_ = v_canceled_2754_;
v_trace_2743_ = v_trace_2755_;
v_buildTime_2744_ = v_buildTime_2756_;
goto v___jp_2738_;
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2848_; uint8_t v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2854_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = lean_io_error_to_string(v_a_2847_);
v___x_2849_ = 3;
v___x_2850_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2850_, 0, v___x_2848_);
lean_ctor_set_uint8(v___x_2850_, sizeof(void*)*1, v___x_2849_);
v___x_2851_ = lean_array_get_size(v_log_2751_);
v___x_2852_ = lean_array_push(v_log_2751_, v___x_2850_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2852_);
v___x_2854_ = v___x_2758_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2852_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_trace_2755_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_buildTime_2756_);
lean_ctor_set_uint8(v_reuseFailAlloc_2856_, sizeof(void*)*3 + 2, v_canceled_2754_);
v___x_2854_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2855_; 
lean_ctor_set_uint8(v___x_2854_, sizeof(void*)*3, v___x_2761_);
lean_ctor_set_uint8(v___x_2854_, sizeof(void*)*3 + 1, v_noBuild_2760_);
v___x_2855_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2851_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
return v___x_2855_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___boxed(lean_object* v_url_2858_, lean_object* v_archiveFile_2859_, lean_object* v_headers_2860_, lean_object* v_depTrace_2861_, lean_object* v_traceFile_2862_, lean_object* v_action_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_){
_start:
{
uint8_t v_action_boxed_2867_; lean_object* v_res_2868_; 
v_action_boxed_2867_ = lean_unbox(v_action_2863_);
v_res_2868_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2858_, v_archiveFile_2859_, v_headers_2860_, v_depTrace_2861_, v_traceFile_2862_, v_action_boxed_2867_, v_a_2864_, v_a_2865_);
lean_dec_ref(v_a_2864_);
lean_dec_ref(v_depTrace_2861_);
lean_dec_ref(v_headers_2860_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(lean_object* v_url_2869_, lean_object* v_archiveFile_2870_, lean_object* v_headers_2871_, lean_object* v_a_2872_, lean_object* v_depTrace_2873_, lean_object* v_traceFile_2874_, uint8_t v_action_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2869_, v_archiveFile_2870_, v_headers_2871_, v_depTrace_2873_, v_traceFile_2874_, v_action_2875_, v_a_2879_, v_a_2880_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___boxed(lean_object* v_url_2883_, lean_object* v_archiveFile_2884_, lean_object* v_headers_2885_, lean_object* v_a_2886_, lean_object* v_depTrace_2887_, lean_object* v_traceFile_2888_, lean_object* v_action_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
uint8_t v_action_boxed_2896_; lean_object* v_res_2897_; 
v_action_boxed_2896_ = lean_unbox(v_action_2889_);
v_res_2897_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(v_url_2883_, v_archiveFile_2884_, v_headers_2885_, v_a_2886_, v_depTrace_2887_, v_traceFile_2888_, v_action_boxed_2896_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec_ref(v_a_2892_);
lean_dec(v_a_2891_);
lean_dec(v_a_2890_);
lean_dec_ref(v_depTrace_2887_);
lean_dec_ref(v_a_2886_);
lean_dec_ref(v_headers_2885_);
return v_res_2897_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object* v_info_2898_, lean_object* v_self_2899_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = lean_io_metadata(v_info_2898_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v_modified_2903_; uint8_t v___x_2904_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
v_modified_2903_ = lean_ctor_get(v_a_2902_, 1);
lean_inc_ref(v_modified_2903_);
lean_dec(v_a_2902_);
v___x_2904_ = l_IO_FS_instOrdSystemTime_ord(v_self_2899_, v_modified_2903_);
lean_dec_ref(v_modified_2903_);
if (v___x_2904_ == 0)
{
uint8_t v___x_2905_; 
v___x_2905_ = 1;
return v___x_2905_;
}
else
{
uint8_t v___x_2906_; 
v___x_2906_ = 0;
return v___x_2906_;
}
}
else
{
uint8_t v___x_2907_; 
lean_dec_ref_known(v___x_2901_, 1);
v___x_2907_ = 0;
return v___x_2907_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object* v_info_2908_, lean_object* v_self_2909_, lean_object* v_a_2910_){
_start:
{
uint8_t v_res_2911_; lean_object* v_r_2912_; 
v_res_2911_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2908_, v_self_2909_);
lean_dec_ref(v_self_2909_);
lean_dec_ref(v_info_2908_);
v_r_2912_ = lean_box(v_res_2911_);
return v_r_2912_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(lean_object* v_x_2913_, lean_object* v_x_2914_){
_start:
{
if (lean_obj_tag(v_x_2913_) == 0)
{
if (lean_obj_tag(v_x_2914_) == 0)
{
uint8_t v___x_2915_; 
v___x_2915_ = 1;
return v___x_2915_;
}
else
{
uint8_t v___x_2916_; 
v___x_2916_ = 0;
return v___x_2916_;
}
}
else
{
if (lean_obj_tag(v_x_2914_) == 0)
{
uint8_t v___x_2917_; 
v___x_2917_ = 0;
return v___x_2917_;
}
else
{
lean_object* v_val_2918_; lean_object* v_val_2919_; uint64_t v___x_2920_; uint64_t v___x_2921_; uint8_t v___x_2922_; 
v_val_2918_ = lean_ctor_get(v_x_2913_, 0);
v_val_2919_ = lean_ctor_get(v_x_2914_, 0);
v___x_2920_ = lean_unbox_uint64(v_val_2918_);
v___x_2921_ = lean_unbox_uint64(v_val_2919_);
v___x_2922_ = lean_uint64_dec_eq(v___x_2920_, v___x_2921_);
return v___x_2922_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2923_, lean_object* v_x_2924_){
_start:
{
uint8_t v_res_2925_; lean_object* v_r_2926_; 
v_res_2925_ = l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v_x_2923_, v_x_2924_);
lean_dec(v_x_2924_);
lean_dec(v_x_2923_);
v_r_2926_ = lean_box(v_res_2925_);
return v_r_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(lean_object* v_info_2927_, lean_object* v_depTrace_2928_, lean_object* v_depHash_2929_, lean_object* v_oldTrace_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
uint64_t v_hash_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; 
v_hash_2934_ = lean_ctor_get_uint64(v_depTrace_2928_, sizeof(void*)*3);
v___x_2935_ = lean_box_uint64(v_hash_2934_);
v___x_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
v___x_2937_ = l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v___x_2936_, v_depHash_2929_);
lean_dec_ref_known(v___x_2936_, 1);
if (v___x_2937_ == 0)
{
lean_object* v_toBuildConfig_2938_; uint8_t v_oldMode_2939_; 
v_toBuildConfig_2938_ = lean_ctor_get(v_a_2931_, 0);
v_oldMode_2939_ = lean_ctor_get_uint8(v_toBuildConfig_2938_, sizeof(void*)*6);
if (v_oldMode_2939_ == 0)
{
uint8_t v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2940_ = 0;
v___x_2941_ = lean_box(v___x_2940_);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v_a_2932_);
return v___x_2942_;
}
else
{
uint8_t v___x_2943_; 
v___x_2943_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2927_, v_oldTrace_2930_);
if (v___x_2943_ == 0)
{
uint8_t v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2944_ = 0;
v___x_2945_ = lean_box(v___x_2944_);
v___x_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
lean_ctor_set(v___x_2946_, 1, v_a_2932_);
return v___x_2946_;
}
else
{
uint8_t v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = 1;
v___x_2948_ = lean_box(v___x_2947_);
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2948_);
lean_ctor_set(v___x_2949_, 1, v_a_2932_);
return v___x_2949_;
}
}
}
else
{
uint8_t v___x_2950_; 
v___x_2950_ = l_System_FilePath_pathExists(v_info_2927_);
if (v___x_2950_ == 0)
{
uint8_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = 0;
v___x_2952_ = lean_box(v___x_2951_);
v___x_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2952_);
lean_ctor_set(v___x_2953_, 1, v_a_2932_);
return v___x_2953_;
}
else
{
uint8_t v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2954_ = 2;
v___x_2955_ = lean_box(v___x_2954_);
v___x_2956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2955_);
lean_ctor_set(v___x_2956_, 1, v_a_2932_);
return v___x_2956_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(lean_object* v_info_2957_, lean_object* v_depTrace_2958_, lean_object* v_depHash_2959_, lean_object* v_oldTrace_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2957_, v_depTrace_2958_, v_depHash_2959_, v_oldTrace_2960_, v_a_2961_, v_a_2962_);
lean_dec_ref(v_a_2961_);
lean_dec_ref(v_oldTrace_2960_);
lean_dec(v_depHash_2959_);
lean_dec_ref(v_depTrace_2958_);
lean_dec_ref(v_info_2957_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(lean_object* v_a_2965_, lean_object* v_info_2966_, lean_object* v_depTrace_2967_, lean_object* v_savedTrace_2968_, lean_object* v_oldTrace_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
if (lean_obj_tag(v_savedTrace_2968_) == 2)
{
lean_object* v_data_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3027_; 
v_data_2976_ = lean_ctor_get(v_savedTrace_2968_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v_savedTrace_2968_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_2978_ = v_savedTrace_2968_;
v_isShared_2979_ = v_isSharedCheck_3027_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_data_2976_);
lean_dec(v_savedTrace_2968_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3027_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
uint64_t v_depHash_2980_; lean_object* v_log_2981_; lean_object* v___x_2982_; lean_object* v___x_2984_; 
v_depHash_2980_ = lean_ctor_get_uint64(v_data_2976_, sizeof(void*)*3);
v_log_2981_ = lean_ctor_get(v_data_2976_, 2);
lean_inc_ref(v_log_2981_);
lean_dec_ref(v_data_2976_);
v___x_2982_ = lean_box_uint64(v_depHash_2980_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set_tag(v___x_2978_, 1);
lean_ctor_set(v___x_2978_, 0, v___x_2982_);
v___x_2984_ = v___x_2978_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_2982_);
v___x_2984_ = v_reuseFailAlloc_3026_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v___x_2985_; lean_object* v_a_2986_; lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3025_; 
v___x_2985_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2966_, v_depTrace_2967_, v___x_2984_, v_oldTrace_2969_, v_a_2973_, v_a_2974_);
lean_dec_ref(v___x_2984_);
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
v_a_2987_ = lean_ctor_get(v___x_2985_, 1);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_2989_ = v___x_2985_;
v_isShared_2990_ = v_isSharedCheck_3025_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_inc(v_a_2986_);
lean_dec(v___x_2985_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3025_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___y_2992_; lean_object* v___x_2996_; lean_object* v___x_2997_; uint8_t v___x_2998_; 
v___x_2996_ = lean_obj_tag_nat(v_a_2986_);
v___x_2997_ = lean_unsigned_to_nat(0u);
v___x_2998_ = lean_nat_dec_eq(v___x_2996_, v___x_2997_);
if (v___x_2998_ == 0)
{
lean_object* v_log_2999_; uint8_t v_action_3000_; uint8_t v_wantsRebuild_3001_; uint8_t v_canceled_3002_; lean_object* v_trace_3003_; lean_object* v_buildTime_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3024_; 
v_log_2999_ = lean_ctor_get(v_a_2987_, 0);
v_action_3000_ = lean_ctor_get_uint8(v_a_2987_, sizeof(void*)*3);
v_wantsRebuild_3001_ = lean_ctor_get_uint8(v_a_2987_, sizeof(void*)*3 + 1);
v_canceled_3002_ = lean_ctor_get_uint8(v_a_2987_, sizeof(void*)*3 + 2);
v_trace_3003_ = lean_ctor_get(v_a_2987_, 1);
v_buildTime_3004_ = lean_ctor_get(v_a_2987_, 2);
v_isSharedCheck_3024_ = !lean_is_exclusive(v_a_2987_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3006_ = v_a_2987_;
v_isShared_3007_ = v_isSharedCheck_3024_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_buildTime_3004_);
lean_inc(v_trace_3003_);
lean_inc(v_log_2999_);
lean_dec(v_a_2987_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3024_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
uint8_t v___x_3008_; uint8_t v___x_3009_; lean_object* v___x_3011_; 
v___x_3008_ = 2;
v___x_3009_ = l_Lake_JobAction_merge(v_action_3000_, v___x_3008_);
if (v_isShared_3007_ == 0)
{
v___x_3011_ = v___x_3006_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_log_2999_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v_trace_3003_);
lean_ctor_set(v_reuseFailAlloc_3023_, 2, v_buildTime_3004_);
lean_ctor_set_uint8(v_reuseFailAlloc_3023_, sizeof(void*)*3 + 1, v_wantsRebuild_3001_);
lean_ctor_set_uint8(v_reuseFailAlloc_3023_, sizeof(void*)*3 + 2, v_canceled_3002_);
v___x_3011_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3012_; 
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*3, v___x_3009_);
v___x_3012_ = l___private_Lake_Build_Common_0__Lake_SavedTrace_replayIfUpToDate_x27_replay(v_log_2981_, v_a_2965_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v___x_3011_);
lean_dec_ref(v_log_2981_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 1);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 2);
v___y_2992_ = v_a_3013_;
goto v___jp_2991_;
}
else
{
lean_object* v_a_3014_; lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_del_object(v___x_2989_);
lean_dec(v_a_2986_);
v_a_3014_ = lean_ctor_get(v___x_3012_, 0);
v_a_3015_ = lean_ctor_get(v___x_3012_, 1);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3012_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_inc(v_a_3014_);
lean_dec(v___x_3012_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3014_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_log_2981_);
v___y_2992_ = v_a_2987_;
goto v___jp_2991_;
}
v___jp_2991_:
{
lean_object* v___x_2994_; 
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 1, v___y_2992_);
v___x_2994_ = v___x_2989_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2986_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v___y_2992_);
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
}
else
{
lean_object* v_toBuildConfig_3028_; uint8_t v_oldMode_3029_; 
lean_dec(v_savedTrace_2968_);
v_toBuildConfig_3028_ = lean_ctor_get(v_a_2973_, 0);
v_oldMode_3029_ = lean_ctor_get_uint8(v_toBuildConfig_3028_, sizeof(void*)*6);
if (v_oldMode_3029_ == 0)
{
uint8_t v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = 0;
v___x_3031_ = lean_box(v___x_3030_);
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
lean_ctor_set(v___x_3032_, 1, v_a_2974_);
return v___x_3032_;
}
else
{
uint8_t v___x_3033_; 
v___x_3033_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2966_, v_oldTrace_2969_);
if (v___x_3033_ == 0)
{
uint8_t v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = 0;
v___x_3035_ = lean_box(v___x_3034_);
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
lean_ctor_set(v___x_3036_, 1, v_a_2974_);
return v___x_3036_;
}
else
{
uint8_t v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3037_ = 1;
v___x_3038_ = lean_box(v___x_3037_);
v___x_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v_a_2974_);
return v___x_3039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0___boxed(lean_object* v_a_3040_, lean_object* v_info_3041_, lean_object* v_depTrace_3042_, lean_object* v_savedTrace_3043_, lean_object* v_oldTrace_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_3040_, v_info_3041_, v_depTrace_3042_, v_savedTrace_3043_, v_oldTrace_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
lean_dec_ref(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec_ref(v_oldTrace_3044_);
lean_dec_ref(v_depTrace_3042_);
lean_dec_ref(v_info_3041_);
lean_dec_ref(v_a_3040_);
return v_res_3051_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = lean_unsigned_to_nat(0u);
v___x_3057_ = lean_nat_to_int(v___x_3056_);
return v___x_3057_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4(void){
_start:
{
uint32_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = 0;
v___x_3059_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__3);
v___x_3060_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
lean_ctor_set_uint32(v___x_3060_, sizeof(void*)*1, v___x_3058_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(lean_object* v_self_3061_, lean_object* v_url_3062_, lean_object* v_archiveFile_3063_, lean_object* v_headers_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; uint8_t v___y_3077_; uint8_t v___y_3078_; uint8_t v___y_3079_; uint8_t v_a_3105_; lean_object* v_a_3106_; lean_object* v_a_3122_; lean_object* v_a_3123_; lean_object* v_log_3125_; uint8_t v_action_3126_; uint8_t v_wantsRebuild_3127_; uint8_t v_canceled_3128_; lean_object* v_trace_3129_; lean_object* v_buildTime_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3169_; 
v_log_3125_ = lean_ctor_get(v_a_3070_, 0);
v_action_3126_ = lean_ctor_get_uint8(v_a_3070_, sizeof(void*)*3);
v_wantsRebuild_3127_ = lean_ctor_get_uint8(v_a_3070_, sizeof(void*)*3 + 1);
v_canceled_3128_ = lean_ctor_get_uint8(v_a_3070_, sizeof(void*)*3 + 2);
v_trace_3129_ = lean_ctor_get(v_a_3070_, 1);
v_buildTime_3130_ = lean_ctor_get(v_a_3070_, 2);
v_isSharedCheck_3169_ = !lean_is_exclusive(v_a_3070_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3132_ = v_a_3070_;
v_isShared_3133_ = v_isSharedCheck_3169_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_buildTime_3130_);
lean_inc(v_trace_3129_);
lean_inc(v_log_3125_);
lean_dec(v_a_3070_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3169_;
goto v_resetjp_3131_;
}
v___jp_3072_:
{
uint8_t v___x_3080_; uint8_t v___x_3081_; uint8_t v___x_3082_; lean_object* v___x_3083_; 
v___x_3080_ = 1;
v___x_3081_ = 3;
v___x_3082_ = l_Lake_JobAction_merge(v___y_3077_, v___x_3081_);
v___x_3083_ = l_Lake_untar(v_archiveFile_3063_, v___y_3074_, v___x_3080_, v___y_3075_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3093_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_a_3085_ = lean_ctor_get(v___x_3083_, 1);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3087_ = v___x_3083_;
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3089_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3089_, 0, v_a_3085_);
lean_ctor_set(v___x_3089_, 1, v___y_3076_);
lean_ctor_set(v___x_3089_, 2, v___y_3073_);
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*3, v___x_3082_);
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*3 + 1, v___y_3079_);
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*3 + 2, v___y_3078_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 1, v___x_3089_);
v___x_3091_ = v___x_3087_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3084_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3089_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3103_; 
v_a_3094_ = lean_ctor_get(v___x_3083_, 0);
v_a_3095_ = lean_ctor_get(v___x_3083_, 1);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3097_ = v___x_3083_;
v_isShared_3098_ = v_isSharedCheck_3103_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_inc(v_a_3094_);
lean_dec(v___x_3083_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3103_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3099_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3099_, 0, v_a_3095_);
lean_ctor_set(v___x_3099_, 1, v___y_3076_);
lean_ctor_set(v___x_3099_, 2, v___y_3073_);
lean_ctor_set_uint8(v___x_3099_, sizeof(void*)*3, v___x_3082_);
lean_ctor_set_uint8(v___x_3099_, sizeof(void*)*3 + 1, v___y_3079_);
lean_ctor_set_uint8(v___x_3099_, sizeof(void*)*3 + 2, v___y_3078_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___x_3099_);
v___x_3101_ = v___x_3097_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3094_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
v___jp_3104_:
{
lean_object* v_config_3107_; lean_object* v_dir_3108_; lean_object* v_buildDir_3109_; lean_object* v_log_3110_; uint8_t v_action_3111_; uint8_t v_wantsRebuild_3112_; uint8_t v_canceled_3113_; lean_object* v_trace_3114_; lean_object* v_buildTime_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v_config_3107_ = lean_ctor_get(v_self_3061_, 6);
lean_inc_ref(v_config_3107_);
v_dir_3108_ = lean_ctor_get(v_self_3061_, 4);
lean_inc_ref(v_dir_3108_);
lean_dec_ref(v_self_3061_);
v_buildDir_3109_ = lean_ctor_get(v_config_3107_, 5);
lean_inc_ref(v_buildDir_3109_);
lean_dec_ref(v_config_3107_);
v_log_3110_ = lean_ctor_get(v_a_3106_, 0);
v_action_3111_ = lean_ctor_get_uint8(v_a_3106_, sizeof(void*)*3);
v_wantsRebuild_3112_ = lean_ctor_get_uint8(v_a_3106_, sizeof(void*)*3 + 1);
v_canceled_3113_ = lean_ctor_get_uint8(v_a_3106_, sizeof(void*)*3 + 2);
v_trace_3114_ = lean_ctor_get(v_a_3106_, 1);
v_buildTime_3115_ = lean_ctor_get(v_a_3106_, 2);
v___x_3116_ = l_System_FilePath_normalize(v_buildDir_3109_);
v___x_3117_ = l_Lake_joinRelative(v_dir_3108_, v___x_3116_);
v___x_3118_ = l_System_FilePath_pathExists(v___x_3117_);
if (v_a_3105_ == 0)
{
lean_inc(v_buildTime_3115_);
lean_inc_ref(v_trace_3114_);
lean_inc_ref(v_log_3110_);
lean_dec_ref(v_a_3106_);
v___y_3073_ = v_buildTime_3115_;
v___y_3074_ = v___x_3117_;
v___y_3075_ = v_log_3110_;
v___y_3076_ = v_trace_3114_;
v___y_3077_ = v_action_3111_;
v___y_3078_ = v_canceled_3113_;
v___y_3079_ = v_wantsRebuild_3112_;
goto v___jp_3072_;
}
else
{
if (v___x_3118_ == 0)
{
lean_inc(v_buildTime_3115_);
lean_inc_ref(v_trace_3114_);
lean_inc_ref(v_log_3110_);
lean_dec_ref(v_a_3106_);
v___y_3073_ = v_buildTime_3115_;
v___y_3074_ = v___x_3117_;
v___y_3075_ = v_log_3110_;
v___y_3076_ = v_trace_3114_;
v___y_3077_ = v_action_3111_;
v___y_3078_ = v_canceled_3113_;
v___y_3079_ = v_wantsRebuild_3112_;
goto v___jp_3072_;
}
else
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_dec_ref(v___x_3117_);
lean_dec_ref(v_archiveFile_3063_);
v___x_3119_ = lean_box(0);
v___x_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
lean_ctor_set(v___x_3120_, 1, v_a_3106_);
return v___x_3120_;
}
}
}
v___jp_3121_:
{
lean_object* v___x_3124_; 
v___x_3124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3124_, 0, v_a_3122_);
lean_ctor_set(v___x_3124_, 1, v_a_3123_);
return v___x_3124_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; uint64_t v___x_3136_; uint64_t v___x_3137_; uint64_t v_depTrace_3138_; lean_object* v___x_3139_; lean_object* v_traceFile_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; lean_object* v___x_3145_; 
v___x_3134_ = lean_unsigned_to_nat(0u);
v___x_3135_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0));
v___x_3136_ = l_Lake_Hash_nil;
v___x_3137_ = lean_string_hash(v_url_3062_);
v_depTrace_3138_ = lean_uint64_mix_hash(v___x_3136_, v___x_3137_);
v___x_3139_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1));
lean_inc_ref(v_archiveFile_3063_);
v_traceFile_3140_ = l_System_FilePath_addExtension(v_archiveFile_3063_, v___x_3139_);
v___x_3141_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2));
v___x_3142_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
v___x_3143_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_3143_, 0, v___x_3141_);
lean_ctor_set(v___x_3143_, 1, v___x_3135_);
lean_ctor_set(v___x_3143_, 2, v___x_3142_);
lean_ctor_set_uint64(v___x_3143_, sizeof(void*)*3, v_depTrace_3138_);
v___x_3144_ = 4;
lean_inc_ref(v_traceFile_3140_);
v___x_3145_ = l_Lake_readTraceFile(v_traceFile_3140_, v_log_3125_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v_a_3147_; lean_object* v___x_3149_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3146_);
v_a_3147_ = lean_ctor_get(v___x_3145_, 1);
lean_inc(v_a_3147_);
lean_dec_ref_known(v___x_3145_, 2);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v_a_3147_);
v___x_3149_ = v___x_3132_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3147_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_trace_3129_);
lean_ctor_set(v_reuseFailAlloc_3163_, 2, v_buildTime_3130_);
lean_ctor_set_uint8(v_reuseFailAlloc_3163_, sizeof(void*)*3, v_action_3126_);
lean_ctor_set_uint8(v_reuseFailAlloc_3163_, sizeof(void*)*3 + 1, v_wantsRebuild_3127_);
lean_ctor_set_uint8(v_reuseFailAlloc_3163_, sizeof(void*)*3 + 2, v_canceled_3128_);
v___x_3149_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_3065_, v_archiveFile_3063_, v___x_3143_, v_a_3146_, v___x_3142_, v_a_3066_, v_a_3067_, v_a_3068_, v_a_3069_, v___x_3149_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v_a_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3151_);
v_a_3152_ = lean_ctor_get(v___x_3150_, 1);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3150_, 2);
v___x_3153_ = lean_obj_tag_nat(v_a_3151_);
lean_dec(v_a_3151_);
v___x_3154_ = lean_nat_dec_eq(v___x_3153_, v___x_3134_);
if (v___x_3154_ == 0)
{
uint8_t v___x_3155_; 
lean_dec_ref_known(v___x_3143_, 3);
lean_dec_ref(v_traceFile_3140_);
lean_dec_ref(v_url_3062_);
v___x_3155_ = 1;
v_a_3105_ = v___x_3155_;
v_a_3106_ = v_a_3152_;
goto v___jp_3104_;
}
else
{
uint8_t v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = 0;
lean_inc_ref(v_archiveFile_3063_);
v___x_3157_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_3062_, v_archiveFile_3063_, v_headers_3064_, v___x_3143_, v_traceFile_3140_, v___x_3144_, v_a_3069_, v_a_3152_);
lean_dec_ref_known(v___x_3143_, 3);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 1);
lean_inc(v_a_3158_);
lean_dec_ref_known(v___x_3157_, 2);
v_a_3105_ = v___x_3156_;
v_a_3106_ = v_a_3158_;
goto v___jp_3104_;
}
else
{
lean_object* v_a_3159_; lean_object* v_a_3160_; 
lean_dec_ref(v_archiveFile_3063_);
lean_dec_ref(v_self_3061_);
v_a_3159_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3159_);
v_a_3160_ = lean_ctor_get(v___x_3157_, 1);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3157_, 2);
v_a_3122_ = v_a_3159_;
v_a_3123_ = v_a_3160_;
goto v___jp_3121_;
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v_a_3162_; 
lean_dec_ref_known(v___x_3143_, 3);
lean_dec_ref(v_traceFile_3140_);
lean_dec_ref(v_archiveFile_3063_);
lean_dec_ref(v_url_3062_);
lean_dec_ref(v_self_3061_);
v_a_3161_ = lean_ctor_get(v___x_3150_, 0);
lean_inc(v_a_3161_);
v_a_3162_ = lean_ctor_get(v___x_3150_, 1);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3150_, 2);
v_a_3122_ = v_a_3161_;
v_a_3123_ = v_a_3162_;
goto v___jp_3121_;
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v_a_3165_; lean_object* v___x_3167_; 
lean_dec_ref_known(v___x_3143_, 3);
lean_dec_ref(v_traceFile_3140_);
lean_dec_ref(v_archiveFile_3063_);
lean_dec_ref(v_url_3062_);
lean_dec_ref(v_self_3061_);
v_a_3164_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3164_);
v_a_3165_ = lean_ctor_get(v___x_3145_, 1);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3145_, 2);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v_a_3165_);
v___x_3167_ = v___x_3132_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3165_);
lean_ctor_set(v_reuseFailAlloc_3168_, 1, v_trace_3129_);
lean_ctor_set(v_reuseFailAlloc_3168_, 2, v_buildTime_3130_);
lean_ctor_set_uint8(v_reuseFailAlloc_3168_, sizeof(void*)*3, v_action_3126_);
lean_ctor_set_uint8(v_reuseFailAlloc_3168_, sizeof(void*)*3 + 1, v_wantsRebuild_3127_);
lean_ctor_set_uint8(v_reuseFailAlloc_3168_, sizeof(void*)*3 + 2, v_canceled_3128_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
v_a_3122_ = v_a_3164_;
v_a_3123_ = v___x_3167_;
goto v___jp_3121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object* v_self_3170_, lean_object* v_url_3171_, lean_object* v_archiveFile_3172_, lean_object* v_headers_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_){
_start:
{
lean_object* v_res_3181_; 
v_res_3181_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_self_3170_, v_url_3171_, v_archiveFile_3172_, v_headers_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_);
lean_dec_ref(v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_a_3176_);
lean_dec(v_a_3175_);
lean_dec_ref(v_a_3174_);
lean_dec_ref(v_headers_3173_);
return v_res_3181_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object* v_a_3182_, lean_object* v_info_3183_, lean_object* v_depTrace_3184_, lean_object* v_depHash_3185_, lean_object* v_oldTrace_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v___x_3193_; 
v___x_3193_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_3183_, v_depTrace_3184_, v_depHash_3185_, v_oldTrace_3186_, v_a_3190_, v_a_3191_);
return v___x_3193_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object* v_a_3194_, lean_object* v_info_3195_, lean_object* v_depTrace_3196_, lean_object* v_depHash_3197_, lean_object* v_oldTrace_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_3194_, v_info_3195_, v_depTrace_3196_, v_depHash_3197_, v_oldTrace_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_);
lean_dec_ref(v_a_3202_);
lean_dec_ref(v_a_3201_);
lean_dec(v_a_3200_);
lean_dec(v_a_3199_);
lean_dec_ref(v_oldTrace_3198_);
lean_dec(v_depHash_3197_);
lean_dec_ref(v_depTrace_3196_);
lean_dec_ref(v_info_3195_);
lean_dec_ref(v_a_3194_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_getUrl_3206_, lean_object* v_pkg_3207_, lean_object* v_archiveFile_3208_, lean_object* v_headers_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
uint8_t v_r_3218_; lean_object* v___y_3219_; lean_object* v_a_3223_; lean_object* v___x_3240_; 
lean_inc_ref(v___y_3214_);
lean_inc_ref(v___y_3213_);
lean_inc(v___y_3212_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc_ref(v_pkg_3207_);
v___x_3240_ = lean_apply_8(v_getUrl_3206_, v_pkg_3207_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, lean_box(0));
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v_a_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_a_3241_);
v_a_3242_ = lean_ctor_get(v___x_3240_, 1);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___x_3240_, 2);
lean_inc_ref(v_pkg_3207_);
v___x_3243_ = lean_apply_1(v_archiveFile_3208_, v_pkg_3207_);
v___x_3244_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_3207_, v_a_3241_, v___x_3243_, v_headers_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v_a_3242_);
lean_dec_ref(v___y_3210_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; uint8_t v___x_3246_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 1);
lean_inc(v_a_3245_);
lean_dec_ref_known(v___x_3244_, 2);
v___x_3246_ = 1;
v_r_3218_ = v___x_3246_;
v___y_3219_ = v_a_3245_;
goto v___jp_3217_;
}
else
{
lean_object* v_a_3247_; 
v_a_3247_ = lean_ctor_get(v___x_3244_, 1);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3244_, 2);
v_a_3223_ = v_a_3247_;
goto v___jp_3222_;
}
}
else
{
lean_object* v_a_3248_; 
lean_dec_ref(v___y_3210_);
lean_dec_ref(v_archiveFile_3208_);
lean_dec_ref(v_pkg_3207_);
v_a_3248_ = lean_ctor_get(v___x_3240_, 1);
lean_inc(v_a_3248_);
lean_dec_ref_known(v___x_3240_, 2);
v_a_3223_ = v_a_3248_;
goto v___jp_3222_;
}
v___jp_3217_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = lean_box(v_r_3218_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3220_);
lean_ctor_set(v___x_3221_, 1, v___y_3219_);
return v___x_3221_;
}
v___jp_3222_:
{
lean_object* v_log_3224_; uint8_t v_action_3225_; uint8_t v_wantsRebuild_3226_; uint8_t v_canceled_3227_; lean_object* v_trace_3228_; lean_object* v_buildTime_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3239_; 
v_log_3224_ = lean_ctor_get(v_a_3223_, 0);
v_action_3225_ = lean_ctor_get_uint8(v_a_3223_, sizeof(void*)*3);
v_wantsRebuild_3226_ = lean_ctor_get_uint8(v_a_3223_, sizeof(void*)*3 + 1);
v_canceled_3227_ = lean_ctor_get_uint8(v_a_3223_, sizeof(void*)*3 + 2);
v_trace_3228_ = lean_ctor_get(v_a_3223_, 1);
v_buildTime_3229_ = lean_ctor_get(v_a_3223_, 2);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_a_3223_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3231_ = v_a_3223_;
v_isShared_3232_ = v_isSharedCheck_3239_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_buildTime_3229_);
lean_inc(v_trace_3228_);
lean_inc(v_log_3224_);
lean_dec(v_a_3223_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3239_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
uint8_t v___x_3233_; uint8_t v___x_3234_; lean_object* v___x_3236_; 
v___x_3233_ = 4;
v___x_3234_ = l_Lake_JobAction_merge(v_action_3225_, v___x_3233_);
if (v_isShared_3232_ == 0)
{
v___x_3236_ = v___x_3231_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_log_3224_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_trace_3228_);
lean_ctor_set(v_reuseFailAlloc_3238_, 2, v_buildTime_3229_);
lean_ctor_set_uint8(v_reuseFailAlloc_3238_, sizeof(void*)*3 + 1, v_wantsRebuild_3226_);
lean_ctor_set_uint8(v_reuseFailAlloc_3238_, sizeof(void*)*3 + 2, v_canceled_3227_);
v___x_3236_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
uint8_t v___x_3237_; 
lean_ctor_set_uint8(v___x_3236_, sizeof(void*)*3, v___x_3234_);
v___x_3237_ = 0;
v_r_3218_ = v___x_3237_;
v___y_3219_ = v___x_3236_;
goto v___jp_3217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_getUrl_3249_, lean_object* v_pkg_3250_, lean_object* v_archiveFile_3251_, lean_object* v_headers_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg___lam__0(v_getUrl_3249_, v_pkg_3250_, v_archiveFile_3251_, v_headers_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v_headers_3252_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* v_getUrl_3261_, lean_object* v_archiveFile_3262_, lean_object* v_headers_3263_, lean_object* v_facet_3264_, lean_object* v___x_3265_, lean_object* v_pkg_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v_baseName_3274_; lean_object* v___f_3275_; uint8_t v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v_baseName_3274_ = lean_ctor_get(v_pkg_3266_, 1);
lean_inc(v_baseName_3274_);
v___f_3275_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3275_, 0, v_getUrl_3261_);
lean_closure_set(v___f_3275_, 1, v_pkg_3266_);
lean_closure_set(v___f_3275_, 2, v_archiveFile_3262_);
lean_closure_set(v___f_3275_, 3, v_headers_3263_);
v___x_3276_ = 1;
v___x_3277_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3274_, v___x_3276_);
v___x_3278_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3279_ = lean_string_append(v___x_3277_, v___x_3278_);
v___x_3280_ = l_Lake_Name_eraseHead(v_facet_3264_);
v___x_3281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3280_, v___x_3276_);
v___x_3282_ = lean_string_append(v___x_3279_, v___x_3281_);
lean_dec_ref(v___x_3281_);
v___x_3283_ = lean_unsigned_to_nat(0u);
v___x_3284_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_3265_);
v___x_3285_ = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(v___x_3285_, 0, lean_box(0));
lean_closure_set(v___x_3285_, 1, v___x_3265_);
lean_closure_set(v___x_3285_, 2, v___f_3275_);
lean_closure_set(v___x_3285_, 3, v___x_3283_);
lean_closure_set(v___x_3285_, 4, v___x_3284_);
v___x_3286_ = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM___boxed), 9, 2);
lean_closure_set(v___x_3286_, 0, lean_box(0));
lean_closure_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM___boxed), 9, 2);
lean_closure_set(v___x_3287_, 0, lean_box(0));
lean_closure_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = l_Lake_ensureJob___redArg(v___x_3265_, v___x_3287_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3313_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
v_a_3290_ = lean_ctor_get(v___x_3288_, 1);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3288_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3292_ = v___x_3288_;
v_isShared_3293_ = v_isSharedCheck_3313_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_inc(v_a_3289_);
lean_dec(v___x_3288_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3313_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v_task_3294_; lean_object* v_kind_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3311_; 
v_task_3294_ = lean_ctor_get(v_a_3289_, 0);
v_kind_3295_ = lean_ctor_get(v_a_3289_, 1);
v_isSharedCheck_3311_ = !lean_is_exclusive(v_a_3289_);
if (v_isSharedCheck_3311_ == 0)
{
lean_object* v_unused_3312_; 
v_unused_3312_ = lean_ctor_get(v_a_3289_, 2);
lean_dec(v_unused_3312_);
v___x_3297_ = v_a_3289_;
v_isShared_3298_ = v_isSharedCheck_3311_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_kind_3295_);
lean_inc(v_task_3294_);
lean_dec(v_a_3289_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3311_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v_registeredJobs_3299_; lean_object* v_job_3301_; 
v_registeredJobs_3299_ = lean_ctor_get(v___y_3271_, 4);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 2, v___x_3282_);
v_job_3301_ = v___x_3297_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_task_3294_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_kind_3295_);
lean_ctor_set(v_reuseFailAlloc_3310_, 2, v___x_3282_);
v_job_3301_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
lean_ctor_set_uint8(v_job_3301_, sizeof(void*)*3, v___x_3276_);
v___x_3302_ = lean_st_ref_take(v_registeredJobs_3299_);
lean_inc_ref(v_job_3301_);
v___x_3303_ = l_Lake_Job_toOpaque___redArg(v_job_3301_);
v___x_3304_ = lean_array_push(v___x_3302_, v___x_3303_);
v___x_3305_ = lean_st_ref_put(v_registeredJobs_3299_, v___x_3304_);
v___x_3306_ = l_Lake_Job_renew___redArg(v_job_3301_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3306_);
v___x_3308_ = v___x_3292_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
lean_ctor_set(v_reuseFailAlloc_3309_, 1, v_a_3290_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3282_);
return v___x_3288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v_getUrl_3314_, lean_object* v_archiveFile_3315_, lean_object* v_headers_3316_, lean_object* v_facet_3317_, lean_object* v___x_3318_, lean_object* v_pkg_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_3314_, v_archiveFile_3315_, v_headers_3316_, v_facet_3317_, v___x_3318_, v_pkg_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___y_3322_);
lean_dec(v___y_3321_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg(lean_object* v_facet_3328_, lean_object* v_archiveFile_3329_, lean_object* v_getUrl_3330_, lean_object* v_headers_3331_){
_start:
{
lean_object* v___x_3332_; lean_object* v___f_3333_; lean_object* v___x_3334_; uint8_t v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3332_ = l_Lake_instDataKindBool;
v___f_3333_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_3333_, 0, v_getUrl_3330_);
lean_closure_set(v___f_3333_, 1, v_archiveFile_3329_);
lean_closure_set(v___f_3333_, 2, v_headers_3331_);
lean_closure_set(v___f_3333_, 3, v_facet_3328_);
lean_closure_set(v___f_3333_, 4, v___x_3332_);
v___x_3334_ = l_Lake_Package_keyword;
v___x_3335_ = 1;
v___x_3336_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__3));
v___x_3337_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3337_, 0, v___x_3334_);
lean_ctor_set(v___x_3337_, 1, v___f_3333_);
lean_ctor_set(v___x_3337_, 2, v___x_3332_);
lean_ctor_set(v___x_3337_, 3, v___x_3336_);
lean_ctor_set_uint8(v___x_3337_, sizeof(void*)*4, v___x_3335_);
lean_ctor_set_uint8(v___x_3337_, sizeof(void*)*4 + 1, v___x_3335_);
return v___x_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig(lean_object* v_facet_3338_, lean_object* v_archiveFile_3339_, lean_object* v_getUrl_3340_, lean_object* v_headers_3341_, lean_object* v_inst_3342_){
_start:
{
lean_object* v___x_3343_; lean_object* v___f_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3343_ = l_Lake_instDataKindBool;
v___f_3344_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_3344_, 0, v_getUrl_3340_);
lean_closure_set(v___f_3344_, 1, v_archiveFile_3339_);
lean_closure_set(v___f_3344_, 2, v_headers_3341_);
lean_closure_set(v___f_3344_, 3, v_facet_3338_);
lean_closure_set(v___f_3344_, 4, v___x_3343_);
v___x_3345_ = l_Lake_Package_keyword;
v___x_3346_ = 1;
v___x_3347_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_mkOptBuildCacheFacetConfig___redArg___closed__3));
v___x_3348_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3348_, 0, v___x_3345_);
lean_ctor_set(v___x_3348_, 1, v___f_3344_);
lean_ctor_set(v___x_3348_, 2, v___x_3343_);
lean_ctor_set(v___x_3348_, 3, v___x_3347_);
lean_ctor_set_uint8(v___x_3348_, sizeof(void*)*4, v___x_3346_);
lean_ctor_set_uint8(v___x_3348_, sizeof(void*)*4 + 1, v___x_3346_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__0(lean_object* v_what_3350_, lean_object* v_baseName_3351_, lean_object* v_optFacet_3352_, uint8_t v_success_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_a_3362_; lean_object* v_a_3363_; 
if (v_success_3353_ == 0)
{
lean_object* v_toBuildConfig_3385_; uint8_t v_verbosity_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; 
v_toBuildConfig_3385_ = lean_ctor_get(v___y_3358_, 0);
v_verbosity_3386_ = lean_ctor_get_uint8(v_toBuildConfig_3385_, sizeof(void*)*6 + 4);
v___x_3387_ = lean_box(v_verbosity_3386_);
v___x_3388_ = lean_obj_tag_nat(v___x_3387_);
lean_dec(v___x_3387_);
v___x_3389_ = lean_unsigned_to_nat(2u);
v___x_3390_ = lean_nat_dec_eq(v___x_3388_, v___x_3389_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; 
lean_dec(v_optFacet_3352_);
lean_dec(v_baseName_3351_);
v___x_3391_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_3362_ = v___x_3391_;
v_a_3363_ = v___y_3359_;
goto v___jp_3361_;
}
else
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3392_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_3393_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3351_, v___x_3390_);
v___x_3394_ = lean_string_append(v___x_3392_, v___x_3393_);
lean_dec_ref(v___x_3393_);
v___x_3395_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3396_ = lean_string_append(v___x_3394_, v___x_3395_);
v___x_3397_ = l_Lake_Name_eraseHead(v_optFacet_3352_);
v___x_3398_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3397_, v___x_3390_);
v___x_3399_ = lean_string_append(v___x_3396_, v___x_3398_);
lean_dec_ref(v___x_3398_);
v___x_3400_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3401_ = lean_string_append(v___x_3399_, v___x_3400_);
v_a_3362_ = v___x_3401_;
v_a_3363_ = v___y_3359_;
goto v___jp_3361_;
}
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec(v_optFacet_3352_);
lean_dec(v_baseName_3351_);
v___x_3402_ = lean_box(0);
v___x_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3402_);
lean_ctor_set(v___x_3403_, 1, v___y_3359_);
return v___x_3403_;
}
v___jp_3361_:
{
lean_object* v_log_3364_; uint8_t v_action_3365_; uint8_t v_wantsRebuild_3366_; uint8_t v_canceled_3367_; lean_object* v_trace_3368_; lean_object* v_buildTime_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3384_; 
v_log_3364_ = lean_ctor_get(v_a_3363_, 0);
v_action_3365_ = lean_ctor_get_uint8(v_a_3363_, sizeof(void*)*3);
v_wantsRebuild_3366_ = lean_ctor_get_uint8(v_a_3363_, sizeof(void*)*3 + 1);
v_canceled_3367_ = lean_ctor_get_uint8(v_a_3363_, sizeof(void*)*3 + 2);
v_trace_3368_ = lean_ctor_get(v_a_3363_, 1);
v_buildTime_3369_ = lean_ctor_get(v_a_3363_, 2);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_a_3363_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3371_ = v_a_3363_;
v_isShared_3372_ = v_isSharedCheck_3384_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_buildTime_3369_);
lean_inc(v_trace_3368_);
lean_inc(v_log_3364_);
lean_dec(v_a_3363_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3384_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; uint8_t v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3381_; 
v___x_3373_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__0___closed__0));
v___x_3374_ = lean_string_append(v___x_3373_, v_what_3350_);
v___x_3375_ = lean_string_append(v___x_3374_, v_a_3362_);
lean_dec_ref(v_a_3362_);
v___x_3376_ = 3;
v___x_3377_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3377_, 0, v___x_3375_);
lean_ctor_set_uint8(v___x_3377_, sizeof(void*)*1, v___x_3376_);
v___x_3378_ = lean_array_get_size(v_log_3364_);
v___x_3379_ = lean_array_push(v_log_3364_, v___x_3377_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3379_);
v___x_3381_ = v___x_3371_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_trace_3368_);
lean_ctor_set(v_reuseFailAlloc_3383_, 2, v_buildTime_3369_);
lean_ctor_set_uint8(v_reuseFailAlloc_3383_, sizeof(void*)*3, v_action_3365_);
lean_ctor_set_uint8(v_reuseFailAlloc_3383_, sizeof(void*)*3 + 1, v_wantsRebuild_3366_);
lean_ctor_set_uint8(v_reuseFailAlloc_3383_, sizeof(void*)*3 + 2, v_canceled_3367_);
v___x_3381_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
lean_object* v___x_3382_; 
v___x_3382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3378_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
return v___x_3382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__0___boxed(lean_object* v_what_3404_, lean_object* v_baseName_3405_, lean_object* v_optFacet_3406_, lean_object* v_success_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
uint8_t v_success_boxed_3415_; lean_object* v_res_3416_; 
v_success_boxed_3415_ = lean_unbox(v_success_3407_);
v_res_3416_ = l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__0(v_what_3404_, v_baseName_3405_, v_optFacet_3406_, v_success_boxed_3415_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec_ref(v_what_3404_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__1(lean_object* v___x_3417_, lean_object* v___x_3418_, lean_object* v___f_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v___x_3427_; 
lean_inc_ref(v___y_3420_);
lean_inc_ref(v___y_3424_);
lean_inc_ref(v___y_3423_);
lean_inc(v___y_3422_);
lean_inc(v___y_3421_);
v___x_3427_ = lean_apply_7(v___y_3420_, v___x_3417_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, lean_box(0));
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3440_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
v_a_3429_ = lean_ctor_get(v___x_3427_, 1);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3431_ = v___x_3427_;
v_isShared_3432_ = v_isSharedCheck_3440_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_inc(v_a_3428_);
lean_dec(v___x_3427_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3440_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3433_; uint8_t v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3438_; 
v___x_3433_ = lean_unsigned_to_nat(0u);
v___x_3434_ = 0;
v___x_3435_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3436_ = l_Lake_Job_mapM___redArg(v___x_3418_, v_a_3428_, v___f_3419_, v___x_3433_, v___x_3434_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___x_3435_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v___x_3436_);
v___x_3438_ = v___x_3431_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3436_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v_a_3429_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
else
{
lean_object* v_a_3441_; lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
lean_dec_ref(v___y_3420_);
lean_dec_ref(v___f_3419_);
lean_dec(v___x_3418_);
v_a_3441_ = lean_ctor_get(v___x_3427_, 0);
v_a_3442_ = lean_ctor_get(v___x_3427_, 1);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3444_ = v___x_3427_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_inc(v_a_3441_);
lean_dec(v___x_3427_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3441_);
lean_ctor_set(v_reuseFailAlloc_3448_, 1, v_a_3442_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__1___boxed(lean_object* v___x_3450_, lean_object* v___x_3451_, lean_object* v___f_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__1(v___x_3450_, v___x_3451_, v___f_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec(v___y_3454_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__2(lean_object* v_what_3461_, lean_object* v_optFacet_3462_, lean_object* v_facet_3463_, lean_object* v___x_3464_, lean_object* v_pkg_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
lean_object* v_baseName_3473_; lean_object* v_keyName_3474_; lean_object* v___f_3475_; uint8_t v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___f_3486_; uint8_t v___x_3487_; lean_object* v___x_3488_; 
v_baseName_3473_ = lean_ctor_get(v_pkg_3465_, 1);
v_keyName_3474_ = lean_ctor_get(v_pkg_3465_, 2);
lean_inc(v_optFacet_3462_);
lean_inc_n(v_baseName_3473_, 2);
v___f_3475_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_3475_, 0, v_what_3461_);
lean_closure_set(v___f_3475_, 1, v_baseName_3473_);
lean_closure_set(v___f_3475_, 2, v_optFacet_3462_);
v___x_3476_ = 1;
v___x_3477_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3473_, v___x_3476_);
v___x_3478_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3479_ = lean_string_append(v___x_3477_, v___x_3478_);
v___x_3480_ = l_Lake_Name_eraseHead(v_facet_3463_);
v___x_3481_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3480_, v___x_3476_);
v___x_3482_ = lean_string_append(v___x_3479_, v___x_3481_);
lean_dec_ref(v___x_3481_);
lean_inc(v_keyName_3474_);
v___x_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3483_, 0, v_keyName_3474_);
v___x_3484_ = l_Lake_Package_keyword;
v___x_3485_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3483_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
lean_ctor_set(v___x_3485_, 2, v_pkg_3465_);
lean_ctor_set(v___x_3485_, 3, v_optFacet_3462_);
lean_inc(v___x_3464_);
v___f_3486_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3486_, 0, v___x_3485_);
lean_closure_set(v___f_3486_, 1, v___x_3464_);
lean_closure_set(v___f_3486_, 2, v___f_3475_);
v___x_3487_ = 0;
v___x_3488_ = l_Lake_ensureJob___redArg(v___x_3464_, v___f_3486_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3513_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
v_a_3490_ = lean_ctor_get(v___x_3488_, 1);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3492_ = v___x_3488_;
v_isShared_3493_ = v_isSharedCheck_3513_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_inc(v_a_3489_);
lean_dec(v___x_3488_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3513_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v_task_3494_; lean_object* v_kind_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3511_; 
v_task_3494_ = lean_ctor_get(v_a_3489_, 0);
v_kind_3495_ = lean_ctor_get(v_a_3489_, 1);
v_isSharedCheck_3511_ = !lean_is_exclusive(v_a_3489_);
if (v_isSharedCheck_3511_ == 0)
{
lean_object* v_unused_3512_; 
v_unused_3512_ = lean_ctor_get(v_a_3489_, 2);
lean_dec(v_unused_3512_);
v___x_3497_ = v_a_3489_;
v_isShared_3498_ = v_isSharedCheck_3511_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_kind_3495_);
lean_inc(v_task_3494_);
lean_dec(v_a_3489_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3511_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v_registeredJobs_3499_; lean_object* v_job_3501_; 
v_registeredJobs_3499_ = lean_ctor_get(v___y_3470_, 4);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 2, v___x_3482_);
v_job_3501_ = v___x_3497_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_task_3494_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_kind_3495_);
lean_ctor_set(v_reuseFailAlloc_3510_, 2, v___x_3482_);
v_job_3501_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3508_; 
lean_ctor_set_uint8(v_job_3501_, sizeof(void*)*3, v___x_3487_);
v___x_3502_ = lean_st_ref_take(v_registeredJobs_3499_);
lean_inc_ref(v_job_3501_);
v___x_3503_ = l_Lake_Job_toOpaque___redArg(v_job_3501_);
v___x_3504_ = lean_array_push(v___x_3502_, v___x_3503_);
v___x_3505_ = lean_st_ref_put(v_registeredJobs_3499_, v___x_3504_);
v___x_3506_ = l_Lake_Job_renew___redArg(v_job_3501_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v___x_3506_);
v___x_3508_ = v___x_3492_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v_a_3490_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3482_);
return v___x_3488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__2___boxed(lean_object* v_what_3514_, lean_object* v_optFacet_3515_, lean_object* v_facet_3516_, lean_object* v___x_3517_, lean_object* v_pkg_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__2(v_what_3514_, v_optFacet_3515_, v_facet_3516_, v___x_3517_, v_pkg_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec(v___y_3520_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg(lean_object* v_facet_3534_, lean_object* v_optFacet_3535_, lean_object* v_what_3536_){
_start:
{
lean_object* v___x_3537_; lean_object* v___f_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3537_ = l_Lake_instDataKindUnit;
v___f_3538_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_3538_, 0, v_what_3536_);
lean_closure_set(v___f_3538_, 1, v_optFacet_3535_);
lean_closure_set(v___f_3538_, 2, v_facet_3534_);
lean_closure_set(v___f_3538_, 3, v___x_3537_);
v___x_3539_ = l_Lake_Package_keyword;
v___x_3540_ = 1;
v___x_3541_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__3));
v___x_3542_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3542_, 0, v___x_3539_);
lean_ctor_set(v___x_3542_, 1, v___f_3538_);
lean_ctor_set(v___x_3542_, 2, v___x_3537_);
lean_ctor_set(v___x_3542_, 3, v___x_3541_);
lean_ctor_set_uint8(v___x_3542_, sizeof(void*)*4, v___x_3540_);
lean_ctor_set_uint8(v___x_3542_, sizeof(void*)*4 + 1, v___x_3540_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig(lean_object* v_facet_3543_, lean_object* v_optFacet_3544_, lean_object* v_what_3545_, lean_object* v_inst_3546_, lean_object* v_inst_3547_){
_start:
{
lean_object* v___x_3548_; lean_object* v___f_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3548_ = l_Lake_instDataKindUnit;
v___f_3549_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_3549_, 0, v_what_3545_);
lean_closure_set(v___f_3549_, 1, v_optFacet_3544_);
lean_closure_set(v___f_3549_, 2, v_facet_3543_);
lean_closure_set(v___f_3549_, 3, v___x_3548_);
v___x_3550_ = l_Lake_Package_keyword;
v___x_3551_ = 1;
v___x_3552_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___closed__3));
v___x_3553_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3553_, 0, v___x_3550_);
lean_ctor_set(v___x_3553_, 1, v___f_3549_);
lean_ctor_set(v___x_3553_, 2, v___x_3548_);
lean_ctor_set(v___x_3553_, 3, v___x_3552_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*4, v___x_3551_);
lean_ctor_set_uint8(v___x_3553_, sizeof(void*)*4 + 1, v___x_3551_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* v_baseName_3555_, lean_object* v___x_3556_, uint8_t v_success_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v_a_3566_; lean_object* v_a_3567_; 
if (v_success_3557_ == 0)
{
lean_object* v_toBuildConfig_3588_; uint8_t v_verbosity_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; uint8_t v___x_3593_; 
v_toBuildConfig_3588_ = lean_ctor_get(v___y_3562_, 0);
v_verbosity_3589_ = lean_ctor_get_uint8(v_toBuildConfig_3588_, sizeof(void*)*6 + 4);
v___x_3590_ = lean_box(v_verbosity_3589_);
v___x_3591_ = lean_obj_tag_nat(v___x_3590_);
lean_dec(v___x_3590_);
v___x_3592_ = lean_unsigned_to_nat(2u);
v___x_3593_ = lean_nat_dec_eq(v___x_3591_, v___x_3592_);
if (v___x_3593_ == 0)
{
lean_object* v___x_3594_; 
lean_dec(v___x_3556_);
lean_dec(v_baseName_3555_);
v___x_3594_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_3566_ = v___x_3594_;
v_a_3567_ = v___y_3563_;
goto v___jp_3565_;
}
else
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3595_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_3596_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3555_, v___x_3593_);
v___x_3597_ = lean_string_append(v___x_3595_, v___x_3596_);
lean_dec_ref(v___x_3596_);
v___x_3598_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3599_ = lean_string_append(v___x_3597_, v___x_3598_);
v___x_3600_ = l_Lake_Name_eraseHead(v___x_3556_);
v___x_3601_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3600_, v___x_3593_);
v___x_3602_ = lean_string_append(v___x_3599_, v___x_3601_);
lean_dec_ref(v___x_3601_);
v___x_3603_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3604_ = lean_string_append(v___x_3602_, v___x_3603_);
v_a_3566_ = v___x_3604_;
v_a_3567_ = v___y_3563_;
goto v___jp_3565_;
}
}
else
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
lean_dec(v___x_3556_);
lean_dec(v_baseName_3555_);
v___x_3605_ = lean_box(0);
v___x_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
lean_ctor_set(v___x_3606_, 1, v___y_3563_);
return v___x_3606_;
}
v___jp_3565_:
{
lean_object* v_log_3568_; uint8_t v_action_3569_; uint8_t v_wantsRebuild_3570_; uint8_t v_canceled_3571_; lean_object* v_trace_3572_; lean_object* v_buildTime_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3587_; 
v_log_3568_ = lean_ctor_get(v_a_3567_, 0);
v_action_3569_ = lean_ctor_get_uint8(v_a_3567_, sizeof(void*)*3);
v_wantsRebuild_3570_ = lean_ctor_get_uint8(v_a_3567_, sizeof(void*)*3 + 1);
v_canceled_3571_ = lean_ctor_get_uint8(v_a_3567_, sizeof(void*)*3 + 2);
v_trace_3572_ = lean_ctor_get(v_a_3567_, 1);
v_buildTime_3573_ = lean_ctor_get(v_a_3567_, 2);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_a_3567_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3575_ = v_a_3567_;
v_isShared_3576_ = v_isSharedCheck_3587_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_buildTime_3573_);
lean_inc(v_trace_3572_);
lean_inc(v_log_3568_);
lean_dec(v_a_3567_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3587_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3584_; 
v___x_3577_ = ((lean_object*)(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0));
v___x_3578_ = lean_string_append(v___x_3577_, v_a_3566_);
lean_dec_ref(v_a_3566_);
v___x_3579_ = 3;
v___x_3580_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3580_, 0, v___x_3578_);
lean_ctor_set_uint8(v___x_3580_, sizeof(void*)*1, v___x_3579_);
v___x_3581_ = lean_array_get_size(v_log_3568_);
v___x_3582_ = lean_array_push(v_log_3568_, v___x_3580_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3582_);
v___x_3584_ = v___x_3575_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_trace_3572_);
lean_ctor_set(v_reuseFailAlloc_3586_, 2, v_buildTime_3573_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, sizeof(void*)*3, v_action_3569_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, sizeof(void*)*3 + 1, v_wantsRebuild_3570_);
lean_ctor_set_uint8(v_reuseFailAlloc_3586_, sizeof(void*)*3 + 2, v_canceled_3571_);
v___x_3584_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3585_; 
v___x_3585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3581_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
return v___x_3585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object* v_baseName_3607_, lean_object* v___x_3608_, lean_object* v_success_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
uint8_t v_success_boxed_3617_; lean_object* v_res_3618_; 
v_success_boxed_3617_ = lean_unbox(v_success_3609_);
v_res_3618_ = l_Lake_Package_buildCacheFacetConfig___lam__1(v_baseName_3607_, v___x_3608_, v_success_boxed_3617_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* v___x_3619_, lean_object* v___x_3620_, lean_object* v___x_3621_, lean_object* v_pkg_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_){
_start:
{
lean_object* v_baseName_3630_; lean_object* v_keyName_3631_; lean_object* v___f_3632_; uint8_t v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___f_3643_; uint8_t v___x_3644_; lean_object* v___x_3645_; 
v_baseName_3630_ = lean_ctor_get(v_pkg_3622_, 1);
v_keyName_3631_ = lean_ctor_get(v_pkg_3622_, 2);
lean_inc(v___x_3619_);
lean_inc_n(v_baseName_3630_, 2);
v___f_3632_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3632_, 0, v_baseName_3630_);
lean_closure_set(v___f_3632_, 1, v___x_3619_);
v___x_3633_ = 1;
v___x_3634_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3630_, v___x_3633_);
v___x_3635_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3636_ = lean_string_append(v___x_3634_, v___x_3635_);
v___x_3637_ = l_Lake_Name_eraseHead(v___x_3620_);
v___x_3638_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3637_, v___x_3633_);
v___x_3639_ = lean_string_append(v___x_3636_, v___x_3638_);
lean_dec_ref(v___x_3638_);
lean_inc(v_keyName_3631_);
v___x_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3640_, 0, v_keyName_3631_);
v___x_3641_ = l_Lake_Package_keyword;
v___x_3642_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3640_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
lean_ctor_set(v___x_3642_, 2, v_pkg_3622_);
lean_ctor_set(v___x_3642_, 3, v___x_3619_);
lean_inc(v___x_3621_);
v___f_3643_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3643_, 0, v___x_3642_);
lean_closure_set(v___f_3643_, 1, v___x_3621_);
lean_closure_set(v___f_3643_, 2, v___f_3632_);
v___x_3644_ = 0;
v___x_3645_ = l_Lake_ensureJob___redArg(v___x_3621_, v___f_3643_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3670_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
v_a_3647_ = lean_ctor_get(v___x_3645_, 1);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3649_ = v___x_3645_;
v_isShared_3650_ = v_isSharedCheck_3670_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_inc(v_a_3646_);
lean_dec(v___x_3645_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3670_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v_task_3651_; lean_object* v_kind_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3668_; 
v_task_3651_ = lean_ctor_get(v_a_3646_, 0);
v_kind_3652_ = lean_ctor_get(v_a_3646_, 1);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_a_3646_);
if (v_isSharedCheck_3668_ == 0)
{
lean_object* v_unused_3669_; 
v_unused_3669_ = lean_ctor_get(v_a_3646_, 2);
lean_dec(v_unused_3669_);
v___x_3654_ = v_a_3646_;
v_isShared_3655_ = v_isSharedCheck_3668_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_kind_3652_);
lean_inc(v_task_3651_);
lean_dec(v_a_3646_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3668_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v_registeredJobs_3656_; lean_object* v_job_3658_; 
v_registeredJobs_3656_ = lean_ctor_get(v___y_3627_, 4);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 2, v___x_3639_);
v_job_3658_ = v___x_3654_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_task_3651_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_kind_3652_);
lean_ctor_set(v_reuseFailAlloc_3667_, 2, v___x_3639_);
v_job_3658_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3665_; 
lean_ctor_set_uint8(v_job_3658_, sizeof(void*)*3, v___x_3644_);
v___x_3659_ = lean_st_ref_take(v_registeredJobs_3656_);
lean_inc_ref(v_job_3658_);
v___x_3660_ = l_Lake_Job_toOpaque___redArg(v_job_3658_);
v___x_3661_ = lean_array_push(v___x_3659_, v___x_3660_);
v___x_3662_ = lean_st_ref_put(v_registeredJobs_3656_, v___x_3661_);
v___x_3663_ = l_Lake_Job_renew___redArg(v_job_3658_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 0, v___x_3663_);
v___x_3665_ = v___x_3649_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3663_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_a_3647_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3639_);
return v___x_3645_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object* v___x_3671_, lean_object* v___x_3672_, lean_object* v___x_3673_, lean_object* v_pkg_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Lake_Package_buildCacheFacetConfig___lam__2(v___x_3671_, v___x_3672_, v___x_3673_, v_pkg_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
lean_dec_ref(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec(v___y_3676_);
return v_res_3682_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___f_3686_; 
v___x_3683_ = l_Lake_instDataKindUnit;
v___x_3684_ = l_Lake_Package_buildCacheFacet;
v___x_3685_ = l_Lake_Package_optBuildCacheFacet;
v___f_3686_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3686_, 0, v___x_3685_);
lean_closure_set(v___f_3686_, 1, v___x_3684_);
lean_closure_set(v___f_3686_, 2, v___x_3683_);
return v___f_3686_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3687_; uint8_t v___x_3688_; lean_object* v___x_3689_; lean_object* v___f_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___f_3687_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3688_ = 1;
v___x_3689_ = l_Lake_instDataKindUnit;
v___f_3690_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__0, &l_Lake_Package_buildCacheFacetConfig___closed__0_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__0);
v___x_3691_ = l_Lake_Package_keyword;
v___x_3692_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
lean_ctor_set(v___x_3692_, 1, v___f_3690_);
lean_ctor_set(v___x_3692_, 2, v___x_3689_);
lean_ctor_set(v___x_3692_, 3, v___f_3687_);
lean_ctor_set_uint8(v___x_3692_, sizeof(void*)*4, v___x_3688_);
lean_ctor_set_uint8(v___x_3692_, sizeof(void*)*4 + 1, v___x_3688_);
return v___x_3692_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig(void){
_start:
{
lean_object* v___x_3693_; 
v___x_3693_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__1, &l_Lake_Package_buildCacheFacetConfig___closed__1_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__1);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_artifactCacheFacetConfig___lam__1(lean_object* v_baseName_3695_, lean_object* v___x_3696_, uint8_t v_success_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
lean_object* v_a_3706_; lean_object* v_a_3707_; 
if (v_success_3697_ == 0)
{
lean_object* v_toBuildConfig_3728_; uint8_t v_verbosity_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; uint8_t v___x_3733_; 
v_toBuildConfig_3728_ = lean_ctor_get(v___y_3702_, 0);
v_verbosity_3729_ = lean_ctor_get_uint8(v_toBuildConfig_3728_, sizeof(void*)*6 + 4);
v___x_3730_ = lean_box(v_verbosity_3729_);
v___x_3731_ = lean_obj_tag_nat(v___x_3730_);
lean_dec(v___x_3730_);
v___x_3732_ = lean_unsigned_to_nat(2u);
v___x_3733_ = lean_nat_dec_eq(v___x_3731_, v___x_3732_);
if (v___x_3733_ == 0)
{
lean_object* v___x_3734_; 
lean_dec(v___x_3696_);
lean_dec(v_baseName_3695_);
v___x_3734_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_3706_ = v___x_3734_;
v_a_3707_ = v___y_3703_;
goto v___jp_3705_;
}
else
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3735_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_3736_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3695_, v___x_3733_);
v___x_3737_ = lean_string_append(v___x_3735_, v___x_3736_);
lean_dec_ref(v___x_3736_);
v___x_3738_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3739_ = lean_string_append(v___x_3737_, v___x_3738_);
v___x_3740_ = l_Lake_Name_eraseHead(v___x_3696_);
v___x_3741_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3740_, v___x_3733_);
v___x_3742_ = lean_string_append(v___x_3739_, v___x_3741_);
lean_dec_ref(v___x_3741_);
v___x_3743_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3744_ = lean_string_append(v___x_3742_, v___x_3743_);
v_a_3706_ = v___x_3744_;
v_a_3707_ = v___y_3703_;
goto v___jp_3705_;
}
}
else
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_dec(v___x_3696_);
lean_dec(v_baseName_3695_);
v___x_3745_ = lean_box(0);
v___x_3746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3745_);
lean_ctor_set(v___x_3746_, 1, v___y_3703_);
return v___x_3746_;
}
v___jp_3705_:
{
lean_object* v_log_3708_; uint8_t v_action_3709_; uint8_t v_wantsRebuild_3710_; uint8_t v_canceled_3711_; lean_object* v_trace_3712_; lean_object* v_buildTime_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3727_; 
v_log_3708_ = lean_ctor_get(v_a_3707_, 0);
v_action_3709_ = lean_ctor_get_uint8(v_a_3707_, sizeof(void*)*3);
v_wantsRebuild_3710_ = lean_ctor_get_uint8(v_a_3707_, sizeof(void*)*3 + 1);
v_canceled_3711_ = lean_ctor_get_uint8(v_a_3707_, sizeof(void*)*3 + 2);
v_trace_3712_ = lean_ctor_get(v_a_3707_, 1);
v_buildTime_3713_ = lean_ctor_get(v_a_3707_, 2);
v_isSharedCheck_3727_ = !lean_is_exclusive(v_a_3707_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3715_ = v_a_3707_;
v_isShared_3716_ = v_isSharedCheck_3727_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_buildTime_3713_);
lean_inc(v_trace_3712_);
lean_inc(v_log_3708_);
lean_dec(v_a_3707_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3727_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3724_; 
v___x_3717_ = ((lean_object*)(l_Lake_Package_artifactCacheFacetConfig___lam__1___closed__0));
v___x_3718_ = lean_string_append(v___x_3717_, v_a_3706_);
lean_dec_ref(v_a_3706_);
v___x_3719_ = 3;
v___x_3720_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3720_, 0, v___x_3718_);
lean_ctor_set_uint8(v___x_3720_, sizeof(void*)*1, v___x_3719_);
v___x_3721_ = lean_array_get_size(v_log_3708_);
v___x_3722_ = lean_array_push(v_log_3708_, v___x_3720_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3722_);
v___x_3724_ = v___x_3715_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3722_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v_trace_3712_);
lean_ctor_set(v_reuseFailAlloc_3726_, 2, v_buildTime_3713_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, sizeof(void*)*3, v_action_3709_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, sizeof(void*)*3 + 1, v_wantsRebuild_3710_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, sizeof(void*)*3 + 2, v_canceled_3711_);
v___x_3724_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
lean_object* v___x_3725_; 
v___x_3725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3721_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
return v___x_3725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_artifactCacheFacetConfig___lam__1___boxed(lean_object* v_baseName_3747_, lean_object* v___x_3748_, lean_object* v_success_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
uint8_t v_success_boxed_3757_; lean_object* v_res_3758_; 
v_success_boxed_3757_ = lean_unbox(v_success_3749_);
v_res_3758_ = l_Lake_Package_artifactCacheFacetConfig___lam__1(v_baseName_3747_, v___x_3748_, v_success_boxed_3757_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_artifactCacheFacetConfig___lam__2(lean_object* v___x_3759_, lean_object* v___x_3760_, lean_object* v___x_3761_, lean_object* v_pkg_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v_baseName_3770_; lean_object* v_keyName_3771_; lean_object* v___f_3772_; uint8_t v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___f_3783_; uint8_t v___x_3784_; lean_object* v___x_3785_; 
v_baseName_3770_ = lean_ctor_get(v_pkg_3762_, 1);
v_keyName_3771_ = lean_ctor_get(v_pkg_3762_, 2);
lean_inc(v___x_3759_);
lean_inc_n(v_baseName_3770_, 2);
v___f_3772_ = lean_alloc_closure((void*)(l_Lake_Package_artifactCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3772_, 0, v_baseName_3770_);
lean_closure_set(v___f_3772_, 1, v___x_3759_);
v___x_3773_ = 1;
v___x_3774_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3770_, v___x_3773_);
v___x_3775_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3776_ = lean_string_append(v___x_3774_, v___x_3775_);
v___x_3777_ = l_Lake_Name_eraseHead(v___x_3760_);
v___x_3778_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3777_, v___x_3773_);
v___x_3779_ = lean_string_append(v___x_3776_, v___x_3778_);
lean_dec_ref(v___x_3778_);
lean_inc(v_keyName_3771_);
v___x_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3780_, 0, v_keyName_3771_);
v___x_3781_ = l_Lake_Package_keyword;
v___x_3782_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3780_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
lean_ctor_set(v___x_3782_, 2, v_pkg_3762_);
lean_ctor_set(v___x_3782_, 3, v___x_3759_);
lean_inc(v___x_3761_);
v___f_3783_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3783_, 0, v___x_3782_);
lean_closure_set(v___f_3783_, 1, v___x_3761_);
lean_closure_set(v___f_3783_, 2, v___f_3772_);
v___x_3784_ = 0;
v___x_3785_ = l_Lake_ensureJob___redArg(v___x_3761_, v___f_3783_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3810_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
v_a_3787_ = lean_ctor_get(v___x_3785_, 1);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3789_ = v___x_3785_;
v_isShared_3790_ = v_isSharedCheck_3810_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_inc(v_a_3786_);
lean_dec(v___x_3785_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3810_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v_task_3791_; lean_object* v_kind_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3808_; 
v_task_3791_ = lean_ctor_get(v_a_3786_, 0);
v_kind_3792_ = lean_ctor_get(v_a_3786_, 1);
v_isSharedCheck_3808_ = !lean_is_exclusive(v_a_3786_);
if (v_isSharedCheck_3808_ == 0)
{
lean_object* v_unused_3809_; 
v_unused_3809_ = lean_ctor_get(v_a_3786_, 2);
lean_dec(v_unused_3809_);
v___x_3794_ = v_a_3786_;
v_isShared_3795_ = v_isSharedCheck_3808_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_kind_3792_);
lean_inc(v_task_3791_);
lean_dec(v_a_3786_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3808_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v_registeredJobs_3796_; lean_object* v_job_3798_; 
v_registeredJobs_3796_ = lean_ctor_get(v___y_3767_, 4);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 2, v___x_3779_);
v_job_3798_ = v___x_3794_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_task_3791_);
lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_kind_3792_);
lean_ctor_set(v_reuseFailAlloc_3807_, 2, v___x_3779_);
v_job_3798_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3805_; 
lean_ctor_set_uint8(v_job_3798_, sizeof(void*)*3, v___x_3784_);
v___x_3799_ = lean_st_ref_take(v_registeredJobs_3796_);
lean_inc_ref(v_job_3798_);
v___x_3800_ = l_Lake_Job_toOpaque___redArg(v_job_3798_);
v___x_3801_ = lean_array_push(v___x_3799_, v___x_3800_);
v___x_3802_ = lean_st_ref_put(v_registeredJobs_3796_, v___x_3801_);
v___x_3803_ = l_Lake_Job_renew___redArg(v_job_3798_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3803_);
v___x_3805_ = v___x_3789_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3803_);
lean_ctor_set(v_reuseFailAlloc_3806_, 1, v_a_3787_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3779_);
return v___x_3785_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_artifactCacheFacetConfig___lam__2___boxed(lean_object* v___x_3811_, lean_object* v___x_3812_, lean_object* v___x_3813_, lean_object* v_pkg_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Lake_Package_artifactCacheFacetConfig___lam__2(v___x_3811_, v___x_3812_, v___x_3813_, v_pkg_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec(v___y_3816_);
return v_res_3822_;
}
}
static lean_object* _init_l_Lake_Package_artifactCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___f_3826_; 
v___x_3823_ = l_Lake_instDataKindUnit;
v___x_3824_ = l_Lake_Package_artifactCacheFacet;
v___x_3825_ = l_Lake_Package_optArtifactCacheFacet;
v___f_3826_ = lean_alloc_closure((void*)(l_Lake_Package_artifactCacheFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3826_, 0, v___x_3825_);
lean_closure_set(v___f_3826_, 1, v___x_3824_);
lean_closure_set(v___f_3826_, 2, v___x_3823_);
return v___f_3826_;
}
}
static lean_object* _init_l_Lake_Package_artifactCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3827_; uint8_t v___x_3828_; lean_object* v___x_3829_; lean_object* v___f_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___f_3827_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3828_ = 1;
v___x_3829_ = l_Lake_instDataKindUnit;
v___f_3830_ = lean_obj_once(&l_Lake_Package_artifactCacheFacetConfig___closed__0, &l_Lake_Package_artifactCacheFacetConfig___closed__0_once, _init_l_Lake_Package_artifactCacheFacetConfig___closed__0);
v___x_3831_ = l_Lake_Package_keyword;
v___x_3832_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3832_, 0, v___x_3831_);
lean_ctor_set(v___x_3832_, 1, v___f_3830_);
lean_ctor_set(v___x_3832_, 2, v___x_3829_);
lean_ctor_set(v___x_3832_, 3, v___f_3827_);
lean_ctor_set_uint8(v___x_3832_, sizeof(void*)*4, v___x_3828_);
lean_ctor_set_uint8(v___x_3832_, sizeof(void*)*4 + 1, v___x_3828_);
return v___x_3832_;
}
}
static lean_object* _init_l_Lake_Package_artifactCacheFacetConfig(void){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = lean_obj_once(&l_Lake_Package_artifactCacheFacetConfig___closed__1, &l_Lake_Package_artifactCacheFacetConfig___closed__1_once, _init_l_Lake_Package_artifactCacheFacetConfig___closed__1);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* v_pkg_3835_, lean_object* v_dir_3836_, lean_object* v___x_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
uint8_t v_r_3846_; lean_object* v___y_3847_; lean_object* v_a_3851_; lean_object* v___x_3868_; 
lean_inc_ref(v_pkg_3835_);
v___x_3868_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_pkg_3835_, v___y_3842_, v___y_3843_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; lean_object* v_a_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
v_a_3870_ = lean_ctor_get(v___x_3868_, 1);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3868_, 2);
v___x_3871_ = l_Lake_defaultLakeDir;
v___x_3872_ = l_Lake_joinRelative(v_dir_3836_, v___x_3871_);
v___x_3873_ = ((lean_object*)(l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0));
v___x_3874_ = l_Lake_joinRelative(v___x_3872_, v___x_3873_);
v___x_3875_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_3835_, v_a_3869_, v___x_3874_, v___x_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v_a_3870_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; uint8_t v___x_3877_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 1);
lean_inc(v_a_3876_);
lean_dec_ref_known(v___x_3875_, 2);
v___x_3877_ = 1;
v_r_3846_ = v___x_3877_;
v___y_3847_ = v_a_3876_;
goto v___jp_3845_;
}
else
{
lean_object* v_a_3878_; 
v_a_3878_ = lean_ctor_get(v___x_3875_, 1);
lean_inc(v_a_3878_);
lean_dec_ref_known(v___x_3875_, 2);
v_a_3851_ = v_a_3878_;
goto v___jp_3850_;
}
}
else
{
lean_object* v_a_3879_; 
lean_dec_ref(v_dir_3836_);
lean_dec_ref(v_pkg_3835_);
v_a_3879_ = lean_ctor_get(v___x_3868_, 1);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___x_3868_, 2);
v_a_3851_ = v_a_3879_;
goto v___jp_3850_;
}
v___jp_3845_:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3848_ = lean_box(v_r_3846_);
v___x_3849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3848_);
lean_ctor_set(v___x_3849_, 1, v___y_3847_);
return v___x_3849_;
}
v___jp_3850_:
{
lean_object* v_log_3852_; uint8_t v_action_3853_; uint8_t v_wantsRebuild_3854_; uint8_t v_canceled_3855_; lean_object* v_trace_3856_; lean_object* v_buildTime_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3867_; 
v_log_3852_ = lean_ctor_get(v_a_3851_, 0);
v_action_3853_ = lean_ctor_get_uint8(v_a_3851_, sizeof(void*)*3);
v_wantsRebuild_3854_ = lean_ctor_get_uint8(v_a_3851_, sizeof(void*)*3 + 1);
v_canceled_3855_ = lean_ctor_get_uint8(v_a_3851_, sizeof(void*)*3 + 2);
v_trace_3856_ = lean_ctor_get(v_a_3851_, 1);
v_buildTime_3857_ = lean_ctor_get(v_a_3851_, 2);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_a_3851_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3859_ = v_a_3851_;
v_isShared_3860_ = v_isSharedCheck_3867_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_buildTime_3857_);
lean_inc(v_trace_3856_);
lean_inc(v_log_3852_);
lean_dec(v_a_3851_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3867_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
uint8_t v___x_3861_; uint8_t v___x_3862_; lean_object* v___x_3864_; 
v___x_3861_ = 4;
v___x_3862_ = l_Lake_JobAction_merge(v_action_3853_, v___x_3861_);
if (v_isShared_3860_ == 0)
{
v___x_3864_ = v___x_3859_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_log_3852_);
lean_ctor_set(v_reuseFailAlloc_3866_, 1, v_trace_3856_);
lean_ctor_set(v_reuseFailAlloc_3866_, 2, v_buildTime_3857_);
lean_ctor_set_uint8(v_reuseFailAlloc_3866_, sizeof(void*)*3 + 1, v_wantsRebuild_3854_);
lean_ctor_set_uint8(v_reuseFailAlloc_3866_, sizeof(void*)*3 + 2, v_canceled_3855_);
v___x_3864_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
uint8_t v___x_3865_; 
lean_ctor_set_uint8(v___x_3864_, sizeof(void*)*3, v___x_3862_);
v___x_3865_ = 0;
v_r_3846_ = v___x_3865_;
v___y_3847_ = v___x_3864_;
goto v___jp_3845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* v_pkg_3880_, lean_object* v_dir_3881_, lean_object* v___x_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lake_Package_optBarrelFacetConfig___lam__0(v_pkg_3880_, v_dir_3881_, v___x_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec_ref(v___x_3882_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* v___x_3891_, lean_object* v___x_3892_, lean_object* v___x_3893_, lean_object* v_pkg_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v_baseName_3902_; lean_object* v_dir_3903_; lean_object* v___f_3904_; uint8_t v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___f_3914_; lean_object* v___x_3915_; 
v_baseName_3902_ = lean_ctor_get(v_pkg_3894_, 1);
lean_inc(v_baseName_3902_);
v_dir_3903_ = lean_ctor_get(v_pkg_3894_, 4);
lean_inc_ref(v_dir_3903_);
v___f_3904_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3904_, 0, v_pkg_3894_);
lean_closure_set(v___f_3904_, 1, v_dir_3903_);
lean_closure_set(v___f_3904_, 2, v___x_3891_);
v___x_3905_ = 1;
v___x_3906_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3902_, v___x_3905_);
v___x_3907_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3908_ = lean_string_append(v___x_3906_, v___x_3907_);
v___x_3909_ = l_Lake_Name_eraseHead(v___x_3892_);
v___x_3910_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3909_, v___x_3905_);
v___x_3911_ = lean_string_append(v___x_3908_, v___x_3910_);
lean_dec_ref(v___x_3910_);
v___x_3912_ = lean_unsigned_to_nat(0u);
v___x_3913_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_3893_);
v___f_3914_ = lean_alloc_closure((void*)(l_Lake_Package_optArtifactCacheFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_3914_, 0, v___x_3893_);
lean_closure_set(v___f_3914_, 1, v___f_3904_);
lean_closure_set(v___f_3914_, 2, v___x_3912_);
lean_closure_set(v___f_3914_, 3, v___x_3913_);
v___x_3915_ = l_Lake_ensureJob___redArg(v___x_3893_, v___f_3914_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3940_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
v_a_3917_ = lean_ctor_get(v___x_3915_, 1);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3919_ = v___x_3915_;
v_isShared_3920_ = v_isSharedCheck_3940_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_inc(v_a_3916_);
lean_dec(v___x_3915_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3940_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v_task_3921_; lean_object* v_kind_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3938_; 
v_task_3921_ = lean_ctor_get(v_a_3916_, 0);
v_kind_3922_ = lean_ctor_get(v_a_3916_, 1);
v_isSharedCheck_3938_ = !lean_is_exclusive(v_a_3916_);
if (v_isSharedCheck_3938_ == 0)
{
lean_object* v_unused_3939_; 
v_unused_3939_ = lean_ctor_get(v_a_3916_, 2);
lean_dec(v_unused_3939_);
v___x_3924_ = v_a_3916_;
v_isShared_3925_ = v_isSharedCheck_3938_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_kind_3922_);
lean_inc(v_task_3921_);
lean_dec(v_a_3916_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3938_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v_registeredJobs_3926_; lean_object* v_job_3928_; 
v_registeredJobs_3926_ = lean_ctor_get(v___y_3899_, 4);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 2, v___x_3911_);
v_job_3928_ = v___x_3924_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_task_3921_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_kind_3922_);
lean_ctor_set(v_reuseFailAlloc_3937_, 2, v___x_3911_);
v_job_3928_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3935_; 
lean_ctor_set_uint8(v_job_3928_, sizeof(void*)*3, v___x_3905_);
v___x_3929_ = lean_st_ref_take(v_registeredJobs_3926_);
lean_inc_ref(v_job_3928_);
v___x_3930_ = l_Lake_Job_toOpaque___redArg(v_job_3928_);
v___x_3931_ = lean_array_push(v___x_3929_, v___x_3930_);
v___x_3932_ = lean_st_ref_put(v_registeredJobs_3926_, v___x_3931_);
v___x_3933_ = l_Lake_Job_renew___redArg(v_job_3928_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 0, v___x_3933_);
v___x_3935_ = v___x_3919_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3933_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_a_3917_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3911_);
return v___x_3915_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object* v___x_3941_, lean_object* v___x_3942_, lean_object* v___x_3943_, lean_object* v_pkg_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_Lake_Package_optBarrelFacetConfig___lam__2(v___x_3941_, v___x_3942_, v___x_3943_, v_pkg_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec(v___y_3946_);
return v_res_3952_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___f_3956_; 
v___x_3953_ = l_Lake_instDataKindBool;
v___x_3954_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3955_ = l_Lake_Reservoir_lakeHeaders;
v___f_3956_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3956_, 0, v___x_3955_);
lean_closure_set(v___f_3956_, 1, v___x_3954_);
lean_closure_set(v___f_3956_, 2, v___x_3953_);
return v___f_3956_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3957_; uint8_t v___x_3958_; lean_object* v___x_3959_; lean_object* v___f_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___f_3957_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_3958_ = 1;
v___x_3959_ = l_Lake_instDataKindBool;
v___f_3960_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__0, &l_Lake_Package_optBarrelFacetConfig___closed__0_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__0);
v___x_3961_ = l_Lake_Package_keyword;
v___x_3962_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set(v___x_3962_, 1, v___f_3960_);
lean_ctor_set(v___x_3962_, 2, v___x_3959_);
lean_ctor_set(v___x_3962_, 3, v___f_3957_);
lean_ctor_set_uint8(v___x_3962_, sizeof(void*)*4, v___x_3958_);
lean_ctor_set_uint8(v___x_3962_, sizeof(void*)*4 + 1, v___x_3958_);
return v___x_3962_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig(void){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__1, &l_Lake_Package_optBarrelFacetConfig___closed__1_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__1);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* v_baseName_3965_, lean_object* v___x_3966_, uint8_t v_success_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
lean_object* v_a_3976_; lean_object* v_a_3977_; 
if (v_success_3967_ == 0)
{
lean_object* v_toBuildConfig_3998_; uint8_t v_verbosity_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; uint8_t v___x_4003_; 
v_toBuildConfig_3998_ = lean_ctor_get(v___y_3972_, 0);
v_verbosity_3999_ = lean_ctor_get_uint8(v_toBuildConfig_3998_, sizeof(void*)*6 + 4);
v___x_4000_ = lean_box(v_verbosity_3999_);
v___x_4001_ = lean_obj_tag_nat(v___x_4000_);
lean_dec(v___x_4000_);
v___x_4002_ = lean_unsigned_to_nat(2u);
v___x_4003_ = lean_nat_dec_eq(v___x_4001_, v___x_4002_);
if (v___x_4003_ == 0)
{
lean_object* v___x_4004_; 
lean_dec(v___x_3966_);
lean_dec(v_baseName_3965_);
v___x_4004_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_3976_ = v___x_4004_;
v_a_3977_ = v___y_3973_;
goto v___jp_3975_;
}
else
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4005_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_4006_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3965_, v___x_4003_);
v___x_4007_ = lean_string_append(v___x_4005_, v___x_4006_);
lean_dec_ref(v___x_4006_);
v___x_4008_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_4009_ = lean_string_append(v___x_4007_, v___x_4008_);
v___x_4010_ = l_Lake_Name_eraseHead(v___x_3966_);
v___x_4011_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4010_, v___x_4003_);
v___x_4012_ = lean_string_append(v___x_4009_, v___x_4011_);
lean_dec_ref(v___x_4011_);
v___x_4013_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_4014_ = lean_string_append(v___x_4012_, v___x_4013_);
v_a_3976_ = v___x_4014_;
v_a_3977_ = v___y_3973_;
goto v___jp_3975_;
}
}
else
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
lean_dec(v___x_3966_);
lean_dec(v_baseName_3965_);
v___x_4015_ = lean_box(0);
v___x_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
lean_ctor_set(v___x_4016_, 1, v___y_3973_);
return v___x_4016_;
}
v___jp_3975_:
{
lean_object* v_log_3978_; uint8_t v_action_3979_; uint8_t v_wantsRebuild_3980_; uint8_t v_canceled_3981_; lean_object* v_trace_3982_; lean_object* v_buildTime_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3997_; 
v_log_3978_ = lean_ctor_get(v_a_3977_, 0);
v_action_3979_ = lean_ctor_get_uint8(v_a_3977_, sizeof(void*)*3);
v_wantsRebuild_3980_ = lean_ctor_get_uint8(v_a_3977_, sizeof(void*)*3 + 1);
v_canceled_3981_ = lean_ctor_get_uint8(v_a_3977_, sizeof(void*)*3 + 2);
v_trace_3982_ = lean_ctor_get(v_a_3977_, 1);
v_buildTime_3983_ = lean_ctor_get(v_a_3977_, 2);
v_isSharedCheck_3997_ = !lean_is_exclusive(v_a_3977_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3985_ = v_a_3977_;
v_isShared_3986_ = v_isSharedCheck_3997_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_buildTime_3983_);
lean_inc(v_trace_3982_);
lean_inc(v_log_3978_);
lean_dec(v_a_3977_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3997_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; uint8_t v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3994_; 
v___x_3987_ = ((lean_object*)(l_Lake_Package_barrelFacetConfig___lam__1___closed__0));
v___x_3988_ = lean_string_append(v___x_3987_, v_a_3976_);
lean_dec_ref(v_a_3976_);
v___x_3989_ = 3;
v___x_3990_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3990_, 0, v___x_3988_);
lean_ctor_set_uint8(v___x_3990_, sizeof(void*)*1, v___x_3989_);
v___x_3991_ = lean_array_get_size(v_log_3978_);
v___x_3992_ = lean_array_push(v_log_3978_, v___x_3990_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 0, v___x_3992_);
v___x_3994_ = v___x_3985_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3992_);
lean_ctor_set(v_reuseFailAlloc_3996_, 1, v_trace_3982_);
lean_ctor_set(v_reuseFailAlloc_3996_, 2, v_buildTime_3983_);
lean_ctor_set_uint8(v_reuseFailAlloc_3996_, sizeof(void*)*3, v_action_3979_);
lean_ctor_set_uint8(v_reuseFailAlloc_3996_, sizeof(void*)*3 + 1, v_wantsRebuild_3980_);
lean_ctor_set_uint8(v_reuseFailAlloc_3996_, sizeof(void*)*3 + 2, v_canceled_3981_);
v___x_3994_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3995_; 
v___x_3995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3991_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
return v___x_3995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object* v_baseName_4017_, lean_object* v___x_4018_, lean_object* v_success_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
uint8_t v_success_boxed_4027_; lean_object* v_res_4028_; 
v_success_boxed_4027_ = lean_unbox(v_success_4019_);
v_res_4028_ = l_Lake_Package_barrelFacetConfig___lam__1(v_baseName_4017_, v___x_4018_, v_success_boxed_4027_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec_ref(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* v___x_4029_, lean_object* v___x_4030_, lean_object* v___x_4031_, lean_object* v_pkg_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v_baseName_4040_; lean_object* v_keyName_4041_; lean_object* v___f_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___f_4053_; uint8_t v___x_4054_; lean_object* v___x_4055_; 
v_baseName_4040_ = lean_ctor_get(v_pkg_4032_, 1);
v_keyName_4041_ = lean_ctor_get(v_pkg_4032_, 2);
lean_inc(v___x_4029_);
lean_inc_n(v_baseName_4040_, 2);
v___f_4042_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_4042_, 0, v_baseName_4040_);
lean_closure_set(v___f_4042_, 1, v___x_4029_);
v___x_4043_ = 1;
v___x_4044_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_4040_, v___x_4043_);
v___x_4045_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_4046_ = lean_string_append(v___x_4044_, v___x_4045_);
v___x_4047_ = l_Lake_Name_eraseHead(v___x_4030_);
v___x_4048_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4047_, v___x_4043_);
v___x_4049_ = lean_string_append(v___x_4046_, v___x_4048_);
lean_dec_ref(v___x_4048_);
lean_inc(v_keyName_4041_);
v___x_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4050_, 0, v_keyName_4041_);
v___x_4051_ = l_Lake_Package_keyword;
v___x_4052_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4050_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
lean_ctor_set(v___x_4052_, 2, v_pkg_4032_);
lean_ctor_set(v___x_4052_, 3, v___x_4029_);
lean_inc(v___x_4031_);
v___f_4053_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_4053_, 0, v___x_4052_);
lean_closure_set(v___f_4053_, 1, v___x_4031_);
lean_closure_set(v___f_4053_, 2, v___f_4042_);
v___x_4054_ = 0;
v___x_4055_ = l_Lake_ensureJob___redArg(v___x_4031_, v___f_4053_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4080_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
v_a_4057_ = lean_ctor_get(v___x_4055_, 1);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4059_ = v___x_4055_;
v_isShared_4060_ = v_isSharedCheck_4080_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_inc(v_a_4056_);
lean_dec(v___x_4055_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4080_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v_task_4061_; lean_object* v_kind_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4078_; 
v_task_4061_ = lean_ctor_get(v_a_4056_, 0);
v_kind_4062_ = lean_ctor_get(v_a_4056_, 1);
v_isSharedCheck_4078_ = !lean_is_exclusive(v_a_4056_);
if (v_isSharedCheck_4078_ == 0)
{
lean_object* v_unused_4079_; 
v_unused_4079_ = lean_ctor_get(v_a_4056_, 2);
lean_dec(v_unused_4079_);
v___x_4064_ = v_a_4056_;
v_isShared_4065_ = v_isSharedCheck_4078_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_kind_4062_);
lean_inc(v_task_4061_);
lean_dec(v_a_4056_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4078_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v_registeredJobs_4066_; lean_object* v_job_4068_; 
v_registeredJobs_4066_ = lean_ctor_get(v___y_4037_, 4);
if (v_isShared_4065_ == 0)
{
lean_ctor_set(v___x_4064_, 2, v___x_4049_);
v_job_4068_ = v___x_4064_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_task_4061_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v_kind_4062_);
lean_ctor_set(v_reuseFailAlloc_4077_, 2, v___x_4049_);
v_job_4068_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4075_; 
lean_ctor_set_uint8(v_job_4068_, sizeof(void*)*3, v___x_4054_);
v___x_4069_ = lean_st_ref_take(v_registeredJobs_4066_);
lean_inc_ref(v_job_4068_);
v___x_4070_ = l_Lake_Job_toOpaque___redArg(v_job_4068_);
v___x_4071_ = lean_array_push(v___x_4069_, v___x_4070_);
v___x_4072_ = lean_st_ref_put(v_registeredJobs_4066_, v___x_4071_);
v___x_4073_ = l_Lake_Job_renew___redArg(v_job_4068_);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 0, v___x_4073_);
v___x_4075_ = v___x_4059_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v___x_4073_);
lean_ctor_set(v_reuseFailAlloc_4076_, 1, v_a_4057_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_4049_);
return v___x_4055_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object* v___x_4081_, lean_object* v___x_4082_, lean_object* v___x_4083_, lean_object* v_pkg_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_Lake_Package_barrelFacetConfig___lam__2(v___x_4081_, v___x_4082_, v___x_4083_, v_pkg_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec(v___y_4086_);
return v_res_4092_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___f_4096_; 
v___x_4093_ = l_Lake_instDataKindUnit;
v___x_4094_ = l_Lake_Package_reservoirBarrelFacet;
v___x_4095_ = l_Lake_Package_optReservoirBarrelFacet;
v___f_4096_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_4096_, 0, v___x_4095_);
lean_closure_set(v___f_4096_, 1, v___x_4094_);
lean_closure_set(v___f_4096_, 2, v___x_4093_);
return v___f_4096_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_4097_; uint8_t v___x_4098_; lean_object* v___x_4099_; lean_object* v___f_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___f_4097_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_4098_ = 1;
v___x_4099_ = l_Lake_instDataKindUnit;
v___f_4100_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__0, &l_Lake_Package_barrelFacetConfig___closed__0_once, _init_l_Lake_Package_barrelFacetConfig___closed__0);
v___x_4101_ = l_Lake_Package_keyword;
v___x_4102_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
lean_ctor_set(v___x_4102_, 1, v___f_4100_);
lean_ctor_set(v___x_4102_, 2, v___x_4099_);
lean_ctor_set(v___x_4102_, 3, v___f_4097_);
lean_ctor_set_uint8(v___x_4102_, sizeof(void*)*4, v___x_4098_);
lean_ctor_set_uint8(v___x_4102_, sizeof(void*)*4 + 1, v___x_4098_);
return v___x_4102_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig(void){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__1, &l_Lake_Package_barrelFacetConfig___closed__1_once, _init_l_Lake_Package_barrelFacetConfig___closed__1);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object* v_pkg_4104_, lean_object* v_dir_4105_, lean_object* v_buildArchive_4106_, lean_object* v___x_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
uint8_t v_r_4116_; lean_object* v___y_4117_; lean_object* v_a_4121_; lean_object* v___x_4138_; 
lean_inc_ref(v_pkg_4104_);
v___x_4138_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_pkg_4104_, v___y_4113_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v_a_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
v_a_4140_ = lean_ctor_get(v___x_4138_, 1);
lean_inc(v_a_4140_);
lean_dec_ref_known(v___x_4138_, 2);
v___x_4141_ = l_Lake_defaultLakeDir;
v___x_4142_ = l_Lake_joinRelative(v_dir_4105_, v___x_4141_);
v___x_4143_ = l_Lake_joinRelative(v___x_4142_, v_buildArchive_4106_);
v___x_4144_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_4104_, v_a_4139_, v___x_4143_, v___x_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v_a_4140_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v_a_4145_; uint8_t v___x_4146_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 1);
lean_inc(v_a_4145_);
lean_dec_ref_known(v___x_4144_, 2);
v___x_4146_ = 1;
v_r_4116_ = v___x_4146_;
v___y_4117_ = v_a_4145_;
goto v___jp_4115_;
}
else
{
lean_object* v_a_4147_; 
v_a_4147_ = lean_ctor_get(v___x_4144_, 1);
lean_inc(v_a_4147_);
lean_dec_ref_known(v___x_4144_, 2);
v_a_4121_ = v_a_4147_;
goto v___jp_4120_;
}
}
else
{
lean_object* v_a_4148_; 
lean_dec_ref(v_buildArchive_4106_);
lean_dec_ref(v_dir_4105_);
lean_dec_ref(v_pkg_4104_);
v_a_4148_ = lean_ctor_get(v___x_4138_, 1);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4138_, 2);
v_a_4121_ = v_a_4148_;
goto v___jp_4120_;
}
v___jp_4115_:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4118_ = lean_box(v_r_4116_);
v___x_4119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4118_);
lean_ctor_set(v___x_4119_, 1, v___y_4117_);
return v___x_4119_;
}
v___jp_4120_:
{
lean_object* v_log_4122_; uint8_t v_action_4123_; uint8_t v_wantsRebuild_4124_; uint8_t v_canceled_4125_; lean_object* v_trace_4126_; lean_object* v_buildTime_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4137_; 
v_log_4122_ = lean_ctor_get(v_a_4121_, 0);
v_action_4123_ = lean_ctor_get_uint8(v_a_4121_, sizeof(void*)*3);
v_wantsRebuild_4124_ = lean_ctor_get_uint8(v_a_4121_, sizeof(void*)*3 + 1);
v_canceled_4125_ = lean_ctor_get_uint8(v_a_4121_, sizeof(void*)*3 + 2);
v_trace_4126_ = lean_ctor_get(v_a_4121_, 1);
v_buildTime_4127_ = lean_ctor_get(v_a_4121_, 2);
v_isSharedCheck_4137_ = !lean_is_exclusive(v_a_4121_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4129_ = v_a_4121_;
v_isShared_4130_ = v_isSharedCheck_4137_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_buildTime_4127_);
lean_inc(v_trace_4126_);
lean_inc(v_log_4122_);
lean_dec(v_a_4121_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4137_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
uint8_t v___x_4131_; uint8_t v___x_4132_; lean_object* v___x_4134_; 
v___x_4131_ = 4;
v___x_4132_ = l_Lake_JobAction_merge(v_action_4123_, v___x_4131_);
if (v_isShared_4130_ == 0)
{
v___x_4134_ = v___x_4129_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_log_4122_);
lean_ctor_set(v_reuseFailAlloc_4136_, 1, v_trace_4126_);
lean_ctor_set(v_reuseFailAlloc_4136_, 2, v_buildTime_4127_);
lean_ctor_set_uint8(v_reuseFailAlloc_4136_, sizeof(void*)*3 + 1, v_wantsRebuild_4124_);
lean_ctor_set_uint8(v_reuseFailAlloc_4136_, sizeof(void*)*3 + 2, v_canceled_4125_);
v___x_4134_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
uint8_t v___x_4135_; 
lean_ctor_set_uint8(v___x_4134_, sizeof(void*)*3, v___x_4132_);
v___x_4135_ = 0;
v_r_4116_ = v___x_4135_;
v___y_4117_ = v___x_4134_;
goto v___jp_4115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object* v_pkg_4149_, lean_object* v_dir_4150_, lean_object* v_buildArchive_4151_, lean_object* v___x_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(v_pkg_4149_, v_dir_4150_, v_buildArchive_4151_, v___x_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec_ref(v___x_4152_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(lean_object* v___x_4161_, lean_object* v___x_4162_, lean_object* v___x_4163_, lean_object* v___x_4164_, lean_object* v_pkg_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v_baseName_4173_; lean_object* v_dir_4174_; lean_object* v_buildArchive_4175_; lean_object* v___f_4176_; uint8_t v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___f_4185_; lean_object* v___x_4186_; 
v_baseName_4173_ = lean_ctor_get(v_pkg_4165_, 1);
lean_inc(v_baseName_4173_);
v_dir_4174_ = lean_ctor_get(v_pkg_4165_, 4);
lean_inc_ref(v_dir_4174_);
v_buildArchive_4175_ = lean_ctor_get(v_pkg_4165_, 22);
lean_inc_ref(v_buildArchive_4175_);
v___f_4176_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4176_, 0, v_pkg_4165_);
lean_closure_set(v___f_4176_, 1, v_dir_4174_);
lean_closure_set(v___f_4176_, 2, v_buildArchive_4175_);
lean_closure_set(v___f_4176_, 3, v___x_4161_);
v___x_4177_ = 1;
v___x_4178_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_4173_, v___x_4177_);
v___x_4179_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_4180_ = lean_string_append(v___x_4178_, v___x_4179_);
v___x_4181_ = l_Lake_Name_eraseHead(v___x_4162_);
v___x_4182_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4181_, v___x_4177_);
v___x_4183_ = lean_string_append(v___x_4180_, v___x_4182_);
lean_dec_ref(v___x_4182_);
v___x_4184_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_4163_);
v___f_4185_ = lean_alloc_closure((void*)(l_Lake_Package_optArtifactCacheFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_4185_, 0, v___x_4163_);
lean_closure_set(v___f_4185_, 1, v___f_4176_);
lean_closure_set(v___f_4185_, 2, v___x_4164_);
lean_closure_set(v___f_4185_, 3, v___x_4184_);
v___x_4186_ = l_Lake_ensureJob___redArg(v___x_4163_, v___f_4185_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4211_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
v_a_4188_ = lean_ctor_get(v___x_4186_, 1);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4190_ = v___x_4186_;
v_isShared_4191_ = v_isSharedCheck_4211_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_inc(v_a_4187_);
lean_dec(v___x_4186_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4211_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v_task_4192_; lean_object* v_kind_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4209_; 
v_task_4192_ = lean_ctor_get(v_a_4187_, 0);
v_kind_4193_ = lean_ctor_get(v_a_4187_, 1);
v_isSharedCheck_4209_ = !lean_is_exclusive(v_a_4187_);
if (v_isSharedCheck_4209_ == 0)
{
lean_object* v_unused_4210_; 
v_unused_4210_ = lean_ctor_get(v_a_4187_, 2);
lean_dec(v_unused_4210_);
v___x_4195_ = v_a_4187_;
v_isShared_4196_ = v_isSharedCheck_4209_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_kind_4193_);
lean_inc(v_task_4192_);
lean_dec(v_a_4187_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4209_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v_registeredJobs_4197_; lean_object* v_job_4199_; 
v_registeredJobs_4197_ = lean_ctor_get(v___y_4170_, 4);
if (v_isShared_4196_ == 0)
{
lean_ctor_set(v___x_4195_, 2, v___x_4183_);
v_job_4199_ = v___x_4195_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_task_4192_);
lean_ctor_set(v_reuseFailAlloc_4208_, 1, v_kind_4193_);
lean_ctor_set(v_reuseFailAlloc_4208_, 2, v___x_4183_);
v_job_4199_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4206_; 
lean_ctor_set_uint8(v_job_4199_, sizeof(void*)*3, v___x_4177_);
v___x_4200_ = lean_st_ref_take(v_registeredJobs_4197_);
lean_inc_ref(v_job_4199_);
v___x_4201_ = l_Lake_Job_toOpaque___redArg(v_job_4199_);
v___x_4202_ = lean_array_push(v___x_4200_, v___x_4201_);
v___x_4203_ = lean_st_ref_put(v_registeredJobs_4197_, v___x_4202_);
v___x_4204_ = l_Lake_Job_renew___redArg(v_job_4199_);
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 0, v___x_4204_);
v___x_4206_ = v___x_4190_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v___x_4204_);
lean_ctor_set(v_reuseFailAlloc_4207_, 1, v_a_4188_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_4183_);
return v___x_4186_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_4212_, lean_object* v___x_4213_, lean_object* v___x_4214_, lean_object* v___x_4215_, lean_object* v_pkg_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(v___x_4212_, v___x_4213_, v___x_4214_, v___x_4215_, v_pkg_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec(v___y_4218_);
return v_res_4224_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___f_4231_; 
v___x_4227_ = lean_unsigned_to_nat(0u);
v___x_4228_ = l_Lake_instDataKindBool;
v___x_4229_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_4230_ = ((lean_object*)(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0));
v___f_4231_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed), 12, 4);
lean_closure_set(v___f_4231_, 0, v___x_4230_);
lean_closure_set(v___f_4231_, 1, v___x_4229_);
lean_closure_set(v___f_4231_, 2, v___x_4228_);
lean_closure_set(v___f_4231_, 3, v___x_4227_);
return v___f_4231_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_4232_; uint8_t v___x_4233_; lean_object* v___x_4234_; lean_object* v___f_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___f_4232_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_4233_ = 1;
v___x_4234_ = l_Lake_instDataKindBool;
v___f_4235_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__1, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1);
v___x_4236_ = l_Lake_Package_keyword;
v___x_4237_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_4237_, 0, v___x_4236_);
lean_ctor_set(v___x_4237_, 1, v___f_4235_);
lean_ctor_set(v___x_4237_, 2, v___x_4234_);
lean_ctor_set(v___x_4237_, 3, v___f_4232_);
lean_ctor_set_uint8(v___x_4237_, sizeof(void*)*4, v___x_4233_);
lean_ctor_set_uint8(v___x_4237_, sizeof(void*)*4 + 1, v___x_4233_);
return v___x_4237_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__2, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* v_baseName_4240_, lean_object* v___x_4241_, uint8_t v_success_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v_a_4251_; lean_object* v_a_4252_; 
if (v_success_4242_ == 0)
{
lean_object* v_toBuildConfig_4273_; uint8_t v_verbosity_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; uint8_t v___x_4278_; 
v_toBuildConfig_4273_ = lean_ctor_get(v___y_4247_, 0);
v_verbosity_4274_ = lean_ctor_get_uint8(v_toBuildConfig_4273_, sizeof(void*)*6 + 4);
v___x_4275_ = lean_box(v_verbosity_4274_);
v___x_4276_ = lean_obj_tag_nat(v___x_4275_);
lean_dec(v___x_4275_);
v___x_4277_ = lean_unsigned_to_nat(2u);
v___x_4278_ = lean_nat_dec_eq(v___x_4276_, v___x_4277_);
if (v___x_4278_ == 0)
{
lean_object* v___x_4279_; 
lean_dec(v___x_4241_);
lean_dec(v_baseName_4240_);
v___x_4279_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_4251_ = v___x_4279_;
v_a_4252_ = v___y_4248_;
goto v___jp_4250_;
}
else
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4280_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_4281_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_4240_, v___x_4278_);
v___x_4282_ = lean_string_append(v___x_4280_, v___x_4281_);
lean_dec_ref(v___x_4281_);
v___x_4283_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_4284_ = lean_string_append(v___x_4282_, v___x_4283_);
v___x_4285_ = l_Lake_Name_eraseHead(v___x_4241_);
v___x_4286_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4285_, v___x_4278_);
v___x_4287_ = lean_string_append(v___x_4284_, v___x_4286_);
lean_dec_ref(v___x_4286_);
v___x_4288_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_4289_ = lean_string_append(v___x_4287_, v___x_4288_);
v_a_4251_ = v___x_4289_;
v_a_4252_ = v___y_4248_;
goto v___jp_4250_;
}
}
else
{
lean_object* v___x_4290_; lean_object* v___x_4291_; 
lean_dec(v___x_4241_);
lean_dec(v_baseName_4240_);
v___x_4290_ = lean_box(0);
v___x_4291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4290_);
lean_ctor_set(v___x_4291_, 1, v___y_4248_);
return v___x_4291_;
}
v___jp_4250_:
{
lean_object* v_log_4253_; uint8_t v_action_4254_; uint8_t v_wantsRebuild_4255_; uint8_t v_canceled_4256_; lean_object* v_trace_4257_; lean_object* v_buildTime_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4272_; 
v_log_4253_ = lean_ctor_get(v_a_4252_, 0);
v_action_4254_ = lean_ctor_get_uint8(v_a_4252_, sizeof(void*)*3);
v_wantsRebuild_4255_ = lean_ctor_get_uint8(v_a_4252_, sizeof(void*)*3 + 1);
v_canceled_4256_ = lean_ctor_get_uint8(v_a_4252_, sizeof(void*)*3 + 2);
v_trace_4257_ = lean_ctor_get(v_a_4252_, 1);
v_buildTime_4258_ = lean_ctor_get(v_a_4252_, 2);
v_isSharedCheck_4272_ = !lean_is_exclusive(v_a_4252_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4260_ = v_a_4252_;
v_isShared_4261_ = v_isSharedCheck_4272_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_buildTime_4258_);
lean_inc(v_trace_4257_);
lean_inc(v_log_4253_);
lean_dec(v_a_4252_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4272_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; uint8_t v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4269_; 
v___x_4262_ = ((lean_object*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0));
v___x_4263_ = lean_string_append(v___x_4262_, v_a_4251_);
lean_dec_ref(v_a_4251_);
v___x_4264_ = 3;
v___x_4265_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4265_, 0, v___x_4263_);
lean_ctor_set_uint8(v___x_4265_, sizeof(void*)*1, v___x_4264_);
v___x_4266_ = lean_array_get_size(v_log_4253_);
v___x_4267_ = lean_array_push(v_log_4253_, v___x_4265_);
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 0, v___x_4267_);
v___x_4269_ = v___x_4260_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4267_);
lean_ctor_set(v_reuseFailAlloc_4271_, 1, v_trace_4257_);
lean_ctor_set(v_reuseFailAlloc_4271_, 2, v_buildTime_4258_);
lean_ctor_set_uint8(v_reuseFailAlloc_4271_, sizeof(void*)*3, v_action_4254_);
lean_ctor_set_uint8(v_reuseFailAlloc_4271_, sizeof(void*)*3 + 1, v_wantsRebuild_4255_);
lean_ctor_set_uint8(v_reuseFailAlloc_4271_, sizeof(void*)*3 + 2, v_canceled_4256_);
v___x_4269_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
lean_object* v___x_4270_; 
v___x_4270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4270_, 0, v___x_4266_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
return v___x_4270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object* v_baseName_4292_, lean_object* v___x_4293_, lean_object* v_success_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
uint8_t v_success_boxed_4302_; lean_object* v_res_4303_; 
v_success_boxed_4302_ = lean_unbox(v_success_4294_);
v_res_4303_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(v_baseName_4292_, v___x_4293_, v_success_boxed_4302_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* v___x_4304_, lean_object* v___x_4305_, lean_object* v___x_4306_, lean_object* v_pkg_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v_baseName_4315_; lean_object* v_keyName_4316_; lean_object* v___f_4317_; uint8_t v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___f_4328_; uint8_t v___x_4329_; lean_object* v___x_4330_; 
v_baseName_4315_ = lean_ctor_get(v_pkg_4307_, 1);
v_keyName_4316_ = lean_ctor_get(v_pkg_4307_, 2);
lean_inc(v___x_4304_);
lean_inc_n(v_baseName_4315_, 2);
v___f_4317_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_4317_, 0, v_baseName_4315_);
lean_closure_set(v___f_4317_, 1, v___x_4304_);
v___x_4318_ = 1;
v___x_4319_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_4315_, v___x_4318_);
v___x_4320_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_4321_ = lean_string_append(v___x_4319_, v___x_4320_);
v___x_4322_ = l_Lake_Name_eraseHead(v___x_4305_);
v___x_4323_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_4322_, v___x_4318_);
v___x_4324_ = lean_string_append(v___x_4321_, v___x_4323_);
lean_dec_ref(v___x_4323_);
lean_inc(v_keyName_4316_);
v___x_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4325_, 0, v_keyName_4316_);
v___x_4326_ = l_Lake_Package_keyword;
v___x_4327_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4325_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
lean_ctor_set(v___x_4327_, 2, v_pkg_4307_);
lean_ctor_set(v___x_4327_, 3, v___x_4304_);
lean_inc(v___x_4306_);
v___f_4328_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_mkBuildCacheFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_4328_, 0, v___x_4327_);
lean_closure_set(v___f_4328_, 1, v___x_4306_);
lean_closure_set(v___f_4328_, 2, v___f_4317_);
v___x_4329_ = 0;
v___x_4330_ = l_Lake_ensureJob___redArg(v___x_4306_, v___f_4328_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; lean_object* v_a_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4355_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
v_a_4332_ = lean_ctor_get(v___x_4330_, 1);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4334_ = v___x_4330_;
v_isShared_4335_ = v_isSharedCheck_4355_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_a_4332_);
lean_inc(v_a_4331_);
lean_dec(v___x_4330_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4355_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v_task_4336_; lean_object* v_kind_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4353_; 
v_task_4336_ = lean_ctor_get(v_a_4331_, 0);
v_kind_4337_ = lean_ctor_get(v_a_4331_, 1);
v_isSharedCheck_4353_ = !lean_is_exclusive(v_a_4331_);
if (v_isSharedCheck_4353_ == 0)
{
lean_object* v_unused_4354_; 
v_unused_4354_ = lean_ctor_get(v_a_4331_, 2);
lean_dec(v_unused_4354_);
v___x_4339_ = v_a_4331_;
v_isShared_4340_ = v_isSharedCheck_4353_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_kind_4337_);
lean_inc(v_task_4336_);
lean_dec(v_a_4331_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4353_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v_registeredJobs_4341_; lean_object* v_job_4343_; 
v_registeredJobs_4341_ = lean_ctor_get(v___y_4312_, 4);
if (v_isShared_4340_ == 0)
{
lean_ctor_set(v___x_4339_, 2, v___x_4324_);
v_job_4343_ = v___x_4339_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_task_4336_);
lean_ctor_set(v_reuseFailAlloc_4352_, 1, v_kind_4337_);
lean_ctor_set(v_reuseFailAlloc_4352_, 2, v___x_4324_);
v_job_4343_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4350_; 
lean_ctor_set_uint8(v_job_4343_, sizeof(void*)*3, v___x_4329_);
v___x_4344_ = lean_st_ref_take(v_registeredJobs_4341_);
lean_inc_ref(v_job_4343_);
v___x_4345_ = l_Lake_Job_toOpaque___redArg(v_job_4343_);
v___x_4346_ = lean_array_push(v___x_4344_, v___x_4345_);
v___x_4347_ = lean_st_ref_put(v_registeredJobs_4341_, v___x_4346_);
v___x_4348_ = l_Lake_Job_renew___redArg(v_job_4343_);
if (v_isShared_4335_ == 0)
{
lean_ctor_set(v___x_4334_, 0, v___x_4348_);
v___x_4350_ = v___x_4334_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4348_);
lean_ctor_set(v_reuseFailAlloc_4351_, 1, v_a_4332_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_4324_);
return v___x_4330_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_4356_, lean_object* v___x_4357_, lean_object* v___x_4358_, lean_object* v_pkg_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(v___x_4356_, v___x_4357_, v___x_4358_, v_pkg_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
lean_dec_ref(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec(v___y_4362_);
lean_dec(v___y_4361_);
return v_res_4367_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___f_4371_; 
v___x_4368_ = l_Lake_instDataKindUnit;
v___x_4369_ = l_Lake_Package_gitHubReleaseFacet;
v___x_4370_ = l_Lake_Package_optGitHubReleaseFacet;
v___f_4371_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_4371_, 0, v___x_4370_);
lean_closure_set(v___f_4371_, 1, v___x_4369_);
lean_closure_set(v___f_4371_, 2, v___x_4368_);
return v___f_4371_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_4372_; uint8_t v___x_4373_; lean_object* v___x_4374_; lean_object* v___f_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___f_4372_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_4373_ = 1;
v___x_4374_ = l_Lake_instDataKindUnit;
v___f_4375_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__0, &l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0);
v___x_4376_ = l_Lake_Package_keyword;
v___x_4377_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
lean_ctor_set(v___x_4377_, 1, v___f_4375_);
lean_ctor_set(v___x_4377_, 2, v___x_4374_);
lean_ctor_set(v___x_4377_, 3, v___f_4372_);
lean_ctor_set_uint8(v___x_4377_, sizeof(void*)*4, v___x_4373_);
lean_ctor_set_uint8(v___x_4377_, sizeof(void*)*4 + 1, v___x_4373_);
return v___x_4377_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_4378_; 
v___x_4378_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__1, &l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* v_build_4379_, uint8_t v_x_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
lean_object* v_log_4388_; uint8_t v_action_4389_; uint8_t v_wantsRebuild_4390_; uint8_t v_canceled_4391_; lean_object* v_buildTime_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4401_; 
v_log_4388_ = lean_ctor_get(v___y_4386_, 0);
v_action_4389_ = lean_ctor_get_uint8(v___y_4386_, sizeof(void*)*3);
v_wantsRebuild_4390_ = lean_ctor_get_uint8(v___y_4386_, sizeof(void*)*3 + 1);
v_canceled_4391_ = lean_ctor_get_uint8(v___y_4386_, sizeof(void*)*3 + 2);
v_buildTime_4392_ = lean_ctor_get(v___y_4386_, 2);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___y_4386_);
if (v_isSharedCheck_4401_ == 0)
{
lean_object* v_unused_4402_; 
v_unused_4402_ = lean_ctor_get(v___y_4386_, 1);
lean_dec(v_unused_4402_);
v___x_4394_ = v___y_4386_;
v_isShared_4395_ = v_isSharedCheck_4401_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_buildTime_4392_);
lean_inc(v_log_4388_);
lean_dec(v___y_4386_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4401_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4396_; lean_object* v___x_4398_; 
v___x_4396_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 1, v___x_4396_);
v___x_4398_ = v___x_4394_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_log_4388_);
lean_ctor_set(v_reuseFailAlloc_4400_, 1, v___x_4396_);
lean_ctor_set(v_reuseFailAlloc_4400_, 2, v_buildTime_4392_);
lean_ctor_set_uint8(v_reuseFailAlloc_4400_, sizeof(void*)*3, v_action_4389_);
lean_ctor_set_uint8(v_reuseFailAlloc_4400_, sizeof(void*)*3 + 1, v_wantsRebuild_4390_);
lean_ctor_set_uint8(v_reuseFailAlloc_4400_, sizeof(void*)*3 + 2, v_canceled_4391_);
v___x_4398_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
lean_object* v___x_4399_; 
lean_inc_ref(v___y_4385_);
lean_inc_ref(v___y_4384_);
lean_inc(v___y_4383_);
lean_inc(v___y_4382_);
v___x_4399_ = lean_apply_7(v_build_4379_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___x_4398_, lean_box(0));
return v___x_4399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* v_build_4403_, lean_object* v_x_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
uint8_t v_x_1605__boxed_4412_; lean_object* v_res_4413_; 
v_x_1605__boxed_4412_ = lean_unbox(v_x_4404_);
v_res_4413_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(v_build_4403_, v_x_1605__boxed_4412_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
lean_dec(v___y_4406_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* v_self_4414_, lean_object* v_build_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_, lean_object* v_a_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_){
_start:
{
lean_object* v_wsIdx_4423_; lean_object* v___x_4424_; uint8_t v___x_4425_; 
v_wsIdx_4423_ = lean_ctor_get(v_self_4414_, 0);
v___x_4424_ = lean_unsigned_to_nat(0u);
v___x_4425_ = lean_nat_dec_eq(v_wsIdx_4423_, v___x_4424_);
if (v___x_4425_ == 0)
{
lean_object* v___f_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___f_4426_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4426_, 0, v_build_4415_);
v___x_4427_ = lean_box(0);
lean_inc_ref(v_a_4416_);
v___x_4428_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_4414_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_);
if (lean_obj_tag(v___x_4428_) == 0)
{
lean_object* v_a_4429_; lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4439_; 
v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
v_a_4430_ = lean_ctor_get(v___x_4428_, 1);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4432_ = v___x_4428_;
v_isShared_4433_ = v_isSharedCheck_4439_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_inc(v_a_4429_);
lean_dec(v___x_4428_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4439_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4437_; 
v___x_4434_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_4435_ = l_Lake_Job_bindM___redArg(v___x_4427_, v_a_4429_, v___f_4426_, v___x_4424_, v___x_4425_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v___x_4434_);
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 0, v___x_4435_);
v___x_4437_ = v___x_4432_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v___x_4435_);
lean_ctor_set(v_reuseFailAlloc_4438_, 1, v_a_4430_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
else
{
lean_object* v_a_4440_; lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4448_; 
lean_dec_ref(v___f_4426_);
lean_dec_ref(v_a_4416_);
v_a_4440_ = lean_ctor_get(v___x_4428_, 0);
v_a_4441_ = lean_ctor_get(v___x_4428_, 1);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4443_ = v___x_4428_;
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_inc(v_a_4440_);
lean_dec(v___x_4428_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4446_; 
if (v_isShared_4444_ == 0)
{
v___x_4446_ = v___x_4443_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4440_);
lean_ctor_set(v_reuseFailAlloc_4447_, 1, v_a_4441_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
}
else
{
uint8_t v___x_4449_; uint8_t v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
lean_dec_ref(v_self_4414_);
v___x_4449_ = 0;
v___x_4450_ = 0;
v___x_4451_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_4452_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_4452_, 0, v_a_4421_);
lean_ctor_set(v___x_4452_, 1, v___x_4451_);
lean_ctor_set(v___x_4452_, 2, v___x_4424_);
lean_ctor_set_uint8(v___x_4452_, sizeof(void*)*3, v___x_4449_);
lean_ctor_set_uint8(v___x_4452_, sizeof(void*)*3 + 1, v___x_4450_);
lean_ctor_set_uint8(v___x_4452_, sizeof(void*)*3 + 2, v___x_4450_);
lean_inc_ref(v_a_4420_);
lean_inc_ref(v_a_4419_);
lean_inc(v_a_4418_);
lean_inc(v_a_4417_);
v___x_4453_ = lean_apply_7(v_build_4415_, v_a_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v___x_4452_, lean_box(0));
if (lean_obj_tag(v___x_4453_) == 0)
{
lean_object* v_a_4454_; lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4463_; 
v_a_4454_ = lean_ctor_get(v___x_4453_, 1);
v_a_4455_ = lean_ctor_get(v___x_4453_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4453_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4457_ = v___x_4453_;
v_isShared_4458_ = v_isSharedCheck_4463_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4454_);
lean_inc(v_a_4455_);
lean_dec(v___x_4453_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4463_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v_log_4459_; lean_object* v___x_4461_; 
v_log_4459_ = lean_ctor_get(v_a_4454_, 0);
lean_inc_ref(v_log_4459_);
lean_dec(v_a_4454_);
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 1, v_log_4459_);
v___x_4461_ = v___x_4457_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_a_4455_);
lean_ctor_set(v_reuseFailAlloc_4462_, 1, v_log_4459_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
}
else
{
lean_object* v_a_4464_; lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4473_; 
v_a_4464_ = lean_ctor_get(v___x_4453_, 1);
v_a_4465_ = lean_ctor_get(v___x_4453_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4453_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4467_ = v___x_4453_;
v_isShared_4468_ = v_isSharedCheck_4473_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4464_);
lean_inc(v_a_4465_);
lean_dec(v___x_4453_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4473_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v_log_4469_; lean_object* v___x_4471_; 
v_log_4469_ = lean_ctor_get(v_a_4464_, 0);
lean_inc_ref(v_log_4469_);
lean_dec(v_a_4464_);
if (v_isShared_4468_ == 0)
{
lean_ctor_set(v___x_4467_, 1, v_log_4469_);
v___x_4471_ = v___x_4467_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4465_);
lean_ctor_set(v_reuseFailAlloc_4472_, 1, v_log_4469_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___boxed(lean_object* v_self_4474_, lean_object* v_build_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_4474_, v_build_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_);
lean_dec_ref(v_a_4480_);
lean_dec_ref(v_a_4479_);
lean_dec(v_a_4478_);
lean_dec(v_a_4477_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* v_00_u03b1_4484_, lean_object* v_self_4485_, lean_object* v_build_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
lean_object* v___x_4494_; 
v___x_4494_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_4485_, v_build_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_);
return v___x_4494_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___boxed(lean_object* v_00_u03b1_4495_, lean_object* v_self_4496_, lean_object* v_build_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l_Lake_Package_afterBuildCacheAsync(v_00_u03b1_4495_, v_self_4496_, v_build_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_);
lean_dec_ref(v_a_4502_);
lean_dec_ref(v_a_4501_);
lean_dec(v_a_4500_);
lean_dec(v_a_4499_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* v_build_4506_, uint8_t v_x_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v_log_4515_; uint8_t v_action_4516_; uint8_t v_wantsRebuild_4517_; uint8_t v_canceled_4518_; lean_object* v_buildTime_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4528_; 
v_log_4515_ = lean_ctor_get(v___y_4513_, 0);
v_action_4516_ = lean_ctor_get_uint8(v___y_4513_, sizeof(void*)*3);
v_wantsRebuild_4517_ = lean_ctor_get_uint8(v___y_4513_, sizeof(void*)*3 + 1);
v_canceled_4518_ = lean_ctor_get_uint8(v___y_4513_, sizeof(void*)*3 + 2);
v_buildTime_4519_ = lean_ctor_get(v___y_4513_, 2);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___y_4513_);
if (v_isSharedCheck_4528_ == 0)
{
lean_object* v_unused_4529_; 
v_unused_4529_ = lean_ctor_get(v___y_4513_, 1);
lean_dec(v_unused_4529_);
v___x_4521_ = v___y_4513_;
v_isShared_4522_ = v_isSharedCheck_4528_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_buildTime_4519_);
lean_inc(v_log_4515_);
lean_dec(v___y_4513_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4528_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4523_; lean_object* v___x_4525_; 
v___x_4523_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_4522_ == 0)
{
lean_ctor_set(v___x_4521_, 1, v___x_4523_);
v___x_4525_ = v___x_4521_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_log_4515_);
lean_ctor_set(v_reuseFailAlloc_4527_, 1, v___x_4523_);
lean_ctor_set(v_reuseFailAlloc_4527_, 2, v_buildTime_4519_);
lean_ctor_set_uint8(v_reuseFailAlloc_4527_, sizeof(void*)*3, v_action_4516_);
lean_ctor_set_uint8(v_reuseFailAlloc_4527_, sizeof(void*)*3 + 1, v_wantsRebuild_4517_);
lean_ctor_set_uint8(v_reuseFailAlloc_4527_, sizeof(void*)*3 + 2, v_canceled_4518_);
v___x_4525_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
lean_object* v___x_4526_; 
lean_inc_ref(v___y_4512_);
lean_inc_ref(v___y_4511_);
lean_inc(v___y_4510_);
lean_inc(v___y_4509_);
v___x_4526_ = lean_apply_7(v_build_4506_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___x_4525_, lean_box(0));
return v___x_4526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* v_build_4530_, lean_object* v_x_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
uint8_t v_x_1635__boxed_4539_; lean_object* v_res_4540_; 
v_x_1635__boxed_4539_ = lean_unbox(v_x_4531_);
v_res_4540_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(v_build_4530_, v_x_1635__boxed_4539_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
lean_dec_ref(v___y_4536_);
lean_dec_ref(v___y_4535_);
lean_dec(v___y_4534_);
lean_dec(v___y_4533_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* v_self_4541_, lean_object* v_build_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_){
_start:
{
lean_object* v_wsIdx_4550_; lean_object* v___x_4551_; uint8_t v___x_4552_; lean_object* v___x_4553_; 
v_wsIdx_4550_ = lean_ctor_get(v_self_4541_, 0);
v___x_4551_ = lean_unsigned_to_nat(0u);
v___x_4552_ = lean_nat_dec_eq(v_wsIdx_4550_, v___x_4551_);
v___x_4553_ = lean_box(0);
if (v___x_4552_ == 0)
{
lean_object* v___f_4554_; lean_object* v___x_4555_; 
v___f_4554_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_4554_, 0, v_build_4542_);
lean_inc_ref(v_a_4543_);
v___x_4555_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_4541_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4566_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
v_a_4557_ = lean_ctor_get(v___x_4555_, 1);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4559_ = v___x_4555_;
v_isShared_4560_ = v_isSharedCheck_4566_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_inc(v_a_4556_);
lean_dec(v___x_4555_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4566_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4564_; 
v___x_4561_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_4562_ = l_Lake_Job_mapM___redArg(v___x_4553_, v_a_4556_, v___f_4554_, v___x_4551_, v___x_4552_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v___x_4561_);
if (v_isShared_4560_ == 0)
{
lean_ctor_set(v___x_4559_, 0, v___x_4562_);
v___x_4564_ = v___x_4559_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4562_);
lean_ctor_set(v_reuseFailAlloc_4565_, 1, v_a_4557_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
else
{
lean_object* v_a_4567_; lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
lean_dec_ref(v___f_4554_);
lean_dec_ref(v_a_4543_);
v_a_4567_ = lean_ctor_get(v___x_4555_, 0);
v_a_4568_ = lean_ctor_get(v___x_4555_, 1);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4570_ = v___x_4555_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_inc(v_a_4567_);
lean_dec(v___x_4555_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4573_; 
if (v_isShared_4571_ == 0)
{
v___x_4573_ = v___x_4570_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4567_);
lean_ctor_set(v_reuseFailAlloc_4574_, 1, v_a_4568_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
}
else
{
lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
lean_dec_ref(v_self_4541_);
v___x_4576_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_4577_ = l_Lake_Job_async___redArg(v___x_4553_, v_build_4542_, v___x_4551_, v___x_4576_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
v___x_4578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
lean_ctor_set(v___x_4578_, 1, v_a_4548_);
return v___x_4578_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___boxed(lean_object* v_self_4579_, lean_object* v_build_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_4579_, v_build_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_);
lean_dec_ref(v_a_4585_);
lean_dec_ref(v_a_4584_);
lean_dec(v_a_4583_);
lean_dec(v_a_4582_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* v_00_u03b1_4589_, lean_object* v_self_4590_, lean_object* v_build_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_){
_start:
{
lean_object* v___x_4599_; 
v___x_4599_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_4590_, v_build_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_);
return v___x_4599_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___boxed(lean_object* v_00_u03b1_4600_, lean_object* v_self_4601_, lean_object* v_build_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_){
_start:
{
lean_object* v_res_4610_; 
v_res_4610_ = l_Lake_Package_afterBuildCacheSync(v_00_u03b1_4600_, v_self_4601_, v_build_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
lean_dec_ref(v_a_4607_);
lean_dec_ref(v_a_4606_);
lean_dec(v_a_4605_);
lean_dec(v_a_4604_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(lean_object* v_k_4611_, lean_object* v_v_4612_, lean_object* v_t_4613_){
_start:
{
if (lean_obj_tag(v_t_4613_) == 0)
{
lean_object* v_size_4614_; lean_object* v_k_4615_; lean_object* v_v_4616_; lean_object* v_l_4617_; lean_object* v_r_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4898_; 
v_size_4614_ = lean_ctor_get(v_t_4613_, 0);
v_k_4615_ = lean_ctor_get(v_t_4613_, 1);
v_v_4616_ = lean_ctor_get(v_t_4613_, 2);
v_l_4617_ = lean_ctor_get(v_t_4613_, 3);
v_r_4618_ = lean_ctor_get(v_t_4613_, 4);
v_isSharedCheck_4898_ = !lean_is_exclusive(v_t_4613_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4620_ = v_t_4613_;
v_isShared_4621_ = v_isSharedCheck_4898_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_r_4618_);
lean_inc(v_l_4617_);
lean_inc(v_v_4616_);
lean_inc(v_k_4615_);
lean_inc(v_size_4614_);
lean_dec(v_t_4613_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4898_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
uint8_t v___x_4622_; 
v___x_4622_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4611_, v_k_4615_);
switch(v___x_4622_)
{
case 0:
{
lean_object* v_impl_4623_; lean_object* v___x_4624_; 
lean_dec(v_size_4614_);
v_impl_4623_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_4611_, v_v_4612_, v_l_4617_);
v___x_4624_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_4618_) == 0)
{
lean_object* v_size_4625_; lean_object* v_size_4626_; lean_object* v_k_4627_; lean_object* v_v_4628_; lean_object* v_l_4629_; lean_object* v_r_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; uint8_t v___x_4633_; 
v_size_4625_ = lean_ctor_get(v_r_4618_, 0);
v_size_4626_ = lean_ctor_get(v_impl_4623_, 0);
v_k_4627_ = lean_ctor_get(v_impl_4623_, 1);
v_v_4628_ = lean_ctor_get(v_impl_4623_, 2);
v_l_4629_ = lean_ctor_get(v_impl_4623_, 3);
v_r_4630_ = lean_ctor_get(v_impl_4623_, 4);
lean_inc(v_r_4630_);
v___x_4631_ = lean_unsigned_to_nat(3u);
v___x_4632_ = lean_nat_mul(v___x_4631_, v_size_4625_);
v___x_4633_ = lean_nat_dec_lt(v___x_4632_, v_size_4626_);
lean_dec(v___x_4632_);
if (v___x_4633_ == 0)
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4637_; 
lean_dec(v_r_4630_);
v___x_4634_ = lean_nat_add(v___x_4624_, v_size_4626_);
v___x_4635_ = lean_nat_add(v___x_4634_, v_size_4625_);
lean_dec(v___x_4634_);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 3, v_impl_4623_);
lean_ctor_set(v___x_4620_, 0, v___x_4635_);
v___x_4637_ = v___x_4620_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4635_);
lean_ctor_set(v_reuseFailAlloc_4638_, 1, v_k_4615_);
lean_ctor_set(v_reuseFailAlloc_4638_, 2, v_v_4616_);
lean_ctor_set(v_reuseFailAlloc_4638_, 3, v_impl_4623_);
lean_ctor_set(v_reuseFailAlloc_4638_, 4, v_r_4618_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
else
{
lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4704_; 
lean_inc(v_l_4629_);
lean_inc(v_v_4628_);
lean_inc(v_k_4627_);
lean_inc(v_size_4626_);
v_isSharedCheck_4704_ = !lean_is_exclusive(v_impl_4623_);
if (v_isSharedCheck_4704_ == 0)
{
lean_object* v_unused_4705_; lean_object* v_unused_4706_; lean_object* v_unused_4707_; lean_object* v_unused_4708_; lean_object* v_unused_4709_; 
v_unused_4705_ = lean_ctor_get(v_impl_4623_, 4);
lean_dec(v_unused_4705_);
v_unused_4706_ = lean_ctor_get(v_impl_4623_, 3);
lean_dec(v_unused_4706_);
v_unused_4707_ = lean_ctor_get(v_impl_4623_, 2);
lean_dec(v_unused_4707_);
v_unused_4708_ = lean_ctor_get(v_impl_4623_, 1);
lean_dec(v_unused_4708_);
v_unused_4709_ = lean_ctor_get(v_impl_4623_, 0);
lean_dec(v_unused_4709_);
v___x_4640_ = v_impl_4623_;
v_isShared_4641_ = v_isSharedCheck_4704_;
goto v_resetjp_4639_;
}
else
{
lean_dec(v_impl_4623_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4704_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v_size_4642_; lean_object* v_size_4643_; lean_object* v_k_4644_; lean_object* v_v_4645_; lean_object* v_l_4646_; lean_object* v_r_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; uint8_t v___x_4650_; 
v_size_4642_ = lean_ctor_get(v_l_4629_, 0);
v_size_4643_ = lean_ctor_get(v_r_4630_, 0);
v_k_4644_ = lean_ctor_get(v_r_4630_, 1);
v_v_4645_ = lean_ctor_get(v_r_4630_, 2);
v_l_4646_ = lean_ctor_get(v_r_4630_, 3);
v_r_4647_ = lean_ctor_get(v_r_4630_, 4);
v___x_4648_ = lean_unsigned_to_nat(2u);
v___x_4649_ = lean_nat_mul(v___x_4648_, v_size_4642_);
v___x_4650_ = lean_nat_dec_lt(v_size_4643_, v___x_4649_);
lean_dec(v___x_4649_);
if (v___x_4650_ == 0)
{
lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4679_; 
lean_inc(v_r_4647_);
lean_inc(v_l_4646_);
lean_inc(v_v_4645_);
lean_inc(v_k_4644_);
v_isSharedCheck_4679_ = !lean_is_exclusive(v_r_4630_);
if (v_isSharedCheck_4679_ == 0)
{
lean_object* v_unused_4680_; lean_object* v_unused_4681_; lean_object* v_unused_4682_; lean_object* v_unused_4683_; lean_object* v_unused_4684_; 
v_unused_4680_ = lean_ctor_get(v_r_4630_, 4);
lean_dec(v_unused_4680_);
v_unused_4681_ = lean_ctor_get(v_r_4630_, 3);
lean_dec(v_unused_4681_);
v_unused_4682_ = lean_ctor_get(v_r_4630_, 2);
lean_dec(v_unused_4682_);
v_unused_4683_ = lean_ctor_get(v_r_4630_, 1);
lean_dec(v_unused_4683_);
v_unused_4684_ = lean_ctor_get(v_r_4630_, 0);
lean_dec(v_unused_4684_);
v___x_4652_ = v_r_4630_;
v_isShared_4653_ = v_isSharedCheck_4679_;
goto v_resetjp_4651_;
}
else
{
lean_dec(v_r_4630_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4679_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___x_4667_; lean_object* v___y_4669_; 
v___x_4654_ = lean_nat_add(v___x_4624_, v_size_4626_);
lean_dec(v_size_4626_);
v___x_4655_ = lean_nat_add(v___x_4654_, v_size_4625_);
lean_dec(v___x_4654_);
v___x_4667_ = lean_nat_add(v___x_4624_, v_size_4642_);
if (lean_obj_tag(v_l_4646_) == 0)
{
lean_object* v_size_4677_; 
v_size_4677_ = lean_ctor_get(v_l_4646_, 0);
lean_inc(v_size_4677_);
v___y_4669_ = v_size_4677_;
goto v___jp_4668_;
}
else
{
lean_object* v___x_4678_; 
v___x_4678_ = lean_unsigned_to_nat(0u);
v___y_4669_ = v___x_4678_;
goto v___jp_4668_;
}
v___jp_4656_:
{
lean_object* v___x_4660_; lean_object* v___x_4662_; 
v___x_4660_ = lean_nat_add(v___y_4657_, v___y_4659_);
lean_dec(v___y_4659_);
lean_dec(v___y_4657_);
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 4, v_r_4618_);
lean_ctor_set(v___x_4652_, 3, v_r_4647_);
lean_ctor_set(v___x_4652_, 2, v_v_4616_);
lean_ctor_set(v___x_4652_, 1, v_k_4615_);
lean_ctor_set(v___x_4652_, 0, v___x_4660_);
v___x_4662_ = v___x_4652_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4660_);
lean_ctor_set(v_reuseFailAlloc_4666_, 1, v_k_4615_);
lean_ctor_set(v_reuseFailAlloc_4666_, 2, v_v_4616_);
lean_ctor_set(v_reuseFailAlloc_4666_, 3, v_r_4647_);
lean_ctor_set(v_reuseFailAlloc_4666_, 4, v_r_4618_);
v___x_4662_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
lean_object* v___x_4664_; 
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 4, v___x_4662_);
lean_ctor_set(v___x_4640_, 3, v___y_4658_);
lean_ctor_set(v___x_4640_, 2, v_v_4645_);
lean_ctor_set(v___x_4640_, 1, v_k_4644_);
lean_ctor_set(v___x_4640_, 0, v___x_4655_);
v___x_4664_ = v___x_4640_;
goto v_reusejp_4663_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4655_);
lean_ctor_set(v_reuseFailAlloc_4665_, 1, v_k_4644_);
lean_ctor_set(v_reuseFailAlloc_4665_, 2, v_v_4645_);
lean_ctor_set(v_reuseFailAlloc_4665_, 3, v___y_4658_);
lean_ctor_set(v_reuseFailAlloc_4665_, 4, v___x_4662_);
v___x_4664_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4663_;
}
v_reusejp_4663_:
{
return v___x_4664_;
}
}
}
v___jp_4668_:
{
lean_object* v___x_4670_; lean_object* v___x_4672_; 
v___x_4670_ = lean_nat_add(v___x_4667_, v___y_4669_);
lean_dec(v___y_4669_);
lean_dec(v___x_4667_);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 4, v_l_4646_);
lean_ctor_set(v___x_4620_, 3, v_l_4629_);
lean_ctor_set(v___x_4620_, 2, v_v_4628_);
lean_ctor_set(v___x_4620_, 1, v_k_4627_);
lean_ctor_set(v___x_4620_, 0, v___x_4670_);
v___x_4672_ = v___x_4620_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4670_);
lean_ctor_set(v_reuseFailAlloc_4676_, 1, v_k_4627_);
lean_ctor_set(v_reuseFailAlloc_4676_, 2, v_v_4628_);
lean_ctor_set(v_reuseFailAlloc_4676_, 3, v_l_4629_);
lean_ctor_set(v_reuseFailAlloc_4676_, 4, v_l_4646_);
v___x_4672_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
lean_object* v___x_4673_; 
v___x_4673_ = lean_nat_add(v___x_4624_, v_size_4625_);
if (lean_obj_tag(v_r_4647_) == 0)
{
lean_object* v_size_4674_; 
v_size_4674_ = lean_ctor_get(v_r_4647_, 0);
lean_inc(v_size_4674_);
v___y_4657_ = v___x_4673_;
v___y_4658_ = v___x_4672_;
v___y_4659_ = v_size_4674_;
goto v___jp_4656_;
}
else
{
lean_object* v___x_4675_; 
v___x_4675_ = lean_unsigned_to_nat(0u);
v___y_4657_ = v___x_4673_;
v___y_4658_ = v___x_4672_;
v___y_4659_ = v___x_4675_;
goto v___jp_4656_;
}
}
}
}
}
else
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4690_; 
lean_del_object(v___x_4620_);
v___x_4685_ = lean_nat_add(v___x_4624_, v_size_4626_);
lean_dec(v_size_4626_);
v___x_4686_ = lean_nat_add(v___x_4685_, v_size_4625_);
lean_dec(v___x_4685_);
v___x_4687_ = lean_nat_add(v___x_4624_, v_size_4625_);
v___x_4688_ = lean_nat_add(v___x_4687_, v_size_4643_);
lean_dec(v___x_4687_);
lean_inc_ref(v_r_4618_);
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 4, v_r_4618_);
lean_ctor_set(v___x_4640_, 3, v_r_4630_);
lean_ctor_set(v___x_4640_, 2, v_v_4616_);
lean_ctor_set(v___x_4640_, 1, v_k_4615_);
lean_ctor_set(v___x_4640_, 0, v___x_4688_);
v___x_4690_ = v___x_4640_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v___x_4688_);
lean_ctor_set(v_reuseFailAlloc_4703_, 1, v_k_4615_);
lean_ctor_set(v_reuseFailAlloc_4703_, 2, v_v_4616_);
lean_ctor_set(v_reuseFailAlloc_4703_, 3, v_r_4630_);
lean_ctor_set(v_reuseFailAlloc_4703_, 4, v_r_4618_);
v___x_4690_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4697_; 
v_isSharedCheck_4697_ = !lean_is_exclusive(v_r_4618_);
if (v_isSharedCheck_4697_ == 0)
{
lean_object* v_unused_4698_; lean_object* v_unused_4699_; lean_object* v_unused_4700_; lean_object* v_unused_4701_; lean_object* v_unused_4702_; 
v_unused_4698_ = lean_ctor_get(v_r_4618_, 4);
lean_dec(v_unused_4698_);
v_unused_4699_ = lean_ctor_get(v_r_4618_, 3);
lean_dec(v_unused_4699_);
v_unused_4700_ = lean_ctor_get(v_r_4618_, 2);
lean_dec(v_unused_4700_);
v_unused_4701_ = lean_ctor_get(v_r_4618_, 1);
lean_dec(v_unused_4701_);
v_unused_4702_ = lean_ctor_get(v_r_4618_, 0);
lean_dec(v_unused_4702_);
v___x_4692_ = v_r_4618_;
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
else
{
lean_dec(v_r_4618_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4697_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4695_; 
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 4, v___x_4690_);
lean_ctor_set(v___x_4692_, 3, v_l_4629_);
lean_ctor_set(v___x_4692_, 2, v_v_4628_);
lean_ctor_set(v___x_4692_, 1, v_k_4627_);
lean_ctor_set(v___x_4692_, 0, v___x_4686_);
v___x_4695_ = v___x_4692_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4696_; 
v_reuseFailAlloc_4696_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4696_, 0, v___x_4686_);
lean_ctor_set(v_reuseFailAlloc_4696_, 1, v_k_4627_);
lean_ctor_set(v_reuseFailAlloc_4696_, 2, v_v_4628_);
lean_ctor_set(v_reuseFailAlloc_4696_, 3, v_l_4629_);
lean_ctor_set(v_reuseFailAlloc_4696_, 4, v___x_4690_);
v___x_4695_ = v_reuseFailAlloc_4696_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
return v___x_4695_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4710_; 
v_l_4710_ = lean_ctor_get(v_impl_4623_, 3);
if (lean_obj_tag(v_l_4710_) == 0)
{
lean_object* v_r_4711_; lean_object* v_k_4712_; lean_object* v_v_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4724_; 
lean_inc_ref(v_l_4710_);
v_r_4711_ = lean_ctor_get(v_impl_4623_, 4);
v_k_4712_ = lean_ctor_get(v_impl_4623_, 1);
v_v_4713_ = lean_ctor_get(v_impl_4623_, 2);
v_isSharedCheck_4724_ = !lean_is_exclusive(v_impl_4623_);
if (v_isSharedCheck_4724_ == 0)
{
lean_object* v_unused_4725_; lean_object* v_unused_4726_; 
v_unused_4725_ = lean_ctor_get(v_impl_4623_, 3);
lean_dec(v_unused_4725_);
v_unused_4726_ = lean_ctor_get(v_impl_4623_, 0);
lean_dec(v_unused_4726_);
v___x_4715_ = v_impl_4623_;
v_isShared_4716_ = v_isSharedCheck_4724_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_r_4711_);
lean_inc(v_v_4713_);
lean_inc(v_k_4712_);
lean_dec(v_impl_4623_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4724_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4717_; lean_object* v___x_4719_; 
v___x_4717_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_4711_);
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 3, v_r_4711_);
lean_ctor_set(v___x_4715_, 2, v_v_4616_);
lean_ctor_set(v___x_4715_, 1, v_k_4615_);
lean_ctor_set(v___x_4715_, 0, v___x_4624_);
v___x_4719_ = v___x_4715_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4624_);
lean_ctor_set(v_reuseFailAlloc_4723_, 1, v_k_4615_);
lean_ctor_set(v_reuseFailAlloc_4723_, 2, v_v_4616_);
lean_ctor_set(v_reuseFailAlloc_4723_, 3, v_r_4711_);
lean_ctor_set(v_reuseFailAlloc_4723_, 4, v_r_4711_);
v___x_4719_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
lean_object* v___x_4721_; 
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 4, v___x_4719_);
lean_ctor_set(v___x_4620_, 3, v_l_4710_);
lean_ctor_set(v___x_4620_, 2, v_v_4713_);
lean_ctor_set(v___x_4620_, 1, v_k_4712_);
lean_ctor_set(v___x_4620_, 0, v___x_4717_);
v___x_4721_ = v___x_4620_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4717_);
lean_ctor_set(v_reuseFailAlloc_4722_, 1, v_k_4712_);
lean_ctor_set(v_reuseFailAlloc_4722_, 2, v_v_4713_);
lean_ctor_set(v_reuseFailAlloc_4722_, 3, v_l_4710_);
lean_ctor_set(v_reuseFailAlloc_4722_, 4, v___x_4719_);
v___x_4721_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
return v___x_4721_;
}
}
}
}
else
{
lean_object* v_r_4727_; 
v_r_4727_ = lean_ctor_get(v_impl_4623_, 4);
lean_inc(v_r_4727_);
if (lean_obj_tag(v_r_4727_) == 0)
{
lean_object* v_k_4728_; lean_object* v_v_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4752_; 
lean_inc(v_l_4710_);
v_k_4728_ = lean_ctor_get(v_impl_4623_, 1);
v_v_4729_ = lean_ctor_get(v_impl_4623_, 2);
v_isSharedCheck_4752_ = !lean_is_exclusive(v_impl_4623_);
if (v_isSharedCheck_4752_ == 0)
{
lean_object* v_unused_4753_; lean_object* v_unused_4754_; lean_object* v_unused_4755_; 
v_unused_4753_ = lean_ctor_get(v_impl_4623_, 4);
lean_dec(v_unused_4753_);
v_unused_4754_ = lean_ctor_get(v_impl_4623_, 3);
lean_dec(v_unused_4754_);
v_unused_4755_ = lean_ctor_get(v_impl_4623_, 0);
lean_dec(v_unused_4755_);
v___x_4731_ = v_impl_4623_;
v_isShared_4732_ = v_isSharedCheck_4752_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_v_4729_);
lean_inc(v_k_4728_);
lean_dec(v_impl_4623_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4752_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v_k_4733_; lean_object* v_v_4734_; lean_object* v___x_4736_; uint8_t v_isShared_4737_; uint8_t v_isSharedCheck_4748_; 
v_k_4733_ = lean_ctor_get(v_r_4727_, 1);
v_v_4734_ = lean_ctor_get(v_r_4727_, 2);
v_isSharedCheck_4748_ = !lean_is_exclusive(v_r_4727_);
if (v_isSharedCheck_4748_ == 0)
{
lean_object* v_unused_4749_; lean_object* v_unused_4750_; lean_object* v_unused_4751_; 
v_unused_4749_ = lean_ctor_get(v_r_4727_, 4);
lean_dec(v_unused_4749_);
v_unused_4750_ = lean_ctor_get(v_r_4727_, 3);
lean_dec(v_unused_4750_);
v_unused_4751_ = lean_ctor_get(v_r_4727_, 0);
lean_dec(v_unused_4751_);
v___x_4736_ = v_r_4727_;
v_isShared_4737_ = v_isSharedCheck_4748_;
goto v_resetjp_4735_;
}
else
{
lean_inc(v_v_4734_);
lean_inc(v_k_4733_);
lean_dec(v_r_4727_);
v___x_4736_ = lean_box(0);
v_isShared_4737_ = v_isSharedCheck_4748_;
goto v_resetjp_4735_;
}
v_resetjp_4735_:
{
lean_object* v___x_4738_; lean_object* v___x_4740_; 
v___x_4738_ = lean_unsigned_to_nat(3u);
if (v_isShared_4737_ == 0)
{
lean_ctor_set(v___x_4736_, 4, v_l_4710_);
lean_ctor_set(v___x_4736_, 3, v_l_4710_);
lean_ctor_set(v___x_4736_, 2, v_v_4729_);
lean_ctor_set(v___x_4736_, 1, v_k_4728_);
lean_ctor_set(v___x_4736_, 0, v___x_4624_);
v___x_4740_ = v___x_4736_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v___x_4624_);
lean_ctor_set(v_reuseFailAlloc_4747_, 1, v_k_4728_);
lean_ctor_set(v_reuseFailAlloc_4747_, 2, v_v_4729_);
lean_ctor_set(v_reuseFailAlloc_4747_, 3, v_l_4710_);
lean_ctor_set(v_reuseFailAlloc_4747_, 4, v_l_4710_);
v___x_4740_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
lean_object* v___x_4742_; 
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 4, v_l_4710_);
lean_ctor_set(v___x_4731_, 2, v_v_4616_);
lean_ctor_set(v___x_4731_, 1, v_k_4615_);
lean_ctor_set(v___x_4731_, 0, v___x_4624_);
v___x_4742_ = v___x_4731_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v___x_4624_);
lean_ctor_set(v_reuseFailAlloc_4746_, 1, v_k_4615_);
lean_ctor_set(v_reuseFailAlloc_4746_, 2, v_v_4616_);
lean_ctor_set(v_reuseFailAlloc_4746_, 3, v_l_4710_);
lean_ctor_set(v_reuseFailAlloc_4746_, 4, v_l_4710_);
v___x_4742_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
lean_object* v___x_4744_; 
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 4, v___x_4742_);
lean_ctor_set(v___x_4620_, 3, v___x_4740_);
lean_ctor_set(v___x_4620_, 2, v_v_4734_);
lean_ctor_set(v___x_4620_, 1, v_k_4733_);
lean_ctor_set(v___x_4620_, 0, v___x_4738_);
v___x_4744_ = v___x_4620_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4738_);
lean_ctor_set(v_reuseFailAlloc_4745_, 1, v_k_4733_);
lean_ctor_set(v_reuseFailAlloc_4745_, 2, v_v_4734_);
lean_ctor_set(v_reuseFailAlloc_4745_, 3, v___x_4740_);
lean_ctor_set(v_reuseFailAlloc_4745_, 4, v___x_4742_);
v___x_4744_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
return v___x_4744_;
}
}
}
}
}
}
else
{
lean_object* v___x_4756_; lean_object* v___x_4758_; 
v___x_4756_ = lean_unsigned_to_nat(2u);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 4, v_r_4727_);
lean_ctor_set(v___x_4620_, 3, v_impl_4623_);
lean_ctor_set(v___x_4620_, 0, v___x_4756_);
v___x_4758_ = v___x_4620_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v___x_4756_);
lean_ctor_set(v_reuseFailAlloc_4759_, 1, v_k_4615_);
lean_ctor_set(v_reuseFailAlloc_4759_, 2, v_v_4616_);
lean_ctor_set(v_reuseFailAlloc_4759_, 3, v_impl_4623_);
lean_ctor_set(v_reuseFailAlloc_4759_, 4, v_r_4727_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
}
case 1:
{
lean_object* v___x_4761_; 
lean_dec(v_v_4616_);
lean_dec(v_k_4615_);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 2, v_v_4612_);
lean_ctor_set(v___x_4620_, 1, v_k_4611_);
v___x_4761_ = v___x_4620_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_size_4614_);
lean_ctor_set(v_reuseFailAlloc_4762_, 1, v_k_4611_);
lean_ctor_set(v_reuseFailAlloc_4762_, 2, v_v_4612_);
lean_ctor_set(v_reuseFailAlloc_4762_, 3, v_l_4617_);
lean_ctor_set(v_reuseFailAlloc_4762_, 4, v_r_4618_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
default: 
{
lean_object* v_impl_4763_; lean_object* v___x_4764_; 
lean_dec(v_size_4614_);
v_impl_4763_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_4611_, v_v_4612_, v_r_4618_);
v___x_4764_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_4617_) == 0)
{
lean_object* v_size_4765_; lean_object* v_size_4766_; lean_object* v_k_4767_; lean_object* v_v_4768_; lean_object* v_l_4769_; lean_object* v_r_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; uint8_t v___x_4773_; 
v_size_4765_ = lean_ctor_get(v_l_4617_, 0);
v_size_4766_ = lean_ctor_get(v_impl_4763_, 0);
v_k_4767_ = lean_ctor_get(v_impl_4763_, 1);
v_v_4768_ = lean_ctor_get(v_impl_4763_, 2);
v_l_4769_ = lean_ctor_get(v_impl_4763_, 3);
lean_inc(v_l_4769_);
v_r_4770_ = lean_ctor_get(v_impl_4763_, 4);
v___x_4771_ = lean_unsigned_to_nat(3u);
v___x_4772_ = lean_nat_mul(v___x_4771_, v_size_4765_);
v___x_4773_ = lean_nat_dec_lt(v___x_4772_, v_size_4766_);
lean_dec(v___x_4772_);
if (v___x_4773_ == 0)
{
lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4777_; 
lean_dec(v_l_4769_);
v___x_4774_ = lean_nat_add(v___x_4764_, v_size_4765_);
v___x_4775_ = lean_nat_add(v___x_4774_, v_size_4766_);
lean_dec(v___x_4774_);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 4, v_impl_4763_);
lean_ctor_set(v___x_4620_, 0, v___x_4775_);
v___x_4777_ = v___x_4620_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v___x_4775_);
lean_ctor_set(v_reuseFailAlloc_4778_, 1, v_k_4615_);
lean_ctor_set(v_reuseFailAlloc_4778_, 2, v_v_4616_);
lean_ctor_set(v_reuseFailAlloc_4778_, 3, v_l_4617_);
lean_ctor_set(v_reuseFailAlloc_4778_, 4, v_impl_4763_);
v___x_4777_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
return v___x_4777_;
}
}
else
{
lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4842_; 
lean_inc(v_r_4770_);
lean_inc(v_v_4768_);
lean_inc(v_k_4767_);
lean_inc(v_size_4766_);
v_isSharedCheck_4842_ = !lean_is_exclusive(v_impl_4763_);
if (v_isSharedCheck_4842_ == 0)
{
lean_object* v_unused_4843_; lean_object* v_unused_4844_; lean_object* v_unused_4845_; lean_object* v_unused_4846_; lean_object* v_unused_4847_; 
v_unused_4843_ = lean_ctor_get(v_impl_4763_, 4);
lean_dec(v_unused_4843_);
v_unused_4844_ = lean_ctor_get(v_impl_4763_, 3);
lean_dec(v_unused_4844_);
v_unused_4845_ = lean_ctor_get(v_impl_4763_, 2);
lean_dec(v_unused_4845_);
v_unused_4846_ = lean_ctor_get(v_impl_4763_, 1);
lean_dec(v_unused_4846_);
v_unused_4847_ = lean_ctor_get(v_impl_4763_, 0);
lean_dec(v_unused_4847_);
v___x_4780_ = v_impl_4763_;
v_isShared_4781_ = v_isSharedCheck_4842_;
goto v_resetjp_4779_;
}
else
{
lean_dec(v_impl_4763_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4842_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v_size_4782_; lean_object* v_k_4783_; lean_object* v_v_4784_; lean_object* v_l_4785_; lean_object* v_r_4786_; lean_object* v_size_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; uint8_t v___x_4790_; 
v_size_4782_ = lean_ctor_get(v_l_4769_, 0);
v_k_4783_ = lean_ctor_get(v_l_4769_, 1);
v_v_4784_ = lean_ctor_get(v_l_4769_, 2);
v_l_4785_ = lean_ctor_get(v_l_4769_, 3);
v_r_4786_ = lean_ctor_get(v_l_4769_, 4);
v_size_4787_ = lean_ctor_get(v_r_4770_, 0);
v___x_4788_ = lean_unsigned_to_nat(2u);
v___x_4789_ = lean_nat_mul(v___x_4788_, v_size_4787_);
v___x_4790_ = lean_nat_dec_lt(v_size_4782_, v___x_4789_);
lean_dec(v___x_4789_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4818_; 
lean_inc(v_r_4786_);
lean_inc(v_l_4785_);
lean_inc(v_v_4784_);
lean_inc(v_k_4783_);
v_isSharedCheck_4818_ = !lean_is_exclusive(v_l_4769_);
if (v_isSharedCheck_4818_ == 0)
{
lean_object* v_unused_4819_; lean_object* v_unused_4820_; lean_object* v_unused_4821_; lean_object* v_unused_4822_; lean_object* v_unused_4823_; 
v_unused_4819_ = lean_ctor_get(v_l_4769_, 4);
lean_dec(v_unused_4819_);
v_unused_4820_ = lean_ctor_get(v_l_4769_, 3);
lean_dec(v_unused_4820_);
v_unused_4821_ = lean_ctor_get(v_l_4769_, 2);
lean_dec(v_unused_4821_);
v_unused_4822_ = lean_ctor_get(v_l_4769_, 1);
lean_dec(v_unused_4822_);
v_unused_4823_ = lean_ctor_get(v_l_4769_, 0);
lean_dec(v_unused_4823_);
v___x_4792_ = v_l_4769_;
v_isShared_4793_ = v_isSharedCheck_4818_;
goto v_resetjp_4791_;
}
else
{
lean_dec(v_l_4769_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4818_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___y_4797_; lean_object* v___y_4798_; lean_object* v___y_4799_; lean_object* v___y_4808_; 
v___x_4794_ = lean_nat_add(v___x_4764_, v_size_4765_);
v___x_4795_ = lean_nat_add(v___x_4794_, v_size_4766_);
lean_dec(v_size_4766_);
if (lean_obj_tag(v_l_4785_) == 0)
{
lean_object* v_size_4816_; 
v_size_4816_ = lean_ctor_get(v_l_4785_, 0);
lean_inc(v_size_4816_);
v___y_4808_ = v_size_4816_;
goto v___jp_4807_;
}
else
{
lean_object* v___x_4817_; 
v___x_4817_ = lean_unsigned_to_nat(0u);
v___y_4808_ = v___x_4817_;
goto v___jp_4807_;
}
v___jp_4796_:
{
lean_object* v___x_4800_; lean_object* v___x_4802_; 
v___x_4800_ = lean_nat_add(v___y_4797_, v___y_4799_);
lean_dec(v___y_4799_);
lean_dec(v___y_4797_);
if (v_isShared_4793_ == 0)
{
lean_ctor_set(v___x_4792_, 4, v_r_4770_);
lean_ctor_set(v___x_4792_, 3, v_r_4786_);
lean_ctor_set(v___x_4792_, 2, v_v_4768_);
lean_ctor_set(v___x_4792_, 1, v_k_4767_);
lean_ctor_set(v___x_4792_, 0, v___x_4800_);
v___x_4802_ = v___x_4792_;
goto v_reusejp_4801_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v___x_4800_);
lean_ctor_set(v_reuseFailAlloc_4806_, 1, v_k_4767_);
lean_ctor_set(v_reuseFailAlloc_4806_, 2, v_v_4768_);
lean_ctor_set(v_reuseFailAlloc_4806_, 3, v_r_4786_);
lean_ctor_set(v_reuseFailAlloc_4806_, 4, v_r_4770_);
v___x_4802_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4801_;
}
v_reusejp_4801_:
{
lean_object* v___x_4804_; 
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 4, v___x_4802_);
lean_ctor_set(v___x_4780_, 3, v___y_4798_);
lean_ctor_set(v___x_4780_, 2, v_v_4784_);
lean_ctor_set(v___x_4780_, 1, v_k_4783_);
lean_ctor_set(v___x_4780_, 0, v___x_4795_);
v___x_4804_ = v___x_4780_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v___x_4795_);
lean_ctor_set(v_reuseFailAlloc_4805_, 1, v_k_4783_);
lean_ctor_set(v_reuseFailAlloc_4805_, 2, v_v_4784_);
lean_ctor_set(v_reuseFailAlloc_4805_, 3, v___y_4798_);
lean_ctor_set(v_reuseFailAlloc_4805_, 4, v___x_4802_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
v___jp_4807_:
{
lean_object* v___x_4809_; lean_object* v___x_4811_; 
v___x_4809_ = lean_nat_add(v___x_4794_, v___y_4808_);
lean_dec(v___y_4808_);
lean_dec(v___x_4794_);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 4, v_l_4785_);
lean_ctor_set(v___x_4620_, 0, v___x_4809_);
v___x_4811_ = v___x_4620_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v___x_4809_);
lean_ctor_set(v_reuseFailAlloc_4815_, 1, v_k_4615_);
lean_ctor_set(v_reuseFailAlloc_4815_, 2, v_v_4616_);
lean_ctor_set(v_reuseFailAlloc_4815_, 3, v_l_4617_);
lean_ctor_set(v_reuseFailAlloc_4815_, 4, v_l_4785_);
v___x_4811_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
lean_object* v___x_4812_; 
v___x_4812_ = lean_nat_add(v___x_4764_, v_size_4787_);
if (lean_obj_tag(v_r_4786_) == 0)
{
lean_object* v_size_4813_; 
v_size_4813_ = lean_ctor_get(v_r_4786_, 0);
lean_inc(v_size_4813_);
v___y_4797_ = v___x_4812_;
v___y_4798_ = v___x_4811_;
v___y_4799_ = v_size_4813_;
goto v___jp_4796_;
}
else
{
lean_object* v___x_4814_; 
v___x_4814_ = lean_unsigned_to_nat(0u);
v___y_4797_ = v___x_4812_;
v___y_4798_ = v___x_4811_;
v___y_4799_ = v___x_4814_;
goto v___jp_4796_;
}
}
}
}
}
else
{
lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4828_; 
lean_del_object(v___x_4620_);
v___x_4824_ = lean_nat_add(v___x_4764_, v_size_4765_);
v___x_4825_ = lean_nat_add(v___x_4824_, v_size_4766_);
lean_dec(v_size_4766_);
v___x_4826_ = lean_nat_add(v___x_4824_, v_size_4782_);
lean_dec(v___x_4824_);
lean_inc_ref(v_l_4617_);
if (v_isShared_4781_ == 0)
{
lean_ctor_set(v___x_4780_, 4, v_l_4769_);
lean_ctor_set(v___x_4780_, 3, v_l_4617_);
lean_ctor_set(v___x_4780_, 2, v_v_4616_);
lean_ctor_set(v___x_4780_, 1, v_k_4615_);
lean_ctor_set(v___x_4780_, 0, v___x_4826_);
v___x_4828_ = v___x_4780_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4826_);
lean_ctor_set(v_reuseFailAlloc_4841_, 1, v_k_4615_);
lean_ctor_set(v_reuseFailAlloc_4841_, 2, v_v_4616_);
lean_ctor_set(v_reuseFailAlloc_4841_, 3, v_l_4617_);
lean_ctor_set(v_reuseFailAlloc_4841_, 4, v_l_4769_);
v___x_4828_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4835_; 
v_isSharedCheck_4835_ = !lean_is_exclusive(v_l_4617_);
if (v_isSharedCheck_4835_ == 0)
{
lean_object* v_unused_4836_; lean_object* v_unused_4837_; lean_object* v_unused_4838_; lean_object* v_unused_4839_; lean_object* v_unused_4840_; 
v_unused_4836_ = lean_ctor_get(v_l_4617_, 4);
lean_dec(v_unused_4836_);
v_unused_4837_ = lean_ctor_get(v_l_4617_, 3);
lean_dec(v_unused_4837_);
v_unused_4838_ = lean_ctor_get(v_l_4617_, 2);
lean_dec(v_unused_4838_);
v_unused_4839_ = lean_ctor_get(v_l_4617_, 1);
lean_dec(v_unused_4839_);
v_unused_4840_ = lean_ctor_get(v_l_4617_, 0);
lean_dec(v_unused_4840_);
v___x_4830_ = v_l_4617_;
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
else
{
lean_dec(v_l_4617_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
lean_ctor_set(v___x_4830_, 4, v_r_4770_);
lean_ctor_set(v___x_4830_, 3, v___x_4828_);
lean_ctor_set(v___x_4830_, 2, v_v_4768_);
lean_ctor_set(v___x_4830_, 1, v_k_4767_);
lean_ctor_set(v___x_4830_, 0, v___x_4825_);
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v___x_4825_);
lean_ctor_set(v_reuseFailAlloc_4834_, 1, v_k_4767_);
lean_ctor_set(v_reuseFailAlloc_4834_, 2, v_v_4768_);
lean_ctor_set(v_reuseFailAlloc_4834_, 3, v___x_4828_);
lean_ctor_set(v_reuseFailAlloc_4834_, 4, v_r_4770_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_4848_; 
v_l_4848_ = lean_ctor_get(v_impl_4763_, 3);
lean_inc(v_l_4848_);
if (lean_obj_tag(v_l_4848_) == 0)
{
lean_object* v_r_4849_; lean_object* v_k_4850_; lean_object* v_v_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4874_; 
v_r_4849_ = lean_ctor_get(v_impl_4763_, 4);
v_k_4850_ = lean_ctor_get(v_impl_4763_, 1);
v_v_4851_ = lean_ctor_get(v_impl_4763_, 2);
v_isSharedCheck_4874_ = !lean_is_exclusive(v_impl_4763_);
if (v_isSharedCheck_4874_ == 0)
{
lean_object* v_unused_4875_; lean_object* v_unused_4876_; 
v_unused_4875_ = lean_ctor_get(v_impl_4763_, 3);
lean_dec(v_unused_4875_);
v_unused_4876_ = lean_ctor_get(v_impl_4763_, 0);
lean_dec(v_unused_4876_);
v___x_4853_ = v_impl_4763_;
v_isShared_4854_ = v_isSharedCheck_4874_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_r_4849_);
lean_inc(v_v_4851_);
lean_inc(v_k_4850_);
lean_dec(v_impl_4763_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4874_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v_k_4855_; lean_object* v_v_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4870_; 
v_k_4855_ = lean_ctor_get(v_l_4848_, 1);
v_v_4856_ = lean_ctor_get(v_l_4848_, 2);
v_isSharedCheck_4870_ = !lean_is_exclusive(v_l_4848_);
if (v_isSharedCheck_4870_ == 0)
{
lean_object* v_unused_4871_; lean_object* v_unused_4872_; lean_object* v_unused_4873_; 
v_unused_4871_ = lean_ctor_get(v_l_4848_, 4);
lean_dec(v_unused_4871_);
v_unused_4872_ = lean_ctor_get(v_l_4848_, 3);
lean_dec(v_unused_4872_);
v_unused_4873_ = lean_ctor_get(v_l_4848_, 0);
lean_dec(v_unused_4873_);
v___x_4858_ = v_l_4848_;
v_isShared_4859_ = v_isSharedCheck_4870_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_v_4856_);
lean_inc(v_k_4855_);
lean_dec(v_l_4848_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4870_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4860_; lean_object* v___x_4862_; 
v___x_4860_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_4849_, 2);
if (v_isShared_4859_ == 0)
{
lean_ctor_set(v___x_4858_, 4, v_r_4849_);
lean_ctor_set(v___x_4858_, 3, v_r_4849_);
lean_ctor_set(v___x_4858_, 2, v_v_4616_);
lean_ctor_set(v___x_4858_, 1, v_k_4615_);
lean_ctor_set(v___x_4858_, 0, v___x_4764_);
v___x_4862_ = v___x_4858_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v___x_4764_);
lean_ctor_set(v_reuseFailAlloc_4869_, 1, v_k_4615_);
lean_ctor_set(v_reuseFailAlloc_4869_, 2, v_v_4616_);
lean_ctor_set(v_reuseFailAlloc_4869_, 3, v_r_4849_);
lean_ctor_set(v_reuseFailAlloc_4869_, 4, v_r_4849_);
v___x_4862_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
lean_object* v___x_4864_; 
lean_inc(v_r_4849_);
if (v_isShared_4854_ == 0)
{
lean_ctor_set(v___x_4853_, 3, v_r_4849_);
lean_ctor_set(v___x_4853_, 0, v___x_4764_);
v___x_4864_ = v___x_4853_;
goto v_reusejp_4863_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v___x_4764_);
lean_ctor_set(v_reuseFailAlloc_4868_, 1, v_k_4850_);
lean_ctor_set(v_reuseFailAlloc_4868_, 2, v_v_4851_);
lean_ctor_set(v_reuseFailAlloc_4868_, 3, v_r_4849_);
lean_ctor_set(v_reuseFailAlloc_4868_, 4, v_r_4849_);
v___x_4864_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4863_;
}
v_reusejp_4863_:
{
lean_object* v___x_4866_; 
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 4, v___x_4864_);
lean_ctor_set(v___x_4620_, 3, v___x_4862_);
lean_ctor_set(v___x_4620_, 2, v_v_4856_);
lean_ctor_set(v___x_4620_, 1, v_k_4855_);
lean_ctor_set(v___x_4620_, 0, v___x_4860_);
v___x_4866_ = v___x_4620_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v___x_4860_);
lean_ctor_set(v_reuseFailAlloc_4867_, 1, v_k_4855_);
lean_ctor_set(v_reuseFailAlloc_4867_, 2, v_v_4856_);
lean_ctor_set(v_reuseFailAlloc_4867_, 3, v___x_4862_);
lean_ctor_set(v_reuseFailAlloc_4867_, 4, v___x_4864_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
}
}
else
{
lean_object* v_r_4877_; 
v_r_4877_ = lean_ctor_get(v_impl_4763_, 4);
lean_inc(v_r_4877_);
if (lean_obj_tag(v_r_4877_) == 0)
{
lean_object* v_k_4878_; lean_object* v_v_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4890_; 
v_k_4878_ = lean_ctor_get(v_impl_4763_, 1);
v_v_4879_ = lean_ctor_get(v_impl_4763_, 2);
v_isSharedCheck_4890_ = !lean_is_exclusive(v_impl_4763_);
if (v_isSharedCheck_4890_ == 0)
{
lean_object* v_unused_4891_; lean_object* v_unused_4892_; lean_object* v_unused_4893_; 
v_unused_4891_ = lean_ctor_get(v_impl_4763_, 4);
lean_dec(v_unused_4891_);
v_unused_4892_ = lean_ctor_get(v_impl_4763_, 3);
lean_dec(v_unused_4892_);
v_unused_4893_ = lean_ctor_get(v_impl_4763_, 0);
lean_dec(v_unused_4893_);
v___x_4881_ = v_impl_4763_;
v_isShared_4882_ = v_isSharedCheck_4890_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_v_4879_);
lean_inc(v_k_4878_);
lean_dec(v_impl_4763_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4890_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4883_; lean_object* v___x_4885_; 
v___x_4883_ = lean_unsigned_to_nat(3u);
if (v_isShared_4882_ == 0)
{
lean_ctor_set(v___x_4881_, 4, v_l_4848_);
lean_ctor_set(v___x_4881_, 2, v_v_4616_);
lean_ctor_set(v___x_4881_, 1, v_k_4615_);
lean_ctor_set(v___x_4881_, 0, v___x_4764_);
v___x_4885_ = v___x_4881_;
goto v_reusejp_4884_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v___x_4764_);
lean_ctor_set(v_reuseFailAlloc_4889_, 1, v_k_4615_);
lean_ctor_set(v_reuseFailAlloc_4889_, 2, v_v_4616_);
lean_ctor_set(v_reuseFailAlloc_4889_, 3, v_l_4848_);
lean_ctor_set(v_reuseFailAlloc_4889_, 4, v_l_4848_);
v___x_4885_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4884_;
}
v_reusejp_4884_:
{
lean_object* v___x_4887_; 
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 4, v_r_4877_);
lean_ctor_set(v___x_4620_, 3, v___x_4885_);
lean_ctor_set(v___x_4620_, 2, v_v_4879_);
lean_ctor_set(v___x_4620_, 1, v_k_4878_);
lean_ctor_set(v___x_4620_, 0, v___x_4883_);
v___x_4887_ = v___x_4620_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4883_);
lean_ctor_set(v_reuseFailAlloc_4888_, 1, v_k_4878_);
lean_ctor_set(v_reuseFailAlloc_4888_, 2, v_v_4879_);
lean_ctor_set(v_reuseFailAlloc_4888_, 3, v___x_4885_);
lean_ctor_set(v_reuseFailAlloc_4888_, 4, v_r_4877_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
else
{
lean_object* v___x_4894_; lean_object* v___x_4896_; 
v___x_4894_ = lean_unsigned_to_nat(2u);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 4, v_impl_4763_);
lean_ctor_set(v___x_4620_, 3, v_r_4877_);
lean_ctor_set(v___x_4620_, 0, v___x_4894_);
v___x_4896_ = v___x_4620_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v___x_4894_);
lean_ctor_set(v_reuseFailAlloc_4897_, 1, v_k_4615_);
lean_ctor_set(v_reuseFailAlloc_4897_, 2, v_v_4616_);
lean_ctor_set(v_reuseFailAlloc_4897_, 3, v_r_4877_);
lean_ctor_set(v_reuseFailAlloc_4897_, 4, v_impl_4763_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
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
lean_object* v___x_4899_; lean_object* v___x_4900_; 
v___x_4899_ = lean_unsigned_to_nat(1u);
v___x_4900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4900_, 0, v___x_4899_);
lean_ctor_set(v___x_4900_, 1, v_k_4611_);
lean_ctor_set(v___x_4900_, 2, v_v_4612_);
lean_ctor_set(v___x_4900_, 3, v_t_4613_);
lean_ctor_set(v___x_4900_, 4, v_t_4613_);
return v___x_4900_;
}
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4901_ = lean_box(1);
v___x_4902_ = l_Lake_Package_depsFacetConfig;
v___x_4903_ = l_Lake_Package_depsFacet;
v___x_4904_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4903_, v___x_4902_, v___x_4901_);
return v___x_4904_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; 
v___x_4905_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__0, &l_Lake_Package_initFacetConfigs___closed__0_once, _init_l_Lake_Package_initFacetConfigs___closed__0);
v___x_4906_ = l_Lake_Package_transDepsFacetConfig;
v___x_4907_ = l_Lake_Package_transDepsFacet;
v___x_4908_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4907_, v___x_4906_, v___x_4905_);
return v___x_4908_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4909_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__1, &l_Lake_Package_initFacetConfigs___closed__1_once, _init_l_Lake_Package_initFacetConfigs___closed__1);
v___x_4910_ = l_Lake_Package_defaultModulesFacetConfig;
v___x_4911_ = l_Lake_Package_defaultModulesFacet;
v___x_4912_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4911_, v___x_4910_, v___x_4909_);
return v___x_4912_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
v___x_4913_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__2, &l_Lake_Package_initFacetConfigs___closed__2_once, _init_l_Lake_Package_initFacetConfigs___closed__2);
v___x_4914_ = l_Lake_Package_extraDepFacetConfig;
v___x_4915_ = l_Lake_Package_extraDepFacet;
v___x_4916_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4915_, v___x_4914_, v___x_4913_);
return v___x_4916_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4917_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__3, &l_Lake_Package_initFacetConfigs___closed__3_once, _init_l_Lake_Package_initFacetConfigs___closed__3);
v___x_4918_ = l_Lake_Package_optBuildCacheFacetConfig;
v___x_4919_ = l_Lake_Package_optBuildCacheFacet;
v___x_4920_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4919_, v___x_4918_, v___x_4917_);
return v___x_4920_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; 
v___x_4921_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__4, &l_Lake_Package_initFacetConfigs___closed__4_once, _init_l_Lake_Package_initFacetConfigs___closed__4);
v___x_4922_ = l_Lake_Package_buildCacheFacetConfig;
v___x_4923_ = l_Lake_Package_buildCacheFacet;
v___x_4924_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4923_, v___x_4922_, v___x_4921_);
return v___x_4924_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4925_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__5, &l_Lake_Package_initFacetConfigs___closed__5_once, _init_l_Lake_Package_initFacetConfigs___closed__5);
v___x_4926_ = l_Lake_Package_optArtifactCacheFacetConfig;
v___x_4927_ = l_Lake_Package_optArtifactCacheFacet;
v___x_4928_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4927_, v___x_4926_, v___x_4925_);
return v___x_4928_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; 
v___x_4929_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__6, &l_Lake_Package_initFacetConfigs___closed__6_once, _init_l_Lake_Package_initFacetConfigs___closed__6);
v___x_4930_ = l_Lake_Package_artifactCacheFacetConfig;
v___x_4931_ = l_Lake_Package_artifactCacheFacet;
v___x_4932_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4931_, v___x_4930_, v___x_4929_);
return v___x_4932_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4933_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__7, &l_Lake_Package_initFacetConfigs___closed__7_once, _init_l_Lake_Package_initFacetConfigs___closed__7);
v___x_4934_ = l_Lake_Package_optBarrelFacetConfig;
v___x_4935_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_4936_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4935_, v___x_4934_, v___x_4933_);
return v___x_4936_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__9(void){
_start:
{
lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___x_4937_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__8, &l_Lake_Package_initFacetConfigs___closed__8_once, _init_l_Lake_Package_initFacetConfigs___closed__8);
v___x_4938_ = l_Lake_Package_barrelFacetConfig;
v___x_4939_ = l_Lake_Package_reservoirBarrelFacet;
v___x_4940_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4939_, v___x_4938_, v___x_4937_);
return v___x_4940_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__10(void){
_start:
{
lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4941_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__9, &l_Lake_Package_initFacetConfigs___closed__9_once, _init_l_Lake_Package_initFacetConfigs___closed__9);
v___x_4942_ = l_Lake_Package_optGitHubReleaseFacetConfig;
v___x_4943_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_4944_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4943_, v___x_4942_, v___x_4941_);
return v___x_4944_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__11(void){
_start:
{
lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
v___x_4945_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__10, &l_Lake_Package_initFacetConfigs___closed__10_once, _init_l_Lake_Package_initFacetConfigs___closed__10);
v___x_4946_ = l_Lake_Package_gitHubReleaseFacetConfig;
v___x_4947_ = l_Lake_Package_gitHubReleaseFacet;
v___x_4948_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_4947_, v___x_4946_, v___x_4945_);
return v___x_4948_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs(void){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__11, &l_Lake_Package_initFacetConfigs___closed__11_once, _init_l_Lake_Package_initFacetConfigs___closed__11);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(lean_object* v_00_u03b2_4950_, lean_object* v_k_4951_, lean_object* v_v_4952_, lean_object* v_t_4953_, lean_object* v_hl_4954_){
_start:
{
lean_object* v___x_4955_; 
v___x_4955_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_4951_, v_v_4952_, v_t_4953_);
return v___x_4955_;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs(void){
_start:
{
lean_object* v___x_4956_; 
v___x_4956_ = l_Lake_Package_initFacetConfigs;
return v___x_4956_;
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
l_Lake_Package_optArtifactCacheFacetConfig = _init_l_Lake_Package_optArtifactCacheFacetConfig();
lean_mark_persistent(l_Lake_Package_optArtifactCacheFacetConfig);
l_Lake_Package_buildCacheFacetConfig = _init_l_Lake_Package_buildCacheFacetConfig();
lean_mark_persistent(l_Lake_Package_buildCacheFacetConfig);
l_Lake_Package_artifactCacheFacetConfig = _init_l_Lake_Package_artifactCacheFacetConfig();
lean_mark_persistent(l_Lake_Package_artifactCacheFacetConfig);
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
