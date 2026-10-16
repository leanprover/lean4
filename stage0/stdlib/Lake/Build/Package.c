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
lean_object* lean_obj_tag_nat(lean_object*);
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
lean_dec(v___y_372_);
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
lean_dec(v___y_435_);
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
lean_dec(v_a_459_);
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
lean_inc(v___y_691_);
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
lean_inc(v___y_691_);
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
lean_dec(v___y_811_);
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
size_t v_sz_boxed_882_; size_t v___x_15377__boxed_883_; lean_object* v_res_884_; 
v_sz_boxed_882_ = lean_unbox_usize(v_sz_870_);
lean_dec(v_sz_870_);
v___x_15377__boxed_883_ = lean_unbox_usize(v___x_871_);
lean_dec(v___x_871_);
v_res_884_ = l___private_Lake_Build_Package_0__Lake_Package_recCollectDefaultModules___lam__0(v_self_868_, v_defaultTargets_869_, v_sz_boxed_882_, v___x_15377__boxed_883_, v___x_872_, v___x_873_, v___x_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
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
lean_dec(v_a_917_);
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
lean_dec(v___y_955_);
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
v_preferReleaseBuild_1081_ = lean_ctor_get_uint8(v_config_1080_, sizeof(void*)*28 + 2);
if (v_preferReleaseBuild_1081_ == 0)
{
lean_object* v_keyName_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_keyName_1082_ = lean_ctor_get(v_self_1072_, 2);
v___x_1083_ = l_Lake_Package_optReservoirBarrelFacet;
lean_inc(v_keyName_1082_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v_keyName_1082_);
v___x_1085_ = l_Lake_Package_keyword;
v___x_1086_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
lean_ctor_set(v___x_1086_, 2, v_self_1072_);
lean_ctor_set(v___x_1086_, 3, v___x_1083_);
lean_inc_ref(v_a_1077_);
lean_inc(v_a_1076_);
lean_inc(v_a_1075_);
lean_inc(v_a_1074_);
v___x_1087_ = lean_apply_7(v_a_1073_, v___x_1086_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, lean_box(0));
return v___x_1087_;
}
else
{
lean_object* v_keyName_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_keyName_1088_ = lean_ctor_get(v_self_1072_, 2);
v___x_1089_ = l_Lake_Package_optGitHubReleaseFacet;
lean_inc(v_keyName_1088_);
v___x_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1090_, 0, v_keyName_1088_);
v___x_1091_ = l_Lake_Package_keyword;
v___x_1092_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
lean_ctor_set(v___x_1092_, 2, v_self_1072_);
lean_ctor_set(v___x_1092_, 3, v___x_1089_);
lean_inc_ref(v_a_1077_);
lean_inc(v_a_1076_);
lean_inc(v_a_1075_);
lean_inc(v_a_1074_);
v___x_1093_ = lean_apply_7(v_a_1073_, v___x_1092_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, lean_box(0));
return v___x_1093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore___boxed(lean_object* v_self_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l___private_Lake_Build_Package_0__Lake_Package_fetchOptBuildCacheCore(v_self_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec(v_a_1096_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(uint8_t v_fmt_1105_, uint8_t v_a_1106_){
_start:
{
if (v_fmt_1105_ == 0)
{
if (v_a_1106_ == 0)
{
lean_object* v___x_1107_; 
v___x_1107_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__0));
return v___x_1107_;
}
else
{
lean_object* v___x_1108_; 
v___x_1108_ = ((lean_object*)(l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___closed__1));
return v___x_1108_;
}
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1109_, 0, v_a_1106_);
v___x_1110_ = l_Lean_Json_compress(v___x_1109_);
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0___boxed(lean_object* v_fmt_1111_, lean_object* v_a_1112_){
_start:
{
uint8_t v_fmt_boxed_1113_; uint8_t v_a_boxed_1114_; lean_object* v_res_1115_; 
v_fmt_boxed_1113_ = lean_unbox(v_fmt_1111_);
v_a_boxed_1114_ = lean_unbox(v_a_1112_);
v_res_1115_ = l_Lake_formatQuery___at___00Lake_Package_optBuildCacheFacetConfig_spec__0(v_fmt_boxed_1113_, v_a_boxed_1114_);
return v_res_1115_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1118_; uint8_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___f_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___f_1118_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_1119_ = 1;
v___x_1120_ = l_Lake_instDataKindBool;
v___f_1121_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__0));
v___x_1122_ = l_Lake_Package_keyword;
v___x_1123_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
lean_ctor_set(v___x_1123_, 1, v___f_1121_);
lean_ctor_set(v___x_1123_, 2, v___x_1120_);
lean_ctor_set(v___x_1123_, 3, v___f_1118_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*4, v___x_1119_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*4 + 1, v___x_1119_);
return v___x_1123_;
}
}
static lean_object* _init_l_Lake_Package_optBuildCacheFacetConfig(void){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_obj_once(&l_Lake_Package_optBuildCacheFacetConfig___closed__2, &l_Lake_Package_optBuildCacheFacetConfig___closed__2_once, _init_l_Lake_Package_optBuildCacheFacetConfig___closed__2);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(lean_object* v_self_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v___y_1136_; uint8_t v___y_1137_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1160_; uint8_t v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v_toContext_1167_; lean_object* v_lakeEnv_1168_; uint8_t v_noCache_1169_; lean_object* v_toolchain_1170_; uint8_t v_a_1172_; lean_object* v_a_1173_; 
v_toContext_1167_ = lean_ctor_get(v_a_1132_, 1);
v_lakeEnv_1168_ = lean_ctor_get(v_toContext_1167_, 0);
v_noCache_1169_ = lean_ctor_get_uint8(v_lakeEnv_1168_, sizeof(void*)*20);
v_toolchain_1170_ = lean_ctor_get(v_lakeEnv_1168_, 19);
if (v_noCache_1169_ == 0)
{
uint8_t v___x_1188_; 
v___x_1188_ = 1;
v_a_1172_ = v___x_1188_;
v_a_1173_ = v_a_1133_;
goto v___jp_1171_;
}
else
{
uint8_t v___x_1189_; 
v___x_1189_ = 0;
v_a_1172_ = v___x_1189_;
v_a_1173_ = v_a_1133_;
goto v___jp_1171_;
}
v___jp_1135_:
{
uint8_t v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1138_ = 1;
v___x_1139_ = lean_box(0);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1142_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1143_ = 0;
v___x_1144_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_1145_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1145_, 0, v___x_1141_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
lean_ctor_set(v___x_1145_, 2, v___x_1140_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*3, v___x_1143_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*3 + 1, v___y_1137_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*3 + 2, v___y_1137_);
v___x_1146_ = lean_box(v___x_1138_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v___x_1145_);
v___x_1148_ = lean_task_pure(v___x_1147_);
v___x_1149_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
lean_ctor_set(v___x_1149_, 1, v___x_1139_);
lean_ctor_set(v___x_1149_, 2, v___x_1142_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*3, v___y_1137_);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
lean_ctor_set(v___x_1150_, 1, v___y_1136_);
return v___x_1150_;
}
v___jp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1154_ = l_Lake_Package_optBuildCacheFacet;
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___y_1153_);
v___x_1156_ = l_Lake_Package_keyword;
v___x_1157_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1155_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
lean_ctor_set(v___x_1157_, 2, v_self_1127_);
lean_ctor_set(v___x_1157_, 3, v___x_1154_);
lean_inc_ref(v_a_1132_);
lean_inc(v_a_1131_);
lean_inc(v_a_1130_);
lean_inc(v_a_1129_);
v___x_1158_ = lean_apply_7(v_a_1128_, v___x_1157_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v___y_1152_, lean_box(0));
return v___x_1158_;
}
v___jp_1159_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1164_ = lean_string_utf8_byte_size(v___y_1163_);
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = lean_nat_dec_eq(v___x_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
v___y_1152_ = v___y_1160_;
v___y_1153_ = v___y_1162_;
goto v___jp_1151_;
}
else
{
lean_dec(v___y_1162_);
lean_dec_ref(v_a_1128_);
lean_dec_ref(v_self_1127_);
v___y_1136_ = v___y_1160_;
v___y_1137_ = v___y_1161_;
goto v___jp_1135_;
}
}
v___jp_1171_:
{
lean_object* v_config_1174_; lean_object* v_keyName_1175_; lean_object* v_dir_1176_; lean_object* v_scope_1177_; lean_object* v_buildDir_1178_; uint8_t v_preferReleaseBuild_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v_config_1174_ = lean_ctor_get(v_self_1127_, 6);
v_keyName_1175_ = lean_ctor_get(v_self_1127_, 2);
v_dir_1176_ = lean_ctor_get(v_self_1127_, 4);
v_scope_1177_ = lean_ctor_get(v_self_1127_, 10);
v_buildDir_1178_ = lean_ctor_get(v_config_1174_, 5);
v_preferReleaseBuild_1179_ = lean_ctor_get_uint8(v_config_1174_, sizeof(void*)*28 + 2);
lean_inc_ref(v_buildDir_1178_);
v___x_1180_ = l_System_FilePath_normalize(v_buildDir_1178_);
lean_inc_ref(v_dir_1176_);
v___x_1181_ = l_Lake_joinRelative(v_dir_1176_, v___x_1180_);
v___x_1182_ = l_System_FilePath_pathExists(v___x_1181_);
lean_dec_ref(v___x_1181_);
if (v_a_1172_ == 0)
{
lean_dec_ref(v_a_1128_);
lean_dec_ref(v_self_1127_);
v___y_1136_ = v_a_1173_;
v___y_1137_ = v_a_1172_;
goto v___jp_1135_;
}
else
{
if (v___x_1182_ == 0)
{
if (v_preferReleaseBuild_1179_ == 0)
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__0));
v___x_1184_ = lean_string_dec_eq(v_scope_1177_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1185_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___closed__1));
v___x_1186_ = lean_string_dec_eq(v_scope_1177_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_dec_ref(v_a_1128_);
lean_dec_ref(v_self_1127_);
v___y_1136_ = v_a_1173_;
v___y_1137_ = v___x_1186_;
goto v___jp_1135_;
}
else
{
lean_inc(v_keyName_1175_);
v___y_1160_ = v_a_1173_;
v___y_1161_ = v_preferReleaseBuild_1179_;
v___y_1162_ = v_keyName_1175_;
v___y_1163_ = v_toolchain_1170_;
goto v___jp_1159_;
}
}
else
{
lean_inc(v_keyName_1175_);
v___y_1160_ = v_a_1173_;
v___y_1161_ = v_preferReleaseBuild_1179_;
v___y_1162_ = v_keyName_1175_;
v___y_1163_ = v_toolchain_1170_;
goto v___jp_1159_;
}
}
else
{
lean_inc(v_keyName_1175_);
v___y_1152_ = v_a_1173_;
v___y_1153_ = v_keyName_1175_;
goto v___jp_1151_;
}
}
else
{
uint8_t v___x_1187_; 
lean_dec_ref(v_a_1128_);
lean_dec_ref(v_self_1127_);
v___x_1187_ = 0;
v___y_1136_ = v_a_1173_;
v___y_1137_ = v___x_1187_;
goto v___jp_1135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache___boxed(lean_object* v_self_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
lean_dec_ref(v_a_1195_);
lean_dec(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec(v_a_1192_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(lean_object* v_self_1203_, lean_object* v_facet_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_toBuildConfig_1208_; uint8_t v_verbosity_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v_toBuildConfig_1208_ = lean_ctor_get(v_a_1205_, 0);
v_verbosity_1209_ = lean_ctor_get_uint8(v_toBuildConfig_1208_, sizeof(void*)*5 + 4);
v___x_1210_ = lean_box(v_verbosity_1209_);
v___x_1211_ = lean_obj_tag_nat(v___x_1210_);
lean_dec(v___x_1210_);
v___x_1212_ = lean_unsigned_to_nat(2u);
v___x_1213_ = lean_nat_dec_eq(v___x_1211_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec(v_facet_1204_);
lean_dec_ref(v_self_1203_);
v___x_1214_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v_a_1206_);
return v___x_1215_;
}
else
{
lean_object* v_baseName_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_baseName_1216_ = lean_ctor_get(v_self_1203_, 1);
lean_inc(v_baseName_1216_);
lean_dec_ref(v_self_1203_);
v___x_1217_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1218_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1216_, v___x_1213_);
v___x_1219_ = lean_string_append(v___x_1217_, v___x_1218_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1221_ = lean_string_append(v___x_1219_, v___x_1220_);
v___x_1222_ = l_Lake_Name_eraseHead(v_facet_1204_);
v___x_1223_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1222_, v___x_1213_);
v___x_1224_ = lean_string_append(v___x_1221_, v___x_1223_);
lean_dec_ref(v___x_1223_);
v___x_1225_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1226_ = lean_string_append(v___x_1224_, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v_a_1206_);
return v___x_1227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___boxed(lean_object* v_self_1228_, lean_object* v_facet_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg(v_self_1228_, v_facet_1229_, v_a_1230_, v_a_1231_);
lean_dec_ref(v_a_1230_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(lean_object* v_self_1234_, lean_object* v_facet_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v_toBuildConfig_1243_; uint8_t v_verbosity_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v_toBuildConfig_1243_ = lean_ctor_get(v_a_1240_, 0);
v_verbosity_1244_ = lean_ctor_get_uint8(v_toBuildConfig_1243_, sizeof(void*)*5 + 4);
v___x_1245_ = lean_box(v_verbosity_1244_);
v___x_1246_ = lean_obj_tag_nat(v___x_1245_);
lean_dec(v___x_1245_);
v___x_1247_ = lean_unsigned_to_nat(2u);
v___x_1248_ = lean_nat_dec_eq(v___x_1246_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec(v_facet_1235_);
lean_dec_ref(v_self_1234_);
v___x_1249_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v_a_1241_);
return v___x_1250_;
}
else
{
lean_object* v_baseName_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_baseName_1251_ = lean_ctor_get(v_self_1234_, 1);
lean_inc(v_baseName_1251_);
lean_dec_ref(v_self_1234_);
v___x_1252_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1253_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1251_, v___x_1248_);
v___x_1254_ = lean_string_append(v___x_1252_, v___x_1253_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1256_ = lean_string_append(v___x_1254_, v___x_1255_);
v___x_1257_ = l_Lake_Name_eraseHead(v_facet_1235_);
v___x_1258_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1257_, v___x_1248_);
v___x_1259_ = lean_string_append(v___x_1256_, v___x_1258_);
lean_dec_ref(v___x_1258_);
v___x_1260_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1261_ = lean_string_append(v___x_1259_, v___x_1260_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
lean_ctor_set(v___x_1262_, 1, v_a_1241_);
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___boxed(lean_object* v_self_1263_, lean_object* v_facet_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails(v_self_1263_, v_facet_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
return v_res_1272_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_1276_ = l_Lake_Name_eraseHead(v___x_1275_);
return v___x_1276_;
}
}
static lean_object* _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_1278_ = l_Lake_Name_eraseHead(v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(lean_object* v_self_1279_, uint8_t v_success_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_a_1289_; lean_object* v_a_1290_; lean_object* v_a_1312_; lean_object* v_a_1313_; 
if (v_success_1280_ == 0)
{
lean_object* v_config_1334_; uint8_t v_preferReleaseBuild_1335_; 
v_config_1334_ = lean_ctor_get(v_self_1279_, 6);
v_preferReleaseBuild_1335_ = lean_ctor_get_uint8(v_config_1334_, sizeof(void*)*28 + 2);
if (v_preferReleaseBuild_1335_ == 0)
{
lean_object* v_toBuildConfig_1336_; lean_object* v_baseName_1337_; uint8_t v_verbosity_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v_toBuildConfig_1336_ = lean_ctor_get(v___y_1285_, 0);
v_baseName_1337_ = lean_ctor_get(v_self_1279_, 1);
lean_inc(v_baseName_1337_);
lean_dec_ref(v_self_1279_);
v_verbosity_1338_ = lean_ctor_get_uint8(v_toBuildConfig_1336_, sizeof(void*)*5 + 4);
v___x_1339_ = lean_box(v_verbosity_1338_);
v___x_1340_ = lean_obj_tag_nat(v___x_1339_);
lean_dec(v___x_1339_);
v___x_1341_ = lean_unsigned_to_nat(2u);
v___x_1342_ = lean_nat_dec_eq(v___x_1340_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
lean_dec(v_baseName_1337_);
v___x_1343_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_1289_ = v___x_1343_;
v_a_1290_ = v___y_1286_;
goto v___jp_1288_;
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1344_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1345_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1337_, v___x_1342_);
v___x_1346_ = lean_string_append(v___x_1344_, v___x_1345_);
lean_dec_ref(v___x_1345_);
v___x_1347_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1348_ = lean_string_append(v___x_1346_, v___x_1347_);
v___x_1349_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__2);
v___x_1350_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1349_, v___x_1342_);
v___x_1351_ = lean_string_append(v___x_1348_, v___x_1350_);
lean_dec_ref(v___x_1350_);
v___x_1352_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1353_ = lean_string_append(v___x_1351_, v___x_1352_);
v_a_1289_ = v___x_1353_;
v_a_1290_ = v___y_1286_;
goto v___jp_1288_;
}
}
else
{
lean_object* v_toBuildConfig_1354_; lean_object* v_baseName_1355_; uint8_t v_verbosity_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; uint8_t v___x_1360_; 
v_toBuildConfig_1354_ = lean_ctor_get(v___y_1285_, 0);
v_baseName_1355_ = lean_ctor_get(v_self_1279_, 1);
lean_inc(v_baseName_1355_);
lean_dec_ref(v_self_1279_);
v_verbosity_1356_ = lean_ctor_get_uint8(v_toBuildConfig_1354_, sizeof(void*)*5 + 4);
v___x_1357_ = lean_box(v_verbosity_1356_);
v___x_1358_ = lean_obj_tag_nat(v___x_1357_);
lean_dec(v___x_1357_);
v___x_1359_ = lean_unsigned_to_nat(2u);
v___x_1360_ = lean_nat_dec_eq(v___x_1358_, v___x_1359_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; 
lean_dec(v_baseName_1355_);
v___x_1361_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_1312_ = v___x_1361_;
v_a_1313_ = v___y_1286_;
goto v___jp_1311_;
}
else
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1362_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_1363_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1355_, v___x_1360_);
v___x_1364_ = lean_string_append(v___x_1362_, v___x_1363_);
lean_dec_ref(v___x_1363_);
v___x_1365_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_1366_ = lean_string_append(v___x_1364_, v___x_1365_);
v___x_1367_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__3);
v___x_1368_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1367_, v___x_1360_);
v___x_1369_ = lean_string_append(v___x_1366_, v___x_1368_);
lean_dec_ref(v___x_1368_);
v___x_1370_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_1371_ = lean_string_append(v___x_1369_, v___x_1370_);
v_a_1312_ = v___x_1371_;
v_a_1313_ = v___y_1286_;
goto v___jp_1311_;
}
}
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_dec_ref(v_self_1279_);
v___x_1372_ = lean_box(0);
v___x_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
lean_ctor_set(v___x_1373_, 1, v___y_1286_);
return v___x_1373_;
}
v___jp_1288_:
{
lean_object* v_log_1291_; uint8_t v_action_1292_; uint8_t v_wantsRebuild_1293_; uint8_t v_canceled_1294_; lean_object* v_trace_1295_; lean_object* v_buildTime_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1310_; 
v_log_1291_ = lean_ctor_get(v_a_1290_, 0);
v_action_1292_ = lean_ctor_get_uint8(v_a_1290_, sizeof(void*)*3);
v_wantsRebuild_1293_ = lean_ctor_get_uint8(v_a_1290_, sizeof(void*)*3 + 1);
v_canceled_1294_ = lean_ctor_get_uint8(v_a_1290_, sizeof(void*)*3 + 2);
v_trace_1295_ = lean_ctor_get(v_a_1290_, 1);
v_buildTime_1296_ = lean_ctor_get(v_a_1290_, 2);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_a_1290_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1298_ = v_a_1290_;
v_isShared_1299_ = v_isSharedCheck_1310_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_buildTime_1296_);
lean_inc(v_trace_1295_);
lean_inc(v_log_1291_);
lean_dec(v_a_1290_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1310_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1300_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__0));
v___x_1301_ = lean_string_append(v___x_1300_, v_a_1289_);
lean_dec_ref(v_a_1289_);
v___x_1302_ = 0;
v___x_1303_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1303_, 0, v___x_1301_);
lean_ctor_set_uint8(v___x_1303_, sizeof(void*)*1, v___x_1302_);
v___x_1304_ = lean_box(0);
v___x_1305_ = lean_array_push(v_log_1291_, v___x_1303_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1305_);
v___x_1307_ = v___x_1298_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_trace_1295_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_buildTime_1296_);
lean_ctor_set_uint8(v_reuseFailAlloc_1309_, sizeof(void*)*3, v_action_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1309_, sizeof(void*)*3 + 1, v_wantsRebuild_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1309_, sizeof(void*)*3 + 2, v_canceled_1294_);
v___x_1307_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1304_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
return v___x_1308_;
}
}
}
v___jp_1311_:
{
lean_object* v_log_1314_; uint8_t v_action_1315_; uint8_t v_wantsRebuild_1316_; uint8_t v_canceled_1317_; lean_object* v_trace_1318_; lean_object* v_buildTime_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1333_; 
v_log_1314_ = lean_ctor_get(v_a_1313_, 0);
v_action_1315_ = lean_ctor_get_uint8(v_a_1313_, sizeof(void*)*3);
v_wantsRebuild_1316_ = lean_ctor_get_uint8(v_a_1313_, sizeof(void*)*3 + 1);
v_canceled_1317_ = lean_ctor_get_uint8(v_a_1313_, sizeof(void*)*3 + 2);
v_trace_1318_ = lean_ctor_get(v_a_1313_, 1);
v_buildTime_1319_ = lean_ctor_get(v_a_1313_, 2);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_a_1313_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1321_ = v_a_1313_;
v_isShared_1322_ = v_isSharedCheck_1333_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_buildTime_1319_);
lean_inc(v_trace_1318_);
lean_inc(v_log_1314_);
lean_dec(v_a_1313_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1333_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1323_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___closed__1));
v___x_1324_ = lean_string_append(v___x_1323_, v_a_1312_);
lean_dec_ref(v_a_1312_);
v___x_1325_ = 2;
v___x_1326_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set_uint8(v___x_1326_, sizeof(void*)*1, v___x_1325_);
v___x_1327_ = lean_box(0);
v___x_1328_ = lean_array_push(v_log_1314_, v___x_1326_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1328_);
v___x_1330_ = v___x_1321_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_trace_1318_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_buildTime_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1332_, sizeof(void*)*3, v_action_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1332_, sizeof(void*)*3 + 1, v_wantsRebuild_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1332_, sizeof(void*)*3 + 2, v_canceled_1317_);
v___x_1330_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1327_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
return v___x_1331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed(lean_object* v_self_1374_, lean_object* v_success_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
uint8_t v_success_boxed_1383_; lean_object* v_res_1384_; 
v_success_boxed_1383_ = lean_unbox(v_success_1375_);
v_res_1384_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0(v_self_1374_, v_success_boxed_1383_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(lean_object* v_self_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v___f_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_inc_ref(v_self_1385_);
v___f_1393_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___lam__0___boxed), 9, 1);
lean_closure_set(v___f_1393_, 0, v_self_1385_);
v___x_1394_ = l_Lake_instDataKindUnit;
lean_inc_ref(v_a_1386_);
v___x_1395_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1408_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_a_1397_ = lean_ctor_get(v___x_1395_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1399_ = v___x_1395_;
v_isShared_1400_ = v_isSharedCheck_1408_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1408_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1401_; uint8_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = 0;
v___x_1403_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_1404_ = l_Lake_Job_mapM___redArg(v___x_1394_, v_a_1396_, v___f_1393_, v___x_1401_, v___x_1402_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v___x_1403_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1404_);
v___x_1406_ = v___x_1399_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_a_1397_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_dec_ref(v___f_1393_);
lean_dec_ref(v_a_1386_);
v_a_1409_ = lean_ctor_get(v___x_1395_, 0);
v_a_1410_ = lean_ctor_get(v___x_1395_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1395_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_inc(v_a_1409_);
lean_dec(v___x_1395_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1409_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning___boxed(lean_object* v_self_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec(v_a_1420_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(lean_object* v_self_1427_, lean_object* v_as_1428_, size_t v_sz_1429_, size_t v_i_1430_, lean_object* v_b_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
uint8_t v___x_1439_; 
v___x_1439_ = lean_usize_dec_lt(v_i_1430_, v_sz_1429_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; 
lean_dec_ref(v___y_1432_);
lean_dec_ref(v_self_1427_);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v_b_1431_);
lean_ctor_set(v___x_1440_, 1, v___y_1437_);
return v___x_1440_;
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1442_; 
v_a_1441_ = lean_array_uget_borrowed(v_as_1428_, v_i_1430_);
lean_inc_ref(v___y_1432_);
lean_inc(v_a_1441_);
lean_inc_ref(v_self_1427_);
v___x_1442_ = l_Lake_Package_fetchTargetJob(v_self_1427_, v_a_1441_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v_a_1444_; lean_object* v___x_1445_; size_t v___x_1446_; size_t v___x_1447_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
v_a_1444_ = lean_ctor_get(v___x_1442_, 1);
lean_inc(v_a_1444_);
lean_dec_ref_known(v___x_1442_, 2);
v___x_1445_ = l_Lake_Job_mix___redArg(v_b_1431_, v_a_1443_);
v___x_1446_ = ((size_t)1ULL);
v___x_1447_ = lean_usize_add(v_i_1430_, v___x_1446_);
v_i_1430_ = v___x_1447_;
v_b_1431_ = v___x_1445_;
v___y_1437_ = v_a_1444_;
goto _start;
}
else
{
lean_object* v_a_1449_; lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v___y_1432_);
lean_dec_ref(v_b_1431_);
lean_dec_ref(v_self_1427_);
v_a_1449_ = lean_ctor_get(v___x_1442_, 0);
v_a_1450_ = lean_ctor_get(v___x_1442_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1442_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_inc(v_a_1449_);
lean_dec(v___x_1442_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1449_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0___boxed(lean_object* v_self_1458_, lean_object* v_as_1459_, lean_object* v_sz_1460_, lean_object* v_i_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
size_t v_sz_boxed_1470_; size_t v_i_boxed_1471_; lean_object* v_res_1472_; 
v_sz_boxed_1470_ = lean_unbox_usize(v_sz_1460_);
lean_dec(v_sz_1460_);
v_i_boxed_1471_ = lean_unbox_usize(v_i_1461_);
lean_dec(v_i_1461_);
v_res_1472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1458_, v_as_1459_, v_sz_boxed_1470_, v_i_boxed_1471_, v_b_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v_as_1459_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(lean_object* v_config_1473_, lean_object* v_self_1474_, lean_object* v_____r_1475_, lean_object* v_job_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_extraDepTargets_1484_; size_t v_sz_1485_; size_t v___x_1486_; lean_object* v___x_1487_; 
v_extraDepTargets_1484_ = lean_ctor_get(v_config_1473_, 2);
v_sz_1485_ = lean_array_size(v_extraDepTargets_1484_);
v___x_1486_ = ((size_t)0ULL);
v___x_1487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets_spec__0(v_self_1474_, v_extraDepTargets_1484_, v_sz_1485_, v___x_1486_, v_job_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed(lean_object* v_config_1488_, lean_object* v_self_1489_, lean_object* v_____r_1490_, lean_object* v_job_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0(v_config_1488_, v_self_1489_, v_____r_1490_, v_job_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v_config_1488_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(uint8_t v___x_1500_, lean_object* v_self_1501_, lean_object* v_job_1502_, lean_object* v___f_1503_, lean_object* v___x_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
if (v___x_1500_ == 0)
{
lean_object* v___x_1512_; 
lean_inc_ref(v___y_1505_);
v___x_1512_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCacheWithWarning(v_self_1501_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v_a_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
v_a_1514_ = lean_ctor_get(v___x_1512_, 1);
lean_inc(v_a_1514_);
lean_dec_ref_known(v___x_1512_, 2);
v___x_1515_ = l_Lake_Job_add___redArg(v_job_1502_, v_a_1513_);
lean_inc_ref(v___y_1509_);
lean_inc(v___y_1508_);
lean_inc(v___y_1507_);
lean_inc(v___y_1506_);
v___x_1516_ = lean_apply_9(v___f_1503_, v___x_1504_, v___x_1515_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v_a_1514_, lean_box(0));
return v___x_1516_;
}
else
{
lean_dec_ref(v___y_1505_);
lean_dec_ref(v___f_1503_);
lean_dec_ref(v_job_1502_);
return v___x_1512_;
}
}
else
{
lean_object* v___x_1517_; 
lean_dec_ref(v_self_1501_);
lean_inc_ref(v___y_1509_);
lean_inc(v___y_1508_);
lean_inc(v___y_1507_);
lean_inc(v___y_1506_);
v___x_1517_ = lean_apply_9(v___f_1503_, v___x_1504_, v_job_1502_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, lean_box(0));
return v___x_1517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed(lean_object* v___x_1518_, lean_object* v_self_1519_, lean_object* v_job_1520_, lean_object* v___f_1521_, lean_object* v___x_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
uint8_t v___x_4126__boxed_1530_; lean_object* v_res_1531_; 
v___x_4126__boxed_1530_ = lean_unbox(v___x_1518_);
v_res_1531_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1(v___x_4126__boxed_1530_, v_self_1519_, v_job_1520_, v___f_1521_, v___x_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec(v___y_1524_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(lean_object* v_self_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_wsIdx_1542_; lean_object* v_baseName_1543_; lean_object* v_config_1544_; lean_object* v___f_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v_job_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___y_1568_; lean_object* v___x_1569_; 
v_wsIdx_1542_ = lean_ctor_get(v_self_1534_, 0);
v_baseName_1543_ = lean_ctor_get(v_self_1534_, 1);
v_config_1544_ = lean_ctor_get(v_self_1534_, 6);
lean_inc_ref(v_self_1534_);
lean_inc_ref(v_config_1544_);
v___f_1545_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1545_, 0, v_config_1544_);
lean_closure_set(v___f_1545_, 1, v_self_1534_);
v___x_1546_ = l_Lake_instDataKindUnit;
v___x_1547_ = 1;
lean_inc(v_baseName_1543_);
v___x_1548_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_1543_, v___x_1547_);
v___x_1549_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__0));
lean_inc_ref(v___x_1548_);
v___x_1550_ = lean_string_append(v___x_1548_, v___x_1549_);
v___x_1551_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___closed__1));
v___x_1552_ = lean_string_append(v___x_1551_, v___x_1548_);
lean_dec_ref(v___x_1548_);
v___x_1553_ = lean_string_append(v___x_1552_, v___x_1549_);
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_box(0);
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_1558_ = 0;
v___x_1559_ = 0;
v___x_1560_ = l_Lake_BuildTrace_nil(v___x_1553_);
v___x_1561_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1561_, 0, v___x_1557_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
lean_ctor_set(v___x_1561_, 2, v___x_1556_);
lean_ctor_set_uint8(v___x_1561_, sizeof(void*)*3, v___x_1558_);
lean_ctor_set_uint8(v___x_1561_, sizeof(void*)*3 + 1, v___x_1559_);
lean_ctor_set_uint8(v___x_1561_, sizeof(void*)*3 + 2, v___x_1559_);
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1554_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = lean_task_pure(v___x_1562_);
v___x_1564_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_job_1565_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_job_1565_, 0, v___x_1563_);
lean_ctor_set(v_job_1565_, 1, v___x_1555_);
lean_ctor_set(v_job_1565_, 2, v___x_1564_);
lean_ctor_set_uint8(v_job_1565_, sizeof(void*)*3, v___x_1559_);
v___x_1566_ = lean_nat_dec_eq(v_wsIdx_1542_, v___x_1556_);
v___x_1567_ = lean_box(v___x_1566_);
v___y_1568_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___lam__1___boxed), 12, 5);
lean_closure_set(v___y_1568_, 0, v___x_1567_);
lean_closure_set(v___y_1568_, 1, v_self_1534_);
lean_closure_set(v___y_1568_, 2, v_job_1565_);
lean_closure_set(v___y_1568_, 3, v___f_1545_);
lean_closure_set(v___y_1568_, 4, v___x_1554_);
v___x_1569_ = l_Lake_ensureJob___redArg(v___x_1546_, v___y_1568_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1594_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_a_1571_ = lean_ctor_get(v___x_1569_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1573_ = v___x_1569_;
v_isShared_1574_ = v_isSharedCheck_1594_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1594_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v_task_1575_; lean_object* v_kind_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1592_; 
v_task_1575_ = lean_ctor_get(v_a_1570_, 0);
v_kind_1576_ = lean_ctor_get(v_a_1570_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_a_1570_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v_a_1570_, 2);
lean_dec(v_unused_1593_);
v___x_1578_ = v_a_1570_;
v_isShared_1579_ = v_isSharedCheck_1592_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_kind_1576_);
lean_inc(v_task_1575_);
lean_dec(v_a_1570_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1592_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v_registeredJobs_1580_; lean_object* v_job_1582_; 
v_registeredJobs_1580_ = lean_ctor_get(v_a_1539_, 4);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 2, v___x_1550_);
v_job_1582_ = v___x_1578_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_task_1575_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_kind_1576_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v___x_1550_);
v_job_1582_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_ctor_set_uint8(v_job_1582_, sizeof(void*)*3, v___x_1559_);
v___x_1583_ = lean_st_ref_take(v_registeredJobs_1580_);
lean_inc_ref(v_job_1582_);
v___x_1584_ = l_Lake_Job_toOpaque___redArg(v_job_1582_);
v___x_1585_ = lean_array_push(v___x_1583_, v___x_1584_);
v___x_1586_ = lean_st_ref_put(v_registeredJobs_1580_, v___x_1585_);
v___x_1587_ = l_Lake_Job_renew___redArg(v_job_1582_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1587_);
v___x_1589_ = v___x_1573_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_a_1571_);
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
else
{
lean_dec_ref(v___x_1550_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets___boxed(lean_object* v_self_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l___private_Lake_Build_Package_0__Lake_Package_recBuildExtraDepTargets(v_self_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec(v_a_1597_);
return v_res_1603_;
}
}
static lean_object* _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_box(0);
v___x_1605_ = l_Lean_Json_compress(v___x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(uint8_t v_fmt_1606_){
_start:
{
if (v_fmt_1606_ == 0)
{
lean_object* v___x_1607_; 
v___x_1607_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
return v___x_1607_;
}
else
{
lean_object* v___x_1608_; 
v___x_1608_ = lean_obj_once(&l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0, &l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0_once, _init_l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___closed__0);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg___boxed(lean_object* v_fmt_1609_){
_start:
{
uint8_t v_fmt_boxed_1610_; lean_object* v_res_1611_; 
v_fmt_boxed_1610_ = lean_unbox(v_fmt_1609_);
v_res_1611_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_boxed_1610_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(uint8_t v_fmt_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v_fmt_1612_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___boxed(lean_object* v_fmt_1615_, lean_object* v_a_1616_){
_start:
{
uint8_t v_fmt_boxed_1617_; lean_object* v_res_1618_; 
v_fmt_boxed_1617_ = lean_unbox(v_fmt_1615_);
v_res_1618_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0(v_fmt_boxed_1617_, v_a_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0(uint8_t v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lake_formatQuery___at___00Lake_Package_extraDepFacetConfig_spec__0___redArg(v___y_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_extraDepFacetConfig___lam__0___boxed(lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
uint8_t v___y_67__boxed_1624_; lean_object* v_res_1625_; 
v___y_67__boxed_1624_ = lean_unbox(v___y_1622_);
v_res_1625_ = l_Lake_Package_extraDepFacetConfig___lam__0(v___y_67__boxed_1624_, v___y_1623_);
return v_res_1625_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_1628_; uint8_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___f_1628_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_1629_ = 1;
v___x_1630_ = l_Lake_instDataKindUnit;
v___x_1631_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__1));
v___x_1632_ = l_Lake_Package_keyword;
v___x_1633_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
lean_ctor_set(v___x_1633_, 1, v___x_1631_);
lean_ctor_set(v___x_1633_, 2, v___x_1630_);
lean_ctor_set(v___x_1633_, 3, v___f_1628_);
lean_ctor_set_uint8(v___x_1633_, sizeof(void*)*4, v___x_1629_);
lean_ctor_set_uint8(v___x_1633_, sizeof(void*)*4 + 1, v___x_1629_);
return v___x_1633_;
}
}
static lean_object* _init_l_Lake_Package_extraDepFacetConfig(void){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = lean_obj_once(&l_Lake_Package_extraDepFacetConfig___closed__2, &l_Lake_Package_extraDepFacetConfig___closed__2_once, _init_l_Lake_Package_extraDepFacetConfig___closed__2);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(lean_object* v_self_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v_origName_1654_; lean_object* v_dir_1655_; lean_object* v_scope_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v_origName_1654_ = lean_ctor_get(v_self_1650_, 3);
lean_inc(v_origName_1654_);
v_dir_1655_ = lean_ctor_get(v_self_1650_, 4);
lean_inc_ref(v_dir_1655_);
v_scope_1656_ = lean_ctor_get(v_self_1650_, 10);
lean_inc_ref(v_scope_1656_);
lean_dec_ref(v_self_1650_);
v___x_1657_ = lean_string_utf8_byte_size(v_scope_1656_);
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_nat_dec_eq(v___x_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_object* v_log_1660_; uint8_t v_action_1661_; uint8_t v_wantsRebuild_1662_; uint8_t v_canceled_1663_; lean_object* v_trace_1664_; lean_object* v_buildTime_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_log_1660_ = lean_ctor_get(v_a_1652_, 0);
v_action_1661_ = lean_ctor_get_uint8(v_a_1652_, sizeof(void*)*3);
v_wantsRebuild_1662_ = lean_ctor_get_uint8(v_a_1652_, sizeof(void*)*3 + 1);
v_canceled_1663_ = lean_ctor_get_uint8(v_a_1652_, sizeof(void*)*3 + 2);
v_trace_1664_ = lean_ctor_get(v_a_1652_, 1);
v_buildTime_1665_ = lean_ctor_get(v_a_1652_, 2);
v___x_1666_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
v___x_1667_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1666_, v_dir_1655_);
if (lean_obj_tag(v___x_1667_) == 1)
{
lean_object* v_toContext_1668_; lean_object* v_lakeEnv_1669_; lean_object* v_val_1670_; lean_object* v_toolchain_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v_toContext_1668_ = lean_ctor_get(v_a_1651_, 1);
v_lakeEnv_1669_ = lean_ctor_get(v_toContext_1668_, 0);
v_val_1670_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_val_1670_);
lean_dec_ref_known(v___x_1667_, 1);
v_toolchain_1671_ = lean_ctor_get(v_lakeEnv_1669_, 19);
v___x_1672_ = lean_string_utf8_byte_size(v_toolchain_1671_);
v___x_1673_ = lean_nat_dec_eq(v___x_1672_, v___x_1658_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1674_ = l_Lean_Name_toString(v_origName_1654_, v___x_1659_);
lean_inc_ref(v_lakeEnv_1669_);
v___x_1675_ = l_Lake_Reservoir_pkgApiUrl(v_lakeEnv_1669_, v_scope_1656_, v___x_1674_);
lean_dec_ref(v___x_1674_);
lean_dec_ref(v_scope_1656_);
v___x_1676_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__1));
v___x_1677_ = lean_string_append(v___x_1675_, v___x_1676_);
v___x_1678_ = lean_string_append(v___x_1677_, v_val_1670_);
lean_dec(v_val_1670_);
v___x_1679_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__2));
v___x_1680_ = lean_string_append(v___x_1678_, v___x_1679_);
v___x_1681_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_1682_ = l_Lake_uriEncode(v_toolchain_1671_, v___x_1681_);
v___x_1683_ = lean_string_append(v___x_1680_, v___x_1682_);
lean_dec_ref(v___x_1682_);
v___x_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
lean_ctor_set(v___x_1684_, 1, v_a_1652_);
return v___x_1684_;
}
else
{
lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1695_; 
lean_inc(v_buildTime_1665_);
lean_inc_ref(v_trace_1664_);
lean_inc_ref(v_log_1660_);
lean_dec(v_val_1670_);
lean_dec_ref(v_scope_1656_);
lean_dec(v_origName_1654_);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_a_1652_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; lean_object* v_unused_1697_; lean_object* v_unused_1698_; 
v_unused_1696_ = lean_ctor_get(v_a_1652_, 2);
lean_dec(v_unused_1696_);
v_unused_1697_ = lean_ctor_get(v_a_1652_, 1);
lean_dec(v_unused_1697_);
v_unused_1698_ = lean_ctor_get(v_a_1652_, 0);
lean_dec(v_unused_1698_);
v___x_1686_ = v_a_1652_;
v_isShared_1687_ = v_isSharedCheck_1695_;
goto v_resetjp_1685_;
}
else
{
lean_dec(v_a_1652_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1695_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1688_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__4));
v___x_1689_ = lean_array_get_size(v_log_1660_);
v___x_1690_ = lean_array_push(v_log_1660_, v___x_1688_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1690_);
v___x_1692_ = v___x_1686_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_trace_1664_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v_buildTime_1665_);
lean_ctor_set_uint8(v_reuseFailAlloc_1694_, sizeof(void*)*3, v_action_1661_);
lean_ctor_set_uint8(v_reuseFailAlloc_1694_, sizeof(void*)*3 + 1, v_wantsRebuild_1662_);
lean_ctor_set_uint8(v_reuseFailAlloc_1694_, sizeof(void*)*3 + 2, v_canceled_1663_);
v___x_1692_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1689_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
return v___x_1693_;
}
}
}
}
else
{
lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1709_; 
lean_inc(v_buildTime_1665_);
lean_inc_ref(v_trace_1664_);
lean_inc_ref(v_log_1660_);
lean_dec(v___x_1667_);
lean_dec_ref(v_scope_1656_);
lean_dec(v_origName_1654_);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_a_1652_);
if (v_isSharedCheck_1709_ == 0)
{
lean_object* v_unused_1710_; lean_object* v_unused_1711_; lean_object* v_unused_1712_; 
v_unused_1710_ = lean_ctor_get(v_a_1652_, 2);
lean_dec(v_unused_1710_);
v_unused_1711_ = lean_ctor_get(v_a_1652_, 1);
lean_dec(v_unused_1711_);
v_unused_1712_ = lean_ctor_get(v_a_1652_, 0);
lean_dec(v_unused_1712_);
v___x_1700_ = v_a_1652_;
v_isShared_1701_ = v_isSharedCheck_1709_;
goto v_resetjp_1699_;
}
else
{
lean_dec(v_a_1652_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1709_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1702_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__6));
v___x_1703_ = lean_array_get_size(v_log_1660_);
v___x_1704_ = lean_array_push(v_log_1660_, v___x_1702_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1704_);
v___x_1706_ = v___x_1700_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v_trace_1664_);
lean_ctor_set(v_reuseFailAlloc_1708_, 2, v_buildTime_1665_);
lean_ctor_set_uint8(v_reuseFailAlloc_1708_, sizeof(void*)*3, v_action_1661_);
lean_ctor_set_uint8(v_reuseFailAlloc_1708_, sizeof(void*)*3 + 1, v_wantsRebuild_1662_);
lean_ctor_set_uint8(v_reuseFailAlloc_1708_, sizeof(void*)*3 + 2, v_canceled_1663_);
v___x_1706_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1703_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
return v___x_1707_;
}
}
}
}
else
{
lean_object* v_log_1713_; uint8_t v_action_1714_; uint8_t v_wantsRebuild_1715_; uint8_t v_canceled_1716_; lean_object* v_trace_1717_; lean_object* v_buildTime_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1729_; 
lean_dec_ref(v_scope_1656_);
lean_dec_ref(v_dir_1655_);
lean_dec(v_origName_1654_);
v_log_1713_ = lean_ctor_get(v_a_1652_, 0);
v_action_1714_ = lean_ctor_get_uint8(v_a_1652_, sizeof(void*)*3);
v_wantsRebuild_1715_ = lean_ctor_get_uint8(v_a_1652_, sizeof(void*)*3 + 1);
v_canceled_1716_ = lean_ctor_get_uint8(v_a_1652_, sizeof(void*)*3 + 2);
v_trace_1717_ = lean_ctor_get(v_a_1652_, 1);
v_buildTime_1718_ = lean_ctor_get(v_a_1652_, 2);
v_isSharedCheck_1729_ = !lean_is_exclusive(v_a_1652_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1720_ = v_a_1652_;
v_isShared_1721_ = v_isSharedCheck_1729_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_buildTime_1718_);
lean_inc(v_trace_1717_);
lean_inc(v_log_1713_);
lean_dec(v_a_1652_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1729_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1722_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__8));
v___x_1723_ = lean_array_get_size(v_log_1713_);
v___x_1724_ = lean_array_push(v_log_1713_, v___x_1722_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1724_);
v___x_1726_ = v___x_1720_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_trace_1717_);
lean_ctor_set(v_reuseFailAlloc_1728_, 2, v_buildTime_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1728_, sizeof(void*)*3, v_action_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1728_, sizeof(void*)*3 + 1, v_wantsRebuild_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1728_, sizeof(void*)*3 + 2, v_canceled_1716_);
v___x_1726_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1723_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
return v___x_1727_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___boxed(lean_object* v_self_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1730_, v_a_1731_, v_a_1732_);
lean_dec_ref(v_a_1731_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(lean_object* v_self_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_self_1735_, v_a_1740_, v_a_1741_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___boxed(lean_object* v_self_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl(v_self_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
lean_dec_ref(v_a_1749_);
lean_dec(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(lean_object* v_self_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v_rev_1766_; lean_object* v_log_1767_; uint8_t v_action_1768_; uint8_t v_wantsRebuild_1769_; uint8_t v_canceled_1770_; lean_object* v_trace_1771_; lean_object* v_buildTime_1772_; lean_object* v_dir_1781_; lean_object* v_config_1782_; lean_object* v_remoteUrl_1783_; lean_object* v_buildArchive_1784_; lean_object* v___y_1786_; lean_object* v___y_1787_; uint8_t v___y_1788_; uint8_t v___y_1789_; uint8_t v___y_1790_; lean_object* v___y_1791_; lean_object* v_val_1792_; lean_object* v___y_1812_; lean_object* v_releaseRepo_1834_; 
v_dir_1781_ = lean_ctor_get(v_self_1762_, 4);
lean_inc_ref(v_dir_1781_);
v_config_1782_ = lean_ctor_get(v_self_1762_, 6);
lean_inc_ref(v_config_1782_);
v_remoteUrl_1783_ = lean_ctor_get(v_self_1762_, 11);
lean_inc_ref(v_remoteUrl_1783_);
v_buildArchive_1784_ = lean_ctor_get(v_self_1762_, 21);
lean_inc_ref(v_buildArchive_1784_);
lean_dec_ref(v_self_1762_);
v_releaseRepo_1834_ = lean_ctor_get(v_config_1782_, 10);
lean_inc(v_releaseRepo_1834_);
lean_dec_ref(v_config_1782_);
if (lean_obj_tag(v_releaseRepo_1834_) == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1835_ = lean_string_utf8_byte_size(v_remoteUrl_1783_);
v___x_1836_ = lean_unsigned_to_nat(0u);
v___x_1837_ = lean_nat_dec_eq(v___x_1835_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1838_, 0, v_remoteUrl_1783_);
v___y_1812_ = v___x_1838_;
goto v___jp_1811_;
}
else
{
lean_dec_ref(v_remoteUrl_1783_);
v___y_1812_ = v_releaseRepo_1834_;
goto v___jp_1811_;
}
}
else
{
lean_dec_ref(v_remoteUrl_1783_);
v___y_1812_ = v_releaseRepo_1834_;
goto v___jp_1811_;
}
v___jp_1765_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1773_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__0));
v___x_1774_ = lean_string_append(v___x_1773_, v_rev_1766_);
lean_dec_ref(v_rev_1766_);
v___x_1775_ = 3;
v___x_1776_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1776_, 0, v___x_1774_);
lean_ctor_set_uint8(v___x_1776_, sizeof(void*)*1, v___x_1775_);
v___x_1777_ = lean_array_get_size(v_log_1767_);
v___x_1778_ = lean_array_push(v_log_1767_, v___x_1776_);
v___x_1779_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
lean_ctor_set(v___x_1779_, 1, v_trace_1771_);
lean_ctor_set(v___x_1779_, 2, v_buildTime_1772_);
lean_ctor_set_uint8(v___x_1779_, sizeof(void*)*3, v_action_1768_);
lean_ctor_set_uint8(v___x_1779_, sizeof(void*)*3 + 1, v_wantsRebuild_1769_);
lean_ctor_set_uint8(v___x_1779_, sizeof(void*)*3 + 2, v_canceled_1770_);
v___x_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1777_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
return v___x_1780_;
}
v___jp_1785_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg___closed__0));
lean_inc_ref(v_dir_1781_);
v___x_1794_ = l_Lake_GitRepo_findTag_x3f(v___x_1793_, v_dir_1781_);
if (lean_obj_tag(v___x_1794_) == 1)
{
lean_object* v_val_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
lean_dec_ref(v_dir_1781_);
v_val_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_val_1795_);
lean_dec_ref_known(v___x_1794_, 1);
v___x_1796_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1796_, 0, v___y_1791_);
lean_ctor_set(v___x_1796_, 1, v___y_1786_);
lean_ctor_set(v___x_1796_, 2, v___y_1787_);
lean_ctor_set_uint8(v___x_1796_, sizeof(void*)*3, v___y_1790_);
lean_ctor_set_uint8(v___x_1796_, sizeof(void*)*3 + 1, v___y_1789_);
lean_ctor_set_uint8(v___x_1796_, sizeof(void*)*3 + 2, v___y_1788_);
v___x_1797_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__1));
v___x_1798_ = lean_string_append(v_val_1792_, v___x_1797_);
v___x_1799_ = lean_string_append(v___x_1798_, v_val_1795_);
lean_dec(v_val_1795_);
v___x_1800_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__2));
v___x_1801_ = lean_string_append(v___x_1799_, v___x_1800_);
v___x_1802_ = lean_string_append(v___x_1801_, v_buildArchive_1784_);
lean_dec_ref(v_buildArchive_1784_);
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
lean_ctor_set(v___x_1803_, 1, v___x_1796_);
return v___x_1803_;
}
else
{
lean_object* v___x_1804_; 
lean_dec(v___x_1794_);
lean_dec_ref(v_val_1792_);
lean_dec_ref(v_buildArchive_1784_);
v___x_1804_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_1793_, v_dir_1781_);
if (lean_obj_tag(v___x_1804_) == 1)
{
lean_object* v_val_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v_val_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_val_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v___x_1806_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__3));
v___x_1807_ = lean_string_append(v___x_1806_, v_val_1805_);
lean_dec(v_val_1805_);
v___x_1808_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__4));
v___x_1809_ = lean_string_append(v___x_1807_, v___x_1808_);
v_rev_1766_ = v___x_1809_;
v_log_1767_ = v___y_1791_;
v_action_1768_ = v___y_1790_;
v_wantsRebuild_1769_ = v___y_1789_;
v_canceled_1770_ = v___y_1788_;
v_trace_1771_ = v___y_1786_;
v_buildTime_1772_ = v___y_1787_;
goto v___jp_1765_;
}
else
{
lean_object* v___x_1810_; 
lean_dec(v___x_1804_);
v___x_1810_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v_rev_1766_ = v___x_1810_;
v_log_1767_ = v___y_1791_;
v_action_1768_ = v___y_1790_;
v_wantsRebuild_1769_ = v___y_1789_;
v_canceled_1770_ = v___y_1788_;
v_trace_1771_ = v___y_1786_;
v_buildTime_1772_ = v___y_1787_;
goto v___jp_1765_;
}
}
}
v___jp_1811_:
{
lean_object* v_log_1813_; uint8_t v_action_1814_; uint8_t v_wantsRebuild_1815_; uint8_t v_canceled_1816_; lean_object* v_trace_1817_; lean_object* v_buildTime_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1833_; 
v_log_1813_ = lean_ctor_get(v_a_1763_, 0);
v_action_1814_ = lean_ctor_get_uint8(v_a_1763_, sizeof(void*)*3);
v_wantsRebuild_1815_ = lean_ctor_get_uint8(v_a_1763_, sizeof(void*)*3 + 1);
v_canceled_1816_ = lean_ctor_get_uint8(v_a_1763_, sizeof(void*)*3 + 2);
v_trace_1817_ = lean_ctor_get(v_a_1763_, 1);
v_buildTime_1818_ = lean_ctor_get(v_a_1763_, 2);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_a_1763_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1820_ = v_a_1763_;
v_isShared_1821_ = v_isSharedCheck_1833_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_buildTime_1818_);
lean_inc(v_trace_1817_);
lean_inc(v_log_1813_);
lean_dec(v_a_1763_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1833_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = l_Lake_Git_defaultRemote;
lean_inc_ref(v_dir_1781_);
v___x_1823_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v___x_1822_, v_dir_1781_);
if (lean_obj_tag(v___y_1812_) == 0)
{
if (lean_obj_tag(v___x_1823_) == 1)
{
lean_object* v_val_1824_; 
lean_del_object(v___x_1820_);
v_val_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_val_1824_);
lean_dec_ref_known(v___x_1823_, 1);
v___y_1786_ = v_trace_1817_;
v___y_1787_ = v_buildTime_1818_;
v___y_1788_ = v_canceled_1816_;
v___y_1789_ = v_wantsRebuild_1815_;
v___y_1790_ = v_action_1814_;
v___y_1791_ = v_log_1813_;
v_val_1792_ = v_val_1824_;
goto v___jp_1785_;
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
lean_dec(v___x_1823_);
lean_dec_ref(v_buildArchive_1784_);
lean_dec_ref(v_dir_1781_);
v___x_1825_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___closed__6));
v___x_1826_ = lean_array_get_size(v_log_1813_);
v___x_1827_ = lean_array_push(v_log_1813_, v___x_1825_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1827_);
v___x_1829_ = v___x_1820_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_trace_1817_);
lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_buildTime_1818_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*3, v_action_1814_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*3 + 1, v_wantsRebuild_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*3 + 2, v_canceled_1816_);
v___x_1829_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1826_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
return v___x_1830_;
}
}
}
else
{
lean_object* v_val_1832_; 
lean_dec(v___x_1823_);
lean_del_object(v___x_1820_);
v_val_1832_ = lean_ctor_get(v___y_1812_, 0);
lean_inc(v_val_1832_);
lean_dec_ref_known(v___y_1812_, 1);
v___y_1786_ = v_trace_1817_;
v___y_1787_ = v_buildTime_1818_;
v___y_1788_ = v_canceled_1816_;
v___y_1789_ = v_wantsRebuild_1815_;
v___y_1790_ = v_action_1814_;
v___y_1791_ = v_log_1813_;
v_val_1792_ = v_val_1832_;
goto v___jp_1785_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg___boxed(lean_object* v_self_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1839_, v_a_1840_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(lean_object* v_self_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_self_1843_, v_a_1849_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___boxed(lean_object* v_self_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl(v_self_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(lean_object* v_val_1861_, lean_object* v_a_x3f_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_log_1865_; uint8_t v_action_1866_; uint8_t v_wantsRebuild_1867_; uint8_t v_canceled_1868_; lean_object* v_trace_1869_; lean_object* v_buildTime_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1882_; 
v_log_1865_ = lean_ctor_get(v___y_1863_, 0);
v_action_1866_ = lean_ctor_get_uint8(v___y_1863_, sizeof(void*)*3);
v_wantsRebuild_1867_ = lean_ctor_get_uint8(v___y_1863_, sizeof(void*)*3 + 1);
v_canceled_1868_ = lean_ctor_get_uint8(v___y_1863_, sizeof(void*)*3 + 2);
v_trace_1869_ = lean_ctor_get(v___y_1863_, 1);
v_buildTime_1870_ = lean_ctor_get(v___y_1863_, 2);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___y_1863_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1872_ = v___y_1863_;
v_isShared_1873_ = v_isSharedCheck_1882_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_buildTime_1870_);
lean_inc(v_trace_1869_);
lean_inc(v_log_1865_);
lean_dec(v___y_1863_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1882_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1874_ = lean_io_mono_ms_now();
v___x_1875_ = lean_nat_sub(v___x_1874_, v_val_1861_);
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
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_log_1865_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_trace_1869_);
lean_ctor_set(v_reuseFailAlloc_1881_, 2, v___x_1877_);
lean_ctor_set_uint8(v_reuseFailAlloc_1881_, sizeof(void*)*3, v_action_1866_);
lean_ctor_set_uint8(v_reuseFailAlloc_1881_, sizeof(void*)*3 + 1, v_wantsRebuild_1867_);
lean_ctor_set_uint8(v_reuseFailAlloc_1881_, sizeof(void*)*3 + 2, v_canceled_1868_);
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
lean_object* v_a_1903_; lean_object* v_a_1904_; lean_object* v_log_1907_; uint8_t v_action_1908_; uint8_t v_wantsRebuild_1909_; uint8_t v_canceled_1910_; lean_object* v_trace_1911_; lean_object* v_buildTime_1912_; lean_object* v_toBuildConfig_1918_; lean_object* v_log_1919_; uint8_t v_action_1920_; uint8_t v_wantsRebuild_1921_; uint8_t v_canceled_1922_; lean_object* v_trace_1923_; lean_object* v_buildTime_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_2014_; 
v_toBuildConfig_1918_ = lean_ctor_get(v_a_1899_, 0);
v_log_1919_ = lean_ctor_get(v_a_1900_, 0);
v_action_1920_ = lean_ctor_get_uint8(v_a_1900_, sizeof(void*)*3);
v_wantsRebuild_1921_ = lean_ctor_get_uint8(v_a_1900_, sizeof(void*)*3 + 1);
v_canceled_1922_ = lean_ctor_get_uint8(v_a_1900_, sizeof(void*)*3 + 2);
v_trace_1923_ = lean_ctor_get(v_a_1900_, 1);
v_buildTime_1924_ = lean_ctor_get(v_a_1900_, 2);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_a_1900_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1926_ = v_a_1900_;
v_isShared_1927_ = v_isSharedCheck_2014_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_buildTime_1924_);
lean_inc(v_trace_1923_);
lean_inc(v_log_1919_);
lean_dec(v_a_1900_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_2014_;
goto v_resetjp_1925_;
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
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1913_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__1));
v___x_1914_ = lean_array_get_size(v_log_1907_);
v___x_1915_ = lean_array_push(v_log_1907_, v___x_1913_);
v___x_1916_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set(v___x_1916_, 1, v_trace_1911_);
lean_ctor_set(v___x_1916_, 2, v_buildTime_1912_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*3, v_action_1908_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*3 + 1, v_wantsRebuild_1909_);
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*3 + 2, v_canceled_1910_);
v___x_1917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1914_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
return v___x_1917_;
}
v_resetjp_1925_:
{
uint8_t v_noBuild_1928_; uint8_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v_noBuild_1928_ = lean_ctor_get_uint8(v_toBuildConfig_1918_, sizeof(void*)*5 + 2);
v___x_1929_ = l_Lake_JobAction_merge(v_action_1920_, v_action_1898_);
v___x_1930_ = ((lean_object*)(l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___closed__2));
lean_inc_ref(v_traceFile_1897_);
v___x_1931_ = l_System_FilePath_addExtension(v_traceFile_1897_, v___x_1930_);
if (v_noBuild_1928_ == 0)
{
lean_object* v___x_1932_; lean_object* v_a_1934_; lean_object* v_a_1935_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1932_ = lean_io_mono_ms_now();
v___x_1939_ = lean_array_get_size(v_log_1919_);
v___x_1940_ = l_Lake_download(v_url_1893_, v_archiveFile_1894_, v_headers_1895_, v_log_1919_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v_a_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
v_a_1942_ = lean_ctor_get(v___x_1940_, 1);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1940_, 2);
v___x_1943_ = lean_array_get_size(v_a_1942_);
v___x_1944_ = l_Array_extract___redArg(v_a_1942_, v___x_1939_, v___x_1943_);
v___x_1945_ = lean_box(0);
v___x_1946_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1896_, v___x_1945_, v___x_1944_);
v___x_1947_ = l_Lake_BuildMetadata_writeFile(v_traceFile_1897_, v___x_1946_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1984_; 
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v___x_1947_, 0);
lean_dec(v_unused_1985_);
v___x_1949_ = v___x_1947_;
v_isShared_1950_ = v_isSharedCheck_1984_;
goto v_resetjp_1948_;
}
else
{
lean_dec(v___x_1947_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1984_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lake_removeFileIfExists(v___x_1931_);
lean_dec_ref(v___x_1931_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1974_; 
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v___x_1951_, 0);
lean_dec(v_unused_1975_);
v___x_1953_ = v___x_1951_;
v_isShared_1954_ = v_isSharedCheck_1974_;
goto v_resetjp_1952_;
}
else
{
lean_dec(v___x_1951_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1974_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v_a_1942_);
v___x_1956_ = v___x_1926_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1942_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_trace_1923_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v_buildTime_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1973_, sizeof(void*)*3 + 1, v_wantsRebuild_1921_);
lean_ctor_set_uint8(v_reuseFailAlloc_1973_, sizeof(void*)*3 + 2, v_canceled_1922_);
v___x_1956_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1958_; 
lean_ctor_set_uint8(v___x_1956_, sizeof(void*)*3, v___x_1929_);
lean_inc(v_a_1941_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v_a_1941_);
v___x_1958_ = v___x_1953_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1941_);
v___x_1958_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1960_; 
if (v_isShared_1950_ == 0)
{
lean_ctor_set_tag(v___x_1949_, 1);
lean_ctor_set(v___x_1949_, 0, v___x_1958_);
v___x_1960_ = v___x_1949_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1961_; lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
v___x_1961_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1932_, v___x_1960_, v___x_1956_);
lean_dec_ref(v___x_1960_);
lean_dec(v___x_1932_);
v_a_1962_ = lean_ctor_get(v___x_1961_, 1);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v___x_1961_, 0);
lean_dec(v_unused_1970_);
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v_a_1941_);
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1941_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1982_; 
lean_del_object(v___x_1949_);
lean_dec(v_a_1941_);
v_a_1976_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1977_ = lean_io_error_to_string(v_a_1976_);
v___x_1978_ = 3;
v___x_1979_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1979_, 0, v___x_1977_);
lean_ctor_set_uint8(v___x_1979_, sizeof(void*)*1, v___x_1978_);
v___x_1980_ = lean_array_push(v_a_1942_, v___x_1979_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1980_);
v___x_1982_ = v___x_1926_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_trace_1923_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_buildTime_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*3 + 1, v_wantsRebuild_1921_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*3 + 2, v_canceled_1922_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_ctor_set_uint8(v___x_1982_, sizeof(void*)*3, v___x_1929_);
v_a_1934_ = v___x_1943_;
v_a_1935_ = v___x_1982_;
goto v___jp_1933_;
}
}
}
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1992_; 
lean_dec(v_a_1941_);
lean_dec_ref(v___x_1931_);
v_a_1986_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1986_);
lean_dec_ref_known(v___x_1947_, 1);
v___x_1987_ = lean_io_error_to_string(v_a_1986_);
v___x_1988_ = 3;
v___x_1989_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set_uint8(v___x_1989_, sizeof(void*)*1, v___x_1988_);
v___x_1990_ = lean_array_push(v_a_1942_, v___x_1989_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1990_);
v___x_1992_ = v___x_1926_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_trace_1923_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_buildTime_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*3 + 1, v_wantsRebuild_1921_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*3 + 2, v_canceled_1922_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*3, v___x_1929_);
v_a_1934_ = v___x_1943_;
v_a_1935_ = v___x_1992_;
goto v___jp_1933_;
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v_a_1995_; lean_object* v___x_1997_; 
lean_dec_ref(v___x_1931_);
lean_dec_ref(v_traceFile_1897_);
v_a_1994_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1994_);
v_a_1995_ = lean_ctor_get(v___x_1940_, 1);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1940_, 2);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v_a_1995_);
v___x_1997_ = v___x_1926_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1995_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_trace_1923_);
lean_ctor_set(v_reuseFailAlloc_1998_, 2, v_buildTime_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1998_, sizeof(void*)*3 + 1, v_wantsRebuild_1921_);
lean_ctor_set_uint8(v_reuseFailAlloc_1998_, sizeof(void*)*3 + 2, v_canceled_1922_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_ctor_set_uint8(v___x_1997_, sizeof(void*)*3, v___x_1929_);
v_a_1934_ = v_a_1994_;
v_a_1935_ = v___x_1997_;
goto v___jp_1933_;
}
}
v___jp_1933_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v_a_1938_; 
v___x_1936_ = lean_box(0);
v___x_1937_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___lam__0(v___x_1932_, v___x_1936_, v_a_1935_);
lean_dec(v___x_1932_);
v_a_1938_ = lean_ctor_get(v___x_1937_, 1);
lean_inc(v_a_1938_);
lean_dec_ref(v___x_1937_);
v_a_1903_ = v_a_1934_;
v_a_1904_ = v_a_1938_;
goto v___jp_1902_;
}
}
else
{
uint8_t v___x_1999_; 
lean_dec_ref(v_archiveFile_1894_);
lean_dec_ref(v_url_1893_);
v___x_1999_ = l_System_FilePath_pathExists(v_traceFile_1897_);
lean_dec_ref(v_traceFile_1897_);
if (v___x_1999_ == 0)
{
lean_dec_ref(v___x_1931_);
lean_del_object(v___x_1926_);
v_log_1907_ = v_log_1919_;
v_action_1908_ = v___x_1929_;
v_wantsRebuild_1909_ = v_noBuild_1928_;
v_canceled_1910_ = v_canceled_1922_;
v_trace_1911_ = v_trace_1923_;
v_buildTime_1912_ = v_buildTime_1924_;
goto v___jp_1906_;
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2000_ = lean_box(0);
v___x_2001_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__0));
v___x_2002_ = l___private_Lake_Build_Common_0__Lake_BuildMetadata_ofBuildCore(v_depTrace_1896_, v___x_2000_, v___x_2001_);
v___x_2003_ = l_Lake_BuildMetadata_writeFile(v___x_1931_, v___x_2002_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_dec_ref_known(v___x_2003_, 1);
lean_del_object(v___x_1926_);
v_log_1907_ = v_log_1919_;
v_action_1908_ = v___x_1929_;
v_wantsRebuild_1909_ = v_noBuild_1928_;
v_canceled_1910_ = v_canceled_1922_;
v_trace_1911_ = v_trace_1923_;
v_buildTime_1912_ = v_buildTime_1924_;
goto v___jp_1906_;
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = lean_io_error_to_string(v_a_2004_);
v___x_2006_ = 3;
v___x_2007_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2007_, 0, v___x_2005_);
lean_ctor_set_uint8(v___x_2007_, sizeof(void*)*1, v___x_2006_);
v___x_2008_ = lean_array_get_size(v_log_1919_);
v___x_2009_ = lean_array_push(v_log_1919_, v___x_2007_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_2009_);
v___x_2011_ = v___x_1926_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2013_, 1, v_trace_1923_);
lean_ctor_set(v_reuseFailAlloc_2013_, 2, v_buildTime_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_2013_, sizeof(void*)*3 + 2, v_canceled_1922_);
v___x_2011_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v___x_2012_; 
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*3, v___x_1929_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*3 + 1, v_noBuild_1928_);
v___x_2012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2008_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
return v___x_2012_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg___boxed(lean_object* v_url_2015_, lean_object* v_archiveFile_2016_, lean_object* v_headers_2017_, lean_object* v_depTrace_2018_, lean_object* v_traceFile_2019_, lean_object* v_action_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
uint8_t v_action_boxed_2024_; lean_object* v_res_2025_; 
v_action_boxed_2024_ = lean_unbox(v_action_2020_);
v_res_2025_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2015_, v_archiveFile_2016_, v_headers_2017_, v_depTrace_2018_, v_traceFile_2019_, v_action_boxed_2024_, v_a_2021_, v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec_ref(v_depTrace_2018_);
lean_dec_ref(v_headers_2017_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(lean_object* v_url_2026_, lean_object* v_archiveFile_2027_, lean_object* v_headers_2028_, lean_object* v_a_2029_, lean_object* v_depTrace_2030_, lean_object* v_traceFile_2031_, uint8_t v_action_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v___x_2039_; 
v___x_2039_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2026_, v_archiveFile_2027_, v_headers_2028_, v_depTrace_2030_, v_traceFile_2031_, v_action_2032_, v_a_2036_, v_a_2037_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___boxed(lean_object* v_url_2040_, lean_object* v_archiveFile_2041_, lean_object* v_headers_2042_, lean_object* v_a_2043_, lean_object* v_depTrace_2044_, lean_object* v_traceFile_2045_, lean_object* v_action_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
uint8_t v_action_boxed_2053_; lean_object* v_res_2054_; 
v_action_boxed_2053_ = lean_unbox(v_action_2046_);
v_res_2054_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1(v_url_2040_, v_archiveFile_2041_, v_headers_2042_, v_a_2043_, v_depTrace_2044_, v_traceFile_2045_, v_action_boxed_2053_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec_ref(v_depTrace_2044_);
lean_dec_ref(v_a_2043_);
lean_dec_ref(v_headers_2042_);
return v_res_2054_;
}
}
LEAN_EXPORT uint8_t l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(lean_object* v_info_2055_, lean_object* v_self_2056_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_io_metadata(v_info_2055_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v_modified_2060_; uint8_t v___x_2061_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v_modified_2060_ = lean_ctor_get(v_a_2059_, 1);
lean_inc_ref(v_modified_2060_);
lean_dec(v_a_2059_);
v___x_2061_ = l_IO_FS_instOrdSystemTime_ord(v_self_2056_, v_modified_2060_);
lean_dec_ref(v_modified_2060_);
if (v___x_2061_ == 0)
{
uint8_t v___x_2062_; 
v___x_2062_ = 1;
return v___x_2062_;
}
else
{
uint8_t v___x_2063_; 
v___x_2063_ = 0;
return v___x_2063_;
}
}
else
{
uint8_t v___x_2064_; 
lean_dec_ref_known(v___x_2058_, 1);
v___x_2064_ = 0;
return v___x_2064_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1___boxed(lean_object* v_info_2065_, lean_object* v_self_2066_, lean_object* v_a_2067_){
_start:
{
uint8_t v_res_2068_; lean_object* v_r_2069_; 
v_res_2068_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2065_, v_self_2066_);
lean_dec_ref(v_self_2066_);
lean_dec_ref(v_info_2065_);
v_r_2069_ = lean_box(v_res_2068_);
return v_r_2069_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(lean_object* v_x_2070_, lean_object* v_x_2071_){
_start:
{
if (lean_obj_tag(v_x_2070_) == 0)
{
if (lean_obj_tag(v_x_2071_) == 0)
{
uint8_t v___x_2072_; 
v___x_2072_ = 1;
return v___x_2072_;
}
else
{
uint8_t v___x_2073_; 
v___x_2073_ = 0;
return v___x_2073_;
}
}
else
{
if (lean_obj_tag(v_x_2071_) == 0)
{
uint8_t v___x_2074_; 
v___x_2074_ = 0;
return v___x_2074_;
}
else
{
lean_object* v_val_2075_; lean_object* v_val_2076_; uint64_t v___x_2077_; uint64_t v___x_2078_; uint8_t v___x_2079_; 
v_val_2075_ = lean_ctor_get(v_x_2070_, 0);
v_val_2076_ = lean_ctor_get(v_x_2071_, 0);
v___x_2077_ = lean_unbox_uint64(v_val_2075_);
v___x_2078_ = lean_unbox_uint64(v_val_2076_);
v___x_2079_ = lean_uint64_dec_eq(v___x_2077_, v___x_2078_);
return v___x_2079_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2080_, lean_object* v_x_2081_){
_start:
{
uint8_t v_res_2082_; lean_object* v_r_2083_; 
v_res_2082_ = l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v_x_2080_, v_x_2081_);
lean_dec(v_x_2081_);
lean_dec(v_x_2080_);
v_r_2083_ = lean_box(v_res_2082_);
return v_r_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(lean_object* v_info_2084_, lean_object* v_depTrace_2085_, lean_object* v_depHash_2086_, lean_object* v_oldTrace_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
uint64_t v_hash_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v_hash_2091_ = lean_ctor_get_uint64(v_depTrace_2085_, sizeof(void*)*3);
v___x_2092_ = lean_box_uint64(v_hash_2091_);
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
v___x_2094_ = l_instBEqOption_beq___at___00__private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0_spec__2(v___x_2093_, v_depHash_2086_);
lean_dec_ref_known(v___x_2093_, 1);
if (v___x_2094_ == 0)
{
lean_object* v_toBuildConfig_2095_; uint8_t v_oldMode_2096_; 
v_toBuildConfig_2095_ = lean_ctor_get(v_a_2088_, 0);
v_oldMode_2096_ = lean_ctor_get_uint8(v_toBuildConfig_2095_, sizeof(void*)*5);
if (v_oldMode_2096_ == 0)
{
uint8_t v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2097_ = 0;
v___x_2098_ = lean_box(v___x_2097_);
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v_a_2089_);
return v___x_2099_;
}
else
{
uint8_t v___x_2100_; 
v___x_2100_ = l_Lake_MTime_checkUpToDate___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__1(v_info_2084_, v_oldTrace_2087_);
if (v___x_2100_ == 0)
{
uint8_t v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2101_ = 0;
v___x_2102_ = lean_box(v___x_2101_);
v___x_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
lean_ctor_set(v___x_2103_, 1, v_a_2089_);
return v___x_2103_;
}
else
{
uint8_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2104_ = 1;
v___x_2105_ = lean_box(v___x_2104_);
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v_a_2089_);
return v___x_2106_;
}
}
}
else
{
uint8_t v___x_2107_; 
v___x_2107_ = l_System_FilePath_pathExists(v_info_2084_);
if (v___x_2107_ == 0)
{
uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = 0;
v___x_2109_ = lean_box(v___x_2108_);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set(v___x_2110_, 1, v_a_2089_);
return v___x_2110_;
}
else
{
uint8_t v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = 2;
v___x_2112_ = lean_box(v___x_2111_);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v_a_2089_);
return v___x_2113_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg___boxed(lean_object* v_info_2114_, lean_object* v_depTrace_2115_, lean_object* v_depHash_2116_, lean_object* v_oldTrace_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2114_, v_depTrace_2115_, v_depHash_2116_, v_oldTrace_2117_, v_a_2118_, v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec_ref(v_oldTrace_2117_);
lean_dec(v_depHash_2116_);
lean_dec_ref(v_depTrace_2115_);
lean_dec_ref(v_info_2114_);
return v_res_2121_;
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
lean_object* v___y_2149_; lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2153_ = lean_obj_tag_nat(v_a_2143_);
v___x_2154_ = lean_unsigned_to_nat(0u);
v___x_2155_ = lean_nat_dec_eq(v___x_2153_, v___x_2154_);
if (v___x_2155_ == 0)
{
lean_object* v_log_2156_; uint8_t v_action_2157_; uint8_t v_wantsRebuild_2158_; uint8_t v_canceled_2159_; lean_object* v_trace_2160_; lean_object* v_buildTime_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2181_; 
v_log_2156_ = lean_ctor_get(v_a_2144_, 0);
v_action_2157_ = lean_ctor_get_uint8(v_a_2144_, sizeof(void*)*3);
v_wantsRebuild_2158_ = lean_ctor_get_uint8(v_a_2144_, sizeof(void*)*3 + 1);
v_canceled_2159_ = lean_ctor_get_uint8(v_a_2144_, sizeof(void*)*3 + 2);
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
lean_inc(v_log_2156_);
lean_dec(v_a_2144_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2181_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
uint8_t v___x_2165_; uint8_t v___x_2166_; lean_object* v___x_2168_; 
v___x_2165_ = 2;
v___x_2166_ = l_Lake_JobAction_merge(v_action_2157_, v___x_2165_);
if (v_isShared_2164_ == 0)
{
v___x_2168_ = v___x_2163_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_log_2156_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_trace_2160_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_buildTime_2161_);
lean_ctor_set_uint8(v_reuseFailAlloc_2180_, sizeof(void*)*3 + 1, v_wantsRebuild_2158_);
lean_ctor_set_uint8(v_reuseFailAlloc_2180_, sizeof(void*)*3 + 2, v_canceled_2159_);
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
v_oldMode_2186_ = lean_ctor_get_uint8(v_toBuildConfig_2185_, sizeof(void*)*5);
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
uint8_t v___y_2230_; lean_object* v___y_2231_; uint8_t v___y_2232_; uint8_t v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; uint8_t v_a_2262_; lean_object* v_a_2263_; lean_object* v_a_2279_; lean_object* v_a_2280_; lean_object* v_log_2282_; uint8_t v_action_2283_; uint8_t v_wantsRebuild_2284_; uint8_t v_canceled_2285_; lean_object* v_trace_2286_; lean_object* v_buildTime_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2326_; 
v_log_2282_ = lean_ctor_get(v_a_2227_, 0);
v_action_2283_ = lean_ctor_get_uint8(v_a_2227_, sizeof(void*)*3);
v_wantsRebuild_2284_ = lean_ctor_get_uint8(v_a_2227_, sizeof(void*)*3 + 1);
v_canceled_2285_ = lean_ctor_get_uint8(v_a_2227_, sizeof(void*)*3 + 2);
v_trace_2286_ = lean_ctor_get(v_a_2227_, 1);
v_buildTime_2287_ = lean_ctor_get(v_a_2227_, 2);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_a_2227_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2289_ = v_a_2227_;
v_isShared_2290_ = v_isSharedCheck_2326_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_buildTime_2287_);
lean_inc(v_trace_2286_);
lean_inc(v_log_2282_);
lean_dec(v_a_2227_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2326_;
goto v_resetjp_2288_;
}
v___jp_2229_:
{
uint8_t v___x_2237_; uint8_t v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; 
v___x_2237_ = 1;
v___x_2238_ = 3;
v___x_2239_ = l_Lake_JobAction_merge(v___y_2232_, v___x_2238_);
v___x_2240_ = l_Lake_untar(v_archiveFile_2220_, v___y_2231_, v___x_2237_, v___y_2235_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2250_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_a_2242_ = lean_ctor_get(v___x_2240_, 1);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2244_ = v___x_2240_;
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2246_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2246_, 0, v_a_2242_);
lean_ctor_set(v___x_2246_, 1, v___y_2236_);
lean_ctor_set(v___x_2246_, 2, v___y_2234_);
lean_ctor_set_uint8(v___x_2246_, sizeof(void*)*3, v___x_2239_);
lean_ctor_set_uint8(v___x_2246_, sizeof(void*)*3 + 1, v___y_2230_);
lean_ctor_set_uint8(v___x_2246_, sizeof(void*)*3 + 2, v___y_2233_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 1, v___x_2246_);
v___x_2248_ = v___x_2244_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2241_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
else
{
lean_object* v_a_2251_; lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2260_; 
v_a_2251_ = lean_ctor_get(v___x_2240_, 0);
v_a_2252_ = lean_ctor_get(v___x_2240_, 1);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2254_ = v___x_2240_;
v_isShared_2255_ = v_isSharedCheck_2260_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_inc(v_a_2251_);
lean_dec(v___x_2240_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2260_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2256_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2256_, 0, v_a_2252_);
lean_ctor_set(v___x_2256_, 1, v___y_2236_);
lean_ctor_set(v___x_2256_, 2, v___y_2234_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*3, v___x_2239_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*3 + 1, v___y_2230_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*3 + 2, v___y_2233_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 1, v___x_2256_);
v___x_2258_ = v___x_2254_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_a_2251_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
v___jp_2261_:
{
lean_object* v_config_2264_; lean_object* v_dir_2265_; lean_object* v_buildDir_2266_; lean_object* v_log_2267_; uint8_t v_action_2268_; uint8_t v_wantsRebuild_2269_; uint8_t v_canceled_2270_; lean_object* v_trace_2271_; lean_object* v_buildTime_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v_config_2264_ = lean_ctor_get(v_self_2218_, 6);
lean_inc_ref(v_config_2264_);
v_dir_2265_ = lean_ctor_get(v_self_2218_, 4);
lean_inc_ref(v_dir_2265_);
lean_dec_ref(v_self_2218_);
v_buildDir_2266_ = lean_ctor_get(v_config_2264_, 5);
lean_inc_ref(v_buildDir_2266_);
lean_dec_ref(v_config_2264_);
v_log_2267_ = lean_ctor_get(v_a_2263_, 0);
v_action_2268_ = lean_ctor_get_uint8(v_a_2263_, sizeof(void*)*3);
v_wantsRebuild_2269_ = lean_ctor_get_uint8(v_a_2263_, sizeof(void*)*3 + 1);
v_canceled_2270_ = lean_ctor_get_uint8(v_a_2263_, sizeof(void*)*3 + 2);
v_trace_2271_ = lean_ctor_get(v_a_2263_, 1);
v_buildTime_2272_ = lean_ctor_get(v_a_2263_, 2);
v___x_2273_ = l_System_FilePath_normalize(v_buildDir_2266_);
v___x_2274_ = l_Lake_joinRelative(v_dir_2265_, v___x_2273_);
v___x_2275_ = l_System_FilePath_pathExists(v___x_2274_);
if (v_a_2262_ == 0)
{
lean_inc(v_buildTime_2272_);
lean_inc_ref(v_trace_2271_);
lean_inc_ref(v_log_2267_);
lean_dec_ref(v_a_2263_);
v___y_2230_ = v_wantsRebuild_2269_;
v___y_2231_ = v___x_2274_;
v___y_2232_ = v_action_2268_;
v___y_2233_ = v_canceled_2270_;
v___y_2234_ = v_buildTime_2272_;
v___y_2235_ = v_log_2267_;
v___y_2236_ = v_trace_2271_;
goto v___jp_2229_;
}
else
{
if (v___x_2275_ == 0)
{
lean_inc(v_buildTime_2272_);
lean_inc_ref(v_trace_2271_);
lean_inc_ref(v_log_2267_);
lean_dec_ref(v_a_2263_);
v___y_2230_ = v_wantsRebuild_2269_;
v___y_2231_ = v___x_2274_;
v___y_2232_ = v_action_2268_;
v___y_2233_ = v_canceled_2270_;
v___y_2234_ = v_buildTime_2272_;
v___y_2235_ = v_log_2267_;
v___y_2236_ = v_trace_2271_;
goto v___jp_2229_;
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_dec_ref(v___x_2274_);
lean_dec_ref(v_archiveFile_2220_);
v___x_2276_ = lean_box(0);
v___x_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
lean_ctor_set(v___x_2277_, 1, v_a_2263_);
return v___x_2277_;
}
}
}
v___jp_2278_:
{
lean_object* v___x_2281_; 
v___x_2281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2281_, 0, v_a_2279_);
lean_ctor_set(v___x_2281_, 1, v_a_2280_);
return v___x_2281_;
}
v_resetjp_2288_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; uint64_t v___x_2293_; uint64_t v___x_2294_; uint64_t v_depTrace_2295_; lean_object* v___x_2296_; lean_object* v_traceFile_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; 
v___x_2291_ = lean_unsigned_to_nat(0u);
v___x_2292_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__0));
v___x_2293_ = l_Lake_Hash_nil;
v___x_2294_ = lean_string_hash(v_url_2219_);
v_depTrace_2295_ = lean_uint64_mix_hash(v___x_2293_, v___x_2294_);
v___x_2296_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__1));
lean_inc_ref(v_archiveFile_2220_);
v_traceFile_2297_ = l_System_FilePath_addExtension(v_archiveFile_2220_, v___x_2296_);
v___x_2298_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__2));
v___x_2299_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4, &l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4_once, _init_l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___closed__4);
v___x_2300_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v___x_2300_, 0, v___x_2298_);
lean_ctor_set(v___x_2300_, 1, v___x_2292_);
lean_ctor_set(v___x_2300_, 2, v___x_2299_);
lean_ctor_set_uint64(v___x_2300_, sizeof(void*)*3, v_depTrace_2295_);
v___x_2301_ = 4;
lean_inc_ref(v_traceFile_2297_);
v___x_2302_ = l_Lake_readTraceFile(v_traceFile_2297_, v_log_2282_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v_a_2304_; lean_object* v___x_2306_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
v_a_2304_ = lean_ctor_get(v___x_2302_, 1);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2302_, 2);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v_a_2304_);
v___x_2306_ = v___x_2289_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2304_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_trace_2286_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_buildTime_2287_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*3, v_action_2283_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*3 + 1, v_wantsRebuild_2284_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*3 + 2, v_canceled_2285_);
v___x_2306_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0(v_a_2222_, v_archiveFile_2220_, v___x_2300_, v_a_2303_, v___x_2299_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v___x_2306_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v_a_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
v_a_2309_ = lean_ctor_get(v___x_2307_, 1);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2307_, 2);
v___x_2310_ = lean_obj_tag_nat(v_a_2308_);
lean_dec(v_a_2308_);
v___x_2311_ = lean_nat_dec_eq(v___x_2310_, v___x_2291_);
if (v___x_2311_ == 0)
{
uint8_t v___x_2312_; 
lean_dec_ref_known(v___x_2300_, 3);
lean_dec_ref(v_traceFile_2297_);
lean_dec_ref(v_url_2219_);
v___x_2312_ = 1;
v_a_2262_ = v___x_2312_;
v_a_2263_ = v_a_2309_;
goto v___jp_2261_;
}
else
{
uint8_t v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = 0;
lean_inc_ref(v_archiveFile_2220_);
v___x_2314_ = l_Lake_buildAction___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__1___redArg(v_url_2219_, v_archiveFile_2220_, v_headers_2221_, v___x_2300_, v_traceFile_2297_, v___x_2301_, v_a_2226_, v_a_2309_);
lean_dec_ref_known(v___x_2300_, 3);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 1);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 2);
v_a_2262_ = v___x_2313_;
v_a_2263_ = v_a_2315_;
goto v___jp_2261_;
}
else
{
lean_object* v_a_2316_; lean_object* v_a_2317_; 
lean_dec_ref(v_archiveFile_2220_);
lean_dec_ref(v_self_2218_);
v_a_2316_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2316_);
v_a_2317_ = lean_ctor_get(v___x_2314_, 1);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2314_, 2);
v_a_2279_ = v_a_2316_;
v_a_2280_ = v_a_2317_;
goto v___jp_2278_;
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v_a_2319_; 
lean_dec_ref_known(v___x_2300_, 3);
lean_dec_ref(v_traceFile_2297_);
lean_dec_ref(v_archiveFile_2220_);
lean_dec_ref(v_url_2219_);
lean_dec_ref(v_self_2218_);
v_a_2318_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2318_);
v_a_2319_ = lean_ctor_get(v___x_2307_, 1);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2307_, 2);
v_a_2279_ = v_a_2318_;
v_a_2280_ = v_a_2319_;
goto v___jp_2278_;
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v_a_2322_; lean_object* v___x_2324_; 
lean_dec_ref_known(v___x_2300_, 3);
lean_dec_ref(v_traceFile_2297_);
lean_dec_ref(v_archiveFile_2220_);
lean_dec_ref(v_url_2219_);
lean_dec_ref(v_self_2218_);
v_a_2321_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2321_);
v_a_2322_ = lean_ctor_get(v___x_2302_, 1);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2302_, 2);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 0, v_a_2322_);
v___x_2324_ = v___x_2289_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2322_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_trace_2286_);
lean_ctor_set(v_reuseFailAlloc_2325_, 2, v_buildTime_2287_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*3, v_action_2283_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*3 + 1, v_wantsRebuild_2284_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*3 + 2, v_canceled_2285_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
v_a_2279_ = v_a_2321_;
v_a_2280_ = v___x_2324_;
goto v___jp_2278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive___boxed(lean_object* v_self_2327_, lean_object* v_url_2328_, lean_object* v_archiveFile_2329_, lean_object* v_headers_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_self_2327_, v_url_2328_, v_archiveFile_2329_, v_headers_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_headers_2330_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(lean_object* v_a_2339_, lean_object* v_info_2340_, lean_object* v_depTrace_2341_, lean_object* v_depHash_2342_, lean_object* v_oldTrace_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___redArg(v_info_2340_, v_depTrace_2341_, v_depHash_2342_, v_oldTrace_2343_, v_a_2347_, v_a_2348_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0___boxed(lean_object* v_a_2351_, lean_object* v_info_2352_, lean_object* v_depTrace_2353_, lean_object* v_depHash_2354_, lean_object* v_oldTrace_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Lake_Build_Common_0__Lake_checkHashUpToDate_x27___at___00Lake_SavedTrace_replayIfUpToDate_x27___at___00__private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive_spec__0_spec__0(v_a_2351_, v_info_2352_, v_depTrace_2353_, v_depHash_2354_, v_oldTrace_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec_ref(v_oldTrace_2355_);
lean_dec(v_depHash_2354_);
lean_dec_ref(v_depTrace_2353_);
lean_dec_ref(v_info_2352_);
lean_dec_ref(v_a_2351_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_getUrl_2363_, lean_object* v_pkg_2364_, lean_object* v_archiveFile_2365_, lean_object* v_headers_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
uint8_t v_r_2375_; lean_object* v___y_2376_; lean_object* v_a_2380_; lean_object* v___x_2397_; 
lean_inc_ref(v___y_2371_);
lean_inc(v___y_2370_);
lean_inc(v___y_2369_);
lean_inc(v___y_2368_);
lean_inc_ref(v___y_2367_);
lean_inc_ref(v_pkg_2364_);
v___x_2397_ = lean_apply_8(v_getUrl_2363_, v_pkg_2364_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, lean_box(0));
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v_a_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_a_2398_);
v_a_2399_ = lean_ctor_get(v___x_2397_, 1);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2397_, 2);
lean_inc_ref(v_pkg_2364_);
v___x_2400_ = lean_apply_1(v_archiveFile_2365_, v_pkg_2364_);
v___x_2401_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2364_, v_a_2398_, v___x_2400_, v_headers_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v_a_2399_);
lean_dec_ref(v___y_2367_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; uint8_t v___x_2403_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 1);
lean_inc(v_a_2402_);
lean_dec_ref_known(v___x_2401_, 2);
v___x_2403_ = 1;
v_r_2375_ = v___x_2403_;
v___y_2376_ = v_a_2402_;
goto v___jp_2374_;
}
else
{
lean_object* v_a_2404_; 
v_a_2404_ = lean_ctor_get(v___x_2401_, 1);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2401_, 2);
v_a_2380_ = v_a_2404_;
goto v___jp_2379_;
}
}
else
{
lean_object* v_a_2405_; 
lean_dec_ref(v___y_2367_);
lean_dec_ref(v_archiveFile_2365_);
lean_dec_ref(v_pkg_2364_);
v_a_2405_ = lean_ctor_get(v___x_2397_, 1);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2397_, 2);
v_a_2380_ = v_a_2405_;
goto v___jp_2379_;
}
v___jp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_box(v_r_2375_);
v___x_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
lean_ctor_set(v___x_2378_, 1, v___y_2376_);
return v___x_2378_;
}
v___jp_2379_:
{
lean_object* v_log_2381_; uint8_t v_action_2382_; uint8_t v_wantsRebuild_2383_; uint8_t v_canceled_2384_; lean_object* v_trace_2385_; lean_object* v_buildTime_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2396_; 
v_log_2381_ = lean_ctor_get(v_a_2380_, 0);
v_action_2382_ = lean_ctor_get_uint8(v_a_2380_, sizeof(void*)*3);
v_wantsRebuild_2383_ = lean_ctor_get_uint8(v_a_2380_, sizeof(void*)*3 + 1);
v_canceled_2384_ = lean_ctor_get_uint8(v_a_2380_, sizeof(void*)*3 + 2);
v_trace_2385_ = lean_ctor_get(v_a_2380_, 1);
v_buildTime_2386_ = lean_ctor_get(v_a_2380_, 2);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_a_2380_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2388_ = v_a_2380_;
v_isShared_2389_ = v_isSharedCheck_2396_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_buildTime_2386_);
lean_inc(v_trace_2385_);
lean_inc(v_log_2381_);
lean_dec(v_a_2380_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2396_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
uint8_t v___x_2390_; uint8_t v___x_2391_; lean_object* v___x_2393_; 
v___x_2390_ = 4;
v___x_2391_ = l_Lake_JobAction_merge(v_action_2382_, v___x_2390_);
if (v_isShared_2389_ == 0)
{
v___x_2393_ = v___x_2388_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_log_2381_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_trace_2385_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_buildTime_2386_);
lean_ctor_set_uint8(v_reuseFailAlloc_2395_, sizeof(void*)*3 + 1, v_wantsRebuild_2383_);
lean_ctor_set_uint8(v_reuseFailAlloc_2395_, sizeof(void*)*3 + 2, v_canceled_2384_);
v___x_2393_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
uint8_t v___x_2394_; 
lean_ctor_set_uint8(v___x_2393_, sizeof(void*)*3, v___x_2391_);
v___x_2394_ = 0;
v_r_2375_ = v___x_2394_;
v___y_2376_ = v___x_2393_;
goto v___jp_2374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_getUrl_2406_, lean_object* v_pkg_2407_, lean_object* v_archiveFile_2408_, lean_object* v_headers_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0(v_getUrl_2406_, v_pkg_2407_, v_archiveFile_2408_, v_headers_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v_headers_2409_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(lean_object* v_getUrl_2418_, lean_object* v_archiveFile_2419_, lean_object* v_headers_2420_, lean_object* v_facet_2421_, lean_object* v___x_2422_, lean_object* v_pkg_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_baseName_2431_; lean_object* v___f_2432_; uint8_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_baseName_2431_ = lean_ctor_get(v_pkg_2423_, 1);
lean_inc(v_baseName_2431_);
v___f_2432_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2432_, 0, v_getUrl_2418_);
lean_closure_set(v___f_2432_, 1, v_pkg_2423_);
lean_closure_set(v___f_2432_, 2, v_archiveFile_2419_);
lean_closure_set(v___f_2432_, 3, v_headers_2420_);
v___x_2433_ = 1;
v___x_2434_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2431_, v___x_2433_);
v___x_2435_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2436_ = lean_string_append(v___x_2434_, v___x_2435_);
v___x_2437_ = l_Lake_Name_eraseHead(v_facet_2421_);
v___x_2438_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2437_, v___x_2433_);
v___x_2439_ = lean_string_append(v___x_2436_, v___x_2438_);
lean_dec_ref(v___x_2438_);
v___x_2440_ = lean_unsigned_to_nat(0u);
v___x_2441_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2422_);
v___x_2442_ = lean_alloc_closure((void*)(l_Lake_Job_async___boxed), 12, 5);
lean_closure_set(v___x_2442_, 0, lean_box(0));
lean_closure_set(v___x_2442_, 1, v___x_2422_);
lean_closure_set(v___x_2442_, 2, v___f_2432_);
lean_closure_set(v___x_2442_, 3, v___x_2440_);
lean_closure_set(v___x_2442_, 4, v___x_2441_);
v___x_2443_ = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM___boxed), 9, 2);
lean_closure_set(v___x_2443_, 0, lean_box(0));
lean_closure_set(v___x_2443_, 1, v___x_2442_);
v___x_2444_ = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM___boxed), 9, 2);
lean_closure_set(v___x_2444_, 0, lean_box(0));
lean_closure_set(v___x_2444_, 1, v___x_2443_);
v___x_2445_ = l_Lake_ensureJob___redArg(v___x_2422_, v___x_2444_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2470_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_a_2447_ = lean_ctor_get(v___x_2445_, 1);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2449_ = v___x_2445_;
v_isShared_2450_ = v_isSharedCheck_2470_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2470_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v_task_2451_; lean_object* v_kind_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2468_; 
v_task_2451_ = lean_ctor_get(v_a_2446_, 0);
v_kind_2452_ = lean_ctor_get(v_a_2446_, 1);
v_isSharedCheck_2468_ = !lean_is_exclusive(v_a_2446_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; 
v_unused_2469_ = lean_ctor_get(v_a_2446_, 2);
lean_dec(v_unused_2469_);
v___x_2454_ = v_a_2446_;
v_isShared_2455_ = v_isSharedCheck_2468_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_kind_2452_);
lean_inc(v_task_2451_);
lean_dec(v_a_2446_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2468_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v_registeredJobs_2456_; lean_object* v_job_2458_; 
v_registeredJobs_2456_ = lean_ctor_get(v___y_2428_, 4);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 2, v___x_2439_);
v_job_2458_ = v___x_2454_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_task_2451_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_kind_2452_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v___x_2439_);
v_job_2458_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
lean_ctor_set_uint8(v_job_2458_, sizeof(void*)*3, v___x_2433_);
v___x_2459_ = lean_st_ref_take(v_registeredJobs_2456_);
lean_inc_ref(v_job_2458_);
v___x_2460_ = l_Lake_Job_toOpaque___redArg(v_job_2458_);
v___x_2461_ = lean_array_push(v___x_2459_, v___x_2460_);
v___x_2462_ = lean_st_ref_put(v_registeredJobs_2456_, v___x_2461_);
v___x_2463_ = l_Lake_Job_renew___redArg(v_job_2458_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2463_);
v___x_2465_ = v___x_2449_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_a_2447_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2439_);
return v___x_2445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v_getUrl_2471_, lean_object* v_archiveFile_2472_, lean_object* v_headers_2473_, lean_object* v_facet_2474_, lean_object* v___x_2475_, lean_object* v_pkg_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1(v_getUrl_2471_, v_archiveFile_2472_, v_headers_2473_, v_facet_2474_, v___x_2475_, v_pkg_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec(v___y_2478_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg(lean_object* v_facet_2492_, lean_object* v_archiveFile_2493_, lean_object* v_getUrl_2494_, lean_object* v_headers_2495_){
_start:
{
lean_object* v___x_2496_; lean_object* v___f_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2496_ = l_Lake_instDataKindBool;
v___f_2497_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2497_, 0, v_getUrl_2494_);
lean_closure_set(v___f_2497_, 1, v_archiveFile_2493_);
lean_closure_set(v___f_2497_, 2, v_headers_2495_);
lean_closure_set(v___f_2497_, 3, v_facet_2492_);
lean_closure_set(v___f_2497_, 4, v___x_2496_);
v___x_2498_ = l_Lake_Package_keyword;
v___x_2499_ = 1;
v___x_2500_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_2501_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2501_, 0, v___x_2498_);
lean_ctor_set(v___x_2501_, 1, v___f_2497_);
lean_ctor_set(v___x_2501_, 2, v___x_2496_);
lean_ctor_set(v___x_2501_, 3, v___x_2500_);
lean_ctor_set_uint8(v___x_2501_, sizeof(void*)*4, v___x_2499_);
lean_ctor_set_uint8(v___x_2501_, sizeof(void*)*4 + 1, v___x_2499_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig(lean_object* v_facet_2502_, lean_object* v_archiveFile_2503_, lean_object* v_getUrl_2504_, lean_object* v_headers_2505_, lean_object* v_inst_2506_){
_start:
{
lean_object* v___x_2507_; lean_object* v___f_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2507_ = l_Lake_instDataKindBool;
v___f_2508_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___lam__1___boxed), 13, 5);
lean_closure_set(v___f_2508_, 0, v_getUrl_2504_);
lean_closure_set(v___f_2508_, 1, v_archiveFile_2503_);
lean_closure_set(v___f_2508_, 2, v_headers_2505_);
lean_closure_set(v___f_2508_, 3, v_facet_2502_);
lean_closure_set(v___f_2508_, 4, v___x_2507_);
v___x_2509_ = l_Lake_Package_keyword;
v___x_2510_ = 1;
v___x_2511_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkOptBuildArchiveFacetConfig___redArg___closed__3));
v___x_2512_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2512_, 0, v___x_2509_);
lean_ctor_set(v___x_2512_, 1, v___f_2508_);
lean_ctor_set(v___x_2512_, 2, v___x_2507_);
lean_ctor_set(v___x_2512_, 3, v___x_2511_);
lean_ctor_set_uint8(v___x_2512_, sizeof(void*)*4, v___x_2510_);
lean_ctor_set_uint8(v___x_2512_, sizeof(void*)*4 + 1, v___x_2510_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(lean_object* v_what_2514_, lean_object* v_baseName_2515_, lean_object* v_optFacet_2516_, uint8_t v_success_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_a_2526_; lean_object* v_a_2527_; 
if (v_success_2517_ == 0)
{
lean_object* v_toBuildConfig_2549_; uint8_t v_verbosity_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v_toBuildConfig_2549_ = lean_ctor_get(v___y_2522_, 0);
v_verbosity_2550_ = lean_ctor_get_uint8(v_toBuildConfig_2549_, sizeof(void*)*5 + 4);
v___x_2551_ = lean_box(v_verbosity_2550_);
v___x_2552_ = lean_obj_tag_nat(v___x_2551_);
lean_dec(v___x_2551_);
v___x_2553_ = lean_unsigned_to_nat(2u);
v___x_2554_ = lean_nat_dec_eq(v___x_2552_, v___x_2553_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; 
lean_dec(v_optFacet_2516_);
lean_dec(v_baseName_2515_);
v___x_2555_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2526_ = v___x_2555_;
v_a_2527_ = v___y_2523_;
goto v___jp_2525_;
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2556_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2557_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2515_, v___x_2554_);
v___x_2558_ = lean_string_append(v___x_2556_, v___x_2557_);
lean_dec_ref(v___x_2557_);
v___x_2559_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2560_ = lean_string_append(v___x_2558_, v___x_2559_);
v___x_2561_ = l_Lake_Name_eraseHead(v_optFacet_2516_);
v___x_2562_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2561_, v___x_2554_);
v___x_2563_ = lean_string_append(v___x_2560_, v___x_2562_);
lean_dec_ref(v___x_2562_);
v___x_2564_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2565_ = lean_string_append(v___x_2563_, v___x_2564_);
v_a_2526_ = v___x_2565_;
v_a_2527_ = v___y_2523_;
goto v___jp_2525_;
}
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_dec(v_optFacet_2516_);
lean_dec(v_baseName_2515_);
v___x_2566_ = lean_box(0);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
lean_ctor_set(v___x_2567_, 1, v___y_2523_);
return v___x_2567_;
}
v___jp_2525_:
{
lean_object* v_log_2528_; uint8_t v_action_2529_; uint8_t v_wantsRebuild_2530_; uint8_t v_canceled_2531_; lean_object* v_trace_2532_; lean_object* v_buildTime_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2548_; 
v_log_2528_ = lean_ctor_get(v_a_2527_, 0);
v_action_2529_ = lean_ctor_get_uint8(v_a_2527_, sizeof(void*)*3);
v_wantsRebuild_2530_ = lean_ctor_get_uint8(v_a_2527_, sizeof(void*)*3 + 1);
v_canceled_2531_ = lean_ctor_get_uint8(v_a_2527_, sizeof(void*)*3 + 2);
v_trace_2532_ = lean_ctor_get(v_a_2527_, 1);
v_buildTime_2533_ = lean_ctor_get(v_a_2527_, 2);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_a_2527_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2535_ = v_a_2527_;
v_isShared_2536_ = v_isSharedCheck_2548_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_buildTime_2533_);
lean_inc(v_trace_2532_);
lean_inc(v_log_2528_);
lean_dec(v_a_2527_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2548_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2537_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___closed__0));
v___x_2538_ = lean_string_append(v___x_2537_, v_what_2514_);
v___x_2539_ = lean_string_append(v___x_2538_, v_a_2526_);
lean_dec_ref(v_a_2526_);
v___x_2540_ = 3;
v___x_2541_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2541_, 0, v___x_2539_);
lean_ctor_set_uint8(v___x_2541_, sizeof(void*)*1, v___x_2540_);
v___x_2542_ = lean_array_get_size(v_log_2528_);
v___x_2543_ = lean_array_push(v_log_2528_, v___x_2541_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v___x_2543_);
v___x_2545_ = v___x_2535_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_trace_2532_);
lean_ctor_set(v_reuseFailAlloc_2547_, 2, v_buildTime_2533_);
lean_ctor_set_uint8(v_reuseFailAlloc_2547_, sizeof(void*)*3, v_action_2529_);
lean_ctor_set_uint8(v_reuseFailAlloc_2547_, sizeof(void*)*3 + 1, v_wantsRebuild_2530_);
lean_ctor_set_uint8(v_reuseFailAlloc_2547_, sizeof(void*)*3 + 2, v_canceled_2531_);
v___x_2545_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2546_; 
v___x_2546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2542_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
return v___x_2546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed(lean_object* v_what_2568_, lean_object* v_baseName_2569_, lean_object* v_optFacet_2570_, lean_object* v_success_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
uint8_t v_success_boxed_2579_; lean_object* v_res_2580_; 
v_success_boxed_2579_ = lean_unbox(v_success_2571_);
v_res_2580_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0(v_what_2568_, v_baseName_2569_, v_optFacet_2570_, v_success_boxed_2579_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec_ref(v_what_2568_);
return v_res_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(lean_object* v___x_2581_, lean_object* v___x_2582_, lean_object* v___f_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v___x_2591_; 
lean_inc_ref(v___y_2584_);
lean_inc_ref(v___y_2588_);
lean_inc(v___y_2587_);
lean_inc(v___y_2586_);
lean_inc(v___y_2585_);
v___x_2591_ = lean_apply_7(v___y_2584_, v___x_2581_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, lean_box(0));
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2604_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_a_2593_ = lean_ctor_get(v___x_2591_, 1);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2595_ = v___x_2591_;
v_isShared_2596_ = v_isSharedCheck_2604_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2604_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2597_; uint8_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2597_ = lean_unsigned_to_nat(0u);
v___x_2598_ = 0;
v___x_2599_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_2600_ = l_Lake_Job_mapM___redArg(v___x_2582_, v_a_2592_, v___f_2583_, v___x_2597_, v___x_2598_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___x_2599_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2600_);
v___x_2602_ = v___x_2595_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_a_2593_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref(v___y_2584_);
lean_dec_ref(v___f_2583_);
lean_dec(v___x_2582_);
v_a_2605_ = lean_ctor_get(v___x_2591_, 0);
v_a_2606_ = lean_ctor_get(v___x_2591_, 1);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2591_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_inc(v_a_2605_);
lean_dec(v___x_2591_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2605_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed(lean_object* v___x_2614_, lean_object* v___x_2615_, lean_object* v___f_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1(v___x_2614_, v___x_2615_, v___f_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec(v___y_2618_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(lean_object* v_what_2625_, lean_object* v_optFacet_2626_, lean_object* v_facet_2627_, lean_object* v___x_2628_, lean_object* v_pkg_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_baseName_2637_; lean_object* v_keyName_2638_; lean_object* v___f_2639_; uint8_t v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___f_2650_; uint8_t v___x_2651_; lean_object* v___x_2652_; 
v_baseName_2637_ = lean_ctor_get(v_pkg_2629_, 1);
v_keyName_2638_ = lean_ctor_get(v_pkg_2629_, 2);
lean_inc(v_optFacet_2626_);
lean_inc_n(v_baseName_2637_, 2);
v___f_2639_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_2639_, 0, v_what_2625_);
lean_closure_set(v___f_2639_, 1, v_baseName_2637_);
lean_closure_set(v___f_2639_, 2, v_optFacet_2626_);
v___x_2640_ = 1;
v___x_2641_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2637_, v___x_2640_);
v___x_2642_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2643_ = lean_string_append(v___x_2641_, v___x_2642_);
v___x_2644_ = l_Lake_Name_eraseHead(v_facet_2627_);
v___x_2645_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2644_, v___x_2640_);
v___x_2646_ = lean_string_append(v___x_2643_, v___x_2645_);
lean_dec_ref(v___x_2645_);
lean_inc(v_keyName_2638_);
v___x_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2647_, 0, v_keyName_2638_);
v___x_2648_ = l_Lake_Package_keyword;
v___x_2649_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2647_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
lean_ctor_set(v___x_2649_, 2, v_pkg_2629_);
lean_ctor_set(v___x_2649_, 3, v_optFacet_2626_);
lean_inc(v___x_2628_);
v___f_2650_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2650_, 0, v___x_2649_);
lean_closure_set(v___f_2650_, 1, v___x_2628_);
lean_closure_set(v___f_2650_, 2, v___f_2639_);
v___x_2651_ = 0;
v___x_2652_ = l_Lake_ensureJob___redArg(v___x_2628_, v___f_2650_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2677_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_a_2654_ = lean_ctor_get(v___x_2652_, 1);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2656_ = v___x_2652_;
v_isShared_2657_ = v_isSharedCheck_2677_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2677_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v_task_2658_; lean_object* v_kind_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2675_; 
v_task_2658_ = lean_ctor_get(v_a_2653_, 0);
v_kind_2659_ = lean_ctor_get(v_a_2653_, 1);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_a_2653_);
if (v_isSharedCheck_2675_ == 0)
{
lean_object* v_unused_2676_; 
v_unused_2676_ = lean_ctor_get(v_a_2653_, 2);
lean_dec(v_unused_2676_);
v___x_2661_ = v_a_2653_;
v_isShared_2662_ = v_isSharedCheck_2675_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_kind_2659_);
lean_inc(v_task_2658_);
lean_dec(v_a_2653_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2675_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v_registeredJobs_2663_; lean_object* v_job_2665_; 
v_registeredJobs_2663_ = lean_ctor_get(v___y_2634_, 4);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 2, v___x_2646_);
v_job_2665_ = v___x_2661_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_task_2658_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_kind_2659_);
lean_ctor_set(v_reuseFailAlloc_2674_, 2, v___x_2646_);
v_job_2665_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
lean_ctor_set_uint8(v_job_2665_, sizeof(void*)*3, v___x_2651_);
v___x_2666_ = lean_st_ref_take(v_registeredJobs_2663_);
lean_inc_ref(v_job_2665_);
v___x_2667_ = l_Lake_Job_toOpaque___redArg(v_job_2665_);
v___x_2668_ = lean_array_push(v___x_2666_, v___x_2667_);
v___x_2669_ = lean_st_ref_put(v_registeredJobs_2663_, v___x_2668_);
v___x_2670_ = l_Lake_Job_renew___redArg(v_job_2665_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2670_);
v___x_2672_ = v___x_2656_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_a_2654_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2646_);
return v___x_2652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed(lean_object* v_what_2678_, lean_object* v_optFacet_2679_, lean_object* v_facet_2680_, lean_object* v___x_2681_, lean_object* v_pkg_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2(v_what_2678_, v_optFacet_2679_, v_facet_2680_, v___x_2681_, v_pkg_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec(v___y_2684_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg(lean_object* v_facet_2698_, lean_object* v_optFacet_2699_, lean_object* v_what_2700_){
_start:
{
lean_object* v___x_2701_; lean_object* v___f_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2701_ = l_Lake_instDataKindUnit;
v___f_2702_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2702_, 0, v_what_2700_);
lean_closure_set(v___f_2702_, 1, v_optFacet_2699_);
lean_closure_set(v___f_2702_, 2, v_facet_2698_);
lean_closure_set(v___f_2702_, 3, v___x_2701_);
v___x_2703_ = l_Lake_Package_keyword;
v___x_2704_ = 1;
v___x_2705_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___closed__3));
v___x_2706_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2706_, 0, v___x_2703_);
lean_ctor_set(v___x_2706_, 1, v___f_2702_);
lean_ctor_set(v___x_2706_, 2, v___x_2701_);
lean_ctor_set(v___x_2706_, 3, v___x_2705_);
lean_ctor_set_uint8(v___x_2706_, sizeof(void*)*4, v___x_2704_);
lean_ctor_set_uint8(v___x_2706_, sizeof(void*)*4 + 1, v___x_2704_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig(lean_object* v_facet_2707_, lean_object* v_optFacet_2708_, lean_object* v_what_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_){
_start:
{
lean_object* v___x_2712_; lean_object* v___f_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2712_ = l_Lake_instDataKindUnit;
v___f_2713_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__2___boxed), 12, 4);
lean_closure_set(v___f_2713_, 0, v_what_2709_);
lean_closure_set(v___f_2713_, 1, v_optFacet_2708_);
lean_closure_set(v___f_2713_, 2, v_facet_2707_);
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
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1(lean_object* v_baseName_2719_, lean_object* v___x_2720_, uint8_t v_success_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_a_2730_; lean_object* v_a_2731_; 
if (v_success_2721_ == 0)
{
lean_object* v_toBuildConfig_2752_; uint8_t v_verbosity_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v_toBuildConfig_2752_ = lean_ctor_get(v___y_2726_, 0);
v_verbosity_2753_ = lean_ctor_get_uint8(v_toBuildConfig_2752_, sizeof(void*)*5 + 4);
v___x_2754_ = lean_box(v_verbosity_2753_);
v___x_2755_ = lean_obj_tag_nat(v___x_2754_);
lean_dec(v___x_2754_);
v___x_2756_ = lean_unsigned_to_nat(2u);
v___x_2757_ = lean_nat_dec_eq(v___x_2755_, v___x_2756_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; 
lean_dec(v___x_2720_);
lean_dec(v_baseName_2719_);
v___x_2758_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_2730_ = v___x_2758_;
v_a_2731_ = v___y_2727_;
goto v___jp_2729_;
}
else
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2759_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_2760_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2719_, v___x_2757_);
v___x_2761_ = lean_string_append(v___x_2759_, v___x_2760_);
lean_dec_ref(v___x_2760_);
v___x_2762_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2763_ = lean_string_append(v___x_2761_, v___x_2762_);
v___x_2764_ = l_Lake_Name_eraseHead(v___x_2720_);
v___x_2765_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2764_, v___x_2757_);
v___x_2766_ = lean_string_append(v___x_2763_, v___x_2765_);
lean_dec_ref(v___x_2765_);
v___x_2767_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_2768_ = lean_string_append(v___x_2766_, v___x_2767_);
v_a_2730_ = v___x_2768_;
v_a_2731_ = v___y_2727_;
goto v___jp_2729_;
}
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_dec(v___x_2720_);
lean_dec(v_baseName_2719_);
v___x_2769_ = lean_box(0);
v___x_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
lean_ctor_set(v___x_2770_, 1, v___y_2727_);
return v___x_2770_;
}
v___jp_2729_:
{
lean_object* v_log_2732_; uint8_t v_action_2733_; uint8_t v_wantsRebuild_2734_; uint8_t v_canceled_2735_; lean_object* v_trace_2736_; lean_object* v_buildTime_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2751_; 
v_log_2732_ = lean_ctor_get(v_a_2731_, 0);
v_action_2733_ = lean_ctor_get_uint8(v_a_2731_, sizeof(void*)*3);
v_wantsRebuild_2734_ = lean_ctor_get_uint8(v_a_2731_, sizeof(void*)*3 + 1);
v_canceled_2735_ = lean_ctor_get_uint8(v_a_2731_, sizeof(void*)*3 + 2);
v_trace_2736_ = lean_ctor_get(v_a_2731_, 1);
v_buildTime_2737_ = lean_ctor_get(v_a_2731_, 2);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_a_2731_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2739_ = v_a_2731_;
v_isShared_2740_ = v_isSharedCheck_2751_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_buildTime_2737_);
lean_inc(v_trace_2736_);
lean_inc(v_log_2732_);
lean_dec(v_a_2731_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2751_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2748_; 
v___x_2741_ = ((lean_object*)(l_Lake_Package_buildCacheFacetConfig___lam__1___closed__0));
v___x_2742_ = lean_string_append(v___x_2741_, v_a_2730_);
lean_dec_ref(v_a_2730_);
v___x_2743_ = 3;
v___x_2744_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2744_, 0, v___x_2742_);
lean_ctor_set_uint8(v___x_2744_, sizeof(void*)*1, v___x_2743_);
v___x_2745_ = lean_array_get_size(v_log_2732_);
v___x_2746_ = lean_array_push(v_log_2732_, v___x_2744_);
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 0, v___x_2746_);
v___x_2748_ = v___x_2739_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2746_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_trace_2736_);
lean_ctor_set(v_reuseFailAlloc_2750_, 2, v_buildTime_2737_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*3, v_action_2733_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*3 + 1, v_wantsRebuild_2734_);
lean_ctor_set_uint8(v_reuseFailAlloc_2750_, sizeof(void*)*3 + 2, v_canceled_2735_);
v___x_2748_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
lean_object* v___x_2749_; 
v___x_2749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2745_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
return v___x_2749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__1___boxed(lean_object* v_baseName_2771_, lean_object* v___x_2772_, lean_object* v_success_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
uint8_t v_success_boxed_2781_; lean_object* v_res_2782_; 
v_success_boxed_2781_ = lean_unbox(v_success_2773_);
v_res_2782_ = l_Lake_Package_buildCacheFacetConfig___lam__1(v_baseName_2771_, v___x_2772_, v_success_boxed_2781_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2(lean_object* v___x_2783_, lean_object* v___x_2784_, lean_object* v___x_2785_, lean_object* v_pkg_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_baseName_2794_; lean_object* v_keyName_2795_; lean_object* v___f_2796_; uint8_t v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___f_2807_; uint8_t v___x_2808_; lean_object* v___x_2809_; 
v_baseName_2794_ = lean_ctor_get(v_pkg_2786_, 1);
v_keyName_2795_ = lean_ctor_get(v_pkg_2786_, 2);
lean_inc(v___x_2783_);
lean_inc_n(v_baseName_2794_, 2);
v___f_2796_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_2796_, 0, v_baseName_2794_);
lean_closure_set(v___f_2796_, 1, v___x_2783_);
v___x_2797_ = 1;
v___x_2798_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2794_, v___x_2797_);
v___x_2799_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2800_ = lean_string_append(v___x_2798_, v___x_2799_);
v___x_2801_ = l_Lake_Name_eraseHead(v___x_2784_);
v___x_2802_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2801_, v___x_2797_);
v___x_2803_ = lean_string_append(v___x_2800_, v___x_2802_);
lean_dec_ref(v___x_2802_);
lean_inc(v_keyName_2795_);
v___x_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2804_, 0, v_keyName_2795_);
v___x_2805_ = l_Lake_Package_keyword;
v___x_2806_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
lean_ctor_set(v___x_2806_, 2, v_pkg_2786_);
lean_ctor_set(v___x_2806_, 3, v___x_2783_);
lean_inc(v___x_2785_);
v___f_2807_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_2807_, 0, v___x_2806_);
lean_closure_set(v___f_2807_, 1, v___x_2785_);
lean_closure_set(v___f_2807_, 2, v___f_2796_);
v___x_2808_ = 0;
v___x_2809_ = l_Lake_ensureJob___redArg(v___x_2785_, v___f_2807_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2834_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
v_a_2811_ = lean_ctor_get(v___x_2809_, 1);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2813_ = v___x_2809_;
v_isShared_2814_ = v_isSharedCheck_2834_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_inc(v_a_2810_);
lean_dec(v___x_2809_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2834_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v_task_2815_; lean_object* v_kind_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2832_; 
v_task_2815_ = lean_ctor_get(v_a_2810_, 0);
v_kind_2816_ = lean_ctor_get(v_a_2810_, 1);
v_isSharedCheck_2832_ = !lean_is_exclusive(v_a_2810_);
if (v_isSharedCheck_2832_ == 0)
{
lean_object* v_unused_2833_; 
v_unused_2833_ = lean_ctor_get(v_a_2810_, 2);
lean_dec(v_unused_2833_);
v___x_2818_ = v_a_2810_;
v_isShared_2819_ = v_isSharedCheck_2832_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_kind_2816_);
lean_inc(v_task_2815_);
lean_dec(v_a_2810_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2832_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v_registeredJobs_2820_; lean_object* v_job_2822_; 
v_registeredJobs_2820_ = lean_ctor_get(v___y_2791_, 4);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 2, v___x_2803_);
v_job_2822_ = v___x_2818_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_task_2815_);
lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_kind_2816_);
lean_ctor_set(v_reuseFailAlloc_2831_, 2, v___x_2803_);
v_job_2822_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2829_; 
lean_ctor_set_uint8(v_job_2822_, sizeof(void*)*3, v___x_2808_);
v___x_2823_ = lean_st_ref_take(v_registeredJobs_2820_);
lean_inc_ref(v_job_2822_);
v___x_2824_ = l_Lake_Job_toOpaque___redArg(v_job_2822_);
v___x_2825_ = lean_array_push(v___x_2823_, v___x_2824_);
v___x_2826_ = lean_st_ref_put(v_registeredJobs_2820_, v___x_2825_);
v___x_2827_ = l_Lake_Job_renew___redArg(v_job_2822_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2827_);
v___x_2829_ = v___x_2813_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2827_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v_a_2811_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2803_);
return v___x_2809_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_buildCacheFacetConfig___lam__2___boxed(lean_object* v___x_2835_, lean_object* v___x_2836_, lean_object* v___x_2837_, lean_object* v_pkg_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_Lake_Package_buildCacheFacetConfig___lam__2(v___x_2835_, v___x_2836_, v___x_2837_, v_pkg_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec(v___y_2840_);
return v_res_2846_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___f_2850_; 
v___x_2847_ = l_Lake_instDataKindUnit;
v___x_2848_ = l_Lake_Package_buildCacheFacet;
v___x_2849_ = l_Lake_Package_optBuildCacheFacet;
v___f_2850_ = lean_alloc_closure((void*)(l_Lake_Package_buildCacheFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_2850_, 0, v___x_2849_);
lean_closure_set(v___f_2850_, 1, v___x_2848_);
lean_closure_set(v___f_2850_, 2, v___x_2847_);
return v___f_2850_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; lean_object* v___f_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___f_2851_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_2852_ = 1;
v___x_2853_ = l_Lake_instDataKindUnit;
v___f_2854_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__0, &l_Lake_Package_buildCacheFacetConfig___closed__0_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__0);
v___x_2855_ = l_Lake_Package_keyword;
v___x_2856_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v___f_2854_);
lean_ctor_set(v___x_2856_, 2, v___x_2853_);
lean_ctor_set(v___x_2856_, 3, v___f_2851_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*4, v___x_2852_);
lean_ctor_set_uint8(v___x_2856_, sizeof(void*)*4 + 1, v___x_2852_);
return v___x_2856_;
}
}
static lean_object* _init_l_Lake_Package_buildCacheFacetConfig(void){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_obj_once(&l_Lake_Package_buildCacheFacetConfig___closed__1, &l_Lake_Package_buildCacheFacetConfig___closed__1_once, _init_l_Lake_Package_buildCacheFacetConfig___closed__1);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0(lean_object* v_pkg_2859_, lean_object* v_dir_2860_, lean_object* v___x_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
uint8_t v_r_2870_; lean_object* v___y_2871_; lean_object* v_a_2875_; lean_object* v___x_2892_; 
lean_inc_ref(v_pkg_2859_);
v___x_2892_ = l___private_Lake_Build_Package_0__Lake_Package_getBarrelUrl___redArg(v_pkg_2859_, v___y_2866_, v___y_2867_);
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
v_a_2894_ = lean_ctor_get(v___x_2892_, 1);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2892_, 2);
v___x_2895_ = l_Lake_defaultLakeDir;
v___x_2896_ = l_Lake_joinRelative(v_dir_2860_, v___x_2895_);
v___x_2897_ = ((lean_object*)(l_Lake_Package_optBarrelFacetConfig___lam__0___closed__0));
v___x_2898_ = l_Lake_joinRelative(v___x_2896_, v___x_2897_);
v___x_2899_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_2859_, v_a_2893_, v___x_2898_, v___x_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v_a_2894_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; uint8_t v___x_2901_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 1);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2899_, 2);
v___x_2901_ = 1;
v_r_2870_ = v___x_2901_;
v___y_2871_ = v_a_2900_;
goto v___jp_2869_;
}
else
{
lean_object* v_a_2902_; 
v_a_2902_ = lean_ctor_get(v___x_2899_, 1);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2899_, 2);
v_a_2875_ = v_a_2902_;
goto v___jp_2874_;
}
}
else
{
lean_object* v_a_2903_; 
lean_dec_ref(v_dir_2860_);
lean_dec_ref(v_pkg_2859_);
v_a_2903_ = lean_ctor_get(v___x_2892_, 1);
lean_inc(v_a_2903_);
lean_dec_ref_known(v___x_2892_, 2);
v_a_2875_ = v_a_2903_;
goto v___jp_2874_;
}
v___jp_2869_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = lean_box(v_r_2870_);
v___x_2873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
lean_ctor_set(v___x_2873_, 1, v___y_2871_);
return v___x_2873_;
}
v___jp_2874_:
{
lean_object* v_log_2876_; uint8_t v_action_2877_; uint8_t v_wantsRebuild_2878_; uint8_t v_canceled_2879_; lean_object* v_trace_2880_; lean_object* v_buildTime_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2891_; 
v_log_2876_ = lean_ctor_get(v_a_2875_, 0);
v_action_2877_ = lean_ctor_get_uint8(v_a_2875_, sizeof(void*)*3);
v_wantsRebuild_2878_ = lean_ctor_get_uint8(v_a_2875_, sizeof(void*)*3 + 1);
v_canceled_2879_ = lean_ctor_get_uint8(v_a_2875_, sizeof(void*)*3 + 2);
v_trace_2880_ = lean_ctor_get(v_a_2875_, 1);
v_buildTime_2881_ = lean_ctor_get(v_a_2875_, 2);
v_isSharedCheck_2891_ = !lean_is_exclusive(v_a_2875_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2883_ = v_a_2875_;
v_isShared_2884_ = v_isSharedCheck_2891_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_buildTime_2881_);
lean_inc(v_trace_2880_);
lean_inc(v_log_2876_);
lean_dec(v_a_2875_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2891_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
uint8_t v___x_2885_; uint8_t v___x_2886_; lean_object* v___x_2888_; 
v___x_2885_ = 4;
v___x_2886_ = l_Lake_JobAction_merge(v_action_2877_, v___x_2885_);
if (v_isShared_2884_ == 0)
{
v___x_2888_ = v___x_2883_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_log_2876_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_trace_2880_);
lean_ctor_set(v_reuseFailAlloc_2890_, 2, v_buildTime_2881_);
lean_ctor_set_uint8(v_reuseFailAlloc_2890_, sizeof(void*)*3 + 1, v_wantsRebuild_2878_);
lean_ctor_set_uint8(v_reuseFailAlloc_2890_, sizeof(void*)*3 + 2, v_canceled_2879_);
v___x_2888_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
uint8_t v___x_2889_; 
lean_ctor_set_uint8(v___x_2888_, sizeof(void*)*3, v___x_2886_);
v___x_2889_ = 0;
v_r_2870_ = v___x_2889_;
v___y_2871_ = v___x_2888_;
goto v___jp_2869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__0___boxed(lean_object* v_pkg_2904_, lean_object* v_dir_2905_, lean_object* v___x_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lake_Package_optBarrelFacetConfig___lam__0(v_pkg_2904_, v_dir_2905_, v___x_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec_ref(v___x_2906_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1(lean_object* v___x_2915_, lean_object* v___f_2916_, lean_object* v___x_2917_, lean_object* v___x_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = l_Lake_Job_async___redArg(v___x_2915_, v___f_2916_, v___x_2917_, v___x_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
v___x_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
lean_ctor_set(v___x_2927_, 1, v___y_2924_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__1___boxed(lean_object* v___x_2928_, lean_object* v___f_2929_, lean_object* v___x_2930_, lean_object* v___x_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lake_Package_optBarrelFacetConfig___lam__1(v___x_2928_, v___f_2929_, v___x_2930_, v___x_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec(v___y_2933_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2(lean_object* v___x_2940_, lean_object* v___x_2941_, lean_object* v___x_2942_, lean_object* v_pkg_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v_baseName_2951_; lean_object* v_dir_2952_; lean_object* v___f_2953_; uint8_t v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___f_2963_; lean_object* v___x_2964_; 
v_baseName_2951_ = lean_ctor_get(v_pkg_2943_, 1);
lean_inc(v_baseName_2951_);
v_dir_2952_ = lean_ctor_get(v_pkg_2943_, 4);
lean_inc_ref(v_dir_2952_);
v___f_2953_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2953_, 0, v_pkg_2943_);
lean_closure_set(v___f_2953_, 1, v_dir_2952_);
lean_closure_set(v___f_2953_, 2, v___x_2940_);
v___x_2954_ = 1;
v___x_2955_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_2951_, v___x_2954_);
v___x_2956_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_2957_ = lean_string_append(v___x_2955_, v___x_2956_);
v___x_2958_ = l_Lake_Name_eraseHead(v___x_2941_);
v___x_2959_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2958_, v___x_2954_);
v___x_2960_ = lean_string_append(v___x_2957_, v___x_2959_);
lean_dec_ref(v___x_2959_);
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_2942_);
v___f_2963_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_2963_, 0, v___x_2942_);
lean_closure_set(v___f_2963_, 1, v___f_2953_);
lean_closure_set(v___f_2963_, 2, v___x_2961_);
lean_closure_set(v___f_2963_, 3, v___x_2962_);
v___x_2964_ = l_Lake_ensureJob___redArg(v___x_2942_, v___f_2963_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2989_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
v_a_2966_ = lean_ctor_get(v___x_2964_, 1);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2968_ = v___x_2964_;
v_isShared_2969_ = v_isSharedCheck_2989_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_inc(v_a_2965_);
lean_dec(v___x_2964_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2989_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v_task_2970_; lean_object* v_kind_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2987_; 
v_task_2970_ = lean_ctor_get(v_a_2965_, 0);
v_kind_2971_ = lean_ctor_get(v_a_2965_, 1);
v_isSharedCheck_2987_ = !lean_is_exclusive(v_a_2965_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v_a_2965_, 2);
lean_dec(v_unused_2988_);
v___x_2973_ = v_a_2965_;
v_isShared_2974_ = v_isSharedCheck_2987_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_kind_2971_);
lean_inc(v_task_2970_);
lean_dec(v_a_2965_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2987_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v_registeredJobs_2975_; lean_object* v_job_2977_; 
v_registeredJobs_2975_ = lean_ctor_get(v___y_2948_, 4);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 2, v___x_2960_);
v_job_2977_ = v___x_2973_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_task_2970_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_kind_2971_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v___x_2960_);
v_job_2977_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2984_; 
lean_ctor_set_uint8(v_job_2977_, sizeof(void*)*3, v___x_2954_);
v___x_2978_ = lean_st_ref_take(v_registeredJobs_2975_);
lean_inc_ref(v_job_2977_);
v___x_2979_ = l_Lake_Job_toOpaque___redArg(v_job_2977_);
v___x_2980_ = lean_array_push(v___x_2978_, v___x_2979_);
v___x_2981_ = lean_st_ref_put(v_registeredJobs_2975_, v___x_2980_);
v___x_2982_ = l_Lake_Job_renew___redArg(v_job_2977_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v___x_2982_);
v___x_2984_ = v___x_2968_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2982_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_a_2966_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2960_);
return v___x_2964_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optBarrelFacetConfig___lam__2___boxed(lean_object* v___x_2990_, lean_object* v___x_2991_, lean_object* v___x_2992_, lean_object* v_pkg_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Lake_Package_optBarrelFacetConfig___lam__2(v___x_2990_, v___x_2991_, v___x_2992_, v_pkg_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec(v___y_2995_);
return v_res_3001_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___f_3005_; 
v___x_3002_ = l_Lake_instDataKindBool;
v___x_3003_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3004_ = l_Lake_Reservoir_lakeHeaders;
v___f_3005_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3005_, 0, v___x_3004_);
lean_closure_set(v___f_3005_, 1, v___x_3003_);
lean_closure_set(v___f_3005_, 2, v___x_3002_);
return v___f_3005_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3006_; uint8_t v___x_3007_; lean_object* v___x_3008_; lean_object* v___f_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___f_3006_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_3007_ = 1;
v___x_3008_ = l_Lake_instDataKindBool;
v___f_3009_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__0, &l_Lake_Package_optBarrelFacetConfig___closed__0_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__0);
v___x_3010_ = l_Lake_Package_keyword;
v___x_3011_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v___f_3009_);
lean_ctor_set(v___x_3011_, 2, v___x_3008_);
lean_ctor_set(v___x_3011_, 3, v___f_3006_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*4, v___x_3007_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*4 + 1, v___x_3007_);
return v___x_3011_;
}
}
static lean_object* _init_l_Lake_Package_optBarrelFacetConfig(void){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = lean_obj_once(&l_Lake_Package_optBarrelFacetConfig___closed__1, &l_Lake_Package_optBarrelFacetConfig___closed__1_once, _init_l_Lake_Package_optBarrelFacetConfig___closed__1);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1(lean_object* v_baseName_3014_, lean_object* v___x_3015_, uint8_t v_success_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_a_3025_; lean_object* v_a_3026_; 
if (v_success_3016_ == 0)
{
lean_object* v_toBuildConfig_3047_; uint8_t v_verbosity_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; 
v_toBuildConfig_3047_ = lean_ctor_get(v___y_3021_, 0);
v_verbosity_3048_ = lean_ctor_get_uint8(v_toBuildConfig_3047_, sizeof(void*)*5 + 4);
v___x_3049_ = lean_box(v_verbosity_3048_);
v___x_3050_ = lean_obj_tag_nat(v___x_3049_);
lean_dec(v___x_3049_);
v___x_3051_ = lean_unsigned_to_nat(2u);
v___x_3052_ = lean_nat_dec_eq(v___x_3050_, v___x_3051_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; 
lean_dec(v___x_3015_);
lean_dec(v_baseName_3014_);
v___x_3053_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_3025_ = v___x_3053_;
v_a_3026_ = v___y_3022_;
goto v___jp_3024_;
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3054_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_3055_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3014_, v___x_3052_);
v___x_3056_ = lean_string_append(v___x_3054_, v___x_3055_);
lean_dec_ref(v___x_3055_);
v___x_3057_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3058_ = lean_string_append(v___x_3056_, v___x_3057_);
v___x_3059_ = l_Lake_Name_eraseHead(v___x_3015_);
v___x_3060_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3059_, v___x_3052_);
v___x_3061_ = lean_string_append(v___x_3058_, v___x_3060_);
lean_dec_ref(v___x_3060_);
v___x_3062_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3063_ = lean_string_append(v___x_3061_, v___x_3062_);
v_a_3025_ = v___x_3063_;
v_a_3026_ = v___y_3022_;
goto v___jp_3024_;
}
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_dec(v___x_3015_);
lean_dec(v_baseName_3014_);
v___x_3064_ = lean_box(0);
v___x_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
lean_ctor_set(v___x_3065_, 1, v___y_3022_);
return v___x_3065_;
}
v___jp_3024_:
{
lean_object* v_log_3027_; uint8_t v_action_3028_; uint8_t v_wantsRebuild_3029_; uint8_t v_canceled_3030_; lean_object* v_trace_3031_; lean_object* v_buildTime_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3046_; 
v_log_3027_ = lean_ctor_get(v_a_3026_, 0);
v_action_3028_ = lean_ctor_get_uint8(v_a_3026_, sizeof(void*)*3);
v_wantsRebuild_3029_ = lean_ctor_get_uint8(v_a_3026_, sizeof(void*)*3 + 1);
v_canceled_3030_ = lean_ctor_get_uint8(v_a_3026_, sizeof(void*)*3 + 2);
v_trace_3031_ = lean_ctor_get(v_a_3026_, 1);
v_buildTime_3032_ = lean_ctor_get(v_a_3026_, 2);
v_isSharedCheck_3046_ = !lean_is_exclusive(v_a_3026_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3034_ = v_a_3026_;
v_isShared_3035_ = v_isSharedCheck_3046_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_buildTime_3032_);
lean_inc(v_trace_3031_);
lean_inc(v_log_3027_);
lean_dec(v_a_3026_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3046_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; uint8_t v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3043_; 
v___x_3036_ = ((lean_object*)(l_Lake_Package_barrelFacetConfig___lam__1___closed__0));
v___x_3037_ = lean_string_append(v___x_3036_, v_a_3025_);
lean_dec_ref(v_a_3025_);
v___x_3038_ = 3;
v___x_3039_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3039_, 0, v___x_3037_);
lean_ctor_set_uint8(v___x_3039_, sizeof(void*)*1, v___x_3038_);
v___x_3040_ = lean_array_get_size(v_log_3027_);
v___x_3041_ = lean_array_push(v_log_3027_, v___x_3039_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 0, v___x_3041_);
v___x_3043_ = v___x_3034_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v_trace_3031_);
lean_ctor_set(v_reuseFailAlloc_3045_, 2, v_buildTime_3032_);
lean_ctor_set_uint8(v_reuseFailAlloc_3045_, sizeof(void*)*3, v_action_3028_);
lean_ctor_set_uint8(v_reuseFailAlloc_3045_, sizeof(void*)*3 + 1, v_wantsRebuild_3029_);
lean_ctor_set_uint8(v_reuseFailAlloc_3045_, sizeof(void*)*3 + 2, v_canceled_3030_);
v___x_3043_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3044_; 
v___x_3044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3040_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
return v___x_3044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__1___boxed(lean_object* v_baseName_3066_, lean_object* v___x_3067_, lean_object* v_success_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
uint8_t v_success_boxed_3076_; lean_object* v_res_3077_; 
v_success_boxed_3076_ = lean_unbox(v_success_3068_);
v_res_3077_ = l_Lake_Package_barrelFacetConfig___lam__1(v_baseName_3066_, v___x_3067_, v_success_boxed_3076_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2(lean_object* v___x_3078_, lean_object* v___x_3079_, lean_object* v___x_3080_, lean_object* v_pkg_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_baseName_3089_; lean_object* v_keyName_3090_; lean_object* v___f_3091_; uint8_t v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___f_3102_; uint8_t v___x_3103_; lean_object* v___x_3104_; 
v_baseName_3089_ = lean_ctor_get(v_pkg_3081_, 1);
v_keyName_3090_ = lean_ctor_get(v_pkg_3081_, 2);
lean_inc(v___x_3078_);
lean_inc_n(v_baseName_3089_, 2);
v___f_3091_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3091_, 0, v_baseName_3089_);
lean_closure_set(v___f_3091_, 1, v___x_3078_);
v___x_3092_ = 1;
v___x_3093_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3089_, v___x_3092_);
v___x_3094_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3095_ = lean_string_append(v___x_3093_, v___x_3094_);
v___x_3096_ = l_Lake_Name_eraseHead(v___x_3079_);
v___x_3097_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3096_, v___x_3092_);
v___x_3098_ = lean_string_append(v___x_3095_, v___x_3097_);
lean_dec_ref(v___x_3097_);
lean_inc(v_keyName_3090_);
v___x_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3099_, 0, v_keyName_3090_);
v___x_3100_ = l_Lake_Package_keyword;
v___x_3101_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3099_);
lean_ctor_set(v___x_3101_, 1, v___x_3100_);
lean_ctor_set(v___x_3101_, 2, v_pkg_3081_);
lean_ctor_set(v___x_3101_, 3, v___x_3078_);
lean_inc(v___x_3080_);
v___f_3102_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3102_, 0, v___x_3101_);
lean_closure_set(v___f_3102_, 1, v___x_3080_);
lean_closure_set(v___f_3102_, 2, v___f_3091_);
v___x_3103_ = 0;
v___x_3104_ = l_Lake_ensureJob___redArg(v___x_3080_, v___f_3102_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3129_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
v_a_3106_ = lean_ctor_get(v___x_3104_, 1);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3108_ = v___x_3104_;
v_isShared_3109_ = v_isSharedCheck_3129_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_inc(v_a_3105_);
lean_dec(v___x_3104_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3129_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v_task_3110_; lean_object* v_kind_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3127_; 
v_task_3110_ = lean_ctor_get(v_a_3105_, 0);
v_kind_3111_ = lean_ctor_get(v_a_3105_, 1);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_a_3105_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v_a_3105_, 2);
lean_dec(v_unused_3128_);
v___x_3113_ = v_a_3105_;
v_isShared_3114_ = v_isSharedCheck_3127_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_kind_3111_);
lean_inc(v_task_3110_);
lean_dec(v_a_3105_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3127_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v_registeredJobs_3115_; lean_object* v_job_3117_; 
v_registeredJobs_3115_ = lean_ctor_get(v___y_3086_, 4);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 2, v___x_3098_);
v_job_3117_ = v___x_3113_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_task_3110_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_kind_3111_);
lean_ctor_set(v_reuseFailAlloc_3126_, 2, v___x_3098_);
v_job_3117_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3124_; 
lean_ctor_set_uint8(v_job_3117_, sizeof(void*)*3, v___x_3103_);
v___x_3118_ = lean_st_ref_take(v_registeredJobs_3115_);
lean_inc_ref(v_job_3117_);
v___x_3119_ = l_Lake_Job_toOpaque___redArg(v_job_3117_);
v___x_3120_ = lean_array_push(v___x_3118_, v___x_3119_);
v___x_3121_ = lean_st_ref_put(v_registeredJobs_3115_, v___x_3120_);
v___x_3122_ = l_Lake_Job_renew___redArg(v_job_3117_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 0, v___x_3122_);
v___x_3124_ = v___x_3108_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v_a_3106_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3098_);
return v___x_3104_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_barrelFacetConfig___lam__2___boxed(lean_object* v___x_3130_, lean_object* v___x_3131_, lean_object* v___x_3132_, lean_object* v_pkg_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Lake_Package_barrelFacetConfig___lam__2(v___x_3130_, v___x_3131_, v___x_3132_, v_pkg_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec(v___y_3135_);
return v_res_3141_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___f_3145_; 
v___x_3142_ = l_Lake_instDataKindUnit;
v___x_3143_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3144_ = l_Lake_Package_optReservoirBarrelFacet;
v___f_3145_ = lean_alloc_closure((void*)(l_Lake_Package_barrelFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3145_, 0, v___x_3144_);
lean_closure_set(v___f_3145_, 1, v___x_3143_);
lean_closure_set(v___f_3145_, 2, v___x_3142_);
return v___f_3145_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3146_; uint8_t v___x_3147_; lean_object* v___x_3148_; lean_object* v___f_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___f_3146_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3147_ = 1;
v___x_3148_ = l_Lake_instDataKindUnit;
v___f_3149_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__0, &l_Lake_Package_barrelFacetConfig___closed__0_once, _init_l_Lake_Package_barrelFacetConfig___closed__0);
v___x_3150_ = l_Lake_Package_keyword;
v___x_3151_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
lean_ctor_set(v___x_3151_, 1, v___f_3149_);
lean_ctor_set(v___x_3151_, 2, v___x_3148_);
lean_ctor_set(v___x_3151_, 3, v___f_3146_);
lean_ctor_set_uint8(v___x_3151_, sizeof(void*)*4, v___x_3147_);
lean_ctor_set_uint8(v___x_3151_, sizeof(void*)*4 + 1, v___x_3147_);
return v___x_3151_;
}
}
static lean_object* _init_l_Lake_Package_barrelFacetConfig(void){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = lean_obj_once(&l_Lake_Package_barrelFacetConfig___closed__1, &l_Lake_Package_barrelFacetConfig___closed__1_once, _init_l_Lake_Package_barrelFacetConfig___closed__1);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(lean_object* v_pkg_3153_, lean_object* v_dir_3154_, lean_object* v_buildArchive_3155_, lean_object* v___x_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
uint8_t v_r_3165_; lean_object* v___y_3166_; lean_object* v_a_3170_; lean_object* v___x_3187_; 
lean_inc_ref(v_pkg_3153_);
v___x_3187_ = l___private_Lake_Build_Package_0__Lake_Package_getReleaseUrl___redArg(v_pkg_3153_, v___y_3162_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v_a_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
v_a_3189_ = lean_ctor_get(v___x_3187_, 1);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3187_, 2);
v___x_3190_ = l_Lake_defaultLakeDir;
v___x_3191_ = l_Lake_joinRelative(v_dir_3154_, v___x_3190_);
v___x_3192_ = l_Lake_joinRelative(v___x_3191_, v_buildArchive_3155_);
v___x_3193_ = l___private_Lake_Build_Package_0__Lake_Package_fetchBuildArchive(v_pkg_3153_, v_a_3188_, v___x_3192_, v___x_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v_a_3189_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; uint8_t v___x_3195_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 1);
lean_inc(v_a_3194_);
lean_dec_ref_known(v___x_3193_, 2);
v___x_3195_ = 1;
v_r_3165_ = v___x_3195_;
v___y_3166_ = v_a_3194_;
goto v___jp_3164_;
}
else
{
lean_object* v_a_3196_; 
v_a_3196_ = lean_ctor_get(v___x_3193_, 1);
lean_inc(v_a_3196_);
lean_dec_ref_known(v___x_3193_, 2);
v_a_3170_ = v_a_3196_;
goto v___jp_3169_;
}
}
else
{
lean_object* v_a_3197_; 
lean_dec_ref(v_buildArchive_3155_);
lean_dec_ref(v_dir_3154_);
lean_dec_ref(v_pkg_3153_);
v_a_3197_ = lean_ctor_get(v___x_3187_, 1);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3187_, 2);
v_a_3170_ = v_a_3197_;
goto v___jp_3169_;
}
v___jp_3164_:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = lean_box(v_r_3165_);
v___x_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
lean_ctor_set(v___x_3168_, 1, v___y_3166_);
return v___x_3168_;
}
v___jp_3169_:
{
lean_object* v_log_3171_; uint8_t v_action_3172_; uint8_t v_wantsRebuild_3173_; uint8_t v_canceled_3174_; lean_object* v_trace_3175_; lean_object* v_buildTime_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3186_; 
v_log_3171_ = lean_ctor_get(v_a_3170_, 0);
v_action_3172_ = lean_ctor_get_uint8(v_a_3170_, sizeof(void*)*3);
v_wantsRebuild_3173_ = lean_ctor_get_uint8(v_a_3170_, sizeof(void*)*3 + 1);
v_canceled_3174_ = lean_ctor_get_uint8(v_a_3170_, sizeof(void*)*3 + 2);
v_trace_3175_ = lean_ctor_get(v_a_3170_, 1);
v_buildTime_3176_ = lean_ctor_get(v_a_3170_, 2);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_a_3170_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3178_ = v_a_3170_;
v_isShared_3179_ = v_isSharedCheck_3186_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_buildTime_3176_);
lean_inc(v_trace_3175_);
lean_inc(v_log_3171_);
lean_dec(v_a_3170_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3186_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
uint8_t v___x_3180_; uint8_t v___x_3181_; lean_object* v___x_3183_; 
v___x_3180_ = 4;
v___x_3181_ = l_Lake_JobAction_merge(v_action_3172_, v___x_3180_);
if (v_isShared_3179_ == 0)
{
v___x_3183_ = v___x_3178_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_log_3171_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v_trace_3175_);
lean_ctor_set(v_reuseFailAlloc_3185_, 2, v_buildTime_3176_);
lean_ctor_set_uint8(v_reuseFailAlloc_3185_, sizeof(void*)*3 + 1, v_wantsRebuild_3173_);
lean_ctor_set_uint8(v_reuseFailAlloc_3185_, sizeof(void*)*3 + 2, v_canceled_3174_);
v___x_3183_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
uint8_t v___x_3184_; 
lean_ctor_set_uint8(v___x_3183_, sizeof(void*)*3, v___x_3181_);
v___x_3184_ = 0;
v_r_3165_ = v___x_3184_;
v___y_3166_ = v___x_3183_;
goto v___jp_3164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed(lean_object* v_pkg_3198_, lean_object* v_dir_3199_, lean_object* v_buildArchive_3200_, lean_object* v___x_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__0(v_pkg_3198_, v_dir_3199_, v_buildArchive_3200_, v___x_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
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
lean_object* v_baseName_3222_; lean_object* v_dir_3223_; lean_object* v_buildArchive_3224_; lean_object* v___f_3225_; uint8_t v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___f_3234_; lean_object* v___x_3235_; 
v_baseName_3222_ = lean_ctor_get(v_pkg_3214_, 1);
lean_inc(v_baseName_3222_);
v_dir_3223_ = lean_ctor_get(v_pkg_3214_, 4);
lean_inc_ref(v_dir_3223_);
v_buildArchive_3224_ = lean_ctor_get(v_pkg_3214_, 21);
lean_inc_ref(v_buildArchive_3224_);
v___f_3225_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3225_, 0, v_pkg_3214_);
lean_closure_set(v___f_3225_, 1, v_dir_3223_);
lean_closure_set(v___f_3225_, 2, v_buildArchive_3224_);
lean_closure_set(v___f_3225_, 3, v___x_3210_);
v___x_3226_ = 1;
v___x_3227_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3222_, v___x_3226_);
v___x_3228_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3229_ = lean_string_append(v___x_3227_, v___x_3228_);
v___x_3230_ = l_Lake_Name_eraseHead(v___x_3211_);
v___x_3231_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3230_, v___x_3226_);
v___x_3232_ = lean_string_append(v___x_3229_, v___x_3231_);
lean_dec_ref(v___x_3231_);
v___x_3233_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
lean_inc(v___x_3212_);
v___f_3234_ = lean_alloc_closure((void*)(l_Lake_Package_optBarrelFacetConfig___lam__1___boxed), 11, 4);
lean_closure_set(v___f_3234_, 0, v___x_3212_);
lean_closure_set(v___f_3234_, 1, v___f_3225_);
lean_closure_set(v___f_3234_, 2, v___x_3213_);
lean_closure_set(v___f_3234_, 3, v___x_3233_);
v___x_3235_ = l_Lake_ensureJob___redArg(v___x_3212_, v___f_3234_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3260_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
v_a_3237_ = lean_ctor_get(v___x_3235_, 1);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3239_ = v___x_3235_;
v_isShared_3240_ = v_isSharedCheck_3260_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_inc(v_a_3236_);
lean_dec(v___x_3235_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3260_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v_task_3241_; lean_object* v_kind_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3258_; 
v_task_3241_ = lean_ctor_get(v_a_3236_, 0);
v_kind_3242_ = lean_ctor_get(v_a_3236_, 1);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_a_3236_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; 
v_unused_3259_ = lean_ctor_get(v_a_3236_, 2);
lean_dec(v_unused_3259_);
v___x_3244_ = v_a_3236_;
v_isShared_3245_ = v_isSharedCheck_3258_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_kind_3242_);
lean_inc(v_task_3241_);
lean_dec(v_a_3236_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3258_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v_registeredJobs_3246_; lean_object* v_job_3248_; 
v_registeredJobs_3246_ = lean_ctor_get(v___y_3219_, 4);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 2, v___x_3232_);
v_job_3248_ = v___x_3244_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_task_3241_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v_kind_3242_);
lean_ctor_set(v_reuseFailAlloc_3257_, 2, v___x_3232_);
v_job_3248_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3255_; 
lean_ctor_set_uint8(v_job_3248_, sizeof(void*)*3, v___x_3226_);
v___x_3249_ = lean_st_ref_take(v_registeredJobs_3246_);
lean_inc_ref(v_job_3248_);
v___x_3250_ = l_Lake_Job_toOpaque___redArg(v_job_3248_);
v___x_3251_ = lean_array_push(v___x_3249_, v___x_3250_);
v___x_3252_ = lean_st_ref_put(v_registeredJobs_3246_, v___x_3251_);
v___x_3253_ = l_Lake_Job_renew___redArg(v_job_3248_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v___x_3253_);
v___x_3255_ = v___x_3239_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3253_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_a_3237_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3232_);
return v___x_3235_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_3261_, lean_object* v___x_3262_, lean_object* v___x_3263_, lean_object* v___x_3264_, lean_object* v_pkg_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Lake_Package_optGitHubReleaseFacetConfig___lam__2(v___x_3261_, v___x_3262_, v___x_3263_, v___x_3264_, v_pkg_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec(v___y_3267_);
return v_res_3273_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___f_3280_; 
v___x_3276_ = lean_unsigned_to_nat(0u);
v___x_3277_ = l_Lake_instDataKindBool;
v___x_3278_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3279_ = ((lean_object*)(l_Lake_Package_optGitHubReleaseFacetConfig___closed__0));
v___f_3280_ = lean_alloc_closure((void*)(l_Lake_Package_optGitHubReleaseFacetConfig___lam__2___boxed), 12, 4);
lean_closure_set(v___f_3280_, 0, v___x_3279_);
lean_closure_set(v___f_3280_, 1, v___x_3278_);
lean_closure_set(v___f_3280_, 2, v___x_3277_);
lean_closure_set(v___f_3280_, 3, v___x_3276_);
return v___f_3280_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2(void){
_start:
{
lean_object* v___f_3281_; uint8_t v___x_3282_; lean_object* v___x_3283_; lean_object* v___f_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___f_3281_ = ((lean_object*)(l_Lake_Package_optBuildCacheFacetConfig___closed__1));
v___x_3282_ = 1;
v___x_3283_ = l_Lake_instDataKindBool;
v___f_3284_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__1, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__1);
v___x_3285_ = l_Lake_Package_keyword;
v___x_3286_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
lean_ctor_set(v___x_3286_, 1, v___f_3284_);
lean_ctor_set(v___x_3286_, 2, v___x_3283_);
lean_ctor_set(v___x_3286_, 3, v___f_3281_);
lean_ctor_set_uint8(v___x_3286_, sizeof(void*)*4, v___x_3282_);
lean_ctor_set_uint8(v___x_3286_, sizeof(void*)*4 + 1, v___x_3282_);
return v___x_3286_;
}
}
static lean_object* _init_l_Lake_Package_optGitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = lean_obj_once(&l_Lake_Package_optGitHubReleaseFacetConfig___closed__2, &l_Lake_Package_optGitHubReleaseFacetConfig___closed__2_once, _init_l_Lake_Package_optGitHubReleaseFacetConfig___closed__2);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1(lean_object* v_baseName_3289_, lean_object* v___x_3290_, uint8_t v_success_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v_a_3300_; lean_object* v_a_3301_; 
if (v_success_3291_ == 0)
{
lean_object* v_toBuildConfig_3322_; uint8_t v_verbosity_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v_toBuildConfig_3322_ = lean_ctor_get(v___y_3296_, 0);
v_verbosity_3323_ = lean_ctor_get_uint8(v_toBuildConfig_3322_, sizeof(void*)*5 + 4);
v___x_3324_ = lean_box(v_verbosity_3323_);
v___x_3325_ = lean_obj_tag_nat(v___x_3324_);
lean_dec(v___x_3324_);
v___x_3326_ = lean_unsigned_to_nat(2u);
v___x_3327_ = lean_nat_dec_eq(v___x_3325_, v___x_3326_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; 
lean_dec(v___x_3290_);
lean_dec(v_baseName_3289_);
v___x_3328_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__0));
v_a_3300_ = v___x_3328_;
v_a_3301_ = v___y_3297_;
goto v___jp_3299_;
}
else
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3329_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__1));
v___x_3330_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3289_, v___x_3327_);
v___x_3331_ = lean_string_append(v___x_3329_, v___x_3330_);
lean_dec_ref(v___x_3330_);
v___x_3332_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3333_ = lean_string_append(v___x_3331_, v___x_3332_);
v___x_3334_ = l_Lake_Name_eraseHead(v___x_3290_);
v___x_3335_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3334_, v___x_3327_);
v___x_3336_ = lean_string_append(v___x_3333_, v___x_3335_);
lean_dec_ref(v___x_3335_);
v___x_3337_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__3));
v___x_3338_ = lean_string_append(v___x_3336_, v___x_3337_);
v_a_3300_ = v___x_3338_;
v_a_3301_ = v___y_3297_;
goto v___jp_3299_;
}
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
lean_dec(v___x_3290_);
lean_dec(v_baseName_3289_);
v___x_3339_ = lean_box(0);
v___x_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3339_);
lean_ctor_set(v___x_3340_, 1, v___y_3297_);
return v___x_3340_;
}
v___jp_3299_:
{
lean_object* v_log_3302_; uint8_t v_action_3303_; uint8_t v_wantsRebuild_3304_; uint8_t v_canceled_3305_; lean_object* v_trace_3306_; lean_object* v_buildTime_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3321_; 
v_log_3302_ = lean_ctor_get(v_a_3301_, 0);
v_action_3303_ = lean_ctor_get_uint8(v_a_3301_, sizeof(void*)*3);
v_wantsRebuild_3304_ = lean_ctor_get_uint8(v_a_3301_, sizeof(void*)*3 + 1);
v_canceled_3305_ = lean_ctor_get_uint8(v_a_3301_, sizeof(void*)*3 + 2);
v_trace_3306_ = lean_ctor_get(v_a_3301_, 1);
v_buildTime_3307_ = lean_ctor_get(v_a_3301_, 2);
v_isSharedCheck_3321_ = !lean_is_exclusive(v_a_3301_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3309_ = v_a_3301_;
v_isShared_3310_ = v_isSharedCheck_3321_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_buildTime_3307_);
lean_inc(v_trace_3306_);
lean_inc(v_log_3302_);
lean_dec(v_a_3301_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3321_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; uint8_t v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3311_ = ((lean_object*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___closed__0));
v___x_3312_ = lean_string_append(v___x_3311_, v_a_3300_);
lean_dec_ref(v_a_3300_);
v___x_3313_ = 3;
v___x_3314_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3314_, 0, v___x_3312_);
lean_ctor_set_uint8(v___x_3314_, sizeof(void*)*1, v___x_3313_);
v___x_3315_ = lean_array_get_size(v_log_3302_);
v___x_3316_ = lean_array_push(v_log_3302_, v___x_3314_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3316_);
v___x_3318_ = v___x_3309_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v_trace_3306_);
lean_ctor_set(v_reuseFailAlloc_3320_, 2, v_buildTime_3307_);
lean_ctor_set_uint8(v_reuseFailAlloc_3320_, sizeof(void*)*3, v_action_3303_);
lean_ctor_set_uint8(v_reuseFailAlloc_3320_, sizeof(void*)*3 + 1, v_wantsRebuild_3304_);
lean_ctor_set_uint8(v_reuseFailAlloc_3320_, sizeof(void*)*3 + 2, v_canceled_3305_);
v___x_3318_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3315_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
return v___x_3319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed(lean_object* v_baseName_3341_, lean_object* v___x_3342_, lean_object* v_success_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
uint8_t v_success_boxed_3351_; lean_object* v_res_3352_; 
v_success_boxed_3351_ = lean_unbox(v_success_3343_);
v_res_3352_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__1(v_baseName_3341_, v___x_3342_, v_success_boxed_3351_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2(lean_object* v___x_3353_, lean_object* v___x_3354_, lean_object* v___x_3355_, lean_object* v_pkg_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
lean_object* v_baseName_3364_; lean_object* v_keyName_3365_; lean_object* v___f_3366_; uint8_t v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___f_3377_; uint8_t v___x_3378_; lean_object* v___x_3379_; 
v_baseName_3364_ = lean_ctor_get(v_pkg_3356_, 1);
v_keyName_3365_ = lean_ctor_get(v_pkg_3356_, 2);
lean_inc(v___x_3353_);
lean_inc_n(v_baseName_3364_, 2);
v___f_3366_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__1___boxed), 10, 2);
lean_closure_set(v___f_3366_, 0, v_baseName_3364_);
lean_closure_set(v___f_3366_, 1, v___x_3353_);
v___x_3367_ = 1;
v___x_3368_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_baseName_3364_, v___x_3367_);
v___x_3369_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_optFacetDetails___redArg___closed__2));
v___x_3370_ = lean_string_append(v___x_3368_, v___x_3369_);
v___x_3371_ = l_Lake_Name_eraseHead(v___x_3354_);
v___x_3372_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_3371_, v___x_3367_);
v___x_3373_ = lean_string_append(v___x_3370_, v___x_3372_);
lean_dec_ref(v___x_3372_);
lean_inc(v_keyName_3365_);
v___x_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3374_, 0, v_keyName_3365_);
v___x_3375_ = l_Lake_Package_keyword;
v___x_3376_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3374_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
lean_ctor_set(v___x_3376_, 2, v_pkg_3356_);
lean_ctor_set(v___x_3376_, 3, v___x_3353_);
lean_inc(v___x_3355_);
v___f_3377_ = lean_alloc_closure((void*)(l___private_Lake_Build_Package_0__Lake_Package_mkBuildArchiveFacetConfig___redArg___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3377_, 0, v___x_3376_);
lean_closure_set(v___f_3377_, 1, v___x_3355_);
lean_closure_set(v___f_3377_, 2, v___f_3366_);
v___x_3378_ = 0;
v___x_3379_ = l_Lake_ensureJob___redArg(v___x_3355_, v___f_3377_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3404_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
v_a_3381_ = lean_ctor_get(v___x_3379_, 1);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3383_ = v___x_3379_;
v_isShared_3384_ = v_isSharedCheck_3404_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_inc(v_a_3380_);
lean_dec(v___x_3379_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3404_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v_task_3385_; lean_object* v_kind_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3402_; 
v_task_3385_ = lean_ctor_get(v_a_3380_, 0);
v_kind_3386_ = lean_ctor_get(v_a_3380_, 1);
v_isSharedCheck_3402_ = !lean_is_exclusive(v_a_3380_);
if (v_isSharedCheck_3402_ == 0)
{
lean_object* v_unused_3403_; 
v_unused_3403_ = lean_ctor_get(v_a_3380_, 2);
lean_dec(v_unused_3403_);
v___x_3388_ = v_a_3380_;
v_isShared_3389_ = v_isSharedCheck_3402_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_kind_3386_);
lean_inc(v_task_3385_);
lean_dec(v_a_3380_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3402_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v_registeredJobs_3390_; lean_object* v_job_3392_; 
v_registeredJobs_3390_ = lean_ctor_get(v___y_3361_, 4);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 2, v___x_3373_);
v_job_3392_ = v___x_3388_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_task_3385_);
lean_ctor_set(v_reuseFailAlloc_3401_, 1, v_kind_3386_);
lean_ctor_set(v_reuseFailAlloc_3401_, 2, v___x_3373_);
v_job_3392_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3399_; 
lean_ctor_set_uint8(v_job_3392_, sizeof(void*)*3, v___x_3378_);
v___x_3393_ = lean_st_ref_take(v_registeredJobs_3390_);
lean_inc_ref(v_job_3392_);
v___x_3394_ = l_Lake_Job_toOpaque___redArg(v_job_3392_);
v___x_3395_ = lean_array_push(v___x_3393_, v___x_3394_);
v___x_3396_ = lean_st_ref_put(v_registeredJobs_3390_, v___x_3395_);
v___x_3397_ = l_Lake_Job_renew___redArg(v_job_3392_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3397_);
v___x_3399_ = v___x_3383_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v_a_3381_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3373_);
return v___x_3379_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed(lean_object* v___x_3405_, lean_object* v___x_3406_, lean_object* v___x_3407_, lean_object* v_pkg_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v_res_3416_; 
v_res_3416_ = l_Lake_Package_gitHubReleaseFacetConfig___lam__2(v___x_3405_, v___x_3406_, v___x_3407_, v_pkg_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec(v___y_3410_);
return v_res_3416_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0(void){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___f_3420_; 
v___x_3417_ = l_Lake_instDataKindUnit;
v___x_3418_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3419_ = l_Lake_Package_optGitHubReleaseFacet;
v___f_3420_ = lean_alloc_closure((void*)(l_Lake_Package_gitHubReleaseFacetConfig___lam__2___boxed), 11, 3);
lean_closure_set(v___f_3420_, 0, v___x_3419_);
lean_closure_set(v___f_3420_, 1, v___x_3418_);
lean_closure_set(v___f_3420_, 2, v___x_3417_);
return v___f_3420_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1(void){
_start:
{
lean_object* v___f_3421_; uint8_t v___x_3422_; lean_object* v___x_3423_; lean_object* v___f_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___f_3421_ = ((lean_object*)(l_Lake_Package_extraDepFacetConfig___closed__0));
v___x_3422_ = 1;
v___x_3423_ = l_Lake_instDataKindUnit;
v___f_3424_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__0, &l_Lake_Package_gitHubReleaseFacetConfig___closed__0_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__0);
v___x_3425_ = l_Lake_Package_keyword;
v___x_3426_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
lean_ctor_set(v___x_3426_, 1, v___f_3424_);
lean_ctor_set(v___x_3426_, 2, v___x_3423_);
lean_ctor_set(v___x_3426_, 3, v___f_3421_);
lean_ctor_set_uint8(v___x_3426_, sizeof(void*)*4, v___x_3422_);
lean_ctor_set_uint8(v___x_3426_, sizeof(void*)*4 + 1, v___x_3422_);
return v___x_3426_;
}
}
static lean_object* _init_l_Lake_Package_gitHubReleaseFacetConfig(void){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_obj_once(&l_Lake_Package_gitHubReleaseFacetConfig___closed__1, &l_Lake_Package_gitHubReleaseFacetConfig___closed__1_once, _init_l_Lake_Package_gitHubReleaseFacetConfig___closed__1);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(lean_object* v_build_3428_, uint8_t v_x_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v_log_3437_; uint8_t v_action_3438_; uint8_t v_wantsRebuild_3439_; uint8_t v_canceled_3440_; lean_object* v_buildTime_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3450_; 
v_log_3437_ = lean_ctor_get(v___y_3435_, 0);
v_action_3438_ = lean_ctor_get_uint8(v___y_3435_, sizeof(void*)*3);
v_wantsRebuild_3439_ = lean_ctor_get_uint8(v___y_3435_, sizeof(void*)*3 + 1);
v_canceled_3440_ = lean_ctor_get_uint8(v___y_3435_, sizeof(void*)*3 + 2);
v_buildTime_3441_ = lean_ctor_get(v___y_3435_, 2);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___y_3435_);
if (v_isSharedCheck_3450_ == 0)
{
lean_object* v_unused_3451_; 
v_unused_3451_ = lean_ctor_get(v___y_3435_, 1);
lean_dec(v_unused_3451_);
v___x_3443_ = v___y_3435_;
v_isShared_3444_ = v_isSharedCheck_3450_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_buildTime_3441_);
lean_inc(v_log_3437_);
lean_dec(v___y_3435_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3450_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3445_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v___x_3445_);
v___x_3447_ = v___x_3443_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_log_3437_);
lean_ctor_set(v_reuseFailAlloc_3449_, 1, v___x_3445_);
lean_ctor_set(v_reuseFailAlloc_3449_, 2, v_buildTime_3441_);
lean_ctor_set_uint8(v_reuseFailAlloc_3449_, sizeof(void*)*3, v_action_3438_);
lean_ctor_set_uint8(v_reuseFailAlloc_3449_, sizeof(void*)*3 + 1, v_wantsRebuild_3439_);
lean_ctor_set_uint8(v_reuseFailAlloc_3449_, sizeof(void*)*3 + 2, v_canceled_3440_);
v___x_3447_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3448_; 
lean_inc_ref(v___y_3434_);
lean_inc(v___y_3433_);
lean_inc(v___y_3432_);
lean_inc(v___y_3431_);
v___x_3448_ = lean_apply_7(v_build_3428_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___x_3447_, lean_box(0));
return v___x_3448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed(lean_object* v_build_3452_, lean_object* v_x_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
uint8_t v_x_1627__boxed_3461_; lean_object* v_res_3462_; 
v_x_1627__boxed_3461_ = lean_unbox(v_x_3453_);
v_res_3462_ = l_Lake_Package_afterBuildCacheAsync___redArg___lam__0(v_build_3452_, v_x_1627__boxed_3461_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec(v___y_3455_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg(lean_object* v_self_3463_, lean_object* v_build_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_){
_start:
{
lean_object* v_wsIdx_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v_wsIdx_3472_ = lean_ctor_get(v_self_3463_, 0);
v___x_3473_ = lean_unsigned_to_nat(0u);
v___x_3474_ = lean_nat_dec_eq(v_wsIdx_3472_, v___x_3473_);
if (v___x_3474_ == 0)
{
lean_object* v___f_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___f_3475_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheAsync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3475_, 0, v_build_3464_);
v___x_3476_ = lean_box(0);
lean_inc_ref(v_a_3465_);
v___x_3477_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3463_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3488_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
v_a_3479_ = lean_ctor_get(v___x_3477_, 1);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3481_ = v___x_3477_;
v_isShared_3482_ = v_isSharedCheck_3488_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_inc(v_a_3478_);
lean_dec(v___x_3477_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3488_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3483_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3484_ = l_Lake_Job_bindM___redArg(v___x_3476_, v_a_3478_, v___f_3475_, v___x_3473_, v___x_3474_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v___x_3483_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v___x_3484_);
v___x_3486_ = v___x_3481_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v_a_3479_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
else
{
lean_object* v_a_3489_; lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
lean_dec_ref(v___f_3475_);
lean_dec_ref(v_a_3465_);
v_a_3489_ = lean_ctor_get(v___x_3477_, 0);
v_a_3490_ = lean_ctor_get(v___x_3477_, 1);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3477_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_inc(v_a_3489_);
lean_dec(v___x_3477_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3489_);
lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
else
{
uint8_t v___x_3498_; uint8_t v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
lean_dec_ref(v_self_3463_);
v___x_3498_ = 0;
v___x_3499_ = 0;
v___x_3500_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3501_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3501_, 0, v_a_3470_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
lean_ctor_set(v___x_3501_, 2, v___x_3473_);
lean_ctor_set_uint8(v___x_3501_, sizeof(void*)*3, v___x_3498_);
lean_ctor_set_uint8(v___x_3501_, sizeof(void*)*3 + 1, v___x_3499_);
lean_ctor_set_uint8(v___x_3501_, sizeof(void*)*3 + 2, v___x_3499_);
lean_inc_ref(v_a_3469_);
lean_inc(v_a_3468_);
lean_inc(v_a_3467_);
lean_inc(v_a_3466_);
v___x_3502_ = lean_apply_7(v_build_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v___x_3501_, lean_box(0));
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3512_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 1);
v_a_3504_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3506_ = v___x_3502_;
v_isShared_3507_ = v_isSharedCheck_3512_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3503_);
lean_inc(v_a_3504_);
lean_dec(v___x_3502_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3512_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v_log_3508_; lean_object* v___x_3510_; 
v_log_3508_ = lean_ctor_get(v_a_3503_, 0);
lean_inc_ref(v_log_3508_);
lean_dec(v_a_3503_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 1, v_log_3508_);
v___x_3510_ = v___x_3506_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3504_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_log_3508_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
else
{
lean_object* v_a_3513_; lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3522_; 
v_a_3513_ = lean_ctor_get(v___x_3502_, 1);
v_a_3514_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3516_ = v___x_3502_;
v_isShared_3517_ = v_isSharedCheck_3522_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3513_);
lean_inc(v_a_3514_);
lean_dec(v___x_3502_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3522_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v_log_3518_; lean_object* v___x_3520_; 
v_log_3518_ = lean_ctor_get(v_a_3513_, 0);
lean_inc_ref(v_log_3518_);
lean_dec(v_a_3513_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 1, v_log_3518_);
v___x_3520_ = v___x_3516_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3514_);
lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_log_3518_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___redArg___boxed(lean_object* v_self_3523_, lean_object* v_build_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3523_, v_build_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_);
lean_dec_ref(v_a_3529_);
lean_dec(v_a_3528_);
lean_dec(v_a_3527_);
lean_dec(v_a_3526_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync(lean_object* v_00_u03b1_3533_, lean_object* v_self_3534_, lean_object* v_build_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Lake_Package_afterBuildCacheAsync___redArg(v_self_3534_, v_build_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheAsync___boxed(lean_object* v_00_u03b1_3544_, lean_object* v_self_3545_, lean_object* v_build_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lake_Package_afterBuildCacheAsync(v_00_u03b1_3544_, v_self_3545_, v_build_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
lean_dec_ref(v_a_3551_);
lean_dec(v_a_3550_);
lean_dec(v_a_3549_);
lean_dec(v_a_3548_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0(lean_object* v_build_3555_, uint8_t v_x_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v_log_3564_; uint8_t v_action_3565_; uint8_t v_wantsRebuild_3566_; uint8_t v_canceled_3567_; lean_object* v_buildTime_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3577_; 
v_log_3564_ = lean_ctor_get(v___y_3562_, 0);
v_action_3565_ = lean_ctor_get_uint8(v___y_3562_, sizeof(void*)*3);
v_wantsRebuild_3566_ = lean_ctor_get_uint8(v___y_3562_, sizeof(void*)*3 + 1);
v_canceled_3567_ = lean_ctor_get_uint8(v___y_3562_, sizeof(void*)*3 + 2);
v_buildTime_3568_ = lean_ctor_get(v___y_3562_, 2);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___y_3562_);
if (v_isSharedCheck_3577_ == 0)
{
lean_object* v_unused_3578_; 
v_unused_3578_ = lean_ctor_get(v___y_3562_, 1);
lean_dec(v_unused_3578_);
v___x_3570_ = v___y_3562_;
v_isShared_3571_ = v_isSharedCheck_3577_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_buildTime_3568_);
lean_inc(v_log_3564_);
lean_dec(v___y_3562_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3577_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3572_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 1, v___x_3572_);
v___x_3574_ = v___x_3570_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_log_3564_);
lean_ctor_set(v_reuseFailAlloc_3576_, 1, v___x_3572_);
lean_ctor_set(v_reuseFailAlloc_3576_, 2, v_buildTime_3568_);
lean_ctor_set_uint8(v_reuseFailAlloc_3576_, sizeof(void*)*3, v_action_3565_);
lean_ctor_set_uint8(v_reuseFailAlloc_3576_, sizeof(void*)*3 + 1, v_wantsRebuild_3566_);
lean_ctor_set_uint8(v_reuseFailAlloc_3576_, sizeof(void*)*3 + 2, v_canceled_3567_);
v___x_3574_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3575_; 
lean_inc_ref(v___y_3561_);
lean_inc(v___y_3560_);
lean_inc(v___y_3559_);
lean_inc(v___y_3558_);
v___x_3575_ = lean_apply_7(v_build_3555_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___x_3574_, lean_box(0));
return v___x_3575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed(lean_object* v_build_3579_, lean_object* v_x_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
uint8_t v_x_1657__boxed_3588_; lean_object* v_res_3589_; 
v_x_1657__boxed_3588_ = lean_unbox(v_x_3580_);
v_res_3589_ = l_Lake_Package_afterBuildCacheSync___redArg___lam__0(v_build_3579_, v_x_1657__boxed_3588_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec(v___y_3582_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg(lean_object* v_self_3590_, lean_object* v_build_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v_wsIdx_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; lean_object* v___x_3602_; 
v_wsIdx_3599_ = lean_ctor_get(v_self_3590_, 0);
v___x_3600_ = lean_unsigned_to_nat(0u);
v___x_3601_ = lean_nat_dec_eq(v_wsIdx_3599_, v___x_3600_);
v___x_3602_ = lean_box(0);
if (v___x_3601_ == 0)
{
lean_object* v___f_3603_; lean_object* v___x_3604_; 
v___f_3603_ = lean_alloc_closure((void*)(l_Lake_Package_afterBuildCacheSync___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3603_, 0, v_build_3591_);
lean_inc_ref(v_a_3592_);
v___x_3604_ = l___private_Lake_Build_Package_0__Lake_Package_maybeFetchBuildCache(v_self_3590_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3615_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
v_a_3606_ = lean_ctor_get(v___x_3604_, 1);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3608_ = v___x_3604_;
v_isShared_3609_ = v_isSharedCheck_3615_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_inc(v_a_3605_);
lean_dec(v___x_3604_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3615_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3610_ = lean_obj_once(&l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3, &l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3_once, _init_l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__3);
v___x_3611_ = l_Lake_Job_mapM___redArg(v___x_3602_, v_a_3605_, v___f_3603_, v___x_3600_, v___x_3601_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v___x_3610_);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 0, v___x_3611_);
v___x_3613_ = v___x_3608_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3614_, 1, v_a_3606_);
v___x_3613_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
return v___x_3613_;
}
}
}
else
{
lean_object* v_a_3616_; lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec_ref(v___f_3603_);
lean_dec_ref(v_a_3592_);
v_a_3616_ = lean_ctor_get(v___x_3604_, 0);
v_a_3617_ = lean_ctor_get(v___x_3604_, 1);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3604_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_inc(v_a_3616_);
lean_dec(v___x_3604_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3616_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
else
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
lean_dec_ref(v_self_3590_);
v___x_3625_ = ((lean_object*)(l___private_Lake_Build_Package_0__Lake_Package_recFetchDeps___redArg___closed__1));
v___x_3626_ = l_Lake_Job_async___redArg(v___x_3602_, v_build_3591_, v___x_3600_, v___x_3625_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_);
v___x_3627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3626_);
lean_ctor_set(v___x_3627_, 1, v_a_3597_);
return v___x_3627_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___redArg___boxed(lean_object* v_self_3628_, lean_object* v_build_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3628_, v_build_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_);
lean_dec_ref(v_a_3634_);
lean_dec(v_a_3633_);
lean_dec(v_a_3632_);
lean_dec(v_a_3631_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync(lean_object* v_00_u03b1_3638_, lean_object* v_self_3639_, lean_object* v_build_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = l_Lake_Package_afterBuildCacheSync___redArg(v_self_3639_, v_build_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lake_Package_afterBuildCacheSync___boxed(lean_object* v_00_u03b1_3649_, lean_object* v_self_3650_, lean_object* v_build_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_Lake_Package_afterBuildCacheSync(v_00_u03b1_3649_, v_self_3650_, v_build_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_);
lean_dec_ref(v_a_3656_);
lean_dec(v_a_3655_);
lean_dec(v_a_3654_);
lean_dec(v_a_3653_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(lean_object* v_k_3660_, lean_object* v_v_3661_, lean_object* v_t_3662_){
_start:
{
if (lean_obj_tag(v_t_3662_) == 0)
{
lean_object* v_size_3663_; lean_object* v_k_3664_; lean_object* v_v_3665_; lean_object* v_l_3666_; lean_object* v_r_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3947_; 
v_size_3663_ = lean_ctor_get(v_t_3662_, 0);
v_k_3664_ = lean_ctor_get(v_t_3662_, 1);
v_v_3665_ = lean_ctor_get(v_t_3662_, 2);
v_l_3666_ = lean_ctor_get(v_t_3662_, 3);
v_r_3667_ = lean_ctor_get(v_t_3662_, 4);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_t_3662_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3669_ = v_t_3662_;
v_isShared_3670_ = v_isSharedCheck_3947_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_r_3667_);
lean_inc(v_l_3666_);
lean_inc(v_v_3665_);
lean_inc(v_k_3664_);
lean_inc(v_size_3663_);
lean_dec(v_t_3662_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3947_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
uint8_t v___x_3671_; 
v___x_3671_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3660_, v_k_3664_);
switch(v___x_3671_)
{
case 0:
{
lean_object* v_impl_3672_; lean_object* v___x_3673_; 
lean_dec(v_size_3663_);
v_impl_3672_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3660_, v_v_3661_, v_l_3666_);
v___x_3673_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_3667_) == 0)
{
lean_object* v_size_3674_; lean_object* v_size_3675_; lean_object* v_k_3676_; lean_object* v_v_3677_; lean_object* v_l_3678_; lean_object* v_r_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
v_size_3674_ = lean_ctor_get(v_r_3667_, 0);
v_size_3675_ = lean_ctor_get(v_impl_3672_, 0);
v_k_3676_ = lean_ctor_get(v_impl_3672_, 1);
v_v_3677_ = lean_ctor_get(v_impl_3672_, 2);
v_l_3678_ = lean_ctor_get(v_impl_3672_, 3);
v_r_3679_ = lean_ctor_get(v_impl_3672_, 4);
lean_inc(v_r_3679_);
v___x_3680_ = lean_unsigned_to_nat(3u);
v___x_3681_ = lean_nat_mul(v___x_3680_, v_size_3674_);
v___x_3682_ = lean_nat_dec_lt(v___x_3681_, v_size_3675_);
lean_dec(v___x_3681_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3686_; 
lean_dec(v_r_3679_);
v___x_3683_ = lean_nat_add(v___x_3673_, v_size_3675_);
v___x_3684_ = lean_nat_add(v___x_3683_, v_size_3674_);
lean_dec(v___x_3683_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 3, v_impl_3672_);
lean_ctor_set(v___x_3669_, 0, v___x_3684_);
v___x_3686_ = v___x_3669_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3684_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_k_3664_);
lean_ctor_set(v_reuseFailAlloc_3687_, 2, v_v_3665_);
lean_ctor_set(v_reuseFailAlloc_3687_, 3, v_impl_3672_);
lean_ctor_set(v_reuseFailAlloc_3687_, 4, v_r_3667_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
else
{
lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3753_; 
lean_inc(v_l_3678_);
lean_inc(v_v_3677_);
lean_inc(v_k_3676_);
lean_inc(v_size_3675_);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_impl_3672_);
if (v_isSharedCheck_3753_ == 0)
{
lean_object* v_unused_3754_; lean_object* v_unused_3755_; lean_object* v_unused_3756_; lean_object* v_unused_3757_; lean_object* v_unused_3758_; 
v_unused_3754_ = lean_ctor_get(v_impl_3672_, 4);
lean_dec(v_unused_3754_);
v_unused_3755_ = lean_ctor_get(v_impl_3672_, 3);
lean_dec(v_unused_3755_);
v_unused_3756_ = lean_ctor_get(v_impl_3672_, 2);
lean_dec(v_unused_3756_);
v_unused_3757_ = lean_ctor_get(v_impl_3672_, 1);
lean_dec(v_unused_3757_);
v_unused_3758_ = lean_ctor_get(v_impl_3672_, 0);
lean_dec(v_unused_3758_);
v___x_3689_ = v_impl_3672_;
v_isShared_3690_ = v_isSharedCheck_3753_;
goto v_resetjp_3688_;
}
else
{
lean_dec(v_impl_3672_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3753_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v_size_3691_; lean_object* v_size_3692_; lean_object* v_k_3693_; lean_object* v_v_3694_; lean_object* v_l_3695_; lean_object* v_r_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; uint8_t v___x_3699_; 
v_size_3691_ = lean_ctor_get(v_l_3678_, 0);
v_size_3692_ = lean_ctor_get(v_r_3679_, 0);
v_k_3693_ = lean_ctor_get(v_r_3679_, 1);
v_v_3694_ = lean_ctor_get(v_r_3679_, 2);
v_l_3695_ = lean_ctor_get(v_r_3679_, 3);
v_r_3696_ = lean_ctor_get(v_r_3679_, 4);
v___x_3697_ = lean_unsigned_to_nat(2u);
v___x_3698_ = lean_nat_mul(v___x_3697_, v_size_3691_);
v___x_3699_ = lean_nat_dec_lt(v_size_3692_, v___x_3698_);
lean_dec(v___x_3698_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3728_; 
lean_inc(v_r_3696_);
lean_inc(v_l_3695_);
lean_inc(v_v_3694_);
lean_inc(v_k_3693_);
v_isSharedCheck_3728_ = !lean_is_exclusive(v_r_3679_);
if (v_isSharedCheck_3728_ == 0)
{
lean_object* v_unused_3729_; lean_object* v_unused_3730_; lean_object* v_unused_3731_; lean_object* v_unused_3732_; lean_object* v_unused_3733_; 
v_unused_3729_ = lean_ctor_get(v_r_3679_, 4);
lean_dec(v_unused_3729_);
v_unused_3730_ = lean_ctor_get(v_r_3679_, 3);
lean_dec(v_unused_3730_);
v_unused_3731_ = lean_ctor_get(v_r_3679_, 2);
lean_dec(v_unused_3731_);
v_unused_3732_ = lean_ctor_get(v_r_3679_, 1);
lean_dec(v_unused_3732_);
v_unused_3733_ = lean_ctor_get(v_r_3679_, 0);
lean_dec(v_unused_3733_);
v___x_3701_ = v_r_3679_;
v_isShared_3702_ = v_isSharedCheck_3728_;
goto v_resetjp_3700_;
}
else
{
lean_dec(v_r_3679_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3728_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___x_3716_; lean_object* v___y_3718_; 
v___x_3703_ = lean_nat_add(v___x_3673_, v_size_3675_);
lean_dec(v_size_3675_);
v___x_3704_ = lean_nat_add(v___x_3703_, v_size_3674_);
lean_dec(v___x_3703_);
v___x_3716_ = lean_nat_add(v___x_3673_, v_size_3691_);
if (lean_obj_tag(v_l_3695_) == 0)
{
lean_object* v_size_3726_; 
v_size_3726_ = lean_ctor_get(v_l_3695_, 0);
lean_inc(v_size_3726_);
v___y_3718_ = v_size_3726_;
goto v___jp_3717_;
}
else
{
lean_object* v___x_3727_; 
v___x_3727_ = lean_unsigned_to_nat(0u);
v___y_3718_ = v___x_3727_;
goto v___jp_3717_;
}
v___jp_3705_:
{
lean_object* v___x_3709_; lean_object* v___x_3711_; 
v___x_3709_ = lean_nat_add(v___y_3707_, v___y_3708_);
lean_dec(v___y_3708_);
lean_dec(v___y_3707_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 4, v_r_3667_);
lean_ctor_set(v___x_3701_, 3, v_r_3696_);
lean_ctor_set(v___x_3701_, 2, v_v_3665_);
lean_ctor_set(v___x_3701_, 1, v_k_3664_);
lean_ctor_set(v___x_3701_, 0, v___x_3709_);
v___x_3711_ = v___x_3701_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v___x_3709_);
lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_k_3664_);
lean_ctor_set(v_reuseFailAlloc_3715_, 2, v_v_3665_);
lean_ctor_set(v_reuseFailAlloc_3715_, 3, v_r_3696_);
lean_ctor_set(v_reuseFailAlloc_3715_, 4, v_r_3667_);
v___x_3711_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
lean_object* v___x_3713_; 
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 4, v___x_3711_);
lean_ctor_set(v___x_3689_, 3, v___y_3706_);
lean_ctor_set(v___x_3689_, 2, v_v_3694_);
lean_ctor_set(v___x_3689_, 1, v_k_3693_);
lean_ctor_set(v___x_3689_, 0, v___x_3704_);
v___x_3713_ = v___x_3689_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3714_, 1, v_k_3693_);
lean_ctor_set(v_reuseFailAlloc_3714_, 2, v_v_3694_);
lean_ctor_set(v_reuseFailAlloc_3714_, 3, v___y_3706_);
lean_ctor_set(v_reuseFailAlloc_3714_, 4, v___x_3711_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
v___jp_3717_:
{
lean_object* v___x_3719_; lean_object* v___x_3721_; 
v___x_3719_ = lean_nat_add(v___x_3716_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec(v___x_3716_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 4, v_l_3695_);
lean_ctor_set(v___x_3669_, 3, v_l_3678_);
lean_ctor_set(v___x_3669_, 2, v_v_3677_);
lean_ctor_set(v___x_3669_, 1, v_k_3676_);
lean_ctor_set(v___x_3669_, 0, v___x_3719_);
v___x_3721_ = v___x_3669_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v_k_3676_);
lean_ctor_set(v_reuseFailAlloc_3725_, 2, v_v_3677_);
lean_ctor_set(v_reuseFailAlloc_3725_, 3, v_l_3678_);
lean_ctor_set(v_reuseFailAlloc_3725_, 4, v_l_3695_);
v___x_3721_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; 
v___x_3722_ = lean_nat_add(v___x_3673_, v_size_3674_);
if (lean_obj_tag(v_r_3696_) == 0)
{
lean_object* v_size_3723_; 
v_size_3723_ = lean_ctor_get(v_r_3696_, 0);
lean_inc(v_size_3723_);
v___y_3706_ = v___x_3721_;
v___y_3707_ = v___x_3722_;
v___y_3708_ = v_size_3723_;
goto v___jp_3705_;
}
else
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_unsigned_to_nat(0u);
v___y_3706_ = v___x_3721_;
v___y_3707_ = v___x_3722_;
v___y_3708_ = v___x_3724_;
goto v___jp_3705_;
}
}
}
}
}
else
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3739_; 
lean_del_object(v___x_3669_);
v___x_3734_ = lean_nat_add(v___x_3673_, v_size_3675_);
lean_dec(v_size_3675_);
v___x_3735_ = lean_nat_add(v___x_3734_, v_size_3674_);
lean_dec(v___x_3734_);
v___x_3736_ = lean_nat_add(v___x_3673_, v_size_3674_);
v___x_3737_ = lean_nat_add(v___x_3736_, v_size_3692_);
lean_dec(v___x_3736_);
lean_inc_ref(v_r_3667_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 4, v_r_3667_);
lean_ctor_set(v___x_3689_, 3, v_r_3679_);
lean_ctor_set(v___x_3689_, 2, v_v_3665_);
lean_ctor_set(v___x_3689_, 1, v_k_3664_);
lean_ctor_set(v___x_3689_, 0, v___x_3737_);
v___x_3739_ = v___x_3689_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_k_3664_);
lean_ctor_set(v_reuseFailAlloc_3752_, 2, v_v_3665_);
lean_ctor_set(v_reuseFailAlloc_3752_, 3, v_r_3679_);
lean_ctor_set(v_reuseFailAlloc_3752_, 4, v_r_3667_);
v___x_3739_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
v_isSharedCheck_3746_ = !lean_is_exclusive(v_r_3667_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; lean_object* v_unused_3748_; lean_object* v_unused_3749_; lean_object* v_unused_3750_; lean_object* v_unused_3751_; 
v_unused_3747_ = lean_ctor_get(v_r_3667_, 4);
lean_dec(v_unused_3747_);
v_unused_3748_ = lean_ctor_get(v_r_3667_, 3);
lean_dec(v_unused_3748_);
v_unused_3749_ = lean_ctor_get(v_r_3667_, 2);
lean_dec(v_unused_3749_);
v_unused_3750_ = lean_ctor_get(v_r_3667_, 1);
lean_dec(v_unused_3750_);
v_unused_3751_ = lean_ctor_get(v_r_3667_, 0);
lean_dec(v_unused_3751_);
v___x_3741_ = v_r_3667_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_dec(v_r_3667_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 4, v___x_3739_);
lean_ctor_set(v___x_3741_, 3, v_l_3678_);
lean_ctor_set(v___x_3741_, 2, v_v_3677_);
lean_ctor_set(v___x_3741_, 1, v_k_3676_);
lean_ctor_set(v___x_3741_, 0, v___x_3735_);
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3735_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v_k_3676_);
lean_ctor_set(v_reuseFailAlloc_3745_, 2, v_v_3677_);
lean_ctor_set(v_reuseFailAlloc_3745_, 3, v_l_3678_);
lean_ctor_set(v_reuseFailAlloc_3745_, 4, v___x_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3759_; 
v_l_3759_ = lean_ctor_get(v_impl_3672_, 3);
if (lean_obj_tag(v_l_3759_) == 0)
{
lean_object* v_r_3760_; lean_object* v_k_3761_; lean_object* v_v_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3773_; 
lean_inc_ref(v_l_3759_);
v_r_3760_ = lean_ctor_get(v_impl_3672_, 4);
v_k_3761_ = lean_ctor_get(v_impl_3672_, 1);
v_v_3762_ = lean_ctor_get(v_impl_3672_, 2);
v_isSharedCheck_3773_ = !lean_is_exclusive(v_impl_3672_);
if (v_isSharedCheck_3773_ == 0)
{
lean_object* v_unused_3774_; lean_object* v_unused_3775_; 
v_unused_3774_ = lean_ctor_get(v_impl_3672_, 3);
lean_dec(v_unused_3774_);
v_unused_3775_ = lean_ctor_get(v_impl_3672_, 0);
lean_dec(v_unused_3775_);
v___x_3764_ = v_impl_3672_;
v_isShared_3765_ = v_isSharedCheck_3773_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_r_3760_);
lean_inc(v_v_3762_);
lean_inc(v_k_3761_);
lean_dec(v_impl_3672_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3773_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3766_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_3760_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 3, v_r_3760_);
lean_ctor_set(v___x_3764_, 2, v_v_3665_);
lean_ctor_set(v___x_3764_, 1, v_k_3664_);
lean_ctor_set(v___x_3764_, 0, v___x_3673_);
v___x_3768_ = v___x_3764_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3772_, 1, v_k_3664_);
lean_ctor_set(v_reuseFailAlloc_3772_, 2, v_v_3665_);
lean_ctor_set(v_reuseFailAlloc_3772_, 3, v_r_3760_);
lean_ctor_set(v_reuseFailAlloc_3772_, 4, v_r_3760_);
v___x_3768_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
lean_object* v___x_3770_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 4, v___x_3768_);
lean_ctor_set(v___x_3669_, 3, v_l_3759_);
lean_ctor_set(v___x_3669_, 2, v_v_3762_);
lean_ctor_set(v___x_3669_, 1, v_k_3761_);
lean_ctor_set(v___x_3669_, 0, v___x_3766_);
v___x_3770_ = v___x_3669_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3766_);
lean_ctor_set(v_reuseFailAlloc_3771_, 1, v_k_3761_);
lean_ctor_set(v_reuseFailAlloc_3771_, 2, v_v_3762_);
lean_ctor_set(v_reuseFailAlloc_3771_, 3, v_l_3759_);
lean_ctor_set(v_reuseFailAlloc_3771_, 4, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
else
{
lean_object* v_r_3776_; 
v_r_3776_ = lean_ctor_get(v_impl_3672_, 4);
lean_inc(v_r_3776_);
if (lean_obj_tag(v_r_3776_) == 0)
{
lean_object* v_k_3777_; lean_object* v_v_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3801_; 
lean_inc(v_l_3759_);
v_k_3777_ = lean_ctor_get(v_impl_3672_, 1);
v_v_3778_ = lean_ctor_get(v_impl_3672_, 2);
v_isSharedCheck_3801_ = !lean_is_exclusive(v_impl_3672_);
if (v_isSharedCheck_3801_ == 0)
{
lean_object* v_unused_3802_; lean_object* v_unused_3803_; lean_object* v_unused_3804_; 
v_unused_3802_ = lean_ctor_get(v_impl_3672_, 4);
lean_dec(v_unused_3802_);
v_unused_3803_ = lean_ctor_get(v_impl_3672_, 3);
lean_dec(v_unused_3803_);
v_unused_3804_ = lean_ctor_get(v_impl_3672_, 0);
lean_dec(v_unused_3804_);
v___x_3780_ = v_impl_3672_;
v_isShared_3781_ = v_isSharedCheck_3801_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_v_3778_);
lean_inc(v_k_3777_);
lean_dec(v_impl_3672_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3801_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v_k_3782_; lean_object* v_v_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3797_; 
v_k_3782_ = lean_ctor_get(v_r_3776_, 1);
v_v_3783_ = lean_ctor_get(v_r_3776_, 2);
v_isSharedCheck_3797_ = !lean_is_exclusive(v_r_3776_);
if (v_isSharedCheck_3797_ == 0)
{
lean_object* v_unused_3798_; lean_object* v_unused_3799_; lean_object* v_unused_3800_; 
v_unused_3798_ = lean_ctor_get(v_r_3776_, 4);
lean_dec(v_unused_3798_);
v_unused_3799_ = lean_ctor_get(v_r_3776_, 3);
lean_dec(v_unused_3799_);
v_unused_3800_ = lean_ctor_get(v_r_3776_, 0);
lean_dec(v_unused_3800_);
v___x_3785_ = v_r_3776_;
v_isShared_3786_ = v_isSharedCheck_3797_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_v_3783_);
lean_inc(v_k_3782_);
lean_dec(v_r_3776_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3797_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3789_; 
v___x_3787_ = lean_unsigned_to_nat(3u);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 4, v_l_3759_);
lean_ctor_set(v___x_3785_, 3, v_l_3759_);
lean_ctor_set(v___x_3785_, 2, v_v_3778_);
lean_ctor_set(v___x_3785_, 1, v_k_3777_);
lean_ctor_set(v___x_3785_, 0, v___x_3673_);
v___x_3789_ = v___x_3785_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_k_3777_);
lean_ctor_set(v_reuseFailAlloc_3796_, 2, v_v_3778_);
lean_ctor_set(v_reuseFailAlloc_3796_, 3, v_l_3759_);
lean_ctor_set(v_reuseFailAlloc_3796_, 4, v_l_3759_);
v___x_3789_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
lean_object* v___x_3791_; 
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 4, v_l_3759_);
lean_ctor_set(v___x_3780_, 2, v_v_3665_);
lean_ctor_set(v___x_3780_, 1, v_k_3664_);
lean_ctor_set(v___x_3780_, 0, v___x_3673_);
v___x_3791_ = v___x_3780_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v_k_3664_);
lean_ctor_set(v_reuseFailAlloc_3795_, 2, v_v_3665_);
lean_ctor_set(v_reuseFailAlloc_3795_, 3, v_l_3759_);
lean_ctor_set(v_reuseFailAlloc_3795_, 4, v_l_3759_);
v___x_3791_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
lean_object* v___x_3793_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 4, v___x_3791_);
lean_ctor_set(v___x_3669_, 3, v___x_3789_);
lean_ctor_set(v___x_3669_, 2, v_v_3783_);
lean_ctor_set(v___x_3669_, 1, v_k_3782_);
lean_ctor_set(v___x_3669_, 0, v___x_3787_);
v___x_3793_ = v___x_3669_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3787_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_k_3782_);
lean_ctor_set(v_reuseFailAlloc_3794_, 2, v_v_3783_);
lean_ctor_set(v_reuseFailAlloc_3794_, 3, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3794_, 4, v___x_3791_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
}
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3807_; 
v___x_3805_ = lean_unsigned_to_nat(2u);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 4, v_r_3776_);
lean_ctor_set(v___x_3669_, 3, v_impl_3672_);
lean_ctor_set(v___x_3669_, 0, v___x_3805_);
v___x_3807_ = v___x_3669_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3805_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_k_3664_);
lean_ctor_set(v_reuseFailAlloc_3808_, 2, v_v_3665_);
lean_ctor_set(v_reuseFailAlloc_3808_, 3, v_impl_3672_);
lean_ctor_set(v_reuseFailAlloc_3808_, 4, v_r_3776_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
case 1:
{
lean_object* v___x_3810_; 
lean_dec(v_v_3665_);
lean_dec(v_k_3664_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 2, v_v_3661_);
lean_ctor_set(v___x_3669_, 1, v_k_3660_);
v___x_3810_ = v___x_3669_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_size_3663_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v_k_3660_);
lean_ctor_set(v_reuseFailAlloc_3811_, 2, v_v_3661_);
lean_ctor_set(v_reuseFailAlloc_3811_, 3, v_l_3666_);
lean_ctor_set(v_reuseFailAlloc_3811_, 4, v_r_3667_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
default: 
{
lean_object* v_impl_3812_; lean_object* v___x_3813_; 
lean_dec(v_size_3663_);
v_impl_3812_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3660_, v_v_3661_, v_r_3667_);
v___x_3813_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_3666_) == 0)
{
lean_object* v_size_3814_; lean_object* v_size_3815_; lean_object* v_k_3816_; lean_object* v_v_3817_; lean_object* v_l_3818_; lean_object* v_r_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
v_size_3814_ = lean_ctor_get(v_l_3666_, 0);
v_size_3815_ = lean_ctor_get(v_impl_3812_, 0);
v_k_3816_ = lean_ctor_get(v_impl_3812_, 1);
v_v_3817_ = lean_ctor_get(v_impl_3812_, 2);
v_l_3818_ = lean_ctor_get(v_impl_3812_, 3);
lean_inc(v_l_3818_);
v_r_3819_ = lean_ctor_get(v_impl_3812_, 4);
v___x_3820_ = lean_unsigned_to_nat(3u);
v___x_3821_ = lean_nat_mul(v___x_3820_, v_size_3814_);
v___x_3822_ = lean_nat_dec_lt(v___x_3821_, v_size_3815_);
lean_dec(v___x_3821_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
lean_dec(v_l_3818_);
v___x_3823_ = lean_nat_add(v___x_3813_, v_size_3814_);
v___x_3824_ = lean_nat_add(v___x_3823_, v_size_3815_);
lean_dec(v___x_3823_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 4, v_impl_3812_);
lean_ctor_set(v___x_3669_, 0, v___x_3824_);
v___x_3826_ = v___x_3669_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3827_, 1, v_k_3664_);
lean_ctor_set(v_reuseFailAlloc_3827_, 2, v_v_3665_);
lean_ctor_set(v_reuseFailAlloc_3827_, 3, v_l_3666_);
lean_ctor_set(v_reuseFailAlloc_3827_, 4, v_impl_3812_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
else
{
lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3891_; 
lean_inc(v_r_3819_);
lean_inc(v_v_3817_);
lean_inc(v_k_3816_);
lean_inc(v_size_3815_);
v_isSharedCheck_3891_ = !lean_is_exclusive(v_impl_3812_);
if (v_isSharedCheck_3891_ == 0)
{
lean_object* v_unused_3892_; lean_object* v_unused_3893_; lean_object* v_unused_3894_; lean_object* v_unused_3895_; lean_object* v_unused_3896_; 
v_unused_3892_ = lean_ctor_get(v_impl_3812_, 4);
lean_dec(v_unused_3892_);
v_unused_3893_ = lean_ctor_get(v_impl_3812_, 3);
lean_dec(v_unused_3893_);
v_unused_3894_ = lean_ctor_get(v_impl_3812_, 2);
lean_dec(v_unused_3894_);
v_unused_3895_ = lean_ctor_get(v_impl_3812_, 1);
lean_dec(v_unused_3895_);
v_unused_3896_ = lean_ctor_get(v_impl_3812_, 0);
lean_dec(v_unused_3896_);
v___x_3829_ = v_impl_3812_;
v_isShared_3830_ = v_isSharedCheck_3891_;
goto v_resetjp_3828_;
}
else
{
lean_dec(v_impl_3812_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3891_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v_size_3831_; lean_object* v_k_3832_; lean_object* v_v_3833_; lean_object* v_l_3834_; lean_object* v_r_3835_; lean_object* v_size_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; uint8_t v___x_3839_; 
v_size_3831_ = lean_ctor_get(v_l_3818_, 0);
v_k_3832_ = lean_ctor_get(v_l_3818_, 1);
v_v_3833_ = lean_ctor_get(v_l_3818_, 2);
v_l_3834_ = lean_ctor_get(v_l_3818_, 3);
v_r_3835_ = lean_ctor_get(v_l_3818_, 4);
v_size_3836_ = lean_ctor_get(v_r_3819_, 0);
v___x_3837_ = lean_unsigned_to_nat(2u);
v___x_3838_ = lean_nat_mul(v___x_3837_, v_size_3836_);
v___x_3839_ = lean_nat_dec_lt(v_size_3831_, v___x_3838_);
lean_dec(v___x_3838_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3867_; 
lean_inc(v_r_3835_);
lean_inc(v_l_3834_);
lean_inc(v_v_3833_);
lean_inc(v_k_3832_);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_l_3818_);
if (v_isSharedCheck_3867_ == 0)
{
lean_object* v_unused_3868_; lean_object* v_unused_3869_; lean_object* v_unused_3870_; lean_object* v_unused_3871_; lean_object* v_unused_3872_; 
v_unused_3868_ = lean_ctor_get(v_l_3818_, 4);
lean_dec(v_unused_3868_);
v_unused_3869_ = lean_ctor_get(v_l_3818_, 3);
lean_dec(v_unused_3869_);
v_unused_3870_ = lean_ctor_get(v_l_3818_, 2);
lean_dec(v_unused_3870_);
v_unused_3871_ = lean_ctor_get(v_l_3818_, 1);
lean_dec(v_unused_3871_);
v_unused_3872_ = lean_ctor_get(v_l_3818_, 0);
lean_dec(v_unused_3872_);
v___x_3841_ = v_l_3818_;
v_isShared_3842_ = v_isSharedCheck_3867_;
goto v_resetjp_3840_;
}
else
{
lean_dec(v_l_3818_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3867_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3857_; 
v___x_3843_ = lean_nat_add(v___x_3813_, v_size_3814_);
v___x_3844_ = lean_nat_add(v___x_3843_, v_size_3815_);
lean_dec(v_size_3815_);
if (lean_obj_tag(v_l_3834_) == 0)
{
lean_object* v_size_3865_; 
v_size_3865_ = lean_ctor_get(v_l_3834_, 0);
lean_inc(v_size_3865_);
v___y_3857_ = v_size_3865_;
goto v___jp_3856_;
}
else
{
lean_object* v___x_3866_; 
v___x_3866_ = lean_unsigned_to_nat(0u);
v___y_3857_ = v___x_3866_;
goto v___jp_3856_;
}
v___jp_3845_:
{
lean_object* v___x_3849_; lean_object* v___x_3851_; 
v___x_3849_ = lean_nat_add(v___y_3846_, v___y_3848_);
lean_dec(v___y_3848_);
lean_dec(v___y_3846_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 4, v_r_3819_);
lean_ctor_set(v___x_3841_, 3, v_r_3835_);
lean_ctor_set(v___x_3841_, 2, v_v_3817_);
lean_ctor_set(v___x_3841_, 1, v_k_3816_);
lean_ctor_set(v___x_3841_, 0, v___x_3849_);
v___x_3851_ = v___x_3841_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3849_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v_k_3816_);
lean_ctor_set(v_reuseFailAlloc_3855_, 2, v_v_3817_);
lean_ctor_set(v_reuseFailAlloc_3855_, 3, v_r_3835_);
lean_ctor_set(v_reuseFailAlloc_3855_, 4, v_r_3819_);
v___x_3851_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
lean_object* v___x_3853_; 
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 4, v___x_3851_);
lean_ctor_set(v___x_3829_, 3, v___y_3847_);
lean_ctor_set(v___x_3829_, 2, v_v_3833_);
lean_ctor_set(v___x_3829_, 1, v_k_3832_);
lean_ctor_set(v___x_3829_, 0, v___x_3844_);
v___x_3853_ = v___x_3829_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3844_);
lean_ctor_set(v_reuseFailAlloc_3854_, 1, v_k_3832_);
lean_ctor_set(v_reuseFailAlloc_3854_, 2, v_v_3833_);
lean_ctor_set(v_reuseFailAlloc_3854_, 3, v___y_3847_);
lean_ctor_set(v_reuseFailAlloc_3854_, 4, v___x_3851_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
v___jp_3856_:
{
lean_object* v___x_3858_; lean_object* v___x_3860_; 
v___x_3858_ = lean_nat_add(v___x_3843_, v___y_3857_);
lean_dec(v___y_3857_);
lean_dec(v___x_3843_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 4, v_l_3834_);
lean_ctor_set(v___x_3669_, 0, v___x_3858_);
v___x_3860_ = v___x_3669_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3864_, 1, v_k_3664_);
lean_ctor_set(v_reuseFailAlloc_3864_, 2, v_v_3665_);
lean_ctor_set(v_reuseFailAlloc_3864_, 3, v_l_3666_);
lean_ctor_set(v_reuseFailAlloc_3864_, 4, v_l_3834_);
v___x_3860_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_nat_add(v___x_3813_, v_size_3836_);
if (lean_obj_tag(v_r_3835_) == 0)
{
lean_object* v_size_3862_; 
v_size_3862_ = lean_ctor_get(v_r_3835_, 0);
lean_inc(v_size_3862_);
v___y_3846_ = v___x_3861_;
v___y_3847_ = v___x_3860_;
v___y_3848_ = v_size_3862_;
goto v___jp_3845_;
}
else
{
lean_object* v___x_3863_; 
v___x_3863_ = lean_unsigned_to_nat(0u);
v___y_3846_ = v___x_3861_;
v___y_3847_ = v___x_3860_;
v___y_3848_ = v___x_3863_;
goto v___jp_3845_;
}
}
}
}
}
else
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3877_; 
lean_del_object(v___x_3669_);
v___x_3873_ = lean_nat_add(v___x_3813_, v_size_3814_);
v___x_3874_ = lean_nat_add(v___x_3873_, v_size_3815_);
lean_dec(v_size_3815_);
v___x_3875_ = lean_nat_add(v___x_3873_, v_size_3831_);
lean_dec(v___x_3873_);
lean_inc_ref(v_l_3666_);
if (v_isShared_3830_ == 0)
{
lean_ctor_set(v___x_3829_, 4, v_l_3818_);
lean_ctor_set(v___x_3829_, 3, v_l_3666_);
lean_ctor_set(v___x_3829_, 2, v_v_3665_);
lean_ctor_set(v___x_3829_, 1, v_k_3664_);
lean_ctor_set(v___x_3829_, 0, v___x_3875_);
v___x_3877_ = v___x_3829_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3875_);
lean_ctor_set(v_reuseFailAlloc_3890_, 1, v_k_3664_);
lean_ctor_set(v_reuseFailAlloc_3890_, 2, v_v_3665_);
lean_ctor_set(v_reuseFailAlloc_3890_, 3, v_l_3666_);
lean_ctor_set(v_reuseFailAlloc_3890_, 4, v_l_3818_);
v___x_3877_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
v_isSharedCheck_3884_ = !lean_is_exclusive(v_l_3666_);
if (v_isSharedCheck_3884_ == 0)
{
lean_object* v_unused_3885_; lean_object* v_unused_3886_; lean_object* v_unused_3887_; lean_object* v_unused_3888_; lean_object* v_unused_3889_; 
v_unused_3885_ = lean_ctor_get(v_l_3666_, 4);
lean_dec(v_unused_3885_);
v_unused_3886_ = lean_ctor_get(v_l_3666_, 3);
lean_dec(v_unused_3886_);
v_unused_3887_ = lean_ctor_get(v_l_3666_, 2);
lean_dec(v_unused_3887_);
v_unused_3888_ = lean_ctor_get(v_l_3666_, 1);
lean_dec(v_unused_3888_);
v_unused_3889_ = lean_ctor_get(v_l_3666_, 0);
lean_dec(v_unused_3889_);
v___x_3879_ = v_l_3666_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_dec(v_l_3666_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 4, v_r_3819_);
lean_ctor_set(v___x_3879_, 3, v___x_3877_);
lean_ctor_set(v___x_3879_, 2, v_v_3817_);
lean_ctor_set(v___x_3879_, 1, v_k_3816_);
lean_ctor_set(v___x_3879_, 0, v___x_3874_);
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3874_);
lean_ctor_set(v_reuseFailAlloc_3883_, 1, v_k_3816_);
lean_ctor_set(v_reuseFailAlloc_3883_, 2, v_v_3817_);
lean_ctor_set(v_reuseFailAlloc_3883_, 3, v___x_3877_);
lean_ctor_set(v_reuseFailAlloc_3883_, 4, v_r_3819_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_3897_; 
v_l_3897_ = lean_ctor_get(v_impl_3812_, 3);
lean_inc(v_l_3897_);
if (lean_obj_tag(v_l_3897_) == 0)
{
lean_object* v_r_3898_; lean_object* v_k_3899_; lean_object* v_v_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3923_; 
v_r_3898_ = lean_ctor_get(v_impl_3812_, 4);
v_k_3899_ = lean_ctor_get(v_impl_3812_, 1);
v_v_3900_ = lean_ctor_get(v_impl_3812_, 2);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_impl_3812_);
if (v_isSharedCheck_3923_ == 0)
{
lean_object* v_unused_3924_; lean_object* v_unused_3925_; 
v_unused_3924_ = lean_ctor_get(v_impl_3812_, 3);
lean_dec(v_unused_3924_);
v_unused_3925_ = lean_ctor_get(v_impl_3812_, 0);
lean_dec(v_unused_3925_);
v___x_3902_ = v_impl_3812_;
v_isShared_3903_ = v_isSharedCheck_3923_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_r_3898_);
lean_inc(v_v_3900_);
lean_inc(v_k_3899_);
lean_dec(v_impl_3812_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3923_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v_k_3904_; lean_object* v_v_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3919_; 
v_k_3904_ = lean_ctor_get(v_l_3897_, 1);
v_v_3905_ = lean_ctor_get(v_l_3897_, 2);
v_isSharedCheck_3919_ = !lean_is_exclusive(v_l_3897_);
if (v_isSharedCheck_3919_ == 0)
{
lean_object* v_unused_3920_; lean_object* v_unused_3921_; lean_object* v_unused_3922_; 
v_unused_3920_ = lean_ctor_get(v_l_3897_, 4);
lean_dec(v_unused_3920_);
v_unused_3921_ = lean_ctor_get(v_l_3897_, 3);
lean_dec(v_unused_3921_);
v_unused_3922_ = lean_ctor_get(v_l_3897_, 0);
lean_dec(v_unused_3922_);
v___x_3907_ = v_l_3897_;
v_isShared_3908_ = v_isSharedCheck_3919_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_v_3905_);
lean_inc(v_k_3904_);
lean_dec(v_l_3897_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3919_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3909_; lean_object* v___x_3911_; 
v___x_3909_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_3898_, 2);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 4, v_r_3898_);
lean_ctor_set(v___x_3907_, 3, v_r_3898_);
lean_ctor_set(v___x_3907_, 2, v_v_3665_);
lean_ctor_set(v___x_3907_, 1, v_k_3664_);
lean_ctor_set(v___x_3907_, 0, v___x_3813_);
v___x_3911_ = v___x_3907_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3918_, 1, v_k_3664_);
lean_ctor_set(v_reuseFailAlloc_3918_, 2, v_v_3665_);
lean_ctor_set(v_reuseFailAlloc_3918_, 3, v_r_3898_);
lean_ctor_set(v_reuseFailAlloc_3918_, 4, v_r_3898_);
v___x_3911_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
lean_object* v___x_3913_; 
lean_inc(v_r_3898_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 3, v_r_3898_);
lean_ctor_set(v___x_3902_, 0, v___x_3813_);
v___x_3913_ = v___x_3902_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3917_, 1, v_k_3899_);
lean_ctor_set(v_reuseFailAlloc_3917_, 2, v_v_3900_);
lean_ctor_set(v_reuseFailAlloc_3917_, 3, v_r_3898_);
lean_ctor_set(v_reuseFailAlloc_3917_, 4, v_r_3898_);
v___x_3913_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3915_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 4, v___x_3913_);
lean_ctor_set(v___x_3669_, 3, v___x_3911_);
lean_ctor_set(v___x_3669_, 2, v_v_3905_);
lean_ctor_set(v___x_3669_, 1, v_k_3904_);
lean_ctor_set(v___x_3669_, 0, v___x_3909_);
v___x_3915_ = v___x_3669_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3909_);
lean_ctor_set(v_reuseFailAlloc_3916_, 1, v_k_3904_);
lean_ctor_set(v_reuseFailAlloc_3916_, 2, v_v_3905_);
lean_ctor_set(v_reuseFailAlloc_3916_, 3, v___x_3911_);
lean_ctor_set(v_reuseFailAlloc_3916_, 4, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
}
}
else
{
lean_object* v_r_3926_; 
v_r_3926_ = lean_ctor_get(v_impl_3812_, 4);
lean_inc(v_r_3926_);
if (lean_obj_tag(v_r_3926_) == 0)
{
lean_object* v_k_3927_; lean_object* v_v_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3939_; 
v_k_3927_ = lean_ctor_get(v_impl_3812_, 1);
v_v_3928_ = lean_ctor_get(v_impl_3812_, 2);
v_isSharedCheck_3939_ = !lean_is_exclusive(v_impl_3812_);
if (v_isSharedCheck_3939_ == 0)
{
lean_object* v_unused_3940_; lean_object* v_unused_3941_; lean_object* v_unused_3942_; 
v_unused_3940_ = lean_ctor_get(v_impl_3812_, 4);
lean_dec(v_unused_3940_);
v_unused_3941_ = lean_ctor_get(v_impl_3812_, 3);
lean_dec(v_unused_3941_);
v_unused_3942_ = lean_ctor_get(v_impl_3812_, 0);
lean_dec(v_unused_3942_);
v___x_3930_ = v_impl_3812_;
v_isShared_3931_ = v_isSharedCheck_3939_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_v_3928_);
lean_inc(v_k_3927_);
lean_dec(v_impl_3812_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3939_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3932_; lean_object* v___x_3934_; 
v___x_3932_ = lean_unsigned_to_nat(3u);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 4, v_l_3897_);
lean_ctor_set(v___x_3930_, 2, v_v_3665_);
lean_ctor_set(v___x_3930_, 1, v_k_3664_);
lean_ctor_set(v___x_3930_, 0, v___x_3813_);
v___x_3934_ = v___x_3930_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3813_);
lean_ctor_set(v_reuseFailAlloc_3938_, 1, v_k_3664_);
lean_ctor_set(v_reuseFailAlloc_3938_, 2, v_v_3665_);
lean_ctor_set(v_reuseFailAlloc_3938_, 3, v_l_3897_);
lean_ctor_set(v_reuseFailAlloc_3938_, 4, v_l_3897_);
v___x_3934_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3936_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 4, v_r_3926_);
lean_ctor_set(v___x_3669_, 3, v___x_3934_);
lean_ctor_set(v___x_3669_, 2, v_v_3928_);
lean_ctor_set(v___x_3669_, 1, v_k_3927_);
lean_ctor_set(v___x_3669_, 0, v___x_3932_);
v___x_3936_ = v___x_3669_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_k_3927_);
lean_ctor_set(v_reuseFailAlloc_3937_, 2, v_v_3928_);
lean_ctor_set(v_reuseFailAlloc_3937_, 3, v___x_3934_);
lean_ctor_set(v_reuseFailAlloc_3937_, 4, v_r_3926_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
else
{
lean_object* v___x_3943_; lean_object* v___x_3945_; 
v___x_3943_ = lean_unsigned_to_nat(2u);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 4, v_impl_3812_);
lean_ctor_set(v___x_3669_, 3, v_r_3926_);
lean_ctor_set(v___x_3669_, 0, v___x_3943_);
v___x_3945_ = v___x_3669_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3943_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_k_3664_);
lean_ctor_set(v_reuseFailAlloc_3946_, 2, v_v_3665_);
lean_ctor_set(v_reuseFailAlloc_3946_, 3, v_r_3926_);
lean_ctor_set(v_reuseFailAlloc_3946_, 4, v_impl_3812_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
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
lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3948_ = lean_unsigned_to_nat(1u);
v___x_3949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
lean_ctor_set(v___x_3949_, 1, v_k_3660_);
lean_ctor_set(v___x_3949_, 2, v_v_3661_);
lean_ctor_set(v___x_3949_, 3, v_t_3662_);
lean_ctor_set(v___x_3949_, 4, v_t_3662_);
return v___x_3949_;
}
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3950_ = lean_box(1);
v___x_3951_ = l_Lake_Package_depsFacetConfig;
v___x_3952_ = l_Lake_Package_depsFacet;
v___x_3953_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3952_, v___x_3951_, v___x_3950_);
return v___x_3953_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3954_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__0, &l_Lake_Package_initFacetConfigs___closed__0_once, _init_l_Lake_Package_initFacetConfigs___closed__0);
v___x_3955_ = l_Lake_Package_transDepsFacetConfig;
v___x_3956_ = l_Lake_Package_transDepsFacet;
v___x_3957_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3956_, v___x_3955_, v___x_3954_);
return v___x_3957_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3958_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__1, &l_Lake_Package_initFacetConfigs___closed__1_once, _init_l_Lake_Package_initFacetConfigs___closed__1);
v___x_3959_ = l_Lake_Package_defaultModulesFacetConfig;
v___x_3960_ = l_Lake_Package_defaultModulesFacet;
v___x_3961_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3960_, v___x_3959_, v___x_3958_);
return v___x_3961_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3962_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__2, &l_Lake_Package_initFacetConfigs___closed__2_once, _init_l_Lake_Package_initFacetConfigs___closed__2);
v___x_3963_ = l_Lake_Package_extraDepFacetConfig;
v___x_3964_ = l_Lake_Package_extraDepFacet;
v___x_3965_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3964_, v___x_3963_, v___x_3962_);
return v___x_3965_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3966_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__3, &l_Lake_Package_initFacetConfigs___closed__3_once, _init_l_Lake_Package_initFacetConfigs___closed__3);
v___x_3967_ = l_Lake_Package_optBuildCacheFacetConfig;
v___x_3968_ = l_Lake_Package_optBuildCacheFacet;
v___x_3969_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3968_, v___x_3967_, v___x_3966_);
return v___x_3969_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3970_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__4, &l_Lake_Package_initFacetConfigs___closed__4_once, _init_l_Lake_Package_initFacetConfigs___closed__4);
v___x_3971_ = l_Lake_Package_buildCacheFacetConfig;
v___x_3972_ = l_Lake_Package_buildCacheFacet;
v___x_3973_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3972_, v___x_3971_, v___x_3970_);
return v___x_3973_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3974_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__5, &l_Lake_Package_initFacetConfigs___closed__5_once, _init_l_Lake_Package_initFacetConfigs___closed__5);
v___x_3975_ = l_Lake_Package_optBarrelFacetConfig;
v___x_3976_ = l_Lake_Package_optReservoirBarrelFacet;
v___x_3977_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3976_, v___x_3975_, v___x_3974_);
return v___x_3977_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__7(void){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3978_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__6, &l_Lake_Package_initFacetConfigs___closed__6_once, _init_l_Lake_Package_initFacetConfigs___closed__6);
v___x_3979_ = l_Lake_Package_barrelFacetConfig;
v___x_3980_ = l_Lake_Package_reservoirBarrelFacet;
v___x_3981_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3980_, v___x_3979_, v___x_3978_);
return v___x_3981_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__8(void){
_start:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3982_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__7, &l_Lake_Package_initFacetConfigs___closed__7_once, _init_l_Lake_Package_initFacetConfigs___closed__7);
v___x_3983_ = l_Lake_Package_optGitHubReleaseFacetConfig;
v___x_3984_ = l_Lake_Package_optGitHubReleaseFacet;
v___x_3985_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3984_, v___x_3983_, v___x_3982_);
return v___x_3985_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs___closed__9(void){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3986_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__8, &l_Lake_Package_initFacetConfigs___closed__8_once, _init_l_Lake_Package_initFacetConfigs___closed__8);
v___x_3987_ = l_Lake_Package_gitHubReleaseFacetConfig;
v___x_3988_ = l_Lake_Package_gitHubReleaseFacet;
v___x_3989_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v___x_3988_, v___x_3987_, v___x_3986_);
return v___x_3989_;
}
}
static lean_object* _init_l_Lake_Package_initFacetConfigs(void){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = lean_obj_once(&l_Lake_Package_initFacetConfigs___closed__9, &l_Lake_Package_initFacetConfigs___closed__9_once, _init_l_Lake_Package_initFacetConfigs___closed__9);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0(lean_object* v_00_u03b2_3991_, lean_object* v_k_3992_, lean_object* v_v_3993_, lean_object* v_t_3994_, lean_object* v_hl_3995_){
_start:
{
lean_object* v___x_3996_; 
v___x_3996_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_Package_initFacetConfigs_spec__0___redArg(v_k_3992_, v_v_3993_, v_t_3994_);
return v___x_3996_;
}
}
static lean_object* _init_l_Lake_initPackageFacetConfigs(void){
_start:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Lake_Package_initFacetConfigs;
return v___x_3997_;
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
